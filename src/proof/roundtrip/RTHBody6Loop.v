(* RT-H: inflate()'s main loop from a header machine: the header passes (RTHCase.case_ok6, the
   headless loop state with hd6 in the frame), then Spec5's loop (Body5Loop.loop_part5) from the first machine
   past the header. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.roundtrip.RTHSpec.
Require Import Zlib.proof.roundtrip.RTHCase.
Require Import Zlib.proof.inflate_api.Body5Loop.
Require Import Zlib.proof.roundtrip.RTHModeKit.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* lstateH with the mode loaded into t'133 *)
Definition lstate_tH (F: frame) (X: mpred) (m: mst) : environ -> mpred :=
  PROP (in_ok (f_ib F) (m_inp m); out_ok (f_ob F) (m_aout m))
  LOCAL (temp _t'133 (zv (m_mode m));
         temp _strm (f_strmp F); temp _flush (zv (f_flush F)); temp _state (f_sp F);
         temp _next (in_ptr (f_ib F) (m_nx m)); temp _put (out_ptr (f_ob F) (Zlength (m_ow m)));
         temp _have (zv (m_have m)); temp _left (zv (m_left m)); temp _hold (lv (m_hold m));
         temp _bits (zv (m_bits m)); temp _in (zv (m_in m)); temp _out (zv (m_out m));
         temp _ret (zv (m_ret m)); temp _leave (zv (m_leave m));
         lvar _here t_code (f_vhere F); lvar _last t_code (f_vlast F);
         lvar _hbuf (tarray tuchar 4) (f_vhbuf F); gvars (f_gv F))
  SEP (mem_repH F m; locals_rep F; hdr_tok F m; mem_mgr (f_gv F); zfuncs (f_gv F); X).

Lemma semax_load_modeH {Espec: OracleKind} (F: frame) (X: mpred) (m: mst):
  semax Delta_inflate5 (lstateH F X m) (Sset _t'133 mode_expr) (normal_ret_assert (lstate_tH F X m)).
Proof.
  unfold lstateH, lstate_tH, mode_expr. rewrite !mem_rep_splitH.
  abbreviate_semax.
  Intros.
  forward.
  entailer!.
Qed.

Lemma pre_split6: forall F X m,
  ENTAIL Delta_inflate5, lstate_tH F (X * hd6 F m) m |--
    (loop_stateH F m * (fun _ => hdr_tok F m * hd6 F m)) * fr2 F X.
Proof.
  intros. unfold lstate_tH, loop_stateH, fr2, ret_locals.
  go_lowerx. normalize.
  apply andp_right; [apply prop_right; tauto | cancel].
Qed.

Lemma switch_case6 {Espec: OracleKind} (F: frame) (X: mpred) (m: mst) (n: nat) (i: nat):
  case_ok6 F (HEAD + Z.of_nat i) i -> m_mode m = HEAD + Z.of_nat i -> m_leave m = 0 -> mwf3 m ->
  hd_ok F m -> i_head (m_s m) = true -> hpass (f_flush F) (S n) m ->
  semax Delta_inflate5 (lstate_tH F (X * hd6 F m) m) (seq_of_labeled_statement (ls_drop i inflate_LS))
    (frame_ret_assert (frame_ret_assert (switch_ret_assert (case_post6 F m)) (fun _ => hdr_tok F m))
       (fr2 F X)).
Proof.
  intros H A B C D E G. eapply semax_pre; [apply pre_split6 |].
  apply semax_frame; [apply fr2_closed |].
  apply semax_cases_inflate5. apply (H m n); auto.
Qed.

Lemma semax_switch_step6 {Espec: OracleKind} (F: frame) (X: mpred) (m: mst) (n: nat) (Post: ret_assert):
  cases6_all -> frame_ok5 F -> mwf3 m -> m_leave m = 0 -> hd_ok F m -> i_head (m_s m) = true ->
  hdr_mode (m_mode m) = true -> hpass (f_flush F) (S n) m ->
  ENTAIL Delta_inflate5,
    RA_normal (case_post6 F m) * (fun _ => hdr_tok F m) * fr2 F X |-- RA_normal Post ->
  semax Delta_inflate5 (lstate_tH F (X * hd6 F m) m) (Sswitch (Etempvar _t'133 tint) inflate_LS) Post.
Proof.
  intros HC HF HW HL HD HI HM HP HN.
  assert (HM2: HEAD <= m_mode m <= HCRC).
  { unfold hdr_mode in HM. apply andb_prop in HM. destruct HM as [H1 H2].
    apply Z.leb_le in H1, H2. unfold IM.HEAD, IM.HCRC in *. unfold HEAD, HCRC. lia. }
  set (i := Z.to_nat (m_mode m - HEAD)).
  assert (Hi: m_mode m = HEAD + Z.of_nat i) by (unfold i; rewrite Z2Nat.id; lia).
  assert (Hi8: (i <= 8)%nat) by (unfold i, HEAD, HCRC in *; lia).
  apply semax_switch_PQR with (n := m_mode m).
  - reflexivity.
  - unfold lstate_tH. entailer!.
  - unfold lstate_tH. entailer!.
  - replace (Int.unsigned (Int.repr (m_mode m))) with (Int.unsigned (Int.repr (HEAD + Z.of_nat i)))
      by (rewrite <- Hi; reflexivity).
    rewrite select_inflate_LS by lia.
    eapply semax_post; [ | | | | apply (switch_case6 F X m n i); auto; apply (HC Espec F HF i Hi8)].
    + destruct Post; simpl. intros rho. simpl. apply andp_left2. normalize.
    + destruct Post; simpl in *. exact HN.
    + destruct Post; simpl. intros rho. simpl. apply andp_left2. normalize.
    + intros vl. destruct Post; simpl. intros rho. simpl. apply andp_left2. normalize.
Qed.

(* the main loop from a header machine m reached from m0, passing the header *)
Lemma hloop6 {Espec: OracleKind} (F: frame) (X: mpred) (m0: mst) (P Q: mst -> Prop) (R: ret_assert):
  cases6_all -> cases_all5 -> stepf2_mwf3_stmt -> stepf2_hd_stmt -> stepf2_hdr_stmt -> frame_ok5 F ->
  p_kept F P Q -> ret_ok5 F X m0 Q R ->
  forall n m, hpass (f_flush F) n m -> hdr_mode (m_mode m) = true -> i_head (m_s m) = true ->
    mwf3 m -> m_leave m = 0 -> hd_ok F m -> P m ->
    (forall o, loop2 (f_flush F) lenfix_list distfix_list m o -> loop2 (f_flush F) lenfix_list distfix_list m0 o) ->
    semax Delta_inflate5 (lstateH F (X * hd6 F m) m) inflate_mainloop (overridePost (loop_exit F X m0 P) R).
Proof.
  intros HC6 HC5 HMW HHD HHR HF HPk HRet n.
  induction n as [|n IH]; intros m HP HM HI W L D Pm Reach; [contradiction | ].
  pose proof HP as HP1. cbn [hpass] in HP1. rewrite HM in HP1.
  destruct (stepf2 (f_flush F) lenfix_list distfix_list m) as [m' | r m'] eqn:E; [ | contradiction].
  destruct HP1 as [L' HP'].
  assert (W' := HMW (f_flush F) m W L). rewrite E in W'.
  assert (D' := HHD F (f_flush F) m D). rewrite E in D'.
  assert (Hs := HHR (f_flush F) m W L). rewrite E in Hs. destruct Hs as [Hs _].
  assert (P' := HPk m W L D Pm). rewrite E in P'.
  assert (Reach': forall o, loop2 (f_flush F) lenfix_list distfix_list m' o ->
                            loop2 (f_flush F) lenfix_list distfix_list m0 o).
  { intros o Ho. apply Reach. eapply loop2_next; eauto. lia. }
  assert (TK: hdr_tok F m' = hdr_tok F m) by (apply hdr_same_tok; exact Hs).
  assert (HI': i_head (m_s m') = true) by (destruct Hs as [Hh _]; congruence).
  set (N := if hdr_mode (m_mode m') then lstateH F (X * hd6 F m') m' else lstate F X m').
  rewrite mainloop_eq.
  apply semax_loop_unroll1 with (P' := N) (Q := N).
  - apply -> semax_skip_seq.
    apply semax_seq with (Q := N).
    + eapply semax_seq'; [apply semax_load_modeH | ].
      apply (semax_switch_step6 F X m n); auto.
      match goal with |- ENTAIL _, _ |-- ?G => replace G with N by (destruct R; reflexivity) end.
      unfold case_post6. simpl RA_normal.
      intros rho. simpl. normalize. rewrite E in H. inv H.
      rewrite <- TK. unfold N, post6.
      match goal with |- context [hdr_mode (m_mode ?y)] => destruct (hdr_mode (m_mode y)) end.
      * unfold loop_stateH, fr2, lstateH, ret_locals. simpl.
        unfold PROPx, LOCALx, SEPx, local, lift1; simpl; normalize.
        apply andp_right; [apply prop_right; tauto | cancel].
      * unfold loop_state, fr2, lstate, ret_locals. simpl.
        unfold PROPx, LOCALx, SEPx, local, lift1; simpl; normalize.
        apply andp_right; [apply prop_right; tauto | cancel].
    + destruct R as [Rn Rb Rc Rr]. unfold N.
      destruct (hdr_mode (m_mode m')); [unfold lstateH | unfold lstate]; rewrite L'; abbreviate_semax.
      all: forward_if; [ contradiction | forward; entailer! ].
  - destruct R as [Rn Rb Rc Rr]. eapply semax_post; [ | | | | apply semax_skip]; simpl.
    + intros rho. apply andp_left2. apply derives_refl.
    + intros rho. simpl. apply andp_left2. normalize.
    + intros rho. simpl. apply andp_left2. normalize.
    + intros vl rho. simpl. apply andp_left2. normalize.
  - rewrite <- mainloop_eq. unfold N. destruct (hdr_mode (m_mode m')) eqn:HM'.
    + apply IH; auto.
    + assert (RO: ret_ok5 F X m' Q R).
      { intros r m2 Hl W2 D2 Q2. apply HRet; auto. }
      pose proof (loop_part5 _ F X m' P Q R HC5 HMW HHD HHR HF HPk W' L' D' P' RO) as LP.
      destruct R as [Rn Rb Rc Rr]. eapply semax_post; [ | | | | exact LP]; simpl.
      * intros rho. apply andp_left2. unfold loop_exit. simpl. apply exp_left. intros m2.
        apply (exp_right m2). simpl. apply derives_extract_prop. intros (A1 & A2 & A3 & A4 & A5).
        apply andp_right; [apply prop_right; auto | apply derives_refl].
      * intros rho. apply andp_left2. apply derives_refl.
      * intros rho. apply andp_left2. apply derives_refl.
      * intros vl rho. apply andp_left2. apply derives_refl.
Qed.
