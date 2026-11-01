(* One pass of inflate()'s main loop from a header mode (for RTH9AKit.loop9_stmt): the mode is loaded, the switch
   runs the header case (RTH9HDefs.cases9h_all) on the real machine with its partial header RTHCase.hd6; the
   pass ends in the machine of one step of the model with its header RTH9HDefs.hd9 ([lmid9]).  As
   round 1's RTH8BCHLoop.semax_switch_step8, without hpass8: a header case never returns. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.roundtrip.RTHSpec.
Require Import Zlib.proof.roundtrip.RTH8Spec.
Require Import Zlib.proof.roundtrip.RTH9AKit.
Require Import Zlib.proof.inflate_api.Body5Loop.
Require Import Zlib.proof.inflate_api.LibProof5.
Require Import Zlib.proof.roundtrip.RTHBody6Loop.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* after the switch: one pass of the model from m, to a machine with the loop's invariants and its header *)
Definition lmid9 (F: frame) (X: mpred) (m0 m: mst) : environ -> mpred :=
  EX m': mst,
    !! (stepf2 (f_flush F) lenfix_list distfix_list m = IBrk m' /\ mwf3_9 m' /\ hd_ok F m' /\
        i_head (m_s m') = true /\ pinv8 m0 m') &&
    lstateH F (X * hd9 F m') m'.

(* the partial header of a header machine carries RTHSpec.hinv6 *)
Lemma lstateH_hinv6_9: forall Delta F X m,
  ENTAIL Delta, lstateH F (X * hd6 F m) m |-- !! hinv6 (m_s m) (m_h m).
Proof.
  intros. unfold lstateH, hd6, head_rep6. go_lowerx. normalize.
Qed.

Lemma pre_split9: forall Delta F X m,
  ENTAIL Delta, lstate_tH F (X * hd6 F m) m |--
    (loop_stateH F m * (fun _ => hdr_tok F m * hd6 F m)) * fr2 F X.
Proof.
  intros. unfold lstate_tH, loop_stateH, fr2, ret_locals.
  go_lowerx. normalize.
  apply andp_right; [apply prop_right; tauto | cancel].
Qed.

(* header case i from the loop state with the mode loaded *)
Lemma switch_case9h {Espec: OracleKind} (fast: funspec) (F: frame) (X: mpred) (m: mst) (i: nat):
  funspec_sub fast (snd inflate_fast_spec3_hl) ->
  case_ok9h F (IM.HEAD + Z.of_nat i) i -> m_mode m = IM.HEAD + Z.of_nat i -> m_leave m = 0 -> mwf3_9 m ->
  hd_ok F m -> i_head (m_s m) = true ->
  semax (Delta_inflate9 fast) (lstate_tH F (X * hd6 F m) m) (seq_of_labeled_statement (ls_drop i inflate_LS))
    (frame_ret_assert (frame_ret_assert (switch_ret_assert (case_post9 F m)) (fun _ => hdr_tok F m))
       (fr2 F X)).
Proof.
  intros FS H A B C D E. eapply semax_pre; [apply pre_split9 |].
  apply semax_frame; [apply fr2_closed |].
  eapply semax_Delta_subsumption; [apply rth9_sub_cases5; exact FS | ]. apply H; auto.
Qed.

(* the switch of one pass from a header mode *)
Lemma semax_switch_step9h {Espec: OracleKind} (fast: funspec) (F: frame) (X: mpred) (m: mst) (Post: ret_assert):
  funspec_sub fast (snd inflate_fast_spec3_hl) ->
  cases9h_all -> frame_ok5 F -> mwf3_9 m -> m_leave m = 0 ->
  hd_ok F m -> i_head (m_s m) = true -> hdr_mode (m_mode m) = true ->
  ENTAIL Delta_inflate9 fast,
    RA_normal (case_post9 F m) * (fun _ => hdr_tok F m) * fr2 F X |-- RA_normal Post ->
  semax (Delta_inflate9 fast) (lstate_tH F (X * hd6 F m) m) (Sswitch (Etempvar _t'133 tint) inflate_LS) Post.
Proof.
  intros FS HC HF HW HL HD HI HM HN.
  assert (HM2: IM.HEAD <= m_mode m <= IM.HCRC).
  { unfold hdr_mode in HM. apply andb_prop in HM. destruct HM as [H1 H2].
    apply Z.leb_le in H1, H2. unfold IM.HEAD, IM.HCRC in *. lia. }
  set (i := Z.to_nat (m_mode m - IM.HEAD)).
  assert (Hi: m_mode m = IM.HEAD + Z.of_nat i) by (unfold i; rewrite Z2Nat.id; lia).
  assert (Hi8: (i <= 8)%nat) by (unfold i, IM.HEAD, IM.HCRC in *; lia).
  apply semax_switch_PQR with (n := m_mode m).
  - reflexivity.
  - unfold lstate_tH. entailer!.
  - unfold lstate_tH. entailer!.
  - replace (Int.unsigned (Int.repr (m_mode m))) with (Int.unsigned (Int.repr (IM.HEAD + Z.of_nat i)))
      by (rewrite <- Hi; reflexivity).
    rewrite select_inflate_LS by lia.
    eapply semax_post; [ | | | | apply (switch_case9h fast F X m i); auto; apply (HC Espec F HF i Hi8)].
    + destruct Post; simpl. intros rho. simpl. apply andp_left2. normalize.
    + destruct Post; simpl in *. exact HN.
    + destruct Post; simpl. intros rho. simpl. apply andp_left2. normalize.
    + intros vl. destruct Post; simpl. intros rho. simpl. apply andp_left2. normalize.
Qed.

(* one pass from a header mode: load the mode, run the header case *)
Lemma pass_hdr9 {Espec: OracleKind} (fast: funspec) (F: frame) (X: mpred) (m0 m: mst) (Post: ret_assert):
  funspec_sub fast (snd inflate_fast_spec3_hl) -> cases9h_all -> hdr9_inv_stmt -> frame_ok5 F ->
  mwf3_9 m -> m_leave m = 0 -> hd_ok F m -> i_head (m_s m) = true -> pinv8 m0 m -> hdr_mode (m_mode m) = true ->
  ENTAIL Delta_inflate9 fast, lmid9 F X m0 m |-- RA_normal Post ->
  semax (Delta_inflate9 fast) (lstateH F (X * hd9 F m) m)
    (Ssequence (Sset _t'133 mode_expr) (Sswitch (Etempvar _t'133 tint) inflate_LS)) Post.
Proof.
  intros FS HC HIv HF W L D HI Pm HM HN.
  unfold hd9 at 1. rewrite HM.
  assert_PROP (hinv6 (m_s m) (m_h m)) as HV by apply lstateH_hinv6_9.
  destruct Pm as (Po & Pw & Pv & Pi).
  assert (Hs := HIv (f_flush F) m W L HM Po Pv (fun _ => HV)).
  assert (D' := stepf2_hd_proof F (f_flush F) m D).
  eapply semax_seq'; [eapply semax_Delta_subsumption; [apply rth9_sub_5; exact FS | apply semax_load_modeH] | ].
  apply (semax_switch_step9h fast F X m); auto.
  eapply derives_trans; [ | exact HN].
  apply andp_right; [apply andp_left1; apply derives_refl | apply andp_left2].
  change (RA_normal (case_post9 F m)) with
    (EX m': mst, !! (stepf2 (f_flush F) lenfix_list distfix_list m = IBrk m') && post9 F m').
  rewrite !exp_sepcon1. apply exp_left. intros m'.
  rewrite !sepcon_andp_prop'. apply derives_extract_prop. intros E0.
  rewrite E0 in Hs, D'.
  destruct Hs as (W' & Hsame & Hinp & Po' & Hw' & Pv').
  assert (TK: hdr_tok F m' = hdr_tok F m) by (apply hdr_same_tok; exact Hsame).
  assert (HI': i_head (m_s m') = true) by (destruct Hsame as [Hh _]; congruence).
  unfold lmid9. apply (exp_right m').
  apply andp_right; [apply prop_right | ].
  { refine (conj E0 (conj W' (conj D' (conj HI' (conj Po' (conj _ (conj Pv' _))))))); congruence. }
  rewrite <- TK. intros rho. unfold post9, loop_stateH, fr2, lstateH, ret_locals. simpl.
  unfold PROPx, LOCALx, SEPx, local, lift1; simpl; normalize.
  apply andp_right; [apply prop_right; tauto | cancel].
Qed.
