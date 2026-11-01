(* inflate()'s main loop (Body5Parts.v loop_part5_stmt). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate_api.Body5Parts.
Require Import Zlib.proof.inflate.ModeKit.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Definition mode_expr : expr :=
  Efield (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr))) (Tstruct _inflate_state noattr))
    _mode tint.

Lemma mainloop_eq: inflate_mainloop =
  Sloop (Ssequence Sskip (Ssequence (Ssequence (Sset _t'133 mode_expr) (Sswitch (Etempvar _t'133 tint) inflate_LS))
                            (Sifthenelse (Etempvar _leave tint) Sbreak Sskip))) Sskip.
Proof. reflexivity. Qed.

Lemma select_inflate_LS: forall i, (i < 32)%nat ->
  select_switch (Int.unsigned (Int.repr (HEAD + Z.of_nat i))) inflate_LS = ls_drop i inflate_LS.
Proof.
  intros i H.
  do 32 (destruct i as [|i]; [reflexivity | ]). lia.
Qed.


(* lstate with the mode loaded into t'133 *)
Definition lstate_t (F: frame) (X: mpred) (m: mst) : environ -> mpred :=
  PROP (in_ok (f_ib F) (m_inp m); out_ok (f_ob F) (m_aout m))
  LOCAL (temp _t'133 (zv (m_mode m));
         temp _strm (f_strmp F); temp _flush (zv (f_flush F)); temp _state (f_sp F);
         temp _next (in_ptr (f_ib F) (m_nx m)); temp _put (out_ptr (f_ob F) (Zlength (m_ow m)));
         temp _have (zv (m_have m)); temp _left (zv (m_left m)); temp _hold (lv (m_hold m));
         temp _bits (zv (m_bits m)); temp _in (zv (m_in m)); temp _out (zv (m_out m));
         temp _ret (zv (m_ret m)); temp _leave (zv (m_leave m));
         lvar _here t_code (f_vhere F); lvar _last t_code (f_vlast F);
         lvar _hbuf (tarray tuchar 4) (f_vhbuf F); gvars (f_gv F))
  SEP (mem_rep F m; locals_rep F; hdr_tok F m; mem_mgr (f_gv F); zfuncs (f_gv F); X).

Lemma semax_load_mode {Espec: OracleKind} (F: frame) (X: mpred) (m: mst):
  semax Delta_inflate5 (lstate F X m) (Sset _t'133 mode_expr) (normal_ret_assert (lstate_t F X m)).
Proof.
  unfold lstate, lstate_t, mode_expr. rewrite !mem_rep_split.
  abbreviate_semax.
  Intros.
  forward.
  entailer!.
Qed.

(* what the switch does not touch: the allocator, the stream's functions, X, and the stack variables'
   and globals' facts (for the returns) *)
Definition fr2 (F: frame) (X: mpred) : environ -> mpred :=
  PROPx [] (LOCALx (ret_locals F) (SEPx [mem_mgr (f_gv F); zfuncs (f_gv F); X])).

Lemma fr2_closed: forall S F X, closed_wrt_vars S (fr2 F X).
Proof.
  intros S F X rho te' _. destruct rho. reflexivity.
Qed.

Lemma pre_split: forall F X m,
  ENTAIL Delta_inflate5, lstate_t F X m |-- (loop_state F m * (fun _ => hdr_tok F m)) * fr2 F X.
Proof.
  intros. unfold lstate_t, loop_state, fr2, ret_locals.
  go_lowerx. normalize.
  apply andp_right; [apply prop_right; tauto | cancel].
Qed.

Lemma switch_case {Espec: OracleKind} (F: frame) (X: mpred) (m: mst) (i: nat):
  case_okT5 F (HEAD + Z.of_nat i) i -> m_mode m = HEAD + Z.of_nat i -> m_leave m = 0 -> mwf3 m ->
  hd_ok F m ->
  semax Delta_inflate5 (lstate_t F X m) (seq_of_labeled_statement (ls_drop i inflate_LS))
    (frame_ret_assert (frame_ret_assert (switch_ret_assert (case_post2 F m)) (fun _ => hdr_tok F m))
       (fr2 F X)).
Proof.
  intros H A B C D. eapply semax_pre; [apply pre_split |].
  apply semax_frame; [apply fr2_closed |].
  apply semax_cases_inflate5. apply H; auto.
Qed.

Lemma all_T5 {Espec: OracleKind} (F: frame):
  cases_all5 -> frame_ok5 F -> forall i, (i < 32)%nat -> case_okT5 F (HEAD + Z.of_nat i) i.
Proof.
  intros HC HF i Hi. destruct (HC Espec F HF) as [A B].
  assert (i < 1 \/ 7 < i \/ 1 <= i <= 7)%nat as [H | [H | H]] by lia.
  - apply case_okT5_of_ok5. apply A; auto.
  - apply case_okT5_of_ok5. apply A; auto.
  - apply B; auto.
Qed.

Lemma semax_switch_step {Espec: OracleKind} (F: frame) (X: mpred) (m: mst) (Post: ret_assert):
  cases_all5 -> frame_ok5 F -> mwf3 m -> m_leave m = 0 -> hd_ok F m ->
  ENTAIL Delta_inflate5,
    (EX m': mst, !! (stepf2 (f_flush F) lenfix_list distfix_list m = IBrk m') && loop_state F m') *
    (fun _ => hdr_tok F m) * fr2 F X |-- RA_normal Post ->
  (forall vl, ENTAIL Delta_inflate5,
    RA_return (case_post2 F m) vl * (fun _ => hdr_tok F m) * fr2 F X |-- RA_return Post vl) ->
  semax Delta_inflate5 (lstate_t F X m) (Sswitch (Etempvar _t'133 tint) inflate_LS) Post.
Proof.
  intros HC HF HW HL HD HN HR.
  assert (HM: HEAD <= m_mode m <= SYNC) by (destruct HW as [W _]; apply (sw_mode _ (mw_s _ W))).
  set (i := Z.to_nat (m_mode m - HEAD)).
  assert (Hi: m_mode m = HEAD + Z.of_nat i) by (unfold i; rewrite Z2Nat.id; lia).
  assert (Hi32: (i < 32)%nat) by (unfold i, HEAD, SYNC in *; lia).
  apply semax_switch_PQR with (n := m_mode m).
  - reflexivity.
  - unfold lstate_t. entailer!.
  - unfold lstate_t. entailer!.
  - replace (Int.unsigned (Int.repr (m_mode m))) with (Int.unsigned (Int.repr (HEAD + Z.of_nat i)))
      by (rewrite <- Hi; reflexivity).
    rewrite select_inflate_LS by auto.
    eapply semax_post; [ | | | | apply (switch_case F X m i); auto using all_T5].
    + destruct Post; simpl. intros rho. simpl. apply andp_left2. normalize.
    + destruct Post; simpl in *. exact HN.
    + destruct Post; simpl. intros rho. simpl. apply andp_left2. normalize.
    + intros vl. specialize (HR vl). destruct Post; simpl in *. exact HR.
Qed.

(* the loop invariant: the machine m at the loop head, reached from m0 *)
Definition linv (F: frame) (X: mpred) (m0: mst) (P: mst -> Prop) : environ -> mpred :=
  EX m: mst,
    !! ((forall o, loop2 (f_flush F) lenfix_list distfix_list m o -> loop2 (f_flush F) lenfix_list distfix_list m0 o) /\
        mwf3 m /\ hd_ok F m /\ m_leave m = 0 /\ P m) &&
    lstate F X m.

(* after the switch: one pass from m *)
Definition lmid (F: frame) (X: mpred) (m: mst) (P: mst -> Prop) : environ -> mpred :=
  EX m': mst,
    !! (stepf2 (f_flush F) lenfix_list distfix_list m = IBrk m' /\ mwf3 m' /\ hd_ok F m' /\ P m') &&
    lstate F X m'.

Lemma leave_if {Espec: OracleKind} (F: frame) (X: mpred) (m0 m: mst) (P: mst -> Prop) (R: ret_assert):
  (forall o, loop2 (f_flush F) lenfix_list distfix_list m o -> loop2 (f_flush F) lenfix_list distfix_list m0 o) ->
  semax Delta_inflate5 (lmid F X m P) (Sifthenelse (Etempvar _leave tint) Sbreak Sskip)
    (loop1_ret_assert (linv F X m0 P) (overridePost (loop_exit F X m0 P) R)).
Proof.
  intros Reach. destruct R as [Rn Rb Rc Rr]. unfold lmid, lstate. Intros m'.
  apply semax_extract_prop. intros (E & W' & D' & P').
  assert (HL: 0 <= m_leave m' <= 1) by (apply (mw_leave _ (mwf3_mwf _ W'))).
  abbreviate_semax.
  forward_if.
  - forward. unfold loop_exit, lstate. Exists m'.
    assert (L1: m_leave m' = 1) by (destruct (zeq (m_leave m') 0) as [Z0 | Z0]; [rewrite Z0 in H; contradiction | lia]).
    entailer!.
    apply Reach. apply loop2_leave; auto.
  - forward. unfold linv, lstate. Exists m'.
    assert (L0: m_leave m' = 0).
    { apply (f_equal Int.unsigned) in H. rewrite Int.unsigned_repr in H by rep_lia. exact H. }
    entailer!.
    intros o Ho. apply Reach. eapply loop2_next; eauto. lia.
Qed.

(* the hypothesis of loop_part5_stmt on P *)
Definition p_kept (F: frame) (P Q: mst -> Prop) : Prop :=
  forall m, mwf3 m -> m_leave m = 0 -> hd_ok F m -> P m ->
    match stepf2 (f_flush F) lenfix_list distfix_list m with IBrk m' => P m' | IRet _ m' => Q m' end.

Lemma norm_ent (F: frame) (X: mpred) (m: mst) (P Q: mst -> Prop):
  stepf2_mwf3_stmt -> stepf2_hd_stmt -> stepf2_hdr_stmt -> p_kept F P Q ->
  mwf3 m -> m_leave m = 0 -> hd_ok F m -> P m ->
  ENTAIL Delta_inflate5,
    (EX m': mst, !! (stepf2 (f_flush F) lenfix_list distfix_list m = IBrk m') && loop_state F m') *
    (fun _ => hdr_tok F m) * fr2 F X |-- lmid F X m P.
Proof.
  intros HMW HHD HHR HP W L D Pm.
  rewrite !exp_sepcon1. apply andp_left2. apply exp_left. intros m'.
  intros rho. unfold lmid. unfold loop_state, fr2, lstate, ret_locals. simpl. normalize.
  assert (W' := HMW (f_flush F) m W L). rewrite H in W'.
  assert (D' := HHD F (f_flush F) m D). rewrite H in D'.
  assert (Hs := HHR (f_flush F) m W L). rewrite H in Hs. destruct Hs as [Hs _].
  assert (P' := HP m W L D Pm). rewrite H in P'.
  rewrite <- (hdr_same_tok F m m' Hs).
  Exists m'. normalize.
  unfold PROPx, LOCALx, SEPx, local, lift1; simpl; normalize.
  apply andp_right; [apply prop_right; tauto | cancel].
Qed.

Lemma ret_ent (F: frame) (X: mpred) (m0 m: mst) (P Q: mst -> Prop) Rn Rb Rc Rr:
  stepf2_mwf3_stmt -> stepf2_hd_stmt -> stepf2_hdr_stmt -> p_kept F P Q ->
  mwf3 m -> m_leave m = 0 -> hd_ok F m -> P m ->
  (forall o, loop2 (f_flush F) lenfix_list distfix_list m o -> loop2 (f_flush F) lenfix_list distfix_list m0 o) ->
  ret_ok5 F X m0 Q {| RA_normal := Rn; RA_break := Rb; RA_continue := Rc; RA_return := Rr |} ->
  forall vl, ENTAIL Delta_inflate5,
    RA_return (case_post2 F m) vl * (fun _ => hdr_tok F m) * fr2 F X |-- Rr vl.
Proof.
  intros HMW HHD HHR HP W L D Pm Reach HRet vl.
  intros rho. unfold case_post2, fr2, ret_locals. simpl. normalize.
  assert (W' := HMW (f_flush F) m W L). rewrite H in W'.
  assert (D' := HHD F (f_flush F) m D). rewrite H in D'.
  assert (Hs := HHR (f_flush F) m W L). rewrite H in Hs. destruct Hs as [Hs _].
  assert (Q' := HP m W L D Pm). rewrite H in Q'.
  rewrite <- (hdr_same_tok F m m' Hs).
  eapply derives_trans; [ | apply (HRet r m' (Reach _ (loop2_ret _ _ _ _ _ _ H)) W' D' Q' rho)].
  unfold PROPx, LOCALx, SEPx, local, lift1; simpl; normalize.
  cancel.
Qed.

Lemma loop_part5 : loop_part5_stmt.
Proof.
  intros Espec F X m0 P Q R HC HMW HHD HHR HF HP W0 L0 D0 P0 HRet.
  destruct R as [Rn Rb Rc Rr].
  rewrite mainloop_eq.
  apply semax_pre with (P' := linv F X m0 P).
  { unfold linv. apply andp_left2. Exists m0. apply andp_right; [apply prop_right; auto | apply derives_refl]. }
  apply semax_loop with (Q' := linv F X m0 P).
  - unfold linv at 1. apply extract_exists_pre. intros m.
    apply semax_extract_prop. intros (Reach & W & D & L & Pm).
    apply -> semax_skip_seq.
    apply semax_seq with (Q := lmid F X m P).
    + eapply semax_seq'; [apply semax_load_mode | ].
      apply semax_switch_step; auto.
      * exact (norm_ent F X m P Q HMW HHD HHR HP W L D Pm).
      * exact (ret_ent F X m0 m P Q Rn Rb Rc Rr HMW HHD HHR HP W L D Pm Reach HRet).
    + apply leave_if; auto.
  - eapply semax_post; [ | | | | apply semax_skip]; simpl.
    + intros rho. apply andp_left2. apply derives_refl.
    + intros rho. simpl. apply andp_left2. normalize.
    + intros rho. simpl. apply andp_left2. normalize.
    + intros vl rho. simpl. apply andp_left2. normalize.
Qed.
