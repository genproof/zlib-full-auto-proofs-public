(* One pass of inflate()'s main loop past the header modes (for RTH9AKit.loop9_stmt): the headless case
   (RTH9Defs.cases_nh9, wide machines) runs on the machine with the small header RTH8W.mcanon, the header
   RTH9HDefs.hd9a of the real machine in the frame; the pass is transferred back to the real machine by
   RTH8Sim.rth8_sim (the model does not read the header past the header modes), as RTH8BCNHLoop.nhloop8 does
   for a whole loop.  A break ends in RTH9ALoopH.lmid9, a return in the function's return by RTH9AKit.ret9. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.roundtrip.RTHSpec.
Require Import Zlib.proof.roundtrip.RTH8Spec.
Require Import Zlib.proof.roundtrip.RTH9AKit.
Require Import Zlib.proof.roundtrip.RTH9ALoopH.
Require Import Zlib.proof.inflate_api.Body5Loop.
Require Import Zlib.proof.inflate_api.LibProof5.
Require Import Zlib.proof.hl.inflate_api.HlBody5Loop.
Require Import Zlib.proof.roundtrip.RTH8BCNHLoop.
Require Import Zlib.proof.roundtrip.RTH8Sim.
Require Zlib.proof.roundtrip.RTH8Pure.
Require Import Zlib.proof.inflate.StepW.
Require Zlib.proof.za.inflate_api.BodyKitZ.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* ---------------------------------------------------------------------------------------------- *)
(* the pure facts of a pass past the header                                                       *)

(* the real machine after a pass whose small machine ends in c: c with the real header, and what the loop
   needs of it (its header frame and header token are those of m) *)
Definition nh_next9 (F: frame) (m c: mst) : Prop :=
  mcanon (set_m_h c (m_h m)) = c /\ mwf3_9 (set_m_h c (m_h m)) /\ hd_ok F (set_m_h c (m_h m)) /\
  hdr_mode (m_mode (set_m_h c (m_h m))) = false /\ i_head (m_s (set_m_h c (m_h m))) = true /\
  hd9a F (set_m_h c (m_h m)) = hd9a F m /\ hdr_tok F c = hdr_tok F (mcanon m).

Lemma nh_step9: forall F flush m0 m, mwf3_9 m -> m_leave m = 0 -> hd_ok F m -> i_head (m_s m) = true ->
  hdr_mode (m_mode m) = false -> pinv8 m0 m ->
  match stepf2 flush lenfix_list distfix_list (mcanon m) with
  | IBrk c => stepf2 flush lenfix_list distfix_list m = IBrk (set_m_h c (m_h m)) /\ nh_next9 F m c /\
              pinv8 m0 (set_m_h c (m_h m))
  | IRet r c => stepf2 flush lenfix_list distfix_list m = IRet r (set_m_h c (m_h m)) /\ nh_next9 F m c /\
                qinv8 m0 (set_m_h c (m_h m))
  end.
Proof.
  intros F flush m0 m [Wc W8] L D HI HM Pm.
  set (mc := mcanon m) in *.
  assert (HMc: hdr_mode (m_mode mc) = false) by (unfold mc; destruct m; exact HM).
  assert (Lc: m_leave mc = 0) by (unfold mc; destruct m; exact L).
  assert (Hmc: m_h mc = hcanon (m_h m)) by (unfold mc; destruct m; reflexivity).
  assert (Pmc: pinv8 m0 mc) by (unfold mc, mcanon; apply (proj2 (pinv8_set_h m0 m _)); exact Pm).
  destruct Pmc as (Po & Pw & Pv & Pi).
  pose proof (proj1 rth8_sim flush mc (m_h m) (or_intror HMc)) as S0.
  pose proof (stepf2_mwf3W flush mc Wc Lc) as S1.
  pose proof (stepf2_hdr9 flush mc Wc Lc) as S2.
  pose proof (stepf_inv9 flush mc Wc Lc Po Pv) as S3.
  pose proof (RTH8Pure.NH.stepf2_ngood flush lenfix_list distfix_list mc HMc) as S4.
  pose proof (stepf2_hd_proof F flush m D) as S5.
  unfold mc in S0. rewrite mcanon_back in S0. fold mc in S0.
  destruct (stepf2 flush lenfix_list distfix_list mc) as [c | r c].
  - destruct S0 as (E & Hc & _). rewrite E in S5.
    destruct S2 as (Hs & Inp). pose proof (proj1 Hs) as Ih. destruct S3 as (Po' & Pw' & Pv'). destruct S4 as ((_ & Fl) & HMc').
    assert (B: mcanon (set_m_h c (m_h m)) = c) by (apply mcanon_set_back; congruence).
    split; [exact E | split; [ | ]].
    + refine (conj B (conj _ (conj S5 (conj _ (conj _ (conj _ _)))))).
      * split; [rewrite B; exact S1 | destruct c; exact W8].
      * destruct c; exact HMc'.
      * destruct c; simpl in *; unfold mc, mcanon in Ih; destruct m; simpl in *; congruence.
      * unfold hd9a. rewrite (hd8a_same F m); [destruct c; reflexivity | | destruct c; reflexivity].
        destruct c; simpl in *; unfold mc, mcanon in Fl; destruct m; simpl in *; congruence.
      * apply hdr_same_tok; exact Hs.
    + apply (proj2 (pinv8_set_h m0 c (m_h m))).
      unfold pinv8. refine (conj Po' (conj _ (conj Pv' _))); congruence.
  - destruct S0 as (E & Hc & _). rewrite E in S5.
    destruct S2 as (Hs & Inp). pose proof (proj1 Hs) as Ih. destruct S3 as (Pw' & Pv'). destruct S4 as ((_ & Fl) & HMc').
    assert (B: mcanon (set_m_h c (m_h m)) = c) by (apply mcanon_set_back; congruence).
    split; [exact E | split; [ | ]].
    + refine (conj B (conj _ (conj S5 (conj _ (conj _ (conj _ _)))))).
      * split; [rewrite B; exact S1 | destruct c; exact W8].
      * destruct c; exact HMc'.
      * destruct c; simpl in *; unfold mc, mcanon in Ih; destruct m; simpl in *; congruence.
      * unfold hd9a. rewrite (hd8a_same F m); [destruct c; reflexivity | | destruct c; reflexivity].
        destruct c; simpl in *; unfold mc, mcanon in Fl; destruct m; simpl in *; congruence.
      * apply hdr_same_tok; exact Hs.
    + apply (proj2 (qinv8_set_h m0 c (m_h m))).
      unfold qinv8. refine (conj _ (conj Pv' _)); congruence.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the switch on the small machine                                                                *)

(* a mode past the header modes is one of the labels 9 .. 31 (DICTID .. SYNC) *)
Lemma nh_label9 (m: mst) :
  mwf3W m -> hdr_mode (m_mode m) = false ->
  m_mode m = IM.HEAD + Z.of_nat (Z.to_nat (m_mode m - IM.HEAD)) /\
  (9 <= Z.to_nat (m_mode m - IM.HEAD) < 32)%nat.
Proof.
  intros HW HH.
  assert (HM: IM.HEAD <= m_mode m <= IM.SYNC) by (apply (sw_mode _ (mwW_s _ (proj1 HW)))).
  unfold hdr_mode in HH. apply andb_false_iff in HH.
  unfold IM.HEAD, IM.HCRC, IM.SYNC in *.
  destruct HH as [HH | HH]; apply Z.leb_gt in HH; split; lia.
Qed.

Lemma pre_split9n: forall Delta F X m,
  ENTAIL Delta, lstate_t_hl F X m |-- (loop_state_hl F m * (fun _ => hdr_tok F m)) * fr2 F X.
Proof.
  intros. unfold lstate_t_hl, loop_state_hl, fr2, ret_locals.
  go_lowerx. normalize.
  apply andp_right; [apply prop_right; tauto | cancel].
Qed.

(* headless case i (in Delta_cases9 fast) from the loop state with the mode loaded *)
Lemma switch_case9n {Espec: OracleKind} (fast: funspec) (F: frame) (X: mpred) (m: mst) (i: nat):
  case_ok_nh9 fast F (IM.HEAD + Z.of_nat i) i -> m_mode m = IM.HEAD + Z.of_nat i -> m_leave m = 0 -> mwf3W m ->
  semax (Delta_inflate9 fast) (lstate_t_hl F X m) (seq_of_labeled_statement (ls_drop i inflate_LS))
    (frame_ret_assert (frame_ret_assert (switch_ret_assert (case_post2_hl F m)) (fun _ => hdr_tok F m))
       (fr2 F X)).
Proof.
  intros H A B C. eapply semax_pre; [apply pre_split9n |].
  apply semax_frame; [apply fr2_closed |].
  apply semax_frame; [intros rho te _; reflexivity | ].
  eapply semax_Delta_subsumption; [apply rth9_sub_cases9 | ]. apply H; auto.
Qed.

Lemma semax_switch_step9n {Espec: OracleKind} (fast: funspec) (F: frame) (X: mpred) (m: mst) (Post: ret_assert):
  cases_nh9 fast -> frame_ok5 F -> mwf3W m -> m_leave m = 0 -> hdr_mode (m_mode m) = false ->
  ENTAIL Delta_inflate9 fast,
    (EX m': mst, !! (stepf2 (f_flush F) lenfix_list distfix_list m = IBrk m') && loop_state_hl F m') *
    (fun _ => hdr_tok F m) * fr2 F X |-- RA_normal Post ->
  (forall vl, ENTAIL Delta_inflate9 fast,
    RA_return (case_post2_hl F m) vl * (fun _ => hdr_tok F m) * fr2 F X |-- RA_return Post vl) ->
  semax (Delta_inflate9 fast) (lstate_t_hl F X m) (Sswitch (Etempvar _t'133 tint) inflate_LS) Post.
Proof.
  intros HC HF HW HL HH HN HR.
  destruct (nh_label9 m HW HH) as [Hi Hi32].
  set (i := Z.to_nat (m_mode m - IM.HEAD)) in *.
  apply semax_switch_PQR with (n := m_mode m).
  - reflexivity.
  - unfold lstate_t_hl. entailer!.
  - unfold lstate_t_hl. entailer!.
  - replace (Int.unsigned (Int.repr (m_mode m))) with (Int.unsigned (Int.repr (IM.HEAD + Z.of_nat i)))
      by (rewrite <- Hi; reflexivity).
    rewrite select_inflate_LS by lia.
    eapply semax_post; [ | | | | apply (switch_case9n fast F X m i); auto].
    + destruct Post; simpl. intros rho. simpl. apply andp_left2. normalize.
    + destruct Post; simpl in *. exact HN.
    + destruct Post; simpl. intros rho. simpl. apply andp_left2. normalize.
    + intros vl. specialize (HR vl). destruct Post; simpl in *. exact HR.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* one pass past the header                                                                       *)

Lemma join_hl: forall F Y c,
  loop_state_hl F c * (fun _ => hdr_tok F c) * fr2 F Y |-- lstate_hl F Y c.
Proof.
  intros. intros rho. unfold loop_state_hl, fr2, lstate_hl, ret_locals. simpl.
  unfold PROPx, LOCALx, SEPx, local, lift1; simpl; normalize.
  apply andp_right; [apply prop_right; tauto | cancel].
Qed.

Lemma pass_nh9 {Espec: OracleKind} (fast: funspec) (F: frame) (X: mpred) (m0 m: mst) (R Post: ret_assert):
  funspec_sub fast (snd inflate_fast_spec3_hl) -> cases_nh9 fast -> frame_ok5 F -> ret9 fast F X m0 R ->
  (forall o, loop2 (f_flush F) lenfix_list distfix_list m o -> loop2 (f_flush F) lenfix_list distfix_list m0 o) ->
  mwf3_9 m -> m_leave m = 0 -> hd_ok F m -> i_head (m_s m) = true -> pinv8 m0 m -> hdr_mode (m_mode m) = false ->
  ENTAIL Delta_inflate9 fast, lmid9 F X m0 m |-- RA_normal Post ->
  (forall vl, RA_return Post vl = RA_return R vl) ->
  semax (Delta_inflate9 fast) (lstateH F (X * hd9 F m) m)
    (Ssequence (Sset _t'133 mode_expr) (Sswitch (Etempvar _t'133 tint) inflate_LS)) Post.
Proof.
  intros FS HC HF HRet Reach W L D HI Pm HM HN HP.
  pose proof (nh_step9 F (f_flush F) m0 m W L D HI HM Pm) as NS.
  unfold hd9 at 1. rewrite HM.
  assert (Wc: mwf3W (mcanon m)) by exact (proj1 W).
  assert (Lc: m_leave (mcanon m) = 0) by (destruct m; exact L).
  assert (HMc: hdr_mode (m_mode (mcanon m)) = false) by (destruct m; exact HM).
  replace (lstateH F (X * hd9a F m) m) with (lstate_hl F (X * hd9a F m) (mcanon m))
    by (rewrite lstate_hl_H, lstateH_mcanon; reflexivity).
  eapply semax_seq'; [eapply semax_Delta_subsumption; [apply rth9_sub_hl; exact FS | apply semax_load_mode_hl] | ].
  apply semax_switch_step9n; auto.
  - eapply derives_trans; [ | exact HN].
    apply andp_right; [apply andp_left1; apply derives_refl | apply andp_left2].
    rewrite !exp_sepcon1. apply exp_left. intros c.
    rewrite !sepcon_andp_prop'. apply derives_extract_prop. intros E0.
    rewrite E0 in NS. destruct NS as (E & (B & W' & D' & M' & I' & H9 & TK) & Pm').
    unfold lmid9. apply (exp_right (set_m_h c (m_h m))).
    apply andp_right; [apply prop_right; auto | ].
    unfold hd9. rewrite M', H9.
    rewrite <- (lstateH_mcanon F _ (set_m_h c (m_h m))), B, <- lstate_hl_H.
    rewrite <- TK. apply join_hl.
  - intros vl. rewrite HP.
    intros rho. unfold case_post2_hl, fr2, ret_locals. simpl. normalize.
    rename m' into c.
    rewrite H in NS. destruct NS as (E & (B & W' & D' & M' & I' & H9 & TK) & Q').
    pose proof (Zlib.proof.za.inflate_api.BodyKitZ.stepf2_ret_swfW _ _ _ _ _ _ E) as SW.
    eapply derives_trans;
      [ | apply (HRet r (set_m_h c (m_h m)) (Reach _ (loop2_ret _ _ _ _ _ _ E)) W' D' M' I' Q' SW rho)].
    rewrite H9, mem_rep_hl_set_h.
    rewrite <- (hdr_tok_mcanon F (set_m_h c (m_h m))), B, TK.
    unfold PROPx, LOCALx, SEPx, local, lift1; simpl; normalize.
    cancel.
Qed.
