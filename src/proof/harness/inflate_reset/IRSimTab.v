(* Law inflate_reset, theory part: one pass of TABLE, LENLENS, CODELENS from related machines. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.inflate_reset.IRDefs.
Require Import Zlib.proof.harness.inflate_reset.IRTabKit.
Require Import Zlib.proof.harness.inflate_reset.IRTabCLLoop.
Require Import Zlib.proof.harness.inflate_reset.IRTabCLPost.
Require Import Zlib.proof.harness.inflate_reset.IRTabLL.
Require Import Zlib.proof.harness.inflate_reset.IRTabTab.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* stepf2 per mode                                                                                *)

Lemma irst_step_TABLE fl m : m_mode m = TABLE ->
  stepf2 fl lenfix_list distfix_list m = irt_run fl (irt_tab m).
Proof.
  intros H. rewrite <- irt_tab_eq. unfold stepf2, Zlib.proof.inflate.Model2.step2. rewrite H. reflexivity.
Qed.

Lemma irst_step_LENLENS fl m : m_mode m = LENLENS ->
  stepf2 fl lenfix_list distfix_list m = irt_run fl (irt_ll m).
Proof.
  intros H. rewrite <- irt_ll_eq. unfold stepf2, Zlib.proof.inflate.Model2.step2. rewrite H. reflexivity.
Qed.

Lemma irst_step_CODELENS fl m : m_mode m = CODELENS ->
  stepf2 fl lenfix_list distfix_list m = irt_run fl (irt_cl m).
Proof.
  intros H. rewrite <- irt_cl_eq. unfold stepf2, Zlib.proof.inflate.Model2.step2. rewrite H. reflexivity.
Qed.

Lemma irst_step_LEN_ fl m : m_mode m = LEN_ ->
  stepf2 fl lenfix_list distfix_list m = c_LEN_ lenfix_list distfix_list (fast lenfix_list distfix_list) m.
Proof. intros H. unfold stepf2, Zlib.proof.inflate.Model2.step2. rewrite H. reflexivity. Qed.

Lemma irst_mwf3_unleave m : mwf3 (set_leave m) -> m_leave m = 0 -> mwf3 m.
Proof.
  intros [W X] L. split; [|exact X].
  destruct W; constructor; auto; lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* CODELENS from its parts                                                                        *)

Lemma irst_cl : irt_clloop_stmt -> irt_clpost_stmt -> irt_cl_stmt.
Proof.
  intros LP PO W0 wrap src pos inp aout ma mb K Wa Wb L Md.
  pose proof (LP 320%nat W0 wrap src pos inp aout ma mb K Wa Wb L Md) as R.
  assert (Ma: m_mode ma = CODELENS)
    by (unfold m_mode in *; rewrite (sr_mode _ _ _ (mr_s _ _ (kr_rel _ _ _ _ _ _ _ _ K))); exact Md).
  assert (La: m_leave ma = 0) by (rewrite (mr_leave _ _ (kr_rel _ _ _ _ _ _ _ _ K)); exact L).
  pose proof (Zlib.proof.inflate.Step3Tables.tb_codelens_loop 320 mb Wb L Md) as LB.
  pose proof (Zlib.proof.inflate.Step3Tables.tb_codelens_loop 320 ma Wa La Ma) as LA.
  pose proof (sw_have _ (mw_s _ (Zlib.proof.inflate.Step3Inv.m3_w _ Wb))) as Hb.
  pose proof (sw_have _ (mw_s _ (Zlib.proof.inflate.Step3Inv.m3_w _ Wa))) as Ha.
  specialize (LB ltac:(simpl; lia)). specialize (LA ltac:(simpl; lia)).
  unfold irt_cl.
  destruct (codelens_loop lenfix_list distfix_list 320 ma) as [ma'|ma'|ma'];
    destruct (codelens_loop lenfix_list distfix_list 320 mb) as [mb'|mb'|mb']; try contradiction;
    cbn [irt_rr]; auto.
  destruct LA as (Wa' & _). destruct LB as (Wb' & Lb' & Mb' & Hf).
  apply PO; auto.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The group                                                                                      *)

Lemma irst_post (DEC: sgroup_ok decode_mode) (SM: stepf2_mwf3_stmt)
  W0 wrap src pos inp aout flush ma mb pa pb :
  ir_ctx src pos inp -> mwf3 ma -> mwf3 mb -> m_leave ma = 0 -> m_leave mb = 0 ->
  irt_rr W0 wrap src pos inp aout pa pb ->
  (forall fl, stepf2 fl lenfix_list distfix_list ma = irt_run fl pa) ->
  (forall fl, stepf2 fl lenfix_list distfix_list mb = irt_run fl pb) ->
  sim_post W0 wrap src pos inp aout (stepf2 flush lenfix_list distfix_list ma)
    (stepf2 flush lenfix_list distfix_list mb).
Proof.
  intros Hc Wa Wb La Lb R Ea Eb. rewrite Ea, Eb.
  destruct pa as [[ma'|ra ma']|ma'], pb as [[mb'|rb mb']|mb']; cbn [irt_rr] in R; try contradiction.
  - exact R.
  - destruct R as (K & L' & Md').
    assert (Ta: mwf3 ma').
    { pose proof (SM Z_TREES ma Wa La) as S. rewrite Ea in S. cbn [irt_run] in S.
      apply irst_mwf3_unleave; [exact S|].
      rewrite (mr_leave _ _ (kr_rel _ _ _ _ _ _ _ _ K)). exact L'. }
    assert (Tb: mwf3 mb').
    { pose proof (SM Z_TREES mb Wb Lb) as S. rewrite Eb in S. cbn [irt_run] in S.
      apply irst_mwf3_unleave; [exact S | exact L']. }
    assert (Ma': m_mode ma' = LEN_)
      by (unfold m_mode in *; rewrite (sr_mode _ _ _ (mr_s _ _ (kr_rel _ _ _ _ _ _ _ _ K))); exact Md').
    cbn [irt_run]. destruct (flush =? Z_TREES).
    + cbn [sim_post]. apply irk_mach with ma' mb'; auto.
      * unfold m_mode, LEN_, HEAD in *. lia.
      * apply irk_leave. apply (irk_mf_of_Kr _ _ _ _ _ _ _ _ K).
    + rewrite <- (irst_step_LEN_ flush ma' Ma'), <- (irst_step_LEN_ flush mb' Md').
      apply (DEC W0 wrap src pos inp aout flush ma' mb' Hc K Ta Tb L').
      left. exact Md'.
Qed.

Lemma tab_sim : tab_sim_stmt.
Proof.
  intros SM C3 TD DEC.
  pose proof (irst_cl irt_clloop_ok (irt_clpost_ok C3 TD)) as CL.
  pose proof (irt_ll_ok C3 TD CL) as LL.
  pose proof (irt_tab_ok LL) as TB.
  intros W0 wrap src pos inp aout flush ma mb Hc K Wa Wb Lb Hmd.
  assert (Em: m_mode ma = m_mode mb)
    by (unfold m_mode; exact (sr_mode _ _ _ (mr_s _ _ (kr_rel _ _ _ _ _ _ _ _ K)))).
  assert (La: m_leave ma = 0) by (rewrite (mr_leave _ _ (kr_rel _ _ _ _ _ _ _ _ K)); exact Lb).
  pose proof (proj1 (irk_mwf3x_iff ma) Wa) as Xa. pose proof (proj1 (irk_mwf3x_iff mb) Wb) as Xb.
  unfold md_tab in Hmd. destruct Hmd as [D|[D|D]].
  - apply (irst_post DEC SM W0 wrap src pos inp aout flush ma mb (irt_tab ma) (irt_tab mb)); auto.
    + intros fl. apply irst_step_TABLE. congruence.
    + intros fl. apply irst_step_TABLE. exact D.
  - apply (irst_post DEC SM W0 wrap src pos inp aout flush ma mb (irt_ll ma) (irt_ll mb)); auto.
    + intros fl. apply irst_step_LENLENS. congruence.
    + intros fl. apply irst_step_LENLENS. exact D.
  - apply (irst_post DEC SM W0 wrap src pos inp aout flush ma mb (irt_cl ma) (irt_cl mb)); auto.
    + intros fl. apply irst_step_CODELENS. congruence.
    + intros fl. apply irst_step_CODELENS. exact D.
Qed.
