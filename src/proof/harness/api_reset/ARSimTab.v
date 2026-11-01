(* Law api_reset, the theory: the group of modes TABLE, LENLENS, CODELENS (which fall into LEN_) under the wide
   machine invariant: x_inflate_reset's IRSimTab.v and IRTab*.v for calls of up to 2^32-1 bytes.  The parts
   under the wide invariant of the table cases (StepWTables.v's mwf3xW) are ARSimTabCL.v, ARSimTabLL.v and
   ARSimTabTab.v; the pure facts are those of x_inflate_reset: the tables of inflate_table are the same where
   a lookup reads them, whatever the code space held before (IRTabDet.v), with the covering fact of
   inflate_table's tables (InvQ5.cover3_proof); one pass of the switch keeps the wide invariant
   (StepW.stepf2_mwf3W). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.api_reset.ARSimDefs.
Require Import Zlib.proof.harness.inflate_reset.IRTabKit.
Require Import Zlib.proof.harness.inflate_reset.IRTabDet.
Require Import Zlib.proof.harness.inflate_reset.IRSimTab.
Require Import Zlib.proof.inflate.StepW.
Require Zlib.proof.inflate.InvQ5.
Require Import Zlib.proof.harness.api_reset.ARSimTabKit.
Require Import Zlib.proof.harness.api_reset.ARSimTabCL.
Require Import Zlib.proof.harness.api_reset.ARSimTabLL.
Require Import Zlib.proof.harness.api_reset.ARSimTabTab.
Import ListNotations.
Local Open Scope Z_scope.

(* the wide invariant of a machine that left its pass (set_leave) holds for the machine that did not leave *)
Lemma arst_mwf3W_unleave m : mwf3W (set_leave m) -> m_leave m = 0 -> mwf3W m.
Proof.
  intros [W X] L. split; [|exact X].
  destruct W; constructor; auto; lia.
Qed.

(* the table modes are neither EXLEN nor EXTRA: the case form of the invariant *)
Lemma arst_xW m : mwf3W m -> m_mode m = TABLE \/ m_mode m = LENLENS \/ m_mode m = CODELENS -> mwf3xW m.
Proof.
  intros W Md. apply mwf3W_xW; [exact W|].
  unfold nohdr. destruct Md as [D|[D|D]]; rewrite D; cbv; split; discriminate.
Qed.

Lemma arst_post (DEC: sgroup_okW decode_mode)
  W0 wrap src pos inp aout flush ma mb pa pb :
  ir_ctx src pos inp -> mwf3W ma -> mwf3W mb -> m_leave ma = 0 -> m_leave mb = 0 ->
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
    assert (Ta: mwf3W ma').
    { pose proof (stepf2_mwf3W Z_TREES ma Wa La) as S. rewrite Ea in S. cbn [irt_run] in S.
      apply arst_mwf3W_unleave; [exact S|].
      rewrite (mr_leave _ _ (kr_rel _ _ _ _ _ _ _ _ K)). exact L'. }
    assert (Tb: mwf3W mb').
    { pose proof (stepf2_mwf3W Z_TREES mb Wb Lb) as S. rewrite Eb in S. cbn [irt_run] in S.
      apply arst_mwf3W_unleave; [exact S | exact L']. }
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

Lemma ar_tab_sim : tab_sim_stmtW.
Proof.
  intros DEC.
  pose proof InvQ5.cover3_proof as C3. pose proof (tabdet_proof C3) as TD.
  pose proof (irst_clW irt_clloop_okW (irt_clpost_okW C3 TD)) as CL.
  pose proof (irt_ll_okW C3 TD CL) as LL.
  pose proof (irt_tab_okW LL) as TB.
  intros W0 wrap src pos inp aout flush ma mb Hc K Wa Wb Lb Hmd.
  assert (Em: m_mode ma = m_mode mb)
    by (unfold m_mode; exact (sr_mode _ _ _ (mr_s _ _ (kr_rel _ _ _ _ _ _ _ _ K)))).
  assert (La: m_leave ma = 0) by (rewrite (mr_leave _ _ (kr_rel _ _ _ _ _ _ _ _ K)); exact Lb).
  unfold md_tab in Hmd.
  pose proof (arst_xW ma Wa ltac:(rewrite Em; exact Hmd)) as Xa. pose proof (arst_xW mb Wb Hmd) as Xb.
  destruct Hmd as [D|[D|D]].
  - apply (arst_post DEC W0 wrap src pos inp aout flush ma mb (irt_tab ma) (irt_tab mb)); auto.
    + intros fl. apply irst_step_TABLE. congruence.
    + intros fl. apply irst_step_TABLE. exact D.
  - apply (arst_post DEC W0 wrap src pos inp aout flush ma mb (irt_ll ma) (irt_ll mb)); auto.
    + intros fl. apply irst_step_LENLENS. congruence.
    + intros fl. apply irst_step_LENLENS. exact D.
  - apply (arst_post DEC W0 wrap src pos inp aout flush ma mb (irt_cl ma) (irt_cl mb)); auto.
    + intros fl. apply irst_step_CODELENS. congruence.
    + intros fl. apply irst_step_CODELENS. exact D.
Qed.
