(* Law rt_dictionary, main (DWKit.v): statement 32, the do-while of inflate(Z_FINISH) calls on clip()-sized pieces (RI -> RB, DWIFacts.di_call: the loop ends only with Z_STREAM_END).
   The loop's invariant is RI, its test state DWTrtLoop1.trt_cont; this file does the body's statements (1) and (2)
   (in_rest, out_rest) and puts together the rest of the body (DWTrtLoop3.v) and the test (DWTrtLoop1.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.EnvBodies.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.clip_streams.CS.
Require Import Zlib.proof.harness.clip_streams.Globals.
Require Import Zlib.proof.harness.clip_streams.RTKit.
Require Import Zlib.proof.harness.clip_streams.RTLoop.
Require Import Zlib.proof.harness.dictionary_w.DWCS.
Require Import Zlib.proof.harness.dictionary_w.DWFacts.
Require Import Zlib.proof.harness.dictionary_w.DWIFacts.
Require Import Zlib.proof.harness.dictionary_w.DWMainDefs.
Require Import Zlib.proof.harness.dictionary_w.DWKit.
Require Import Zlib.proof.harness.dictionary_w.DWTrtLoop1.
Require Import Zlib.proof.harness.dictionary_w.DWTrtLoop1.
Require Import Zlib.proof.harness.dictionary_w.DWTrtLoop3.
Import DWKit.DRT.
#[local] Existing Instance CS.CS.
Local Open Scope logic.

Ltac simplify_remove_localdef_temp ::= rt_rlt.

Lemma trt_loop_ok : trt_loop_stmt.
Proof.
  intros Espec Q P gv vc vd wbits n b D O dict dp op ddp cp PF.
  unfold trt_loop, Delta_drt, POST_drt. abbreviate_semax.
  assert_PROP (dw_hf wbits n b D O dict dp op ddp cp /\ 6 <= Zlength O) as HF0.
  { unfold RI. Intros pos out z L. entailer!. }
  destruct HF0 as [HF H6O].
  pose proof HF as HF'. destruct HF' as (DF & CF & HO & Hb & BD & BO & Pcp).
  destruct CF as (Hn & HD & ID & Pdp & Pop & Hdl & IDd & Pddp & Hw).
  unfold max_size in Hn.
  forward_loop (RI lit_drt gv vc vd P wbits n b D O dict dp op ddp cp)
    continue: (trt_cont P wbits n b D O dict dp op ddp cp gv vc vd)
    break: (RB lit_drt gv vc vd wbits n b D O dict dp op ddp cp).
  { apply ENTAIL_refl. }
  2: { unfold MORE_COMMANDS, POSTCONDITION, abbreviate.
       apply (trt_incr_ok Q P gv vc vd wbits n b D O dict dp op ddp cp); auto. }
  2: { apply ENTAIL_refl. }
  unfold RI. Intros pos out z L.
  rewrite rtl_istreamA_unfold. Intros.
  rename H into HP, H0 into Hsw, H1 into Hni, H2 into Hno, H3 into Zo, H5 into Lo. clear H4.
  unfold rtl_tup. rewrite Hni, Hno.
  destruct (di_ok _ _ PF _ _ _ _ _ _ _ _ HP) as (Hhd & Hwr & Hpos & rest & Erest).
  assert (Hout: Zlength out <= n) by (rewrite <- HD, Erest, Zlength_app; pose proof (Zlength_nonneg rest); lia).
  clear Erest rest.
  forward.
  forward.
  { entailer!. first [apply rtl_sameblock; auto | apply prop_right; apply rtl_sameblock; auto]. }
  rewrite trt_rest by (auto; rep_lia).
  forward.
  forward.
  { entailer!. first [apply rtl_sameblock; auto | apply prop_right; apply rtl_sameblock; auto]. }
  rewrite trt_rest by (auto; rep_lia).
  unfold MORE_COMMANDS, POSTCONDITION, abbreviate.
  eapply semax_pre; [ | apply (trt_clips_ok Q P gv vc vd wbits n b D O dict dp op ddp cp pos out z L); auto].
  unfold trt_mid0, rtl_tup. rewrite Hni, Hno. apply ENTAIL_refl.
Qed.
