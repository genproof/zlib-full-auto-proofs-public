(* Law rt_dictionary, main (DWKit.v), statement 32 (DWTrtLoop1.v): (3)-(5), avail_in = clip(in_rest),
   avail_out = clip(out_rest), then the call (DWTrtLoop2.v). *)
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
Require Import Zlib.proof.harness.dictionary_w.DWTrtLoop2.
Import DWKit.DRT.
#[local] Existing Instance CS.CS.
Local Open Scope logic.

Ltac simplify_remove_localdef_temp ::= rt_rlt.

Lemma trt_clips_ok {Espec : OracleKind} Q P gv vc vd wbits n b D O dict dp op ddp cp pos out z L
    (X Y : environ -> mpred) :
  dict_ifacts Q P -> dw_hf wbits n b D O dict dp op ddp cp -> 6 <= Zlength O ->
  P wbits dict D O pos out z L -> swfW (l_s L) -> zf_ok z -> live_ok L ->
  zf_ni z = offset_val pos cp -> zf_no z = offset_val (Zlength out) op ->
  semax Delta_drt (trt_mid0 n b D O dict dp op ddp cp gv vc vd pos out z L) trt_clips
    (loop1_ret_assert (trt_cont P wbits n b D O dict dp op ddp cp gv vc vd)
       (overridePost X (overridePost Y POST_drt))).
Proof.
  intros PF HF H6O HP Hsw Zo Lo Hni Hno.
  pose proof HF as HF'. destruct HF' as (DF & CF & HO & Hb & BD & BO & Pcp).
  destruct CF as (Hn & HD & ID & Pdp & Pop & Hdl & IDd & Pddp & Hw).
  unfold max_size in Hn.
  destruct (di_ok _ _ PF _ _ _ _ _ _ _ _ HP) as (Hhd & Hwr & Hpos & rest & Erest).
  assert (Hout: Zlength out <= n) by (rewrite <- HD, Erest, Zlength_app; pose proof (Zlength_nonneg rest); lia).
  clear Erest rest.
  unfold trt_clips, trt_mid0, Delta_drt, POST_drt. abbreviate_semax.
  unfold rtl_tup. rewrite Hni, Hno.
  forward_call (Zlength O - pos).
  forward.
  forward_call (n - Zlength out).
  forward.
  unfold MORE_COMMANDS, POSTCONDITION, abbreviate.
  apply (trt_call_ok Q P gv vc vd wbits n b D O dict dp op ddp cp pos out z L X Y PF HF H6O HP Hsw Zo Lo).
Qed.
