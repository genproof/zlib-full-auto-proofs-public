(* Law rj_uncompress_any: the entries of RUAsmKit.G_top, from main's body (RUMainDefs.body_main_stmt with the
   theory UTheoryWAny.uw_any_stmt), the helpers of laws_common.h (laws_common_ok; copy_of's variant for a Z_NULL
   source, CopyOfNull.copy_of_n_stmt) and uncompr.c's uncompress2(_z) for any sizes with possibly Z_NULL buffers
   (USpecW.uncompr_bodies_w_stmt).  The entries use rt_roundtrip's tactics (rt_roundtrip/WAsmKit.v w_entry). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.laws_common.CopyOfNull.
Require Import Zlib.proof.uncompr.USpecW.
Require Import Zlib.proof.uncompr.UTheoryWAny.
Require Zlib.proof.inflate_api.SpecWLib.
Require Zlib.proof.harness.rt_roundtrip.WAsmKit.
Require Import Zlib.proof.harness.rj_uncompress_any.RUCS.
Require Import Zlib.proof.harness.rj_uncompress_any.RUMainDefs.
Require Import Zlib.proof.harness.rj_uncompress_any.RUAsmKit.
#[local] Existing Instance Zlib.proof.harness.rj_uncompress_any.RUCS.CS.

Lemma ru_entries_top :
  laws_common_ok -> copy_of_n_stmt -> Zlib.proof.inflate_api.SpecWLib.specw_bridge_stmt ->
  body_main_stmt -> uncompr_bodies_w_stmt -> uw_any_stmt ->
  ru_entries G_top.
Proof.
  intros LC CN BR BM HU UA.
  pose proof (main_entry BM UA) as M.
  pose proof (CN LC) as B_copy.
  destruct LC as (B_upto & _ & B_any & _ & B_eq & _ & _).
  destruct (HU NullExtension.Espec) as (U_u2z & U_u2).
  unfold ru_entries, G_top.
  Zlib.proof.harness.rt_roundtrip.WAsmKit.w_entry M BR.
  Zlib.proof.harness.rt_roundtrip.WAsmKit.w_entry B_upto BR.
  Zlib.proof.harness.rt_roundtrip.WAsmKit.w_entry B_any BR.
  Zlib.proof.harness.rt_roundtrip.WAsmKit.w_entry B_copy BR.
  Zlib.proof.harness.rt_roundtrip.WAsmKit.w_entry B_eq BR.
  Zlib.proof.harness.rt_roundtrip.WAsmKit.w_entry U_u2z BR.
  Zlib.proof.harness.rt_roundtrip.WAsmKit.w_entry U_u2 BR.
  apply Forall_nil.
Qed.
