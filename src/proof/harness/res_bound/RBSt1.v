(* Law res_bound, main: the stores of text and time (drawn with nondet_u32) into head, msuf 17 -> msuf 19
   (RBStKit.st1_stmt). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DCS Zlib.proof.deflate.Rep Zlib.proof.deflate.DSpec Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.deflate.LawFacts Zlib.proof.deflate.LawFactsW Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.deflate.Obligations.
Require Zlib.proof.harness.bound_common.BoundKit Zlib.proof.harness.deflate_bound.MainKit.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.res_bound.RBCS Zlib.proof.harness.res_bound.RBString Zlib.proof.harness.res_bound.RBKit.
Require Import Zlib.proof.harness.res_bound.RBStKit.
Require Import Zlib.harness.res_bound.code.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.

Lemma st1 : st1_stmt.
Proof.
  intros Espec gv vh vs rs HB.
  unfold A1, msuf17, POST_m, Delta_m, rs_locals. simplify_func_tycontext.
  cbn [app]. Intros.
  forward_call tt. Intros t1. forward.
  forward_call tt. Intros t2. forward.
  apply (semax_pre (Ahd2 gv vh vs rs (Int.signed (Int.repr t1)) t2)).
  2: apply HB.
  unfold Ahd2, rs_locals, hval2; cbn [app].
  unfold vi, vl. rewrite !Int.repr_signed, Int.unsigned_repr by rep_lia.
  pose proof (Int.signed_range (Int.repr t1)).
  entailer!.
Qed.
