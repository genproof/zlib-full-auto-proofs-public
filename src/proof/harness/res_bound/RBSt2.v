(* Law res_bound, main: the stores of os and hcrc (drawn with nondet_u32) into head, msuf 19 -> msuf 21
   (RBStKit.st2_stmt). *)
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

Lemma st2 : st2_stmt.
Proof.
  intros Espec gv vh vs rs text time HB.
  unfold Ahd2, msuf19, POST_m, Delta_m, rs_locals. simplify_func_tycontext.
  cbn [app]. Intros.
  forward_call tt. Intros t3. forward.
  forward_call tt. Intros t4. forward.
  apply (semax_pre (Ahd gv vh vs rs (mkHV text time (Int.signed (Int.repr t3)) (Int.signed (Int.repr t4)))
    (hval4 (mkHV text time (Int.signed (Int.repr t3)) (Int.signed (Int.repr t4)))))).
  2: apply HB.
  unfold Ahd, rs_locals, hval4, hval2, hv_ok; cbn [app h_text h_time h_os h_hcrc].
  unfold vi, vl. rewrite !Int.repr_signed.
  pose proof (Int.signed_range (Int.repr t3)). pose proof (Int.signed_range (Int.repr t4)).
  entailer!.
Qed.
