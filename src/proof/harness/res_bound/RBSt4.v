(* Law res_bound, main: head.name (the name's object when bit 2 of choice is set, else Z_NULL), msuf 23 ->
   msuf 24 (RBStKit.st4_stmt). *)
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

Lemma st4 : st4_stmt.
Proof.
  intros Espec gv vh vs rs hv HB.
  unfold Ahd, msuf23, POST_m, Delta_m, rs_locals. simplify_func_tycontext.
  cbn [app]. Intros.
  pose proof H as OK. unfold rs_ok in OK.
  destruct OK as (_ & _ & _ & _ & _ & Hch & _).
  ifptr _t'26 (selp rs 4 (r_np rs)); [ forward; entailer!; selp_tac .. | ].
  forward.
  apply (semax_pre (Ahd gv vh vs rs hv (hval7 rs hv))).
  2: apply HB.
  unfold Ahd, rs_locals, hval6, hval7; cbn [app].
  entailer!.
Qed.
