(* Law res_bound, main: head.extra (the extra field's object when bit 1 of choice is set, else Z_NULL) and
   head.extra_len, msuf 21 -> msuf 23 (RBStKit.st3_stmt). *)
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

Lemma st3 : st3_stmt.
Proof.
  intros Espec gv vh vs rs hv HB.
  unfold Ahd, msuf21, POST_m, Delta_m, rs_locals. simplify_func_tycontext.
  cbn [app]. Intros.
  pose proof H as OK. unfold rs_ok in OK.
  destruct OK as (_ & _ & _ & _ & _ & Hch & _ & Hxl & _).
  ifptr _t'25 (selp rs 2 (r_xp rs)); [ forward; entailer!; selp_tac .. | ].
  forward. forward.
  apply (semax_pre (Ahd gv vh vs rs hv (hval6 rs hv))).
  2: apply HB.
  unfold Ahd, rs_locals, hval4, hval6; cbn [app].
  unfold vi, vl. rewrite Int64.Z_mod_modulus_eq, Z.mod_small by rep_lia.
  entailer!.
Qed.
