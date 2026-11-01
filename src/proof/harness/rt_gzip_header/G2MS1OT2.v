(* Law rt_gzip_header, main's body, segment 1, statement 33: _t'30 and _t'31 when the previous temporary is 1. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.Rep.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rt_gzip_header.CS.
Require Import Zlib.proof.harness.rt_gzip_header.G2MainDefs.
Require Import Zlib.proof.harness.rt_gzip_header.G2MainKit.
Require Import Zlib.proof.harness.rt_gzip_header.G2MS1Kit.
Require Import Zlib.harness.rt_gzip_header.code.
#[local] Existing Instance Zlib.proof.harness.rt_gzip_header.CS.CS.
Local Open Scope logic.

Lemma g1t30_ok {Espec : OracleKind} gv vh vg vc vd vr g :
  f29 g = true ->
  semax Delta_m (NS gv vh vg vc vd vr g [temp _t'29 (vb (f29 g))]) I30
    (overridePost (NS gv vh vg vc vd vr g [temp _t'30 (vb (f30 g))]) POST_m).
Proof.
  intros Hf. unfold f30. rewrite Hf. cbn [orb].
  unfold NS, I30, gs_ok0, gp_locals, gs_locals, lv_locals, hvals, hval, gval, nb. s1_destr_g g. cbn [app].
  unfold Delta_m; simplify_func_tycontext. abbreviate_semax.
  Intros. s1_facts.
  change (vb true) with (Vint Int.one). forward_if; [ forward; s1_end | s1_nob ].
Qed.

Lemma g1t31_ok {Espec : OracleKind} gv vh vg vc vd vr g :
  f30 g = true ->
  semax Delta_m (NS gv vh vg vc vd vr g [temp _t'30 (vb (f30 g))]) I31
    (overridePost (NS gv vh vg vc vd vr g [temp _t'31 (vb (f31 g))]) POST_m).
Proof.
  intros Hf. unfold f31. rewrite Hf. cbn [orb].
  unfold NS, I31, gs_ok0, gp_locals, gs_locals, lv_locals, hvals, hval, gval, nb. s1_destr_g g. cbn [app].
  unfold Delta_m; simplify_func_tycontext. abbreviate_semax.
  Intros. s1_facts.
  change (vb true) with (Vint Int.one). forward_if; [ forward; s1_end | s1_nob ].
Qed.
