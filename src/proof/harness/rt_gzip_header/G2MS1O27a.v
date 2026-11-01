(* Law rt_gzip_header, main's body, segment 1, statement 33: _t'27 = !extra_copy || !name_copy when extra_copy is
   NULL. *)
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

Lemma g1o27_null {Espec : OracleKind} gv vh vg vc vd vr g :
  g_xcp g = nullval ->
  semax Delta_m (NS gv vh vg vc vd vr g []) I27
    (overridePost (NS gv vh vg vc vd vr g [temp _t'27 (vb (f27 g))]) POST_m).
Proof.
  intros Hx. unfold f27.
  unfold NS, I27, gs_ok0, gp_locals, gs_locals, lv_locals, hvals, hval, gval, nb. s1_destr_g g. cbn [app].
  unfold Delta_m; simplify_func_tycontext. abbreviate_semax.
  Intros. s1_facts.
  destruct (eq_dec xcp nullval) as [Px | Px]; [ | contradiction].
  subst xcp. rewrite obj0_null.
  forward_if.
  - forward. s1_end.
  - s1_nob.
Qed.
