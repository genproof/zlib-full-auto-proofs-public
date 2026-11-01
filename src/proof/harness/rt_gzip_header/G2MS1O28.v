(* Law rt_gzip_header, main's body, segment 1, statement 33: _t'28 = _t'27 || !comment_copy when _t'27 is 0. *)
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

Lemma g1f28_ok {Espec : OracleKind} gv vh vg vc vd vr g :
  f27 g = false ->
  semax Delta_m (NS gv vh vg vc vd vr g [temp _t'27 (vb (f27 g))]) I28
    (overridePost (NS gv vh vg vc vd vr g [temp _t'28 (vb (f28 g))]) POST_m).
Proof.
  intros Hf. unfold f28. rewrite Hf. cbn [orb].
  unfold NS, I28, gs_ok0, gp_locals, gs_locals, lv_locals, hvals, hval, gval, nb. s1_destr_g g. cbn [app].
  unfold Delta_m; simplify_func_tycontext. abbreviate_semax.
  Intros. s1_facts.
  change (vb false) with (Vint Int.zero). forward_if; [ s1_nob | ].
  destruct (eq_dec ccp nullval) as [Pq | Pq].
  - subst ccp. rewrite obj0_null. forward. s1_end.
  - rewrite (obj0_cobj ccp (cl + 1) (cm ++ [0]) Pq) by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
      s1_mkptr
      ccp bq oq.
    forward. { s1_tceq. }
    s1_end.
Qed.
