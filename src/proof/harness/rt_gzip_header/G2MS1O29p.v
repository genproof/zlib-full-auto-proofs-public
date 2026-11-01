(* Law rt_gzip_header, main's body, segment 1, statement 33: _t'29 = _t'28 || !got.extra when _t'28 is 0 and
   got.extra is not NULL. *)
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

Lemma g1f29p_ok {Espec : OracleKind} gv vh vg vc vd vr g :
  f28 g = false -> g_gxp g <> nullval ->
  semax Delta_m (NS gv vh vg vc vd vr g [temp _t'28 (vb (f28 g))]) I29
    (overridePost (NS gv vh vg vc vd vr g [temp _t'29 (vb (f29 g))]) POST_m).
Proof.
  intros Hf Hq. unfold f29. rewrite Hf. cbn [orb].
  unfold NS, I29, gs_ok0, gp_locals, gs_locals, lv_locals, hvals, hval, gval, nb. s1_destr_g g. cbn [app].
  unfold Delta_m; simplify_func_tycontext. abbreviate_semax.
  Intros. s1_facts.
  destruct (eq_dec gxp nullval) as [Pq | Pq]; [contradiction | ].
  change (vb false) with (Vint Int.zero). forward_if; [ s1_nob | ].
  rewrite (new0_cnew gxp xl Pq). s1_mkptr gxp bq oq.
  forward.
  forward. { s1_tceq. }
  s1_end.
Qed.
