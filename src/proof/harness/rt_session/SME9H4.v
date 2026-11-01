(* Law rt_session (harness/rt_session.c), main's header checks: statement 79's gp_assert. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rt_session.SCS.
Require Import Zlib.proof.harness.rt_session.SMainStmt.
Require Import Zlib.proof.harness.rt_session.SMKit.
Require Import Zlib.proof.harness.rt_session.SME9Kit.
Require Zlib.proof.harness.rt_gzip_header.G2MS7Kit.
Require Import Zlib.harness.rt_session.code.
#[local] Existing Instance SCS.CS.
Local Open Scope logic.
Require Import Zlib.proof.harness.rt_session.SME9H3.

Lemma e79b_ok {Espec : OracleKind} gv vh vg vc va vd u vxf vxl :
  semax Delta_s (Q9 gv vh vg vc va vd u vxf vxl [temp _t'90 (Vint Int.one)] (rest78 u)) E79b
    (overridePost (Q9 gv vh vg vc va vd u vxf vxl [] (rest78 u)) POST_s).
Proof.
  unfold E79b.
  unfold Q9, locals9, lvs, lv_locals, c_locals, d_locals.
  unfold Delta_s; simplify_func_tycontext. abbreviate_semax.
  Intros. cbn [app].
  forward_call (Int.repr 1).
  destruct POST_s as [r1 r2 r3 r4]. cbn [tycontext.RA_normal]. unfold rest78. cbn [app]. entailer!.
Qed.

Lemma e79_ok {Espec : OracleKind} gv vh vg vc va vd u vxf vxl :
  semax Delta_s (Q9 gv vh vg vc va vd u vxf vxl [] (rest78 u)) E79
    (overridePost (Q9 gv vh vg vc va vd u vxf vxl [] (rest78 u)) POST_s).
Proof.
  rewrite E79_split. eapply semax_seq; [ | apply e79b_ok ]. apply e79a_ok.
Qed.
