(* Law rt_session (harness/rt_session.c), main's header checks: the test of statement 79 (got.os == (os & 255) && got.time == time). *)
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

Lemma e79a_ok {Espec : OracleKind} gv vh vg vc va vd u vxf vxl :
  semax Delta_s (Q9 gv vh vg vc va vd u vxf vxl [] (rest78 u)) E79a
    (overridePost (Q9 gv vh vg vc va vd u vxf vxl [temp _t'90 (Vint Int.one)] (rest78 u)) POST_s).
Proof.
  unfold E79a.
  unfold Q9, locals9, lvs, lv_locals, c_locals, d_locals.
  unfold Delta_s; simplify_func_tycontext. abbreviate_semax.
  Intros. cbn [app].
  unfold gotv, rest78.
  freeze [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12] FR0.
  forward.
  forward_if.
  { forward. forward.
    destruct POST_s as [r1 r2 r3 r4]. cbn [tycontext.RA_normal]. thaw FR0.
    unfold gotv, rest78. cbn [app]. entailer!. unfold Int64.cmpu. rewrite Int64.eq_true. reflexivity. }
  { exfalso. match goal with H : Int.repr (Z.land _ 255) <> _ |- _ => apply H end.
    apply Int.same_if_eq, E9K7.os_eq. }
Qed.
