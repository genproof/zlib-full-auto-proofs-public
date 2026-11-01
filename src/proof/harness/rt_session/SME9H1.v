(* Law rt_session (harness/rt_session.c), main's header checks: the first test of statement 78 (got.done == 1 && got.text == (text != 0)), from SME9Kit.Q9. *)
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

Lemma e78a_ok {Espec : OracleKind} gv vh vg vc va vd u vxf vxl :
  semax Delta_s (Q9 gv vh vg vc va vd u vxf vxl [] (rest78 u)) E78a
    (overridePost (Q9 gv vh vg vc va vd u vxf vxl [temp _t'88 (Vint Int.one)] (rest78 u)) POST_s).
Proof.
  unfold Q9, E78a, locals9, lvs, lv_locals, c_locals, d_locals.
  unfold Delta_s; simplify_func_tycontext. abbreviate_semax.
  Intros. cbn [app].
  pose proof (su_ok_e9 u ltac:(assumption)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Rt & _).
  unfold gotv, rest78.
  freeze [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12] FR0.
  forward.
  forward_if.
  { forward. forward. rewrite (E9K7.flag_eq (su_text u) Rt).
    destruct POST_s as [r1 r2 r3 r4]. cbn [tycontext.RA_normal]. thaw FR0.
    unfold gotv, rest78. cbn [app]. entailer!. }
  { exfalso. auto. }
Qed.
