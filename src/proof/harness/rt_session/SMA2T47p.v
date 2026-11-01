(* Law rt_session, main's statement 46, `if (!got.extra || !got.name || !got.comment) return 0;`: the first
   operand (temporary _t'47, loads of got.extra and got.name) when got.extra is not NULL, by the cases of
   got.name. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.Rep.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rt_session.SCS.
Require Import Zlib.proof.harness.rt_session.SMainStmt.
Require Import Zlib.proof.harness.rt_session.SMKit.
Require Import Zlib.proof.harness.rt_session.SMA2Kit.
Require Import Zlib.harness.rt_session.code.
#[local] Existing Instance SCS.CS.
Local Open Scope logic.

(* got.extra not NULL, got.name NULL or not *)
Lemma a2_t47_p {Espec : OracleKind} gv vh vg vc va vd u :
  su_gxp u <> nullval ->
  semax Delta_s (NS gv vh vg vc va vd u []) J47
    (overridePost (NS gv vh vg vc va vd u [temp _t'47 (vb (f47 u))]) POST_s).
Proof.
  intros Hq. unfold f47, J47. a2_tstart u.
  destruct (eq_dec gxp nullval) as [Pq | Pq]; [contradiction | ].
  rewrite (new0_cnew gxp _ Pq). a2_mkptr gxp bq oq.
  forward.
  forward_if.
  - a2_tceq.
  - a2_nob.
  - destruct (eq_dec gnp nullval) as [Pn | Pn].
    + subst gnp. rewrite new0_null. forward. forward. a2_end.
    + rewrite (new0_cnew gnp _ Pn). a2_mkptr gnp bn on.
      forward. forward. { a2_tceq. }
      a2_end.
Qed.
