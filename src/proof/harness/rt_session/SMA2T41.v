(* Law rt_session, main's statement 45, `if (!dict_copy || !extra_copy || ..) return 0;`: the first operand
   (temporary _t'41) when dict_copy is not NULL, by the cases of extra_copy. *)
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

(* dict_copy not NULL, extra_copy NULL or not *)
Lemma a2_t41_p {Espec : OracleKind} gv vh vg vc va vd u :
  su_dcp u <> nullval ->
  semax Delta_s (NS gv vh vg vc va vd u []) I41
    (overridePost (NS gv vh vg vc va vd u [temp _t'41 (vb (f41 u))]) POST_s).
Proof.
  intros Hx. unfold f41, I41. a2_tstart u.
  destruct (eq_dec dcp nullval) as [Px | Px]; [contradiction | ].
  rewrite (obj0_bobj dcp _ Px). a2_mkptr dcp bx ox.
  destruct (eq_dec xcp nullval) as [Pq | Pq].
  - subst xcp. rewrite obj0_null.
    forward_if.
    + a2_tceq.
    + a2_nob.
    + forward. a2_end.
  - rewrite (obj0_bobj xcp _ Pq). a2_mkptr xcp bq oq.
    forward_if.
    + a2_tceq.
    + a2_nob.
    + forward. { a2_tceq. } a2_end.
Qed.
