(* Law rt_session, main's statement 46: the second operand, _t'48 = _t'47 || !got.comment (a load of
   got.comment), when _t'47 is 0, by the cases of got.comment. *)
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

(* _t'47 is 0: got.comment NULL or not *)
Lemma a2_t48_f {Espec : OracleKind} gv vh vg vc va vd u :
  f47 u = false ->
  semax Delta_s (NS gv vh vg vc va vd u [temp _t'47 (vb (f47 u))]) J48
    (overridePost (NS gv vh vg vc va vd u [temp _t'48 (vb (f48 u))]) POST_s).
Proof.
  intros Hf. unfold f48. rewrite Hf. cbn [orb]. unfold J48. a2_tstart u.
  change (vb false) with (Vint Int.zero). forward_if; [ a2_nob | ].
  destruct (eq_dec gcp nullval) as [Pq | Pq].
  - subst gcp. rewrite new0_null. forward. forward. a2_end.
  - rewrite (new0_cnew gcp _ Pq). a2_mkptr gcp bq oq.
    forward. forward. { a2_tceq. }
    a2_end.
Qed.
