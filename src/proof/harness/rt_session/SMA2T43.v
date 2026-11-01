(* Law rt_session, main's statement 45: the operand setting _t'43 = _t'42 || !comment_copy when _t'42 is 0, by the
   cases of comment_copy. *)
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

Lemma a2_t43_f {Espec : OracleKind} gv vh vg vc va vd u :
  f42 u = false ->
  semax Delta_s (NS gv vh vg vc va vd u [temp _t'42 (vb (f42 u))]) I43
    (overridePost (NS gv vh vg vc va vd u [temp _t'43 (vb (f43 u))]) POST_s).
Proof.
  intros Hf. unfold f43. rewrite Hf. cbn [orb]. unfold I43. a2_tstart u.
  change (vb false) with (Vint Int.zero). forward_if; [ a2_nob | ].
  destruct (eq_dec ccp nullval) as [Pq | Pq].
  - subst ccp. rewrite obj0_null. forward. a2_end.
  - rewrite (obj0_bobj ccp _ Pq). a2_mkptr ccp bq oq.
    forward. { a2_tceq. }
    a2_end.
Qed.
