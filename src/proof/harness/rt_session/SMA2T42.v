(* Law rt_session, main's statement 45: the operand setting _t'42 = _t'41 || !name_copy when _t'41 is 0, by the
   cases of name_copy. *)
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

Lemma a2_t42_f {Espec : OracleKind} gv vh vg vc va vd u :
  f41 u = false ->
  semax Delta_s (NS gv vh vg vc va vd u [temp _t'41 (vb (f41 u))]) I42
    (overridePost (NS gv vh vg vc va vd u [temp _t'42 (vb (f42 u))]) POST_s).
Proof.
  intros Hf. unfold f42. rewrite Hf. cbn [orb]. unfold I42. a2_tstart u.
  change (vb false) with (Vint Int.zero). forward_if; [ a2_nob | ].
  destruct (eq_dec ncp nullval) as [Pq | Pq].
  - subst ncp. rewrite obj0_null. forward. a2_end.
  - rewrite (obj0_bobj ncp _ Pq). a2_mkptr ncp bq oq.
    forward. { a2_tceq. }
    a2_end.
Qed.
