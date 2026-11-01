(* Law rt_session, main's statement 45: the operand setting _t'46 = _t'45 || !out when _t'45 is 0, by the
   cases of out. *)
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

Lemma a2_t46_f {Espec : OracleKind} gv vh vg vc va vd u :
  f45 u = false ->
  semax Delta_s (NS gv vh vg vc va vd u [temp _t'45 (vb (f45 u))]) I46
    (overridePost (NS gv vh vg vc va vd u [temp _t'46 (vb (f46 u))]) POST_s).
Proof.
  intros Hf. unfold f46. rewrite Hf. cbn [orb]. unfold I46. a2_tstart u.
  change (vb false) with (Vint Int.zero). forward_if; [ a2_nob | ].
  destruct (eq_dec op nullval) as [Pq | Pq].
  - subst op. rewrite new0_null. forward. a2_end.
  - rewrite (new0_cnew op _ Pq). a2_mkptr op bq oq.
    forward. { a2_tceq. }
    a2_end.
Qed.
