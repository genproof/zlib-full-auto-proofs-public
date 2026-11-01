(* Law rt_session, main's statement 45: the first operand, _t'41 = !dict_copy || !extra_copy, when dict_copy is
   NULL. *)
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

Lemma a2_t41_n {Espec : OracleKind} gv vh vg vc va vd u :
  su_dcp u = nullval ->
  semax Delta_s (NS gv vh vg vc va vd u []) I41
    (overridePost (NS gv vh vg vc va vd u [temp _t'41 (vb (f41 u))]) POST_s).
Proof.
  intros Hx. unfold f41, I41. a2_tstart u.
  destruct (eq_dec dcp nullval) as [Px | Px]; [ | contradiction].
  subst dcp. rewrite obj0_null.
  forward_if.
  - forward. a2_end.
  - a2_nob.
Qed.
