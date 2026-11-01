(* Law rt_session, main's statement 46: the second operand, _t'48 = _t'47 || !got.comment, when _t'47 is 1. *)
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

(* _t'48 = 1 when _t'47 is 1 *)
Lemma a2_t48_t {Espec : OracleKind} gv vh vg vc va vd u :
  f47 u = true ->
  semax Delta_s (NS gv vh vg vc va vd u [temp _t'47 (vb (f47 u))]) J48
    (overridePost (NS gv vh vg vc va vd u [temp _t'48 (vb (f48 u))]) POST_s).
Proof.
  intros Hf. unfold f48. rewrite Hf. cbn [orb]. unfold J48. a2_tstart u.
  change (vb true) with (Vint Int.one). forward_if; [ forward; a2_end | a2_nob ].
Qed.
