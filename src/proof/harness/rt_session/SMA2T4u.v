(* Law rt_session, main's statement 45: the operands setting _t'45 and _t'46 when the previous temporary is 1
   (one of the objects tested before is NULL). *)
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

(* _t'45 = 1 when _t'44 is 1 *)
Lemma a2_t45_t {Espec : OracleKind} gv vh vg vc va vd u :
  f44 u = true ->
  semax Delta_s (NS gv vh vg vc va vd u [temp _t'44 (vb (f44 u))]) I45
    (overridePost (NS gv vh vg vc va vd u [temp _t'45 (vb (f45 u))]) POST_s).
Proof.
  intros Hf. unfold f45. rewrite Hf. cbn [orb]. unfold I45. a2_tstart u.
  change (vb true) with (Vint Int.one). forward_if; [ forward; a2_end | a2_nob ].
Qed.

(* _t'46 = 1 when _t'45 is 1 *)
Lemma a2_t46_t {Espec : OracleKind} gv vh vg vc va vd u :
  f45 u = true ->
  semax Delta_s (NS gv vh vg vc va vd u [temp _t'45 (vb (f45 u))]) I46
    (overridePost (NS gv vh vg vc va vd u [temp _t'46 (vb (f46 u))]) POST_s).
Proof.
  intros Hf. unfold f46. rewrite Hf. cbn [orb]. unfold I46. a2_tstart u.
  change (vb true) with (Vint Int.one). forward_if; [ forward; a2_end | a2_nob ].
Qed.

