(* Law rt_session, main's statement 45: the operands setting _t'42 .. _t'44 when the previous temporary is 1
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

(* _t'42 = 1 when _t'41 is 1 *)
Lemma a2_t42_t {Espec : OracleKind} gv vh vg vc va vd u :
  f41 u = true ->
  semax Delta_s (NS gv vh vg vc va vd u [temp _t'41 (vb (f41 u))]) I42
    (overridePost (NS gv vh vg vc va vd u [temp _t'42 (vb (f42 u))]) POST_s).
Proof.
  intros Hf. unfold f42. rewrite Hf. cbn [orb]. unfold I42. a2_tstart u.
  change (vb true) with (Vint Int.one). forward_if; [ forward; a2_end | a2_nob ].
Qed.

(* _t'43 = 1 when _t'42 is 1 *)
Lemma a2_t43_t {Espec : OracleKind} gv vh vg vc va vd u :
  f42 u = true ->
  semax Delta_s (NS gv vh vg vc va vd u [temp _t'42 (vb (f42 u))]) I43
    (overridePost (NS gv vh vg vc va vd u [temp _t'43 (vb (f43 u))]) POST_s).
Proof.
  intros Hf. unfold f43. rewrite Hf. cbn [orb]. unfold I43. a2_tstart u.
  change (vb true) with (Vint Int.one). forward_if; [ forward; a2_end | a2_nob ].
Qed.

(* _t'44 = 1 when _t'43 is 1 *)
Lemma a2_t44_t {Espec : OracleKind} gv vh vg vc va vd u :
  f43 u = true ->
  semax Delta_s (NS gv vh vg vc va vd u [temp _t'43 (vb (f43 u))]) I44
    (overridePost (NS gv vh vg vc va vd u [temp _t'44 (vb (f44 u))]) POST_s).
Proof.
  intros Hf. unfold f44. rewrite Hf. cbn [orb]. unfold I44. a2_tstart u.
  change (vb true) with (Vint Int.one). forward_if; [ forward; a2_end | a2_nob ].
Qed.
