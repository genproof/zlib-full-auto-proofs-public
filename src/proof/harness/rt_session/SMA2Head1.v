(* Law rt_session, main's statements 31-34: head's fields text, time, os and hcrc. *)
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

Lemma a2_head1 {Espec : OracleKind} gv vh vg vc va vd u dcp xcp ncp ccp ep cp op :
  semax Delta_s (QH gv vh vg vc va vd u dcp xcp ncp ccp ep cp op h00)
    (Ssequence S31 (Ssequence S32 (Ssequence S33 S34)))
    (overridePost (QH gv vh vg vc va vd u dcp xcp ncp ccp ep cp op (h2 u)) POST_s).
Proof.
  unfold QH, Qs, base, ctemps, cobjs, h00, gw, U, lvs, lv_locals, o_locals, d_locals,
    S31, S32, S33, S34.
  cbn [app].
  unfold Delta_s; simplify_func_tycontext. abbreviate_semax.
  Intros. a2_facts.
  forward. forward. forward. forward.
  destruct POST_s as [r1 r2 r3 r4]; cbn [tycontext.RA_normal].
  unfold QH, Qs, base, ctemps, cobjs, h2, hv, h00, gw, U, lvs, lv_locals, o_locals, d_locals.
  cbn [app].
  entailer!.
Qed.
