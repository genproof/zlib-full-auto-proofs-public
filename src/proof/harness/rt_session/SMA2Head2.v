(* Law rt_session, main's statements 35-36: head's fields extra (the object when bit 2 of choice is set, else
   Z_NULL) and extra_len. *)
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

Lemma a2_head2 {Espec : OracleKind} gv vh vg vc va vd u dcp xcp ncp ccp ep cp op :
  semax Delta_s (QH gv vh vg vc va vd u dcp xcp ncp ccp ep cp op (h2 u))
    (Ssequence S35 S36)
    (overridePost (QH gv vh vg vc va vd u dcp xcp ncp ccp ep cp op (hv (vi (su_text u)) (vl (su_time u))
       (vi (su_os u)) (selp u 2 (su_xp u)) (vi (Zlength (su_xf u))) U U (vi (su_hcrc u)))) POST_s).
Proof.
  unfold QH, Qs, base, ctemps, cobjs, h2, hv, h00, gw, U, lvs, lv_locals, o_locals, d_locals, S35, S36.
  cbn [app].
  unfold Delta_s; simplify_func_tycontext. abbreviate_semax.
  Intros. a2_facts.
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?S))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _t'35 (selp u 2 (su_xp u)) :: L) (SEPx S))) end.
  - forward. rewrite (selp_nz u 2 (su_xp u)) by (auto; rep_lia). entailer!.
  - forward. rewrite (selp_zero u 2 (su_xp u)) by (auto; rep_lia). entailer!.
  - forward. forward.
    destruct POST_s as [r1 r2 r3 r4]; cbn [tycontext.RA_normal].
    unfold QH, Qs, base, ctemps, cobjs, hv, h00, gw, U, lvs, lv_locals, o_locals, d_locals.
    cbn [app].
    rewrite Int64.Z_mod_modulus_eq, (Z.mod_small (Zlength (su_xf u))) by rep_lia.
    fold (vi (Zlength (su_xf u))).
    entailer!.
Qed.
