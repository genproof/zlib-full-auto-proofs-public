(* Law rt_session, main's statements 37-38: head's fields name and comment (the object when bit 4, 8 of choice is
   set, else Z_NULL). *)
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

Lemma a2_head3 {Espec : OracleKind} gv vh vg vc va vd u dcp xcp ncp ccp ep cp op :
  semax Delta_s (QH gv vh vg vc va vd u dcp xcp ncp ccp ep cp op (hv (vi (su_text u)) (vl (su_time u))
       (vi (su_os u)) (selp u 2 (su_xp u)) (vi (Zlength (su_xf u))) U U (vi (su_hcrc u))))
    (Ssequence S37 S38)
    (overridePost (QH gv vh vg vc va vd u dcp xcp ncp ccp ep cp op (hvals u)) POST_s).
Proof.
  unfold QH, Qs, base, ctemps, cobjs, hv, h00, gw, U, lvs, lv_locals, o_locals, d_locals, S37, S38.
  cbn [app].
  unfold Delta_s; simplify_func_tycontext. abbreviate_semax.
  Intros. a2_facts.
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?S))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _t'36 (selp u 4 (su_np u)) :: L) (SEPx S))) end.
  - forward. rewrite (selp_nz u 4 (su_np u)) by (auto; rep_lia). entailer!.
  - forward. rewrite (selp_zero u 4 (su_np u)) by (auto; rep_lia). entailer!.
  - forward.
    match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?S))) _ _ =>
      forward_if (PROPx P (LOCALx (temp _t'37 (selp u 8 (su_cmp u)) :: L) (SEPx S))) end.
    + forward. rewrite (selp_nz u 8 (su_cmp u)) by (auto; rep_lia). entailer!.
    + forward. rewrite (selp_zero u 8 (su_cmp u)) by (auto; rep_lia). entailer!.
    + forward.
      destruct POST_s as [r1 r2 r3 r4]; cbn [tycontext.RA_normal].
      unfold QH, Qs, base, ctemps, cobjs, hvals, h00, gw, U, lvs, lv_locals, o_locals, d_locals.
      cbn [app].
      entailer!.
Qed.
