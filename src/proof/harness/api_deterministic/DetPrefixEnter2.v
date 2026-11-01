(* Law api_deterministic (data of any length): main's body from offered = 0 to the loop
   (DetPrefixKit2.det_enter_stmt): offered, read and flush, then the loop invariant J_at. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Rep.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.deflate.DetFacts2.
Require Zlib.proof.deflate.DModel5.
Require Import Zlib.proof.deflate.DetGz.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.api_deterministic.DetCS2.
Require Import Zlib.proof.harness.api_deterministic.DetMainStmt2.
Require Import Zlib.proof.harness.api_deterministic.DetKit2.
Require Import Zlib.proof.harness.api_deterministic.DetPrefixKit2.
Require Import Zlib.harness.api_deterministic.code.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.

(* after_forward_call builds [remove_localdef_temp] syntactically (DetPrefixKit2.rlt_list) *)
Local Ltac simplify_remove_localdef_temp ::=
  match goal with |- context [remove_localdef_temp ?i ?L] =>
    let u' := rlt_list i L in change (remove_localdef_temp i L) with u' end.

Lemma det_enter : det_enter_stmt.
Proof.
  intros Espec v1 v2 gv J JF level wbits mem strategy n bs datap s z' msgv1 msgv2 sp1 sp2 K.
  unfold P14, P_loc, version_at, msuf14, Delta_m, Gmain, POST_m. simplify_func_tycontext.
  abbreviate_semax. Intros.
  rename H into Hpre, H0 into HJ, H1 into Hgz, H2 into Had, H3 into H7, H4 into H8.
  destruct Hpre as (H3 & H4 & H5 & H6 & H & H0 & H1 & Pdp).
  forward. forward. forward.
  eapply semax_pre; [| apply (K J n bs datap sp1 sp2 (mkLS s None 0 0 0 0 (z_adler z') (z_msg z') msgv1 msgv2))].
  unfold J_at, J_ok, setup_ok, J_loc, J_sep, shead, strm_at, api_fields; cbn [ls_s ls_fin ls_offered ls_read
    ls_flush ls_tout ls_adler ls_msg ls_msgv1 ls_msgv2].
  Exists nullval 0 nullval 0 nullval 0 nullval 0.
  change (bytes_rep bs) with (map vi bs).
  entailer!.
  - unfold bytes, is_bytes, u64r, u32_ok, u64_ok in *. split; [split; [| rep_lia] |].
    + eapply Forall_impl; [| exact H1]. intros b Hb. simpl in Hb. rep_lia.
    + rep_lia.
  - unfold reset_fields. cancel.
Qed.
