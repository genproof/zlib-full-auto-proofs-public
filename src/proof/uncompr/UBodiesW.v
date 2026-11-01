(* The bodies of uncompr.c's uncompress2_z and uncompress2 for any sizes, with a destination and a source that may
   be Z_NULL (USpecW.v).  uncompress2_z's body: for a source object (snull = false) the chain of its segments of
   UWSegs.v: the checks (UWSegP1.v), the stores into the stream (UWSegP2.v), inflateInit and the loop's entry
   (UWSegP3.v), the loop (UWSegLoop.v), the end (UWSegExit.v); for a Z_NULL source of length 0 (snull = true) the
   same cuts with no input (UWNSegs.v).  Each chain's pre- and postcondition differ from the specification's only
   in how the source's resource is written (src_rep). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Uncompr.
Require Import Zlib.uncompr.code.
Require Import Zlib.proof.uncompr.USpecW.
Require Import Zlib.proof.uncompr.UWSegs.
Require Import Zlib.proof.uncompr.UWNSegs.
Require Import Zlib.proof.uncompr.UWSegP1.
Require Import Zlib.proof.uncompr.UWSegP2.
Require Import Zlib.proof.uncompr.UWSegP3.
Require Import Zlib.proof.uncompr.UWSegLoop.
Require Import Zlib.proof.uncompr.UWSegExit.
Require Import Zlib.proof.uncompr.UWNSegP1.
Require Import Zlib.proof.uncompr.UWNSegP23.
Require Import Zlib.proof.uncompr.UWNSegLoop.
Require Import Zlib.proof.uncompr.UWNSegExit.
#[local] Existing Instance Zlib.units.Uncompr.CS.

(* the postconditions of the chains are the specification's (src_rep unfolded): the return case, the others
   are False *)
Ltac uw_post_tac :=
  intros vl; cbn [RA_return frame_ret_assert function_body_ret_assert]; apply andp_left2; intros rho;
  apply sepcon_derives; [| apply derives_refl];
  unfold bind_ret; destruct vl; [| apply derives_refl]; simpl;
  apply andp_derives; [apply derives_refl |]; unfold liftx; simpl;
  let r := fresh "r" in let slen := fresh "slen" in let dlen := fresh "dlen" in let out := fresh "out" in
  apply exp_left; intro r; apply exp_right with r; apply exp_left; intro slen; apply exp_right with slen;
  apply exp_left; intro dlen; apply exp_right with dlen; apply exp_left; intro out; apply exp_right with out;
  unfold src_rep; unfold PROPx, LOCALx, SEPx; simpl; rewrite ?emp_sepcon, ?sepcon_assoc; apply derives_refl.

Lemma body_uncompress2_z_w :
  semax_body UBodies5.Vprog_uncompr5 Gp_uncompress2_z_w f_uncompress2_z uncompress2_z_spec_w.
Proof.
  start_function.
  assert_PROP (isptr v_stream) as Pv by entailer!.
  destruct snull.
  - (* a Z_NULL source of length 0: the chain of UWNSegs.v *)
    destruct H0 as (-> & -> & -> & -> & ->). unfold src_rep. rewrite Zlength_nil.
    pose (A := UNA gv dnull dsh dp dn dc cap dlp dtok slp gsh tsh).
    assert (F: un_facts A) by (simpl; tauto).
    pose proof (un_p1 Espec A v_stream F (un_p2 Espec A v_stream F (un_p3 Espec A v_stream F Pv
                  (un_loop Espec A v_stream F Pv (un_exit Espec A v_stream F Pv))))) as X.
    subst MORE_COMMANDS POSTCONDITION Delta Delta_specs. unfold abbreviate.
    eapply semax_pre_post; [ | | | | | exact X]; subst A.
    + unfold PRE_un. entailer!.
    + unfold POST_un. simpl. intros. normalize.
    + unfold POST_un. simpl. intros. normalize.
    + unfold POST_un. simpl. intros. normalize.
    + unfold POST_un. uw_post_tac.
  - (* a source object: the chain of UWSegs.v *)
    destruct H0 as (Hsp & Hsn & Hsl & Hsc & Hsmax & Hsub).
    pose (A := UWA gv dnull dsh dp dn dc cap dlp dtok stok ssh sp sn sc src slp gsh tsh).
    assert (F: uw_facts A) by (simpl; tauto).
    pose proof (uw_p1 Espec A v_stream F (uw_p2 Espec A v_stream F (uw_p3 Espec A v_stream F Pv
                  (uw_loop Espec A v_stream F Pv (uw_exit Espec A v_stream F Pv))))) as X.
    subst MORE_COMMANDS POSTCONDITION Delta Delta_specs. unfold abbreviate.
    eapply semax_pre_post; [ | | | | | exact X]; subst A.
    + unfold PRE_uw, src_rep. entailer!.
    + unfold POST_uw. simpl. intros. normalize.
    + unfold POST_uw. simpl. intros. normalize.
    + unfold POST_uw. simpl. intros. normalize.
    + unfold POST_uw. uw_post_tac.
Qed.

Lemma body_uncompress2_w :
  semax_body UBodies5.Vprog_uncompr5 [uncompress2_z_spec_w] f_uncompress2 uncompress2_spec_w.
Proof.
  start_function.
  forward. forward. forward. forward.
  forward_call (gv, dnull, dsh, dp, dn, dc, cap, v_got, dtok, snull, stok, ssh, sp, sn, sc, src, v_used, gsh, tsh).
  Intros vret. destruct vret as [[[r slen] dlen] out]. simpl fst; simpl snd.
  forward. forward. forward. forward. forward.
  Exists r slen dlen out. entailer!.
Qed.

Lemma uncompr_bodies_w : uncompr_bodies_w_stmt.
Proof.
  intros Espec. split.
  - apply body_uncompress2_z_w.
  - apply body_uncompress2_w.
Qed.
