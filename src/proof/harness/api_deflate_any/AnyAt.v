(* Law api_deflate_any: the memory of main's locals for laws_session.h's position_of and unmoved.
   - main's two locals between the law's compspecs (AnyCS.CS, main's statement and POST_m's frame) and the
     compspecs main's body is proved at (DCS.CS for the z_stream, laws_session/Spec.v's CS_session for struct
     position);
   - the stream of the kit (DetKit2.strm_at, field by field at DCS.CS) lent as one z_stream at CS_session, as
     position_of and unmoved take it, and given back by a wand;
   - unmoved's pointer comparisons: next_in in the piece and next_out at the start of an output space of 0 bytes,
     each compared with itself, are defined in the memory of the two objects. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Rep.
Require Import Zlib.proof.deflate.DSpec.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.proof.harness.laws_session.Spec.
Require Zlib.proof.harness.api_deterministic.DetKit2.
Require Import Zlib.proof.harness.api_deflate_any.AnyCS.
Require Import Zlib.proof.harness.api_deflate_any.AnyKit.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.
Module DK := Zlib.proof.harness.api_deterministic.DetKit2.
Module LS := Zlib.proof.harness.laws_session.Spec.

(** ** main's locals at the law's compspecs *)
Lemma any_strm_cs (sh : share) (p : val) :
  @data_at_ DCS.CS sh t_strm p = @data_at_ AnyCS.CS sh t_strm p.
Proof. apply equal_f. apply (@data_at__change_composite _ _ CC_dcs). reflexivity. Qed.

Lemma any_at_cs (ap : val) : at_free ap = @data_at_ AnyCS.CS Tsh LS.t_pos ap.
Proof. unfold at_free. apply equal_f. apply (@data_at__change_composite _ _ CC_session). reflexivity. Qed.

(* [at] after the checks: its position is not read any more *)
Lemma any_at_free (a : LS.posz) (ap : val) :
  @data_at LS.CS_session Tsh LS.t_pos (LS.pos_of a) ap |-- at_free ap.
Proof. unfold at_free. apply data_at_data_at_. Qed.

(** ** The stream lent to position_of and unmoved *)

(* the six members a position records, of the kit's stream *)
Definition sposz (nin : val) (ain tin : Z) (nout : val) (aout tout : Z) : LS.posz :=
  LS.mk_posz nin ain tin nout aout tout.

Module DM := Zlib.proof.harness.api_deterministic.DetMem2.
Module DC := Zlib.deflate.code.

(* the converse of DetMem2.det_offer_pre: a whole z_stream at the compress unit's compspecs, split into the
   kit's pieces *)
Lemma any_offer_back (p ni ai tin no ao tout msgv adler sp za zf op dt : val) :
  @data_at Zlib.units.Compress.CS Ews t_zs (zs_val ni ai tin no ao tout msgv sp za zf op dt adler Vundef) p
  |-- field_at Ews t_strm (DOT DC._next_in) ni p * Zlib.proof.deflate.DSpec9.reset_fields p tin tout msgv adler *
      (field_at Ews t_strm (DOT DC._avail_in) ai p * field_at Ews t_strm (DOT DC._next_out) no p *
       field_at Ews t_strm (DOT DC._avail_out) ao p) *
      DM.strm_own p sp za zf op dt * BoundKit.strm_pad p.
Proof.
  rewrite DM.det_strm_cs. unfold Zlib.proof.deflate.DSpec9.reset_fields, DM.strm_own, BoundKit.strm_pad.
  unfold_data_at (data_at _ _ _ p). unfold field_at_; simpl. cancel.
Qed.

(* a z_stream of the kit's members at laws_session's compspecs is the same memory at the compress unit's *)
Lemma any_zs_cs (sh : share) (p : val) (nin : val) (ain tin : Z) (nout : val) (aout tout : Z)
    (msgv st za zf op dt ad rs : val) :
  @data_at LS.CS_session sh t_zs (LS.zs_of (sposz nin ain tin nout aout tout) (msgv, st, za, zf, op, dt, ad, rs)) p =
  @data_at Zlib.units.Compress.CS sh t_zs
    (zs_val nin (vi ain) (vl tin) nout (vi aout) (vl tout) msgv st za zf op dt ad rs) p.
Proof.
  apply equal_f. transitivity (@data_at AnyCS.CS sh t_zs
    (zs_val nin (vi ain) (vl tin) nout (vi aout) (vl tout) msgv st za zf op dt ad rs)).
  - apply (@data_at_change_composite _ _ CC_session); [apply JMeq_refl | reflexivity].
  - symmetry. apply (@data_at_change_composite _ _ CC_compress); [apply JMeq_refl | reflexivity].
Qed.

Lemma any_strm_lend (p : val) (s : dstate) (sp nin : val) (ain tin : Z) (nout : val) (aout tout : Z)
    (msgv : val) (adler : Z) (gv : globals) :
  DK.strm_at p s sp nin ain tin nout aout tout msgv adler gv |--
  EX r : LS.zs_rest,
    @data_at LS.CS_session Ews t_zs (LS.zs_of (sposz nin ain tin nout aout tout) r) p *
    (@data_at LS.CS_session Ews t_zs (LS.zs_of (sposz nin ain tin nout aout tout) r) p -*
     DK.strm_at p s sp nin ain tin nout aout tout msgv adler gv).
Proof.
  unfold DK.strm_at. sep_apply (DK.det_dstream_open s p nullval sp gv). unfold api_fields. Intros.
  Exists (msgv, sp, gv DC._zcalloc, gv DC._zcfree, nullval, DK.det_dt s, vl adler, Vundef).
  rewrite any_zs_cs. unfold DK.strm_own_live.
  apply derives_trans with
    ((@field_at DCS.CS Ews t_strm (DOT DC._next_in) nin p *
      Zlib.proof.deflate.DSpec9.reset_fields p (vl tin) (vl tout) msgv (vl adler) *
      (@field_at DCS.CS Ews t_strm (DOT DC._avail_in) (vi ain) p * @field_at DCS.CS Ews t_strm (DOT DC._next_out) nout p *
       @field_at DCS.CS Ews t_strm (DOT DC._avail_out) (vi aout) p) *
      DM.strm_own p sp (gv DC._zcalloc) (gv DC._zcfree) nullval (DK.det_dt s) * BoundKit.strm_pad p) *
     ((DM.strm_own p sp (gv DC._zcalloc) (gv DC._zcfree) nullval (DK.det_dt s) -*
       dstream_sp 2 (Some s) p nullval sp gv) * @data_at_ DCS.CS BoundKit.Ecomp t_strm p)).
  { unfold Zlib.proof.deflate.DSpec9.reset_fields. cancel. }
  apply sepcon_derives; [apply DM.det_offer_pre |].
  rewrite <- wand_sepcon_adjoint.
  sep_apply (any_offer_back p nin (vi ain) (vl tin) nout (vi aout) (vl tout) msgv (vl adler) sp
               (gv DC._zcalloc) (gv DC._zcfree) nullval (DK.det_dt s)).
  sep_apply (modus_ponens_wand
               (DM.strm_own p sp (gv DC._zcalloc) (gv DC._zcfree) nullval (DK.det_dt s))
               (dstream_sp 2 (Some s) p nullval sp gv)).
  unfold Zlib.proof.deflate.DSpec9.reset_fields. entailer!.
Qed.

(** ** unmoved's comparisons *)

(* a pointer compared with itself: both sides are in one block, so the comparison is defined when the pointer is
   weakly valid *)
Lemma any_test_eq_self (P : mpred) (v : val) :
  isptr v -> (P |-- weak_valid_pointer v) -> P |-- denote_tc_test_eq v v.
Proof.
  intros Hv H. destruct v; try contradiction.
  with_strategy transparent [denote_tc_test_eq] unfold denote_tc_test_eq.
  unfold test_eq_ptrs, sameblock. destruct (peq b b); [| congruence]. cbv [proj_sumbool].
  apply andp_right; exact H.
Qed.

(* next_in at [k] in a piece of bytes [l] and next_out at the start of an output space of 0 bytes (any
   contents [lo], i.e. none), each compared with itself *)
Lemma any_cmp_self (piece out : val) (l : list Z) (k : Z) (lo : list val) :
  0 <= k <= Zlength l ->
  BoundKit.obj piece l * DK.out_at out 0 lo |--
  denote_tc_test_eq (offset_val k piece) (offset_val k piece) &&
  denote_tc_test_eq (offset_val 0 out) (offset_val 0 out).
Proof.
  intros Hk. unfold BoundKit.obj, DK.out_at.
  assert_PROP (isptr piece /\ isptr out) as Hp by entailer!. destruct Hp as [Hp Ho].
  apply andp_right; apply any_test_eq_self.
  - destruct piece; try contradiction. exact I.
  - apply sepcon_weak_valid_pointer1.
    destruct (Z.eq_dec (Zlength l) 0) as [E|E].
    + assert (k = 0) by lia. subst k. rewrite isptr_offset_val_zero by exact Hp.
      apply valid_pointer_weak'. apply sepcon_valid_pointer1.
      apply malloc_token_valid_pointer. rewrite E. simpl. lia.
    + apply sepcon_weak_valid_pointer2.
      eapply derives_trans; [apply data_at_memory_block |].
      apply memory_block_weak_valid_pointer.
      * simpl. rewrite Z.max_r by lia. lia.
      * simpl. rewrite Z.max_r by lia. lia.
      * auto.
  - destruct out; try contradiction. exact I.
  - rewrite isptr_offset_val_zero by exact Ho. apply sepcon_weak_valid_pointer2.
    apply valid_pointer_weak'. apply sepcon_valid_pointer1.
    apply malloc_token_valid_pointer. simpl. lia.
Qed.
