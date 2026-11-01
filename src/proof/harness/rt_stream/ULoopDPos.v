(* Law rt_stream: the compressor and the struct position for laws_session.h's position_of and unmoved.

   deflate.c's specifications hold a live z_stream field by field at Ews (DSpec.dstream: the state pointer, the
   allocator fields, reserved, and data_type inside the deflate_state's trees_at; DSpec.api_fields: the caller's
   fields), with the complement of Ews and the struct's padding kept aside (BoundKit.Ecomp, BoundKit.strm_pad).
   position_of and unmoved take the whole struct at Ews as one [data_at] at laws_session's compspecs
   (Spec.CS_session).  [strm_lend] lends it and gives the fields back by a wand; it is stated for any live
   compressor between deflate() calls, so every law that drives deflate this way can use it.  [cstream_lend] is
   the same for rt_stream's [cstream].

   main's local struct position [at] is any bytes at the law's compspecs between the calls, and at laws_session's
   compspecs when position_of writes it and unmoved reads it ([at_cs], [at_free]). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.DSpec.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.proof.harness.laws_session.Spec.
Require Import Zlib.proof.harness.rt_stream.LawCS.
Require Import Zlib.proof.harness.rt_stream.UMainKit.
Require Import Zlib.proof.harness.rt_stream.ULoopDKit.
Require Zlib.deflate.code.
Require Zlib.trees.code.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.
Module LS := Zlib.proof.harness.laws_session.Spec.
Module DC := Zlib.deflate.code.
Module TC := Zlib.trees.code.

(* lending [B] out of [A'] (an unfolded form of [A]) with a wand back to [A] *)
Lemma lend_frame (A' A B R : mpred) : (A' |-- B * R) -> (B * R |-- A) -> A' |-- B * (B -* A).
Proof.
  intros H1 H2. eapply derives_trans; [exact H1 |]. apply sepcon_derives; [apply derives_refl |].
  apply wand_sepcon_adjoint. rewrite sepcon_comm. exact H2.
Qed.

(* trees.c's part of the deflate_state without strm->data_type (which trees_at keeps, TRep.dtype_at) *)
Definition trees_nodt (cs : tstate * list bool) (sp pbp strmp : val) (gv : globals) : mpred :=
  ltree_at (tr_ltree (fst cs)) sp * dtree_at (tr_dtree (fst cs)) sp * bltree_at (tr_bltree (fst cs)) sp *
  ldesc_at (field_address t_ds (DOT TC._dyn_ltree) sp) (tr_lmax (fst cs)) (gv TC._static_l_desc) sp *
  ddesc_at (field_address t_ds (DOT TC._dyn_dtree) sp) (tr_dmax (fst cs)) (gv TC._static_d_desc) sp *
  bldesc_at (field_address t_ds (DOT TC._bl_tree) sp) (tr_blmax (fst cs)) (gv TC._static_bl_desc) sp *
  work_at (tr_wk (fst cs)) sp * out_at (tr_out (fst cs)) (snd cs) sp pbp * sym_at (fst cs) sp pbp *
  lvl_at (fst cs) sp * field_at Ews t_ds (DOT TC._strm) strmp sp.

(* a live compressor without the fourteen fields of its z_stream and their padding *)
Definition dstrm_rest (gv : globals) (p : val) (s : dstate) (p0 : dptrs) : mpred :=
  zfuncs gv * trees_nodt (d_trm s) (p_s p0) (p_pbuf p0) p gv * win_at s p0 * hash_at s p0 * match_at s p0 *
  cfg_at s p0 * stat_at s p0 * dtokens s p0 * data_at_ BoundKit.Ecomp t_strm p.

(** ** The compressor lent as one z_stream *)

(* the z_stream at laws_session's compspecs, field by field at deflate.c's, with the padding *)
Lemma zs_fields (p : val) (c : LS.posz) (msgv st za zf op dt ad rs : val) :
  @data_at LS.CS_session Ews t_zs (LS.zs_of c (msgv, st, za, zf, op, dt, ad, rs)) p =
  field_at Ews t_strm (DOT DC._next_in) (LS.pz_next_in c) p *
  field_at Ews t_strm (DOT DC._avail_in) (vi (LS.pz_avail_in c)) p *
  field_at Ews t_strm (DOT DC._total_in) (vl (LS.pz_total_in c)) p *
  field_at Ews t_strm (DOT DC._next_out) (LS.pz_next_out c) p *
  field_at Ews t_strm (DOT DC._avail_out) (vi (LS.pz_avail_out c)) p *
  field_at Ews t_strm (DOT DC._total_out) (vl (LS.pz_total_out c)) p *
  field_at Ews t_strm (DOT DC._msg) msgv p * field_at Ews t_strm (DOT DC._state) st p *
  field_at Ews t_strm (DOT DC._zalloc) za p * field_at Ews t_strm (DOT DC._zfree) zf p *
  field_at Ews t_strm (DOT DC._opaque) op p * field_at Ews t_strm (DOT DC._data_type) dt p *
  field_at Ews t_strm (DOT DC._adler) ad p * field_at Ews t_strm (DOT DC._reserved) rs p *
  BoundKit.strm_pad p.
Proof.
  transitivity (@data_at LawCS.CS Ews t_z (LS.zs_of c (msgv, st, za, zf, op, dt, ad, rs)) p).
  { apply equal_f. apply (@data_at_change_composite _ _ CC_session); [apply JMeq_refl | reflexivity]. }
  transitivity (@data_at DCS.CS Ews t_strm (LS.zs_of c (msgv, st, za, zf, op, dt, ad, rs)) p).
  { symmetry. apply equal_f. apply (@data_at_change_composite _ _ CC_dcs); [apply JMeq_refl | reflexivity]. }
  unfold BoundKit.strm_pad. unfold_data_at (data_at _ _ _ p). simpl.
  apply pred_ext; cancel.
Qed.

(* a live compressor between deflate() calls (no gzip header), with the complement of Ews and the padding *)
Definition dstrm (gv : globals) (p : val) (s : dstate) (ni : val) (ain tin : Z) (no : val) (aout tout : Z)
    (msgv : val) (adler : Z) : mpred :=
  dstream 2 (Some s) p nullval gv * api_fields p ni ain tin no aout tout msgv adler *
  data_at_ BoundKit.Ecomp t_strm p * BoundKit.strm_pad p.

Lemma strm_lend (gv : globals) (p : val) (s : dstate) (ni : val) (ain tin : Z) (no : val) (aout tout : Z)
    (msgv : val) (adler : Z) :
  dstrm gv p s ni ain tin no aout tout msgv adler |--
  EX r : LS.zs_rest,
    @data_at LS.CS_session Ews t_zs (LS.zs_of (LS.mk_posz ni ain tin no aout tout) r) p *
    (@data_at LS.CS_session Ews t_zs (LS.zs_of (LS.mk_posz ni ain tin no aout tout) r) p -*
     dstrm gv p s ni ain tin no aout tout msgv adler).
Proof.
  unfold dstrm at 1, dstream at 1. Intros p0.
  unfold dstate_at'. simpl Z.eqb. cbv iota.
  unfold dstate_at at 1, trees_at at 1, dtype_at at 1, api_fields at 1. Intros. subst p.
  Exists (msgv, p_s p0, gv DC._zcalloc, gv DC._zcfree, nullval, vi (tr_data_type (fst (d_trm s))), vl adler, Vundef).
  apply (lend_frame _ _ _ (dstrm_rest gv (p_strm p0) s p0)).
  - unfold dstrm_rest, trees_nodt. rewrite zs_fields. cbn [LS.pz_next_in LS.pz_avail_in LS.pz_total_in LS.pz_next_out LS.pz_avail_out LS.pz_total_out].
    unfold field_at_. simpl default_val.
    cancel.
  - unfold dstrm_rest, trees_nodt. rewrite zs_fields.
    cbn [LS.pz_next_in LS.pz_avail_in LS.pz_total_in LS.pz_next_out LS.pz_avail_out LS.pz_total_out].
    unfold dstrm, dstream, api_fields, dstate_at', dstate_at, trees_at, dtype_at. simpl Z.eqb. cbv iota.
    Exists p0. unfold field_at_. simpl default_val. entailer!.
Qed.

(* rt_stream's compressor is such a compressor *)
Lemma cstream_dstrm (gv : globals) (vc : val) (c : cst) :
  cstream gv vc c =
  dstrm gv vc (cs_s c) (cs_ni c) (cs_ain c) (cs_tin c) (cs_no c) (cs_aout c) (cs_tout c) (cs_msgv c) (cs_adler c).
Proof.
  unfold cstream, dstrm, srest.
  rewrite (@data_at__change_composite DCS.CS LawCS.CS CC_dcs BoundKit.Ecomp t_strm) by reflexivity.
  apply pred_ext; cancel.
Qed.

Lemma cstream_lend (gv : globals) (vc : val) (c : cst) :
  cstream gv vc c |--
  EX r : LS.zs_rest,
    @data_at LS.CS_session Ews t_zs (LS.zs_of (cpos c) r) vc *
    (@data_at LS.CS_session Ews t_zs (LS.zs_of (cpos c) r) vc -* cstream gv vc c).
Proof. rewrite cstream_dstrm. apply strm_lend. Qed.

(* the six members of the compressor are well typed *)
Lemma cstream_posz_ok (gv : globals) (vc : val) (c : cst) :
  is_pointer_or_null (cs_ni c) -> is_pointer_or_null (cs_no c) ->
  cstream gv vc c |-- !! LS.posz_ok (cpos c).
Proof.
  intros Hi Ho. unfold cstream, api_fields. Intros. apply prop_right.
  unfold LS.posz_ok, cpos, u32_ok, u64_ok in *; cbn [LS.pz_next_in LS.pz_avail_in LS.pz_total_in LS.pz_next_out
    LS.pz_avail_out LS.pz_total_out]. repeat split; auto; rep_lia.
Qed.

(** ** main's struct position *)

Lemma at_cs (va : val) : @data_at_ LawCS.CS Tsh t_p va = @data_at_ LS.CS_session Tsh LS.t_pos va.
Proof. symmetry. apply equal_f. apply (@data_at__change_composite _ _ CC_session). reflexivity. Qed.

Lemma at_free (a : LS.posz) (va : val) :
  @data_at LS.CS_session Tsh LS.t_pos (LS.pos_of a) va |-- @data_at_ LawCS.CS Tsh t_p va.
Proof. rewrite at_cs. apply data_at_data_at_. Qed.
