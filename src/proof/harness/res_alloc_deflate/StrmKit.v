(* The laws res_free_deflate and res_memory_deflate: main's z_stream between the specifications it is handed to.

   laws_common.h's offer and the harness's counted_stream take the whole struct (data_at of t_zs at the
   compress unit's compspecs, any member values); deflate.c's specifications take it member by member at
   deflate.c's compspecs (DCS.CS): the members the application sets and reads ([api_fields], [reset_fields]),
   those of the allocator and the state (inside [dstream_za] once deflateInit2_ succeeded; strm->data_type is
   then a member of the deflate_state's representation, written by deflate()), and the padding [strm_pad].
   - [zs_fields]: the struct is its 14 members and its padding;
   - [dstream_za_open]: a live stream lends offer() the members it holds (state, zalloc, zfree, opaque,
     data_type, reserved) and gets them back unchanged;
   - the returns of main: whatever the stream holds, its memory is again data_at_ Ews t_strm (the rest of
     the stream's memory, the deflate_state and its buffers, is dropped). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.za.deflate.ZSpec.
Require Import Zlib.proof.za.deflate.Obligations.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.bound_common.BoundKit.
Require Zlib.units.Compress Zlib.trees.code.
Require Import Zlib.deflate.code.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.

#[local] Instance CC_compress : change_composite_env Zlib.units.Compress.CS DCS.CS.
Proof. make_cs_preserve Zlib.units.Compress.CS DCS.CS. Defined.

(* the 14 members of a z_stream, at DCS.CS *)
Definition strm_members (sp ni ai ti no ao to msg st za zf op dt ad rs : val) : mpred :=
  field_at Ews t_strm (DOT _next_in) ni sp * field_at Ews t_strm (DOT _avail_in) ai sp *
  field_at Ews t_strm (DOT _total_in) ti sp * field_at Ews t_strm (DOT _next_out) no sp *
  field_at Ews t_strm (DOT _avail_out) ao sp * field_at Ews t_strm (DOT _total_out) to sp *
  field_at Ews t_strm (DOT _msg) msg sp * field_at Ews t_strm (DOT _state) st sp *
  field_at Ews t_strm (DOT _zalloc) za sp * field_at Ews t_strm (DOT _zfree) zf sp *
  field_at Ews t_strm (DOT _opaque) op sp * field_at Ews t_strm (DOT _data_type) dt sp *
  field_at Ews t_strm (DOT _adler) ad sp * field_at Ews t_strm (DOT _reserved) rs sp.

(* the struct at DCS.CS *)
Lemma strm_fields (sp ni ai ti no ao to msg st za zf op dt ad rs : val) :
  @data_at DCS.CS Ews t_strm (zs_val ni ai ti no ao to msg st za zf op dt ad rs) sp =
  strm_members sp ni ai ti no ao to msg st za zf op dt ad rs * strm_pad sp.
Proof.
  unfold strm_members, strm_pad, zs_val.
  apply pred_ext.
  - unfold_data_at (data_at _ _ _ sp). cancel.
  - unfold_data_at (data_at _ _ _ sp). cancel.
Qed.

Lemma zs_fields (sp ni ai ti no ao to msg st za zf op dt ad rs : val) :
  @data_at Zlib.units.Compress.CS Ews t_zs (zs_val ni ai ti no ao to msg st za zf op dt ad rs) sp =
  strm_members sp ni ai ti no ao to msg st za zf op dt ad rs * strm_pad sp.
Proof.
  rewrite <- strm_fields. change t_zs with t_strm.
  rewrite (@data_at_change_composite Zlib.units.Compress.CS DCS.CS CC_compress Ews t_strm _ _ (JMeq_refl _))
    by reflexivity.
  reflexivity.
Qed.

(* the members main's returns give back *)
Lemma strm_members_data_at_ (sp ni ai ti no ao to msg st za zf op dt ad rs : val) :
  strm_members sp ni ai ti no ao to msg st za zf op dt ad rs * strm_pad sp |-- data_at_ Ews t_strm sp.
Proof.
  rewrite <- strm_fields. apply data_at_data_at_.
Qed.

(* the struct as deflateInit2_ wants it, and what is left for after the call *)
Lemma zs_init_pre (sp ni ai ti no ao to msg st za zf op dt ad rs : val) :
  @data_at Zlib.units.Compress.CS Ews t_zs (zs_val ni ai ti no ao to msg st za zf op dt ad rs) sp |--
  field_at Ews t_strm (DOT _next_in) ni sp * reset_fields sp ti to msg ad *
  field_at Ews t_strm (DOT _zalloc) za sp * field_at Ews t_strm (DOT _zfree) zf sp *
  field_at Ews t_strm (DOT _opaque) op sp * field_at Ews t_strm (DOT _data_type) dt sp *
  field_at Ews t_strm (DOT _state) st sp * field_at_ Ews t_strm (DOT _reserved) sp *
  (field_at Ews t_strm (DOT _avail_in) ai sp * field_at Ews t_strm (DOT _next_out) no sp *
   field_at Ews t_strm (DOT _avail_out) ao sp * strm_pad sp).
Proof.
  rewrite zs_fields. unfold strm_members, reset_fields. cancel.
Qed.

(* deflateInit2_ failed: the stream's members, whatever they hold, back to data_at_ *)
Lemma init_fail_back {ZA : zallocator} (sp ni ai ti no ao to msg ad st dt : val) :
  field_at Ews t_strm (DOT _next_in) ni sp * reset_fields sp ti to msg ad *
  (za_funcs * field_at_ Ews t_strm (DOT _reserved) sp * field_at Ews t_strm (DOT _state) st sp *
   field_at Ews t_strm (DOT _zalloc) za_alloc sp * field_at Ews t_strm (DOT _zfree) za_free sp *
   field_at Ews t_strm (DOT _opaque) za_opaque sp * field_at Ews t_strm (DOT _data_type) dt sp) *
  (field_at Ews t_strm (DOT _avail_in) ai sp * field_at Ews t_strm (DOT _next_out) no sp *
   field_at Ews t_strm (DOT _avail_out) ao sp * strm_pad sp)
  |-- data_at_ Ews t_strm sp * TT.
Proof.
  unfold reset_fields.
  eapply derives_trans with
    (strm_members sp ni ai ti no ao to msg st za_alloc za_free za_opaque dt ad Vundef * strm_pad sp * TT).
  { unfold strm_members. cancel. }
  sep_apply strm_members_data_at_. cancel.
Qed.

(* the members of the z_stream a live stream holds besides the application's *)
Definition strm_live {ZA : zallocator} (sp st dt : val) : mpred :=
  field_at Ews t_strm (DOT _state) st sp * field_at Ews t_strm (DOT _zalloc) za_alloc sp *
  field_at Ews t_strm (DOT _zfree) za_free sp * field_at Ews t_strm (DOT _opaque) za_opaque sp *
  field_at Ews t_strm (DOT _data_type) dt sp * field_at_ Ews t_strm (DOT _reserved) sp.

Lemma wand_lend (P Q R F : mpred) : P |-- Q * F -> Q * F |-- R -> P |-- Q * (Q -* R).
Proof.
  intros H1 H2. eapply derives_trans; [exact H1 | ]. apply sepcon_derives; [apply derives_refl | ].
  apply wand_sepcon_adjoint. rewrite sepcon_comm. exact H2.
Qed.

(* what a live stream keeps while its members are lent *)
Definition dlive_rest {ZA : zallocator} (s : dstate) (p : dptrs) (gv : globals) : mpred :=
  !! (dsizes s /\ dstate_ranges s /\ Int.min_signed <= tr_data_type (d_tr s) <= Int.max_signed) &&
  (zfuncs_za gv * ltree_at (tr_ltree (d_tr s)) (p_s p) * dtree_at (tr_dtree (d_tr s)) (p_s p) *
   bltree_at (tr_bltree (d_tr s)) (p_s p) *
   ldesc_at (field_address t_ds (DOT Zlib.trees.code._dyn_ltree) (p_s p)) (tr_lmax (d_tr s)) (gv Zlib.trees.code._static_l_desc) (p_s p) *
   ddesc_at (field_address t_ds (DOT Zlib.trees.code._dyn_dtree) (p_s p)) (tr_dmax (d_tr s)) (gv Zlib.trees.code._static_d_desc) (p_s p) *
   bldesc_at (field_address t_ds (DOT Zlib.trees.code._bl_tree) (p_s p)) (tr_blmax (d_tr s)) (gv Zlib.trees.code._static_bl_desc) (p_s p) *
   work_at (tr_wk (d_tr s)) (p_s p) * out_at (tr_out (d_tr s)) (d_pbm s) (p_s p) (p_pbuf p) *
   sym_at (d_tr s) (p_s p) (p_pbuf p) * lvl_at (d_tr s) (p_s p) *
   field_at Ews t_ds (DOT _strm) (p_strm p) (p_s p) *
   win_at s p * hash_at s p * match_at s p * cfg_at s p * stat_at s p * dtokens_za s p).

(* A live stream lends its members (strm->data_type is the deflate_state's) and takes them back. *)
Lemma dstream_za_open {ZA : zallocator} (s : dstate) (sp ghp : val) (gv : globals) :
  dstream_za 2 (Some s) sp ghp gv |--
  EX spp : val, strm_live sp spp (vi (tr_data_type (d_tr s))) *
    (strm_live sp spp (vi (tr_data_type (d_tr s))) -* dstream_sp_za 2 (Some s) sp ghp spp gv).
Proof.
  unfold dstream_za. Intros p. Exists (p_s p). subst sp ghp.
  apply (wand_lend _ _ _ (dlive_rest s p gv)).
  - unfold dstate_at', dstate_at, trees_at, dtype_at, strm_live, dlive_rest. simpl. Intros.
    rewrite prop_true_andp by auto. cancel.
  - unfold dstream_sp_za, strm_live, dlive_rest. Intros. Exists p.
    unfold dstate_at', dstate_at, trees_at, dtype_at. simpl.
    rewrite !prop_true_andp by auto. cancel.
Qed.

(* main's return after deflate(): the stream, live or not, back to data_at_ *)
Lemma dstream_sp_back {ZA : zallocator} (os : option dstate) (sp ghp spp : val) (gv : globals)
    (nin : val) (ain tin : Z) (nout : val) (aout tout : Z) (msgv : val) (adler : Z) :
  @ob_dstream_to_end_za ZA ->
  dstream_sp_za 2 os sp ghp spp gv * api_fields sp nin ain tin nout aout tout msgv adler * strm_pad sp
  |-- data_at_ Ews t_strm sp * TT.
Proof.
  intros TE.
  assert (E : dstream_sp_za 2 os sp ghp spp gv |-- dstream_end_za os sp gv).
  { eapply derives_trans; [ | apply TE]. rewrite dstream_sp_eq_za. Exists spp. apply derives_refl. }
  sep_apply E. clear E.
  unfold dstream_end_za, api_fields. destruct os as [s|].
  - Intros p dt.
    eapply derives_trans with
      (strm_members sp nin (vi ain) (vl tin) nout (vi aout) (vl tout) msgv (p_s p) za_alloc za_free za_opaque dt
         (vl adler) Vundef * strm_pad sp * TT).
    { unfold strm_members. cancel. }
    sep_apply strm_members_data_at_. cancel.
  - Intros za zf op dt.
    eapply derives_trans with
      (strm_members sp nin (vi ain) (vl tin) nout (vi aout) (vl tout) msgv nullval za zf op dt
         (vl adler) Vundef * strm_pad sp * TT).
    { unfold strm_members. cancel. }
    sep_apply strm_members_data_at_. cancel.
Qed.

(* offer() on a live stream: the members as offer takes them (the struct at the compress unit's compspecs) *)
Lemma offer_pre {ZA : zallocator} (sp ni ai ti no ao to msg st dt ad : val) :
  field_at Ews t_strm (DOT _next_in) ni sp * reset_fields sp ti to msg ad *
  field_at Ews t_strm (DOT _avail_in) ai sp * field_at Ews t_strm (DOT _next_out) no sp *
  field_at Ews t_strm (DOT _avail_out) ao sp * strm_pad sp * strm_live sp st dt
  |-- @data_at Zlib.units.Compress.CS Ews t_zs
        (zs_val ni ai ti no ao to msg st za_alloc za_free za_opaque dt ad Vundef) sp.
Proof.
  rewrite zs_fields. unfold strm_members, reset_fields, strm_live. cancel.
Qed.

(* and back: the application's members as offer left them, the rest lent back to the stream *)
Lemma offer_post {ZA : zallocator} (sp ni ai ti no ao to msg st dt ad : val) :
  @data_at Zlib.units.Compress.CS Ews t_zs
    (zs_val ni ai ti no ao to msg st za_alloc za_free za_opaque dt ad Vundef) sp
  |-- field_at Ews t_strm (DOT _next_in) ni sp * field_at Ews t_strm (DOT _avail_in) ai sp *
      field_at Ews t_strm (DOT _total_in) ti sp * field_at Ews t_strm (DOT _next_out) no sp *
      field_at Ews t_strm (DOT _avail_out) ao sp * field_at Ews t_strm (DOT _total_out) to sp *
      field_at Ews t_strm (DOT _msg) msg sp * field_at Ews t_strm (DOT _adler) ad sp * strm_pad sp *
      strm_live sp st dt.
Proof.
  rewrite zs_fields. unfold strm_members, strm_live. cancel.
Qed.
