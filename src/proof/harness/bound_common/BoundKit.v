(* The mains of harness/deflate_bound.c and harness/deflate_bound_split.c: memory lemmas shared by both (no
   harness Clight, compspecs DCS.CS).
   - (a) main's locals z_stream s and gz_header h are Tsh; the API specifications are on Ews: split Tsh into Ews
     and its complement [Ecomp] (kept as a frame until the return) and rejoin;
   - (b) stream_defaults' postcondition (its Ews part) as deflateInit2_'s precondition pieces;
   - (c) the stores of the 13 fields of h and the extra / name / comment objects as gzh_at, and back;
   - (d) the stream's memory, whatever its state, back to data_at_ Ews t_strm (for the returns of main). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Zlib.proof.deflate.DCS Zlib.proof.deflate.DSpec.
Require Zlib.proof.deflate.Obligations.
Require Import Zlib.deflate.code.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.

(** ** (a) Tsh = Ews + Ecomp *)
Definition Ecomp : share := Share.comp Ews.

Lemma join_Ews_Ecomp : sepalg.join Ews Ecomp Tsh.
Proof. apply join_comp_Tsh. Qed.

Lemma data_at__Tsh_split {cs : compspecs} (t : type) (q : val) :
  @data_at_ cs Tsh t q = @data_at_ cs Ews t q * @data_at_ cs Ecomp t q.
Proof.
  symmetry. apply data_at__share_join. apply join_Ews_Ecomp.
Qed.

Lemma data_at_Tsh_split {cs : compspecs} (t : type) (v : reptype t) (q : val) :
  @data_at cs Tsh t v q |-- @data_at cs Ews t v q * @data_at_ cs Ecomp t q.
Proof.
  rewrite <- (data_at_share_join Ews Ecomp Tsh) by apply join_Ews_Ecomp. cancel.
Qed.

(** ** Objects of bytes: a malloc'd object of exactly the bytes [l] *)
Definition obj (q : val) (l : list Z) : mpred :=
  malloc_token Ews (tarray tuchar (Zlength l)) q * data_at Ews (tarray tuchar (Zlength l)) (map vi l) q.

(* what opt_obj (Some l) does not hold of the object: its token, unless the object is empty *)
Definition obj_rest (q : val) (l : list Z) : mpred :=
  if Zlength l =? 0 then emp else malloc_token Ews (tarray tuchar (Zlength l)) q.

Lemma obj_opt_obj (q : val) (l : list Z) :
  Forall (fun x => 0 <= x < 256) l -> obj q l = opt_obj Ews (Some l) q * obj_rest q l.
Proof.
  intros HB. unfold obj, opt_obj, obj_rest. rewrite prop_true_andp by exact HB.
  destruct (Zlength l =? 0) eqn:E; [apply Z.eqb_eq in E; rewrite E |];
  apply pred_ext; cancel.
Qed.

(** ** The padding of the two structs (data_at holds it, field_at does not): kept as a frame by main *)
Definition strm_pad (sp : val) : mpred := spacer Ews 12 16 sp * spacer Ews 36 40 sp * spacer Ews 92 96 sp.
Definition gzh_pad (hp : val) : mpred := spacer Ews 4 8 hp * spacer Ews 52 56 hp * spacer Ews 76 80 hp.

(** ** (b) stream_defaults' postcondition (Ews part) *)
Lemma defaults_split (sp msg st : val) (tin tout adler dt rs : Z) :
  u64_ok tin -> u64_ok tout -> u64_ok adler ->
  data_at Ews t_strm (nullval, (vi 0, (vl tin, (nullval, (vi 0, (vl tout, (msg, (st,
    (nullval, (nullval, (nullval, (vi dt, (vl adler, vl rs))))))))))))) sp
  |-- api_fields_r sp (mkAF nullval 0 tin nullval 0 tout msg adler) *
      field_at Ews t_strm (DOT _zalloc) nullval sp * field_at Ews t_strm (DOT _zfree) nullval sp *
      field_at Ews t_strm (DOT _opaque) nullval sp * field_at Ews t_strm (DOT _data_type) (vi dt) sp *
      field_at Ews t_strm (DOT _state) st sp * field_at_ Ews t_strm (DOT _reserved) sp * strm_pad sp.
Proof.
  intros. unfold api_fields_r, api_fields, strm_pad; simpl. unfold_data_at (data_at _ _ _ sp). entailer!.
  unfold u32_ok; rep_lia.
Qed.

(** ** (c) the gzip header *)
Lemma gzh_of_stores (h : gzh) (hp xp np cp xv xm nm cm dn : val) :
  gzh_ok h ->
  data_at Ews t_gzh (vi (gz_text h), (vl (gz_time h), (xv, (vi (gz_os h), (xp, (vi (gz_extra_len h),
    (xm, (np, (nm, (cp, (cm, (vi (gz_hcrc h), dn)))))))))))) hp *
  opt_obj Ews (gz_extra h) xp * opt_obj Ews (gz_name h) np * opt_obj Ews (gz_comment h) cp
  |-- gzh_at Ews h hp xp np cp * gzh_pad hp.
Proof.
  intros. unfold gzh_at, gzh_pad. unfold_data_at (data_at _ _ _ hp). Exists dn cm nm xm xv.
  entailer!.
Qed.

Lemma gzh_at_back (h : gzh) (hp xp np cp : val) :
  gzh_at Ews h hp xp np cp * gzh_pad hp
  |-- data_at_ Ews t_gzh hp *
      opt_obj Ews (gz_extra h) xp * opt_obj Ews (gz_name h) np * opt_obj Ews (gz_comment h) cp.
Proof.
  unfold gzh_at, gzh_pad. Intros v1 v2 v3 v4 v5. unfold_data_at (data_at_ _ _ hp). cancel.
Qed.

(** ** (d) the stream back to data_at_ *)
Lemma strm_fields_data_at_ (sp nin : val) (ain tin : Z) (nout : val) (aout tout : Z) (msgv : val) (adler : Z)
    (st za zf op dt : val) :
  api_fields sp nin ain tin nout aout tout msgv adler *
  field_at Ews t_strm (DOT _state) st sp * field_at Ews t_strm (DOT _zalloc) za sp *
  field_at Ews t_strm (DOT _zfree) zf sp * field_at Ews t_strm (DOT _opaque) op sp *
  field_at Ews t_strm (DOT _data_type) dt sp * field_at_ Ews t_strm (DOT _reserved) sp * strm_pad sp
  |-- data_at_ Ews t_strm sp.
Proof.
  unfold api_fields, strm_pad. Intros. unfold_data_at (data_at_ _ _ sp). cancel. unfold field_at_. apply derives_refl.
Qed.

Lemma dstream_sp_dstream (lvl : Z) (os : option dstate) (sp ghp spp : val) (gv : globals) :
  dstream_sp lvl os sp ghp spp gv |-- dstream lvl os sp ghp gv.
Proof.
  rewrite dstream_sp_eq. Exists spp. cancel.
Qed.

Lemma dstream_end_data_at_ (os : option dstate) (sp : val) (gv : globals) (nin : val) (ain tin : Z)
    (nout : val) (aout tout : Z) (msgv : val) (adler : Z) :
  dstream_end os sp gv * api_fields sp nin ain tin nout aout tout msgv adler * strm_pad sp
  |-- data_at_ Ews t_strm sp * TT.
Proof.
  unfold dstream_end. destruct os as [s|].
  - Intros p0 dt. sep_apply (strm_fields_data_at_ sp nin ain tin nout aout tout msgv adler (p_s p0) (gv _zcalloc) (gv _zcfree) nullval dt). cancel.
  - Intros za zf op dt. sep_apply (strm_fields_data_at_ sp nin ain tin nout aout tout msgv adler nullval za zf op dt). cancel.
Qed.

Lemma dstream_data_at_ (os : option dstate) (sp ghp : val) (gv : globals) (nin : val) (ain tin : Z)
    (nout : val) (aout tout : Z) (msgv : val) (adler : Z) :
  Obligations.ob_dstream_to_end ->
  dstream 2 os sp ghp gv * api_fields sp nin ain tin nout aout tout msgv adler * strm_pad sp
  |-- data_at_ Ews t_strm sp * TT.
Proof.
  intros TE. eapply derives_trans; [ | apply (dstream_end_data_at_ os sp gv nin ain tin nout aout tout msgv adler)].
  apply sepcon_derives; [ apply sepcon_derives; [ apply (TE os sp ghp gv) | apply derives_refl ] | apply derives_refl ].
Qed.

Lemma dstream_none_data_at_ (sp ghp : val) (gv : globals) (nin : val) (ain tin : Z)
    (nout : val) (aout tout : Z) (msgv : val) (adler : Z) :
  dstream 2 None sp ghp gv * api_fields sp nin ain tin nout aout tout msgv adler * strm_pad sp
  |-- data_at_ Ews t_strm sp * TT.
Proof.
  unfold dstream. Intros za zf op dt. sep_apply (strm_fields_data_at_ sp nin ain tin nout aout tout msgv adler nullval za zf op dt). cancel.
Qed.

(* deflateInit2_'s postcondition when it returned no state *)
Lemma init_fail_data_at_ (sp st za zf op dt : val) (gv : globals) (nin : val) (ain tin : Z)
    (nout : val) (aout tout : Z) (msgv : val) (adler : Z) :
  zfuncs gv * field_at_ Ews t_strm (DOT _reserved) sp *
  field_at Ews t_strm (DOT _state) st sp * field_at Ews t_strm (DOT _zalloc) za sp *
  field_at Ews t_strm (DOT _zfree) zf sp * field_at Ews t_strm (DOT _opaque) op sp *
  field_at Ews t_strm (DOT _data_type) dt sp * api_fields sp nin ain tin nout aout tout msgv adler *
  strm_pad sp
  |-- data_at_ Ews t_strm sp * TT.
Proof.
  sep_apply (strm_fields_data_at_ sp nin ain tin nout aout tout msgv adler st za zf op dt). cancel.
Qed.
