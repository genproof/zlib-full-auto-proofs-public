(* Law api_inflate_any, main: its kit, on top of the kit of the laws of the same loop (inflate_pieces/MainKit.v,
   MainSession.v).
   - the specifications main calls besides MainKit.Gk_of's: those of api_untouched_output's main
     (MainSession.Gk_extra_unt but unmoved) and counted;
   - what inflate() gives for counted(&strm, &at) (MainSession.after_call: total_in and total_out raised by what
     the call consumed and wrote, modulo 2^64);
   - the moves of the stream, the objects and the struct position between the units' compspecs, the helpers'
     (laws_session's CS_session) and this program's (modules AiaK, AiaS: MainKit's UntK and MainSession's UntS at
     this program's compspecs). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5 Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.inflate_pieces.Globals.
Require Import Zlib.proof.harness.inflate_pieces.Facts.
Require Import Zlib.proof.harness.inflate_pieces.MainKit.
Require Import Zlib.proof.harness.inflate_pieces.MainSession.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.harness.api_inflate_any.LawCS.
Require Zlib.proof.harness.laws_session.Spec.
Require Zlib.proof.harness.laws_session.Facts.
Module LS := Zlib.proof.harness.laws_session.Spec.

(* main's callees besides MainKit.Gk_of's *)
Definition Gk_extra_aia : funspecs :=
  [bytes_eq_spec; gp_assume_spec; LS.inflate_window_ok_spec; LS.position_of_spec; LS.accounted_spec;
   LS.counted_spec].

(* counted(&strm, &at) after any call: total_in and total_out raised by what the call consumed and wrote *)
Lemma counted_after z z' piece take outp room :
  zf_ok z -> 0 <= take <= Int.max_unsigned -> 0 <= room <= Int.max_unsigned ->
  after_call z z' piece take outp room ->
  LS.counted_b (pz_of z') (pz_offer z piece take outp room) = true.
Proof.
  intros (Z1 & Z2 & Z3 & Z4 & _) Ht Hr (A1 & A2 & _ & _ & Hti & Hto).
  unfold LS.counted_b, pz_of, pz_offer; cbn. rewrite Hti, Hto.
  rewrite (Z.mod_small (take - zf_ai z')), (Z.mod_small (room - zf_ao z')) by rep_lia.
  rewrite !Z.eqb_refl. reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The moves at the compspecs of this program (as MainKit's UntK)                                *)
Module AiaK.
#[local] Existing Instance Aia.CS.

Lemma strm_cs sh (v: pk_tuple) q:
  @data_at Zlib.units.Inflate.CS sh t_zsl v q = @data_at Aia.CS sh t_zsl v q.
Proof. strm_cs_tac Aia.CC_inflate. Qed.
Lemma strm_cs_c sh (v: pk_tuple) q:
  @data_at Zlib.units.Compress.CS sh t_zsl v q = @data_at Aia.CS sh t_zsl v q.
Proof. strm_cs_tac Aia.CC_compress. Qed.
Lemma bytes_a sh n (v: list val) q:
  @data_at Zlib.units.Adler32.CS sh (tarray tuchar n) v q = @data_at Aia.CS sh (tarray tuchar n) v q.
Proof. strm_cs_tac Aia.CC_adler32. Qed.
Lemma tok_a sh n q:
  @malloc_token Zlib.units.Adler32.CS sh (tarray tuchar n) q = @malloc_token Aia.CS sh (tarray tuchar n) q.
Proof. apply equal_f; apply (@malloc_token_change_composite _ _ Aia.CC_adler32). reflexivity. Qed.

(* the local z_stream before new_stream() *)
Lemma strm_undef sh p:
  @data_at_ Aia.CS sh t_zsl p =
  @data_at Zlib.units.Compress.CS sh t_zs
    (zs_val Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef) p.
Proof. unfold data_at_. change t_zs with t_zsl. unfold zs_val. rewrite strm_cs_c. reflexivity. Qed.

(* after new_stream(): inflateInit2_'s raw stream *)
Lemma ns_raw_eq gv p:
  @data_at Zlib.units.Compress.CS Tsh t_zs
    (zs_val nullval (Vint (Int.repr 0)) Vundef nullval (Vint (Int.repr 0)) Vundef Vundef Vundef nullval nullval
       nullval Vundef Vundef Vundef) p =
  raw_strm gv Tsh p ns_raw Vundef Vundef nullval nullval nullval.
Proof.
  unfold raw_strm, ns_raw, zs_val; simpl. change t_zs with t_zsl. change Rep.t_strm with t_zsl.
  rewrite strm_cs, strm_cs_c. reflexivity.
Qed.

(* at a `return`: the struct of the stream given back to the stack frame *)
Lemma raw_frame gv sh p r m s za zf o: raw_strm gv sh p r m s za zf o |-- @data_at_ Aia.CS sh t_zsl p.
Proof. unfold raw_strm. change Rep.t_strm with t_zsl. rewrite strm_cs. apply data_at_data_at_. Qed.
Lemma c_frame sh (v: pk_tuple) p: @data_at Zlib.units.Compress.CS sh t_zs v p |-- @data_at_ Aia.CS sh t_zsl p.
Proof. change t_zs with t_zsl. rewrite strm_cs_c. apply data_at_data_at_. Qed.

(* the harness's "1.3.2" as inflateInit2_ takes it *)
Lemma hversion i gv:
  @hversion_at Aia.CS i gv = @data_at Zlib.units.Inflate.CS Ers (tarray tschar (Zlength hv_list)) hv_list (gv i).
Proof.
  unfold hversion_at, hv_list. change (Zlength _) with 6. symmetry.
  apply equal_f; apply (@data_at_change_composite _ _ Aia.CC_inflate); [apply JMeq_refl | reflexivity].
Qed.

(* a live stream: the struct at the law's compspecs and the memory behind strm->state *)
Lemma istreamA_unfold gv shs vs z av L:
  istreamA gv shs vs z av (Some L) =
  (!! (zf_ok z /\ writable_share shs /\ live_ok L) &&
   (data_at shs t_zsl (pk_tup gv z (adler_v (raw_live (Some L)) z av) (l_sp L)) vs * state_mem gv vs L))%logic.
Proof.
  unfold istreamA, zstrm_atA.
  change Rep.t_strm with t_zsl. rewrite strm_cs.
  apply pred_ext; entailer!.
Qed.

Lemma istreamA_fold gv shs vs z av L:
  zf_ok z -> writable_share shs -> live_ok L ->
  (data_at shs t_zsl (pk_tup gv z (adler_v (raw_live (Some L)) z av) (l_sp L)) vs * state_mem gv vs L)%logic
  |-- istreamA gv shs vs z av (Some L).
Proof. intros. rewrite istreamA_unfold. entailer!. Qed.

Lemma a_frame gv shs vs z av L: istreamA gv shs vs z av (Some L) |-- (data_at_ shs t_zsl vs * TT)%logic.
Proof. rewrite istreamA_unfold. Intros. sep_apply (data_at_data_at_ shs t_zsl). cancel. Qed.

Lemma a_frame_opt gv shs vs z av st: isptr vs ->
  istreamA_opt gv shs vs z av st |-- (data_at_ shs t_zsl vs * TT)%logic.
Proof.
  intros Pv. rewrite istreamA_opt_ptr by auto. destruct st as [L|]; [apply a_frame | ].
  unfold istreamA, zstrm_atA. change Rep.t_strm with t_zsl. rewrite strm_cs. Intros.
  sep_apply (data_at_data_at_ shs t_zsl). cancel.
Qed.

(* the struct as offer() takes it *)
Lemma istreamA_zs gv vs z av L:
  istreamA gv Tsh vs z av (Some L) |--
  (!! (zf_ok z /\ live_ok L) &&
   (@data_at Zlib.units.Compress.CS Tsh t_zs
      (zs_val (zf_ni z) (Vint (Int.repr (zf_ai z))) (Vlong (Int64.repr (zf_tin z))) (zf_no z)
         (Vint (Int.repr (zf_ao z))) (Vlong (Int64.repr (zf_tout z))) (msg_val gv (zf_msg z)) (l_sp L)
         (gv Zlib.inflate.code._zcalloc) (gv Zlib.inflate.code._zcfree) nullval (Vint (Int.repr (zf_dt z)))
         (adler_v (raw_live (Some L)) z av) (zf_res z)) vs * state_mem gv vs L))%logic.
Proof.
  rewrite istreamA_unfold. Intros. change t_zs with t_zsl. rewrite strm_cs_c. entailer!.
Qed.

(* after offer(strm, piece, take, outp, room): the stream inflate() takes (no gz_header) *)
Lemma offer_fold gv vs z av L piece take data outp room bs:
  isptr vs -> isptr piece -> isptr outp -> zf_ok z -> live_ok L -> i_head (l_s L) = false ->
  0 <= take <= Int.max_unsigned -> 0 <= room <= Int.max_unsigned ->
  (@data_at Zlib.units.Compress.CS Tsh t_zs
      (zs_val piece (Vint (Int.repr take)) (Vlong (Int64.repr (zf_tin z))) outp
         (Vint (Int.repr room)) (Vlong (Int64.repr (zf_tout z))) (msg_val gv (zf_msg z)) (l_sp L)
         (gv Zlib.inflate.code._zcalloc) (gv Zlib.inflate.code._zcfree) nullval (Vint (Int.repr (zf_dt z)))
         (adler_v (raw_live (Some L)) z av) (zf_res z)) vs * state_mem gv vs L)%logic
  |-- (istreamA_opt gv Tsh vs (offer_z z (in_ptr (ib_of piece take data) 0) take (out_ptr (ob_of outp room bs) 0) room)
         av (Some L) * head_opt (is_live vs (Some L)))%logic.
Proof.
  intros Pv Pp Po Zo Lo Hh Ht Hr.
  rewrite head_none, istreamA_opt_ptr by auto. rewrite sepcon_emp.
  eapply derives_trans;
    [ | apply (istreamA_fold gv Tsh vs (offer_z z (in_ptr (ib_of piece take data) 0) take
                                         (out_ptr (ob_of outp room bs) 0) room) av L);
        [apply zf_ok_offer; auto | auto | auto]].
  change t_zs with t_zsl. rewrite strm_cs_c.
  unfold pk_tup, offer_z, adler_v, ib_of, ob_of, in_ptr, out_ptr; simpl.
  destruct piece; try contradiction. destruct outp; try contradiction. simpl.
  rewrite !Ptrofs.add_zero. apply derives_refl.
Qed.

(* free() of an object of n bytes *)
Lemma free_pre n (c: list val) p:
  p <> nullval ->
  (malloc_token Ews (tarray tuchar n) p * data_at Ews (tarray tuchar n) c p)%logic
  |-- if eq_dec p nullval then emp else (malloc_token Ews (tarray tuchar n) p * data_at_ Ews (tarray tuchar n) p)%logic.
Proof.
  intros N. rewrite if_false by auto. sep_apply (data_at_data_at_ Ews (tarray tuchar n) c p). cancel.
Qed.

(* the input and output objects of an inflate() call, at the law's compspecs *)
Lemma bufs_pre_l vs L piece take data outp room bs:
  isptr vs -> Zlength bs = room ->
  (data_at Ews (tarray tuchar take) (bytes_rep data) piece * malloc_token Ews (tarray tuchar take) piece *
   data_at Ews (tarray tuchar room) (bytes_rep bs) outp * malloc_token Ews (tarray tuchar room) outp)%logic
  |-- bufs_opt (is_live vs (Some L)) (ib_of piece take data) (Some (ob_of outp room bs)) [] true true.
Proof. intros. rewrite <- !bytes_a, <- !tok_a. apply bufs_pre; auto. Qed.

Lemma bufs_post_l vs L piece take data outp room bs ow:
  isptr vs -> Zlength bs = room -> Zlength ow <= room ->
  bufs_opt (is_live vs (Some L)) (ib_of piece take data) (Some (ob_of outp room bs)) ow true true
  |-- (data_at Ews (tarray tuchar take) (bytes_rep data) piece * malloc_token Ews (tarray tuchar take) piece *
       data_at Ews (tarray tuchar room) (bytes_rep (ow ++ sublist (Zlength ow) room bs)) outp *
       malloc_token Ews (tarray tuchar room) outp)%logic.
Proof. intros. rewrite <- !bytes_a, <- !tok_a. apply bufs_post; auto. Qed.

(* a dictionary object (any_bytes) as inflateSetDictionary takes it, and back *)
Lemma dict_i n (c: list val) p:
  @data_at Aia.CS Ews (tarray tuchar n) c p = @data_at Zlib.units.Inflate.CS Ews (tarray tuchar n) c p.
Proof. rewrite <- bytes_a. apply bytes_ai. Qed.
Lemma dtok_i n p:
  @malloc_token Aia.CS Ews (tarray tuchar n) p = @malloc_token Zlib.units.Inflate.CS Ews (tarray tuchar n) p.
Proof. rewrite <- tok_a. apply tok_ai. Qed.
End AiaK.

(* ---------------------------------------------------------------------------------------------- *)
(* The moves of the two structs between the helpers' compspecs and this program's (as MainSession's UntS) *)
Module AiaS.
#[local] Existing Instance Aia.CS.
#[export] Instance CC_session : change_composite_env LS.CS_session Aia.CS.
  make_cs_preserve LS.CS_session Aia.CS. Defined.

Lemma set_ses sh ni ai ti no ao to msg st za zf op dt ad rs q:
  @data_at Zlib.units.Compress.CS sh t_zs
    (zs_val ni (Vint (Int.repr ai)) (Vlong (Int64.repr ti)) no (Vint (Int.repr ao)) (Vlong (Int64.repr to))
       msg st za zf op dt ad rs) q =
  @data_at LS.CS_session sh t_zs (LS.zs_of (LS.mk_posz ni ai ti no ao to) (msg, st, za, zf, op, dt, ad, rs)) q.
Proof.
  unfold LS.zs_of; cbn [LS.pz_next_in LS.pz_avail_in LS.pz_total_in LS.pz_next_out LS.pz_avail_out LS.pz_total_out].
  change t_zs with t_zsl. rewrite AiaK.strm_cs_c. symmetry. ses_tac CC_session.
Qed.

Lemma pk_ses sh gv z adv sp q:
  @data_at Aia.CS sh t_zsl (pk_tup gv z adv sp) q =
  @data_at LS.CS_session sh t_zs (LS.zs_of (pz_of z) (rest_of gv z adv sp)) q.
Proof. symmetry. change t_zs with t_zsl. ses_tac CC_session. Qed.

Lemma pos_ses_ sh q: @data_at_ Aia.CS sh t_posl q = @data_at_ LS.CS_session sh LS.t_pos q.
Proof. unfold data_at_. symmetry. ses_tac CC_session. Qed.

Lemma pos_back sh v q: @data_at LS.CS_session sh LS.t_pos v q |-- @data_at_ Aia.CS sh t_posl q.
Proof. rewrite pos_ses_. apply data_at_data_at_. Qed.
End AiaS.
