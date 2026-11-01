(* The laws rj_any_input, api_counters and api_untouched_output, mains: the kit shared by the three mains
   (harness/rj_any_input.c, api_counters.c, api_untouched_output.c are the same loop).
   - Gk_of (= Mains.Gmain_of): the specifications main calls;
   - the stream as main sees it: istreamA's struct as the 14-tuple pk_tup, at the compspecs of the compress
     unit (offer's and new_stream's) and of the law (field reads);
   - the stream after inflateInit2_ returned Z_OK as an istreamA (init_istreamA);
   - the input and output objects of an inflate() call as Spec5's bufs_opt (bufs_pre, bufs_post);
   - per law (modules AnyK, CntK, UntK): the moves of byte arrays, malloc tokens and struct z_stream between
     the units' compspecs and the law's, the stack frame given back at a `return`;
   - the loop invariant pk_inv (at the head of the do-while). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5 Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.inflate_pieces.LawCS.
Require Import Zlib.proof.harness.inflate_pieces.Globals.
Require Import Zlib.proof.harness.inflate_pieces.Facts.
Require Import Zlib.proof.crc32.Spec.
Require Zlib.harness.api_counters.code.
Require Zlib.proof.harness.inflate_codes.MainKit.

(* the specifications main calls (Mains.Gmain_of) *)
Definition Gk_of {cs: compspecs} (extra: funspecs) : funspecs :=
  [inflateInit2__spec; inflate_specW; inflateSetDictionary_specW; zcalloc_i; zcfree_i;
   upto_spec; clip_spec; any_bytes_spec; copy_of_spec; offer_spec; new_stream_spec] ++ extra ++
  [(_quickproof_malloc, malloc_spec'); (_quickproof_free, free_spec');
   nondet_u32_spec; nondet_u8_spec; gp_assert_spec].

Definition t_zsl : type := Tstruct HL._z_stream_s noattr.

(* the 14 members of struct z_stream as istreamA holds them *)
Definition pk_tuple : Type :=
  (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * val)))))))))))))%type.

Definition pk_tup (gv: globals) (z: zfields) (adv sp: val) : pk_tuple :=
  (zf_ni z, (Vint (Int.repr (zf_ai z)), (Vlong (Int64.repr (zf_tin z)), (zf_no z, (Vint (Int.repr (zf_ao z)),
   (Vlong (Int64.repr (zf_tout z)), (msg_val gv (zf_msg z), (sp, (gv Zlib.inflate.code._zcalloc,
   (gv Zlib.inflate.code._zcfree, (nullval, (Vint (Int.repr (zf_dt z)), (adv, zf_res z))))))))))))).

(* the struct after new_stream() on a local z_stream (every other member undefined) *)
Definition ns_tup : pk_tuple :=
  (nullval, (Vint (Int.repr 0), (Vundef, (nullval, (Vint (Int.repr 0), (Vundef, (Vundef, (Vundef, (nullval,
   (nullval, (nullval, (Vundef, (Vundef, Vundef))))))))))))).
Definition ns_raw : rawf :=
  RF nullval (Vint (Int.repr 0)) Vundef nullval (Vint (Int.repr 0)) Vundef Vundef Vundef Vundef.

(* the harness's ZLIB_VERSION literal "1.3.2" *)
Definition hv_list : list val := map (fun c => Vint (Int.repr c)) [49; 46; 51; 46; 50; 0].

Lemma istreamA_opt_ptr gv shs (vs: val) z av st: isptr vs -> istreamA_opt gv shs vs z av st = istreamA gv shs vs z av st.
Proof. intros Pv. unfold istreamA_opt. destruct (eq_dec vs nullval); [subst; contradiction | reflexivity]. Qed.

Lemma is_live_ptr (vs: val) st: isptr vs -> is_live vs st = st.
Proof. intros Pv. unfold is_live. destruct (eq_dec vs nullval); [subst; contradiction | reflexivity]. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The stream after inflateInit2_ returned Z_OK                                                   *)

(* the fields: next_in/next_out NULL and avail_in/avail_out 0 (new_stream), totals 0, msg NULL, data_type 0,
   adler = wrap & 1 for a wrapped stream (0 in the model of a raw stream, whose member keeps its value) *)
Definition z_init (L: live) (rs: val) : zfields :=
  ZF nullval 0 0 nullval 0 0 None 0 (if i_wrap (l_s L) =? 0 then 0 else Z.land (i_wrap (l_s L)) 1) rs.

Lemma land1_range x: 0 <= Z.land x 1 <= 1.
Proof.
  change (Z.land x 1) with (Z.land x (Z.ones 1)). rewrite Z.land_ones by lia.
  pose proof (Z.mod_pos_bound x (2 ^ 1) ltac:(reflexivity)). simpl in *. lia.
Qed.

Lemma z_init_ok L rs: zf_ok (z_init L rs).
Proof.
  unfold zf_ok, z_init; simpl. pose proof (land1_range (i_wrap (l_s L))).
  destruct (i_wrap (l_s L) =? 0); rep_lia.
Qed.

(* inflateInit2_(strm, w, "1.3.2", sizeof(z_stream)) on a stream: what it returns *)
Lemma init_ret_ok vs w a: isptr vs ->
  init_ret vs 49 112 w a = if a then (if wbits_ok w then Z_OK else Z_STREAM_ERROR) else Z_MEM_ERROR.
Proof.
  intros Pv. unfold init_ret. simpl.
  destruct (EqDec_val vs nullval); [subst; contradiction | ]. destruct a; reflexivity.
Qed.

Lemma init_istreamA gv shs vs L:
  istream_raw gv shs vs (raw_after_init ns_raw (l_s L)) L |-- istreamA gv shs vs (z_init L Vundef) Vundef (Some L).
Proof.
  unfold istream_raw, istreamA, raw_strm, zstrm_atA, raw_after_init, z_init, adler_v, raw_live, ns_raw.
  Intros. simpl. pose proof (land1_range (i_wrap (l_s L))).
  destruct (i_wrap (l_s L) =? 0) eqn:E; entailer!; unfold zf_ok; simpl; rep_lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* One inflate() call: the stream and the objects offered                                         *)

(* the input object (piece, take bytes data) and the output object (outp, room bytes bs) *)
Definition ib_of (piece: val) (take: Z) (data: list Z) : inbuf := InBuf Ews piece 0 take (bytes_rep data).
Definition ob_of (outp: val) (room: Z) (bs: list Z) : outbuf := OutBuf Ews outp 0 room (bytes_rep bs).

Lemma in_ok_of piece take data: isptr piece -> Zlength data = take -> take <= Ptrofs.max_unsigned ->
  is_bytes data -> in_ok (ib_of piece take data) data.
Proof.
  intros Pp Hl Ht Hb. unfold in_ok, ib_of. pose proof (Zlength_nonneg data).
  assert (Zlength (bytes_rep data) = take) by (unfold bytes_rep; rewrite Zlength_map; auto).
  repeat split; auto; try lia.
  rewrite Z.add_0_l, sublist_same by lia. reflexivity.
Qed.

Lemma out_ok_of outp room bs: isptr outp -> Zlength bs = room -> room <= Ptrofs.max_unsigned ->
  out_ok (ob_of outp room bs) room.
Proof.
  intros Pp Hl Hr. unfold out_ok, ob_of. pose proof (Zlength_nonneg bs).
  assert (Zlength (bytes_rep bs) = room) by (unfold bytes_rep; rewrite Zlength_map; auto).
  split; [apply writable_Ews | ]. repeat split; auto; try lia.
Qed.

(* read += take - avail_in, without overflow: total_in after the call *)
Lemma read_step tin take ai:
  0 <= tin -> 0 <= ai <= take -> tin + take <= Int64.max_unsigned -> ai <= Int.max_unsigned ->
  Int64.add (Int64.repr tin) (Int64.sub (Int64.repr take) (Int64.repr (Int.unsigned (Int.repr ai)))) =
  Int64.repr ((tin + (take - ai)) mod 2 ^ 64).
Proof.
  intros H1 H2 H3 H4. rewrite Int.unsigned_repr by rep_lia.
  unfold Int64.add, Int64.sub.
  rewrite (Int64.unsigned_repr take), (Int64.unsigned_repr ai), (Int64.unsigned_repr (take - ai)),
    (Int64.unsigned_repr tin) by rep_lia.
  rewrite (Z.mod_small (tin + (take - ai))) by rep_lia. reflexivity.
Qed.

(* inflateSetDictionary on a live stream: the function of the live state *)
Lemma on_live_fst (vs: val) z L f: isptr vs -> fst3 (on_live vs z (Some L) f) = fst3 (f z L).
Proof. intros Pv. unfold on_live. rewrite is_live_ptr by auto. destruct (f z L) as [[a b] c]. reflexivity. Qed.
Lemma on_live_snd (vs: val) z L f: isptr vs -> snd3 (on_live vs z (Some L) f) = snd3 (f z L).
Proof. intros Pv. unfold on_live. rewrite is_live_ptr by auto. destruct (f z L) as [[a b] c]. reflexivity. Qed.
Lemma on_live_thd (vs: val) z L f: isptr vs -> thd3 (on_live vs z (Some L) f) = Some (thd3 (f z L)).
Proof. intros Pv. unfold on_live. rewrite is_live_ptr by auto. destruct (f z L) as [[a b] c]. reflexivity. Qed.

Lemma zf_ok_offer z ni ai no ao: zf_ok z -> 0 <= ai <= Int.max_unsigned -> 0 <= ao <= Int.max_unsigned ->
  zf_ok (offer_z z ni ai no ao).
Proof. unfold zf_ok, offer_z; simpl; intuition. Qed.

Lemma bytes_rep_out (bs ow: list Z) room:
  Zlength bs = room -> Zlength ow <= room ->
  sublist 0 0 (bytes_rep bs) ++ byte_vals ow ++ sublist (0 + Zlength ow) room (bytes_rep bs) =
  bytes_rep (ow ++ sublist (Zlength ow) room bs).
Proof.
  intros Hb Ho. pose proof (Zlength_nonneg ow). rewrite sublist_nil, app_nil_l, Z.add_0_l.
  unfold bytes_rep, byte_vals. rewrite map_app. f_equal. rewrite sublist_map. reflexivity.
Qed.

Lemma bytes_ai sh n (v: list val) q:
  @data_at Zlib.units.Adler32.CS sh (tarray tuchar n) v q = @data_at Zlib.units.Inflate.CS sh (tarray tuchar n) v q.
Proof.
  apply equal_f; apply (@data_at_change_composite _ _ Zlib.proof.inflate.Callees.CCE_adler32);
    [apply JMeq_refl | reflexivity].
Qed.
Lemma tok_ai sh n q:
  @malloc_token Zlib.units.Adler32.CS sh (tarray tuchar n) q = @malloc_token Zlib.units.Inflate.CS sh (tarray tuchar n) q.
Proof. apply equal_f; apply (@malloc_token_change_composite _ _ Zlib.proof.inflate.Callees.CCE_adler32). reflexivity. Qed.

(* the two new objects (as any_bytes / copy_of give them) as inflate()'s buffers *)
Lemma bufs_pre vs L piece take data outp room bs:
  isptr vs -> Zlength bs = room ->
  (@data_at Zlib.units.Adler32.CS Ews (tarray tuchar take) (bytes_rep data) piece *
   @malloc_token Zlib.units.Adler32.CS Ews (tarray tuchar take) piece *
   @data_at Zlib.units.Adler32.CS Ews (tarray tuchar room) (bytes_rep bs) outp *
   @malloc_token Zlib.units.Adler32.CS Ews (tarray tuchar room) outp)%logic
  |-- bufs_opt (is_live vs (Some L)) (ib_of piece take data) (Some (ob_of outp room bs)) [] true true.
Proof.
  intros Pv Hb. rewrite is_live_ptr by auto.
  unfold bufs_opt, in_rep, out_opt, out_rep, in_tok, out_tok, ib_of, ob_of.
  rewrite (bytes_rep_out bs [] room) by (auto; rewrite Zlength_nil; pose proof (Zlength_nonneg bs); lia).
  rewrite app_nil_l, Zlength_nil, sublist_same by lia.
  rewrite !bytes_ai, !tok_ai. cancel.
Qed.

(* after the call: the output object holds the bytes written (ow) and the rest of its old contents *)
Lemma bufs_post vs L piece take data outp room bs ow:
  isptr vs -> Zlength bs = room -> Zlength ow <= room ->
  bufs_opt (is_live vs (Some L)) (ib_of piece take data) (Some (ob_of outp room bs)) ow true true
  |-- (@data_at Zlib.units.Adler32.CS Ews (tarray tuchar take) (bytes_rep data) piece *
       @malloc_token Zlib.units.Adler32.CS Ews (tarray tuchar take) piece *
       @data_at Zlib.units.Adler32.CS Ews (tarray tuchar room) (bytes_rep (ow ++ sublist (Zlength ow) room bs)) outp *
       @malloc_token Zlib.units.Adler32.CS Ews (tarray tuchar room) outp)%logic.
Proof.
  intros Pv Hb Ho. rewrite is_live_ptr by auto.
  unfold bufs_opt, in_rep, out_opt, out_rep, in_tok, out_tok, ib_of, ob_of.
  rewrite (bytes_rep_out bs ow room) by auto.
  rewrite !bytes_ai, !tok_ai. cancel.
Qed.

Lemma head_none vs L: isptr vs -> i_head (l_s L) = false -> head_opt (is_live vs (Some L)) = emp.
Proof. intros Pv H. rewrite is_live_ptr by auto. unfold head_opt, head_mem. rewrite H. reflexivity. Qed.

(* the moves between the units' compspecs and a law's *)
Ltac strm_cs_tac CC := apply equal_f; apply (@data_at_change_composite _ _ CC); [apply JMeq_refl | reflexivity].

(* ---------------------------------------------------------------------------------------------- *)
(* The moves at the compspecs of law Any                                                          *)
Module AnyK.
#[local] Existing Instance Any.CS.

Lemma strm_cs sh (v: pk_tuple) q:
  @data_at Zlib.units.Inflate.CS sh t_zsl v q = @data_at Any.CS sh t_zsl v q.
Proof. strm_cs_tac Any.CC_inflate. Qed.
Lemma strm_cs_c sh (v: pk_tuple) q:
  @data_at Zlib.units.Compress.CS sh t_zsl v q = @data_at Any.CS sh t_zsl v q.
Proof. strm_cs_tac Any.CC_compress. Qed.
Lemma bytes_a sh n (v: list val) q:
  @data_at Zlib.units.Adler32.CS sh (tarray tuchar n) v q = @data_at Any.CS sh (tarray tuchar n) v q.
Proof. strm_cs_tac Any.CC_adler32. Qed.
Lemma tok_a sh n q:
  @malloc_token Zlib.units.Adler32.CS sh (tarray tuchar n) q = @malloc_token Any.CS sh (tarray tuchar n) q.
Proof. apply equal_f; apply (@malloc_token_change_composite _ _ Any.CC_adler32). reflexivity. Qed.

(* the local z_stream before new_stream() *)
Lemma strm_undef sh p:
  @data_at_ Any.CS sh t_zsl p =
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
Lemma raw_frame gv sh p r m s za zf o: raw_strm gv sh p r m s za zf o |-- @data_at_ Any.CS sh t_zsl p.
Proof. unfold raw_strm. change Rep.t_strm with t_zsl. rewrite strm_cs. apply data_at_data_at_. Qed.
Lemma c_frame sh (v: pk_tuple) p: @data_at Zlib.units.Compress.CS sh t_zs v p |-- @data_at_ Any.CS sh t_zsl p.
Proof. change t_zs with t_zsl. rewrite strm_cs_c. apply data_at_data_at_. Qed.

(* the harness's "1.3.2" as inflateInit2_ takes it *)
Lemma hversion i gv:
  @hversion_at Any.CS i gv = @data_at Zlib.units.Inflate.CS Ers (tarray tschar (Zlength hv_list)) hv_list (gv i).
Proof.
  unfold hversion_at, hv_list. change (Zlength _) with 6. symmetry.
  apply equal_f; apply (@data_at_change_composite _ _ Any.CC_inflate); [apply JMeq_refl | reflexivity].
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
  @data_at Any.CS Ews (tarray tuchar n) c p = @data_at Zlib.units.Inflate.CS Ews (tarray tuchar n) c p.
Proof. rewrite <- bytes_a. apply bytes_ai. Qed.
Lemma dtok_i n p:
  @malloc_token Any.CS Ews (tarray tuchar n) p = @malloc_token Zlib.units.Inflate.CS Ews (tarray tuchar n) p.
Proof. rewrite <- tok_a. apply tok_ai. Qed.
End AnyK.

(* ---------------------------------------------------------------------------------------------- *)
(* The moves at the compspecs of law Cnt                                                          *)
Module CntK.
#[local] Existing Instance Cnt.CS.

Lemma strm_cs sh (v: pk_tuple) q:
  @data_at Zlib.units.Inflate.CS sh t_zsl v q = @data_at Cnt.CS sh t_zsl v q.
Proof. strm_cs_tac Cnt.CC_inflate. Qed.
Lemma strm_cs_c sh (v: pk_tuple) q:
  @data_at Zlib.units.Compress.CS sh t_zsl v q = @data_at Cnt.CS sh t_zsl v q.
Proof. strm_cs_tac Cnt.CC_compress. Qed.
Lemma bytes_a sh n (v: list val) q:
  @data_at Zlib.units.Adler32.CS sh (tarray tuchar n) v q = @data_at Cnt.CS sh (tarray tuchar n) v q.
Proof. strm_cs_tac Cnt.CC_adler32. Qed.
Lemma tok_a sh n q:
  @malloc_token Zlib.units.Adler32.CS sh (tarray tuchar n) q = @malloc_token Cnt.CS sh (tarray tuchar n) q.
Proof. apply equal_f; apply (@malloc_token_change_composite _ _ Cnt.CC_adler32). reflexivity. Qed.

(* the local z_stream before new_stream() *)
Lemma strm_undef sh p:
  @data_at_ Cnt.CS sh t_zsl p =
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
Lemma raw_frame gv sh p r m s za zf o: raw_strm gv sh p r m s za zf o |-- @data_at_ Cnt.CS sh t_zsl p.
Proof. unfold raw_strm. change Rep.t_strm with t_zsl. rewrite strm_cs. apply data_at_data_at_. Qed.
Lemma c_frame sh (v: pk_tuple) p: @data_at Zlib.units.Compress.CS sh t_zs v p |-- @data_at_ Cnt.CS sh t_zsl p.
Proof. change t_zs with t_zsl. rewrite strm_cs_c. apply data_at_data_at_. Qed.

(* the harness's "1.3.2" as inflateInit2_ takes it *)
Lemma hversion i gv:
  @hversion_at Cnt.CS i gv = @data_at Zlib.units.Inflate.CS Ers (tarray tschar (Zlength hv_list)) hv_list (gv i).
Proof.
  unfold hversion_at, hv_list. change (Zlength _) with 6. symmetry.
  apply equal_f; apply (@data_at_change_composite _ _ Cnt.CC_inflate); [apply JMeq_refl | reflexivity].
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
  @data_at Cnt.CS Ews (tarray tuchar n) c p = @data_at Zlib.units.Inflate.CS Ews (tarray tuchar n) c p.
Proof. rewrite <- bytes_a. apply bytes_ai. Qed.
Lemma dtok_i n p:
  @malloc_token Cnt.CS Ews (tarray tuchar n) p = @malloc_token Zlib.units.Inflate.CS Ews (tarray tuchar n) p.
Proof. rewrite <- tok_a. apply tok_ai. Qed.
End CntK.

(* ---------------------------------------------------------------------------------------------- *)
(* The moves at the compspecs of law Unt                                                          *)
Module UntK.
#[local] Existing Instance Unt.CS.

Lemma strm_cs sh (v: pk_tuple) q:
  @data_at Zlib.units.Inflate.CS sh t_zsl v q = @data_at Unt.CS sh t_zsl v q.
Proof. strm_cs_tac Unt.CC_inflate. Qed.
Lemma strm_cs_c sh (v: pk_tuple) q:
  @data_at Zlib.units.Compress.CS sh t_zsl v q = @data_at Unt.CS sh t_zsl v q.
Proof. strm_cs_tac Unt.CC_compress. Qed.
Lemma bytes_a sh n (v: list val) q:
  @data_at Zlib.units.Adler32.CS sh (tarray tuchar n) v q = @data_at Unt.CS sh (tarray tuchar n) v q.
Proof. strm_cs_tac Unt.CC_adler32. Qed.
Lemma tok_a sh n q:
  @malloc_token Zlib.units.Adler32.CS sh (tarray tuchar n) q = @malloc_token Unt.CS sh (tarray tuchar n) q.
Proof. apply equal_f; apply (@malloc_token_change_composite _ _ Unt.CC_adler32). reflexivity. Qed.

(* the local z_stream before new_stream() *)
Lemma strm_undef sh p:
  @data_at_ Unt.CS sh t_zsl p =
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
Lemma raw_frame gv sh p r m s za zf o: raw_strm gv sh p r m s za zf o |-- @data_at_ Unt.CS sh t_zsl p.
Proof. unfold raw_strm. change Rep.t_strm with t_zsl. rewrite strm_cs. apply data_at_data_at_. Qed.
Lemma c_frame sh (v: pk_tuple) p: @data_at Zlib.units.Compress.CS sh t_zs v p |-- @data_at_ Unt.CS sh t_zsl p.
Proof. change t_zs with t_zsl. rewrite strm_cs_c. apply data_at_data_at_. Qed.

(* the harness's "1.3.2" as inflateInit2_ takes it *)
Lemma hversion i gv:
  @hversion_at Unt.CS i gv = @data_at Zlib.units.Inflate.CS Ers (tarray tschar (Zlength hv_list)) hv_list (gv i).
Proof.
  unfold hversion_at, hv_list. change (Zlength _) with 6. symmetry.
  apply equal_f; apply (@data_at_change_composite _ _ Unt.CC_inflate); [apply JMeq_refl | reflexivity].
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
  @data_at Unt.CS Ews (tarray tuchar n) c p = @data_at Zlib.units.Inflate.CS Ews (tarray tuchar n) c p.
Proof. rewrite <- bytes_a. apply bytes_ai. Qed.
Lemma dtok_i n p:
  @malloc_token Unt.CS Ews (tarray tuchar n) p = @malloc_token Zlib.units.Inflate.CS Ews (tarray tuchar n) p.
Proof. rewrite <- tok_a. apply tok_ai. Qed.
End UntK.

(* ---------------------------------------------------------------------------------------------- *)
(* The loop invariant                                                                              *)

Section Inv.
Context {cs: compspecs}.

(* At the head of the do-while: the stream (z, L) with P z L, `read` = total_in (the bytes consumed so far, at
   most the input's length), the input object src at inp; Fr: the rest (the version literals). *)
Definition pk_inv (P: zfields -> live -> Prop) (gv: globals) (vs inp: val) (src: list Z) (Fr: mpred)
    : environ -> mpred :=
  EX z: zfields, EX L: live,
  PROP (P z L; zf_ok z; 0 <= zf_tin z <= Zlength src)
  LOCAL (temp HL._input_len (Vlong (Int64.repr (Zlength src))); temp HL._input inp;
         temp HL._read (Vlong (Int64.repr (zf_tin z))); lvar HL._strm t_zsl vs; gvars gv)
  SEP (istreamA gv Tsh vs z Vundef (Some L); mem_mgr gv; zfuncs gv; tables_rep Ers gv; crc_table_at Ers gv;
       malloc_token Ews (tarray tuchar (Zlength src)) inp;
       data_at Ews (tarray tuchar (Zlength src)) (bytes_rep src) inp; Fr).

(* the same with api_counters' `written` = total_out *)
Definition pk_inv_c (P: zfields -> live -> Prop) (gv: globals) (vs inp: val) (src: list Z) (Fr: mpred)
    : environ -> mpred :=
  EX z: zfields, EX L: live,
  PROP (P z L; zf_ok z; 0 <= zf_tin z <= Zlength src)
  LOCAL (temp HL._input_len (Vlong (Int64.repr (Zlength src))); temp HL._input inp;
         temp HL._read (Vlong (Int64.repr (zf_tin z)));
         temp Zlib.harness.api_counters.code._written (Vlong (Int64.repr (zf_tout z)));
         lvar HL._strm t_zsl vs; gvars gv)
  SEP (istreamA gv Tsh vs z Vundef (Some L); mem_mgr gv; zfuncs gv; tables_rep Ers gv; crc_table_at Ers gv;
       malloc_token Ews (tarray tuchar (Zlength src)) inp;
       data_at Ews (tarray tuchar (Zlength src)) (bytes_rep src) inp; Fr).

End Inv.

(* ---------------------------------------------------------------------------------------------- *)
(* Tactics of the mains                                                                            *)

(* the body of the first do-while of function f (the loop of the three mains) *)
Ltac get_loop_body f :=
  let p := eval vm_compute in
    (match Zlib.proof.harness.inflate_codes.MainKit.find_loop (fn_body f) with
     | Some l => l ++ [0; 0]%nat | None => nil end) in
  let x := eval cbv beta iota zeta delta [Zlib.proof.harness.inflate_codes.MainKit.sub_stmt f fn_body]
             in (Zlib.proof.harness.inflate_codes.MainKit.sub_stmt p (fn_body f)) in
  exact x.

(* a branch that cannot be taken *)
Ltac infeas := exfalso; first [ match goal with H: ?a <> ?b |- _ => solve [apply H; reflexivity] end
                              | match goal with H: _ |- _ => solve [discriminate H] end
                              | contradiction
                              | match goal with H: Int.repr _ = Int.repr _ |- _ =>
                                  apply repr_inj_signed in H; [lia | rep_lia | rep_lia] end
                              | lia ].
(* forward_if whose join adds temp t = v to the current assertion *)
Ltac ifpostv t v := match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx ?R))) _ _ =>
  forward_if (PROPx [] (LOCALx (temp t v :: Q) (SEPx R))) end.
(* `if (c) t = 1; else t = (expr);` with the value v of t known *)
Ltac ifk t v := ifpostv t (Vint (Int.repr v)); [ first [infeas | forward; entailer!] | first [infeas | forward; entailer!] | ].
(* push the statements after an `if` into both branches *)
Ltac if_seq := first [apply semax_if_seq | apply -> seq_assoc; apply semax_if_seq].
(* right-associate the statement, so that `x = f(...)` is a call followed by a set: forward_call on a call of a
   function returning a pointer immediately followed by `x = t'` is very slow (forward_call_id1_y_wow) *)
Ltac split_call := repeat match goal with |- semax _ _ (Ssequence (Ssequence _ _) _) _ => apply -> seq_assoc end.
(* isptr p from a data_at at p (at any compspecs) *)
Ltac aptr p H := assert_PROP (isptr p) as H by (entailer;
  match goal with |- context [@data_at ?cs ?sh ?t ?c p] =>
    rewrite (@data_at_isptr cs sh t c p) end; normalize; try (apply prop_right; auto)).
