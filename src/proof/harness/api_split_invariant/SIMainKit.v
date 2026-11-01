(* Law api_split_invariant, main (SIMain.v): the kit shared by the segment lemmas of main's proof.
   - Gmain_k (= SIMain.Gmain), Delta_m (main's type context), POST_m (main's postcondition after start_function),
     POST_B (the postcondition of a suffix of main's statement chain: it never ends normally);
   - the segments of f_main's body: main's statements form one chain s1; (s2; (s3; ...)) followed by an unreachable
     `return 0`; sm_segK is the suffix of the chain from its K-th statement;
   - the assertions at the segments' boundaries (sm_pre0, sm_A, sm_B, sm_inv, sm_brk);
   - the moves of byte arrays, malloc tokens and struct z_stream between the units' compspecs and the law's, the
     stream after inflateInit2_ as an istreamA, the input and output objects of an inflate() call (bufs_opt). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.EnvBodies.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.api_split_invariant.SILawCS.
Require Import Zlib.proof.harness.api_split_invariant.SIGlobals.
Require Import Zlib.proof.harness.api_split_invariant.SIFacts.
Require Zlib.proof.uncompr.URunRet.
Require Import Zlib.harness.api_split_invariant.code.
Local Open Scope logic.

(* final(code) (the same specification as SIMain.final_spec) *)
Definition sm_final_spec :=
  DECLARE _final
  WITH r: Z
  PRE [ tint ]
    PROP (Int.min_signed <= r <= Int.max_signed)
    PARAMS (Vint (Int.repr r))
    SEP ()
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr (if final_code r then 1 else 0)))
    SEP ().

Definition Gmain_k : funspecs :=
  [inflateInit2__spec; inflate_specW; zcalloc_i; zcfree_i;
   upto_spec; any_bytes_spec; copy_of_spec; bytes_eq_spec; offer_spec; new_stream_spec; sm_final_spec;
   (_quickproof_malloc, malloc_spec'); nondet_u32_spec; gp_assume_spec; gp_assert_spec].

Definition Delta_m : tycontext := func_tycontext f_main (QPvarspecs p) Gmain_k nil.

(* main's postcondition after start_function (main_core_spec) *)
Definition POST_m : ret_assert :=
  frame_ret_assert (function_body_ret_assert tint (EX r : int, PROP () RETURN (Vint r) SEP (TT))%argsassert)
    (stackframe_of f_main).

(* the postcondition of every suffix of the chain: it never ends normally *)
Definition POST_B : ret_assert := overridePost FF POST_m.

(* ---------------------------------------------------------------------------------------------- *)
(* The segments of f_main's body                                                                 *)

(* drop the first n statements of a chain Ssequence s1 (Ssequence s2 ...) *)
Fixpoint sm_drop (n: nat) (s: statement) : statement :=
  match n, s with
  | O, _ => s
  | S n', Ssequence _ b => sm_drop n' b
  | _, _ => Sskip
  end.

(* the chain of main's statements (the body is `chain; return 0`) *)
Definition sm_chain (s: statement) : statement := match s with Ssequence a _ => a | _ => Sskip end.

Ltac sm_get_seg k :=
  let n := eval compute in (k - 1)%nat in
  let x := eval cbv beta iota zeta delta [sm_drop sm_chain f_main fn_body] in
    (sm_drop n (sm_chain (fn_body f_main))) in
  exact x.

(* main's statements: 1-4 window_bits[0..3], 5 window = window_bits[upto(3)], 6-7 input_len, room (nondet_u32()),
   8 input = alloc_any_bytes(input_len), 9 its NULL check, 10 input_split = copy_of(input, input_len), 11-12 out_one,
   out_split (malloc), 13 flush, 14 gp_assume, 15 the NULL check of the copy and the outputs, 16 new_stream(&one),
   17 code_one = inflateInit2_(&one, ...), 18 its Z_MEM_ERROR check, 19 gp_assert(code_one == Z_OK), 20 set_buffer,
   21 code_one = inflate(&one, flush), 22 its Z_MEM_ERROR check, 23 new_stream(&split), 24 code_split =
   inflateInit2_(&split, ...), 25 its Z_MEM_ERROR check, 26 gp_assert(code_split == Z_OK), 27-28 split.next_in =
   input_split, split.next_out, 29 the for(;;) of the split, 30 the check of the codes, 31 the check of the output,
   32 `return 0` *)
Definition sm_seg1 : statement := ltac:(sm_get_seg 1%nat).
Definition sm_seg16 : statement := ltac:(sm_get_seg 16%nat).
Definition sm_seg23 : statement := ltac:(sm_get_seg 23%nat).
Definition sm_seg29 : statement := ltac:(sm_get_seg 29%nat).
Definition sm_seg30 : statement := ltac:(sm_get_seg 30%nat).

(* the for(;;) loop of the split (statement 29) and its body *)
Definition sm_loop : statement := match sm_seg29 with Ssequence l _ => l | _ => Sskip end.
Definition sm_body : statement := match sm_loop with Sloop b _ => b | _ => Sskip end.

(* main's body: the chain, then `return 0` (never reached: the chain ends with its own return) *)
Lemma sm_body_eq : fn_body f_main = Ssequence sm_seg1 (Sreturn (Some (Econst_int (Int.repr 0) tint))).
Proof. reflexivity. Qed.
Lemma sm_seg29_eq : sm_seg29 = Ssequence (Sloop sm_body Sskip) sm_seg30.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Compspecs moves (the specs are at the units' CS, main at the law's CS)                          *)

Definition t_zsl : type := Tstruct _z_stream_s noattr.

(* the 14 members of struct z_stream *)
Definition sm_tuple : Type :=
  (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * val)))))))))))))%type.

Ltac sm_cs_tac CC := apply equal_f; apply (@data_at_change_composite _ _ CC); [apply JMeq_refl | reflexivity].

Lemma sm_strm_cs sh (v: sm_tuple) q:
  @data_at Zlib.units.Inflate.CS sh t_zsl v q = @data_at CS sh t_zsl v q.
Proof. sm_cs_tac CC_inflate. Qed.
Lemma sm_strm_cs_c sh (v: sm_tuple) q:
  @data_at Zlib.units.Compress.CS sh t_zsl v q = @data_at CS sh t_zsl v q.
Proof. sm_cs_tac CC_compress. Qed.
Lemma sm_bytes_a sh n (v: list val) q:
  @data_at Zlib.units.Adler32.CS sh (tarray tuchar n) v q = @data_at CS sh (tarray tuchar n) v q.
Proof. sm_cs_tac CC_adler32. Qed.
Lemma sm_bytes_i sh n (v: list val) q:
  @data_at Zlib.units.Inflate.CS sh (tarray tuchar n) v q = @data_at CS sh (tarray tuchar n) v q.
Proof. sm_cs_tac CC_inflate. Qed.
Lemma sm_tok_a sh n q:
  @malloc_token Zlib.units.Adler32.CS sh (tarray tuchar n) q = @malloc_token CS sh (tarray tuchar n) q.
Proof. apply equal_f; apply (@malloc_token_change_composite _ _ CC_adler32). reflexivity. Qed.
Lemma sm_tok_i sh n q:
  @malloc_token Zlib.units.Inflate.CS sh (tarray tuchar n) q = @malloc_token CS sh (tarray tuchar n) q.
Proof. apply equal_f; apply (@malloc_token_change_composite _ _ CC_inflate). reflexivity. Qed.

(* the harness's "1.3.2" as inflateInit2_ takes it *)
Definition sm_hv : list val := map (fun c => Vint (Int.repr c)) [49; 46; 51; 46; 50; 0].
Lemma sm_hversion gv:
  si_hversion gv =
  @data_at Zlib.units.Inflate.CS Ers (tarray tschar (Zlength sm_hv)) sm_hv (gv ___stringlit_api_split_invariant_1).
Proof.
  unfold si_hversion, sm_hv. change (Zlength _) with 6. symmetry.
  apply equal_f; apply (@data_at_change_composite _ _ CC_inflate); [apply JMeq_refl | reflexivity].
Qed.

(* the local z_stream before new_stream() *)
Lemma sm_strm_undef sh q:
  @data_at_ CS sh t_zsl q =
  @data_at Zlib.units.Compress.CS sh t_zs
    (zs_val Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef) q.
Proof. unfold data_at_. change t_zs with t_zsl. unfold zs_val. rewrite sm_strm_cs_c. reflexivity. Qed.

(* the struct after new_stream() on it: inflateInit2_'s raw stream *)
Definition sm_ns_raw : rawf :=
  RF nullval (Vint (Int.repr 0)) Vundef nullval (Vint (Int.repr 0)) Vundef Vundef Vundef Vundef.

Lemma sm_ns_raw_eq gv q:
  @data_at Zlib.units.Compress.CS Tsh t_zs
    (zs_val nullval (Vint (Int.repr 0)) Vundef nullval (Vint (Int.repr 0)) Vundef Vundef Vundef nullval nullval
       nullval Vundef Vundef Vundef) q =
  raw_strm gv Tsh q sm_ns_raw Vundef Vundef nullval nullval nullval.
Proof.
  unfold raw_strm, sm_ns_raw, zs_val; simpl. change t_zs with t_zsl. change Rep.t_strm with t_zsl.
  rewrite sm_strm_cs, sm_strm_cs_c. reflexivity.
Qed.

(* at a `return`: the struct given back to the stack frame *)
Lemma sm_raw_frame gv sh q r m s za zf o: raw_strm gv sh q r m s za zf o |-- @data_at_ CS sh t_zsl q.
Proof. unfold raw_strm. change Rep.t_strm with t_zsl. rewrite sm_strm_cs. apply data_at_data_at_. Qed.
Lemma sm_c_frame sh (v: sm_tuple) q: @data_at Zlib.units.Compress.CS sh t_zs v q |-- @data_at_ CS sh t_zsl q.
Proof. change t_zs with t_zsl. rewrite sm_strm_cs_c. apply data_at_data_at_. Qed.

(* the stream as istreamA holds it, at the law's compspecs *)
Definition sm_tup (gv: globals) (z: zfields) (adv sp: val) : sm_tuple :=
  (zf_ni z, (Vint (Int.repr (zf_ai z)), (Vlong (Int64.repr (zf_tin z)), (zf_no z, (Vint (Int.repr (zf_ao z)),
   (Vlong (Int64.repr (zf_tout z)), (msg_val gv (zf_msg z), (sp, (gv Zlib.inflate.code._zcalloc,
   (gv Zlib.inflate.code._zcfree, (nullval, (Vint (Int.repr (zf_dt z)), (adv, zf_res z))))))))))))).

Lemma sm_istreamA_unfold gv shs vs z av L:
  istreamA gv shs vs z av (Some L) =
  (!! (zf_ok z /\ writable_share shs /\ live_ok L) &&
   (data_at shs t_zsl (sm_tup gv z (adler_v (raw_live (Some L)) z av) (l_sp L)) vs * state_mem gv vs L)).
Proof.
  unfold istreamA, zstrm_atA. change Rep.t_strm with t_zsl. rewrite sm_strm_cs.
  apply pred_ext; entailer!.
Qed.

Lemma sm_istreamA_fold gv shs vs z av L:
  zf_ok z -> writable_share shs -> live_ok L ->
  data_at shs t_zsl (sm_tup gv z (adler_v (raw_live (Some L)) z av) (l_sp L)) vs * state_mem gv vs L
  |-- istreamA gv shs vs z av (Some L).
Proof. intros. rewrite sm_istreamA_unfold. entailer!. Qed.

Lemma sm_a_frame gv shs vs z av L: istreamA gv shs vs z av (Some L) |-- data_at_ shs t_zsl vs * TT.
Proof. rewrite sm_istreamA_unfold. Intros. sep_apply (data_at_data_at_ shs t_zsl). cancel. Qed.

Lemma sm_a_frame_opt gv shs vs z av st: isptr vs ->
  istreamA_opt gv shs vs z av st |-- data_at_ shs t_zsl vs * TT.
Proof.
  intros Pv. unfold istreamA_opt. destruct (eq_dec vs nullval); [subst; contradiction | ].
  destruct st as [L|]; [apply sm_a_frame | ].
  unfold istreamA, zstrm_atA. change Rep.t_strm with t_zsl. rewrite sm_strm_cs. Intros.
  sep_apply (data_at_data_at_ shs t_zsl). cancel.
Qed.

Lemma sm_istreamA_opt_ptr gv shs (vs: val) z av st:
  isptr vs -> istreamA_opt gv shs vs z av st = istreamA gv shs vs z av st.
Proof. intros Pv. unfold istreamA_opt. destruct (eq_dec vs nullval); [subst; contradiction | reflexivity]. Qed.

Lemma sm_is_live_ptr (vs: val) st: isptr vs -> is_live vs st = st.
Proof. intros Pv. unfold is_live. destruct (eq_dec vs nullval); [subst; contradiction | reflexivity]. Qed.

(* the struct as offer() takes it *)
Lemma sm_istreamA_zs gv vs z av L:
  istreamA gv Tsh vs z av (Some L) |--
  !! (zf_ok z /\ live_ok L) &&
  (@data_at Zlib.units.Compress.CS Tsh t_zs
     (zs_val (zf_ni z) (Vint (Int.repr (zf_ai z))) (Vlong (Int64.repr (zf_tin z))) (zf_no z)
        (Vint (Int.repr (zf_ao z))) (Vlong (Int64.repr (zf_tout z))) (msg_val gv (zf_msg z)) (l_sp L)
        (gv Zlib.inflate.code._zcalloc) (gv Zlib.inflate.code._zcfree) nullval (Vint (Int.repr (zf_dt z)))
        (adler_v (raw_live (Some L)) z av) (zf_res z)) vs * state_mem gv vs L).
Proof.
  rewrite sm_istreamA_unfold. Intros. change t_zs with t_zsl. rewrite sm_strm_cs_c. entailer!.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The stream after inflateInit2_ returned Z_OK                                                   *)

(* the fields: next_in/next_out NULL and avail_in/avail_out 0 (new_stream), totals 0, msg NULL, data_type 0,
   adler = wrap & 1 for a wrapped stream (0 in the model of a raw stream, whose member stays undefined) *)
Definition sm_z_init (L: live) : zfields :=
  ZF nullval 0 0 nullval 0 0 None 0 (if i_wrap (l_s L) =? 0 then 0 else Z.land (i_wrap (l_s L)) 1) Vundef.

Lemma sm_land1_range x: 0 <= Z.land x 1 <= 1.
Proof.
  change (Z.land x 1) with (Z.land x (Z.ones 1)). rewrite Z.land_ones by lia.
  pose proof (Z.mod_pos_bound x (2 ^ 1) ltac:(reflexivity)). simpl in *. lia.
Qed.

Lemma sm_z_init_ok L: zf_ok (sm_z_init L).
Proof.
  unfold zf_ok, sm_z_init; simpl. pose proof (sm_land1_range (i_wrap (l_s L))).
  destruct (i_wrap (l_s L) =? 0); rep_lia.
Qed.

Lemma sm_init_istreamA gv shs vs L:
  istream_raw gv shs vs (raw_after_init sm_ns_raw (l_s L)) L |-- istreamA gv shs vs (sm_z_init L) Vundef (Some L).
Proof.
  unfold istream_raw, istreamA, raw_strm, zstrm_atA, raw_after_init, sm_z_init, adler_v, raw_live, sm_ns_raw.
  Intros. simpl. pose proof (sm_land1_range (i_wrap (l_s L))).
  destruct (i_wrap (l_s L) =? 0) eqn:E; entailer!; unfold zf_ok; simpl; rep_lia.
Qed.

(* inflateInit2_(strm, w, "1.3.2", sizeof(z_stream)) on a local stream: what it returns *)
Lemma sm_init_ret vs w a: isptr vs ->
  init_ret vs 49 112 w a = if a then (if wbits_ok w then Z_OK else Z_STREAM_ERROR) else Z_MEM_ERROR.
Proof.
  intros Pv. unfold init_ret. simpl.
  destruct (EqDec_val vs nullval); [subst; contradiction | ]. destruct a; reflexivity.
Qed.

(* the four windowBits of the harness are accepted *)
Lemma sm_window_wbits w: si_window w -> wbits_ok w = true.
Proof. intros [E|[E|[E|E]]]; subst w; reflexivity. Qed.

(* a fresh stream holds no gz_header: inflate() takes no header memory *)
Lemma sm_head_init sp w: head_opt (Some (init_live sp w)) = emp.
Proof. unfold head_opt, head_mem, init_live. destruct (reset2_wb w) as [[? ?]|]; reflexivity. Qed.

(* a fresh stream satisfies the wide invariant's extra conditions (it is in HEAD, or the raw stream's TYPE) *)
Lemma sm_swfW_init sp w: si_window w -> swfW (l_s (init_live sp w)).
Proof.
  intros _. unfold swfW, init_live. destruct (reset2_wb w) as [[? ?]|]; simpl; split; intro E; discriminate E.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* inflate() calls                                                                                *)

(* inflate()'s return code is one of zlib's codes Z_BUF_ERROR .. Z_NEED_DICT *)
Lemma sm_inflate_ret flush strmp z st ib inp ob r z' st' ow:
  inflate_rel flush strmp z st ib inp ob r z' st' ow -> -5 <= r <= 2.
Proof.
  intros [(_ & E & _) | (_ & L & o & res & winp & _ & _ & RUN & _ & E & _)]; subst r; [ | ].
  - unfold Z_STREAM_ERROR. lia.
  - eapply Zlib.proof.uncompr.URunRet.run2_ret; [ | exact RUN]. unfold m_init. simpl. unfold Z_OK. lia.
Qed.

(* the stream offered avail_in = ai and avail_out = ao *)
Definition sm_avail (z: zfields) (ai ao: Z) : zfields :=
  ZF (zf_ni z) ai (zf_tin z) (zf_no z) ao (zf_tout z) (zf_msg z) (zf_dt z) (zf_adler z) (zf_res z).
(* the stream with next_in = ni and next_out = no *)
Definition sm_next (z: zfields) (ni no: val) : zfields :=
  ZF ni (zf_ai z) (zf_tin z) no (zf_ao z) (zf_tout z) (zf_msg z) (zf_dt z) (zf_adler z) (zf_res z).

(* the input object (all of src at inp, offered from byte P) and the output object (room bytes at outp holding the
   output O so far, offered from byte |O|) *)
Definition sm_ib (inp: val) (src: list Z) (P: Z) : inbuf := InBuf Ews inp P (Zlength src) (bytes_rep src).
Definition sm_out (O: list Z) (room: Z) : list val := bytes_rep O ++ Zrepeat Vundef (room - Zlength O).
Definition sm_ob (outp: val) (O: list Z) (room: Z) : outbuf := OutBuf Ews outp (Zlength O) room (sm_out O room).

Lemma sm_out_len O room: Zlength O <= room -> Zlength (sm_out O room) = room.
Proof.
  intros H. unfold sm_out, bytes_rep. rewrite Zlength_app, Zlength_map, Zlength_Zrepeat; lia.
Qed.

(* malloc's object is an output object with no output *)
Lemma sm_out_nil room: 0 <= room -> sm_out [] room = Zrepeat Vundef room.
Proof. intros. unfold sm_out. rewrite Zlength_nil, Z.sub_0_r. reflexivity. Qed.

(* the output object after a call that wrote ow *)
Lemma sm_out_after O ow room: Zlength O + Zlength ow <= room ->
  sublist 0 (Zlength O) (sm_out O room) ++ byte_vals ow ++
  sublist (Zlength O + Zlength ow) room (sm_out O room) = sm_out (O ++ ow) room.
Proof.
  intros H. pose proof (Zlength_nonneg O). pose proof (Zlength_nonneg ow).
  assert (LO: Zlength (bytes_rep O) = Zlength O) by (unfold bytes_rep; apply Zlength_map).
  unfold sm_out. rewrite sublist_app1 by lia. rewrite <- LO at 2. rewrite sublist_same by lia.
  rewrite sublist_app2 by lia. rewrite LO, Zlength_app.
  rewrite sublist_Zrepeat by lia. unfold bytes_rep, byte_vals. rewrite map_app, <- app_assoc. f_equal. f_equal.
  f_equal. lia.
Qed.

Lemma sm_in_ok inp src P take: isptr inp -> is_bytes src -> 0 <= P -> 0 <= take -> P + take <= Zlength src ->
  Zlength src <= Ptrofs.max_unsigned ->
  in_ok (sm_ib inp src P) (sublist P (P + take) src).
Proof.
  intros Pi Bs H0 Ht H1 H2. unfold in_ok, sm_ib.
  assert (L: Zlength (sublist P (P + take) src) = take) by (rewrite Zlength_sublist; lia).
  rewrite L. repeat split; auto; try lia.
  - unfold bytes_rep. apply Zlength_map.
  - unfold bytes_rep, byte_vals. rewrite sublist_map. reflexivity.
  - apply Forall_sublist. exact Bs.
Qed.

Lemma sm_out_ok outp O room give: isptr outp -> 0 <= give -> Zlength O + give <= room ->
  room <= Ptrofs.max_unsigned -> out_ok (sm_ob outp O room) give.
Proof.
  intros Po Hg H1 H2. pose proof (Zlength_nonneg O). unfold out_ok, sm_ob.
  split; [apply writable_Ews | ]. repeat split; auto; try lia. apply sm_out_len. lia.
Qed.

(* the two objects as inflate() takes them (at the law's compspecs in main) *)
Lemma sm_bufs_pre vs L inp src P outp O room:
  isptr vs -> Zlength O <= room ->
  data_at Ews (tarray tuchar (Zlength src)) (bytes_rep src) inp * malloc_token Ews (tarray tuchar (Zlength src)) inp *
  data_at Ews (tarray tuchar room) (sm_out O room) outp * malloc_token Ews (tarray tuchar room) outp
  |-- bufs_opt (is_live vs (Some L)) (sm_ib inp src P) (Some (sm_ob outp O room)) [] true true.
Proof.
  intros Pv H. pose proof (Zlength_nonneg O). rewrite sm_is_live_ptr by auto.
  unfold bufs_opt, in_rep, out_opt, out_rep, in_tok, out_tok, sm_ib, sm_ob.
  rewrite <- !sm_bytes_i, <- !sm_tok_i.
  change (byte_vals []) with (@nil val). rewrite app_nil_l, Zlength_nil, Z.add_0_r.
  rewrite <- sublist_split by (rewrite ?sm_out_len by lia; lia).
  rewrite sublist_same by (rewrite ?sm_out_len by lia; lia). cancel.
  rewrite ?sm_tok_i. apply derives_refl.
Qed.

Lemma sm_bufs_post vs L inp src P outp O room ow:
  isptr vs -> Zlength O + Zlength ow <= room ->
  bufs_opt (is_live vs (Some L)) (sm_ib inp src P) (Some (sm_ob outp O room)) ow true true
  |-- data_at Ews (tarray tuchar (Zlength src)) (bytes_rep src) inp * malloc_token Ews (tarray tuchar (Zlength src)) inp *
      data_at Ews (tarray tuchar room) (sm_out (O ++ ow) room) outp * malloc_token Ews (tarray tuchar room) outp.
Proof.
  intros Pv H. rewrite sm_is_live_ptr by auto.
  unfold bufs_opt, in_rep, out_opt, out_rep, in_tok, out_tok, sm_ib, sm_ob.
  rewrite sm_out_after by auto. rewrite !sm_bytes_i, !sm_tok_i. cancel.
  rewrite ?sm_tok_i. apply derives_refl.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The assertions at the segments' boundaries                                                    *)

(* Ghost values: gv; vwb, vone, vsplit (the local variables window_bits, one, split); w (the window), src (the
   input), room, flush; inp, ins, o1, o2 (the objects input, input_split, out_one, out_split). *)

(* the stack frame: the three local variables *)
Definition sm_frame (vwb vone vsplit: val) : mpred :=
  data_at_ Tsh (tarray tint 4) vwb * data_at_ Tsh t_zsl vone * data_at_ Tsh t_zsl vsplit.

(* after start_function (and zfuncs folded) *)
Definition sm_pre0 (gv: globals) (vwb vone vsplit: val) : environ -> mpred :=
  PROP ()
  LOCAL (lvar _window_bits (tarray tint 4) vwb; lvar _one t_zsl vone; lvar _split t_zsl vsplit; gvars gv)
  SEP (data_at_ Tsh (tarray tint 4) vwb; data_at_ Tsh t_zsl vone; data_at_ Tsh t_zsl vsplit;
       mem_mgr gv; zfuncs gv; tables_rep Ers gv; crc_table_at Ers gv; version_lit gv; si_hversion gv).

(* the facts of the choices and the objects *)
Definition sm_A_facts (w: Z) (src: list Z) (room flush: Z) (inp ins o1 o2: val) : Prop :=
  si_window w /\ is_bytes src /\ Zlength src <= Int.max_unsigned /\ 0 <= room <= Int.max_unsigned /\
  Int.min_signed <= flush <= Int.max_signed /\ flush <> Z_BLOCK /\ flush <> Z_TREES /\
  isptr inp /\ isptr ins /\ isptr o1 /\ isptr o2.

(* before statement 16 (the one call): the inputs chosen, the four objects made (the input and its copy hold the
   same bytes src) *)
Definition sm_A (gv: globals) (vwb vone vsplit: val) (w: Z) (src: list Z) (room flush: Z) (inp ins o1 o2: val)
    : environ -> mpred :=
  PROP ()
  LOCAL (temp _window (Vint (Int.repr w)); temp _input_len (Vlong (Int64.repr (Zlength src)));
         temp _room (Vlong (Int64.repr room)); temp _input inp; temp _input_split ins; temp _out_one o1;
         temp _out_split o2;
         temp _flush (Vint (Int.repr flush));
         lvar _window_bits (tarray tint 4) vwb; lvar _one t_zsl vone; lvar _split t_zsl vsplit; gvars gv)
  SEP (data_at_ Tsh (tarray tint 4) vwb; data_at_ Tsh t_zsl vone; data_at_ Tsh t_zsl vsplit;
       mem_mgr gv; zfuncs gv; tables_rep Ers gv; crc_table_at Ers gv; version_lit gv; si_hversion gv;
       malloc_token Ews (tarray tuchar (Zlength src)) inp;
       data_at Ews (tarray tuchar (Zlength src)) (bytes_rep src) inp;
       malloc_token Ews (tarray tuchar (Zlength src)) ins;
       data_at Ews (tarray tuchar (Zlength src)) (bytes_rep src) ins;
       malloc_token Ews (tarray tuchar room) o1; data_at_ Ews (tarray tuchar room) o1;
       malloc_token Ews (tarray tuchar room) o2; data_at_ Ews (tarray tuchar room) o2).

(* how a stream stops: Some r for one of the three final codes, None otherwise *)
Definition sm_stop (r: Z) : option Z := if final_code r then Some r else None.

(* the facts of the one call: it returned r1 and wrote ow1, which is where the stream stops (Max) *)
Definition sm_B_facts (Max: Z -> list Z -> Z -> list Z -> option Z -> Prop) (w: Z) (src: list Z) (room: Z)
    (r1: Z) (z1: zfields) (ow1: list Z) : Prop :=
  Max w src room ow1 (sm_stop r1) /\ -5 <= r1 <= 2 /\ zf_tout z1 = Zlength ow1 /\ Zlength ow1 <= room.

(* the one stream after its call, with its output object: what the rest of main keeps (and reads at the end) *)
Definition sm_one (gv: globals) (vone o1: val) (room: Z) (z1: zfields) (L1: live) (ow1: list Z) : mpred :=
  istreamA gv Tsh vone z1 Vundef (Some L1) * head_opt (Some L1) *
  malloc_token Ews (tarray tuchar room) o1 * data_at Ews (tarray tuchar room) (sm_out ow1 room) o1.

(* before statement 23 (the split stream): the one call done (code_one = r1) *)
Definition sm_B (gv: globals) (vwb vone vsplit: val) (w: Z) (src: list Z) (room: Z) (inp ins o1 o2: val)
    (r1: Z) (z1: zfields) (L1: live) (ow1: list Z) : environ -> mpred :=
  PROP ()
  LOCAL (temp _window (Vint (Int.repr w)); temp _input_len (Vlong (Int64.repr (Zlength src)));
         temp _room (Vlong (Int64.repr room)); temp _input inp; temp _input_split ins; temp _out_one o1;
         temp _out_split o2;
         temp _code_one (Vint (Int.repr r1));
         lvar _window_bits (tarray tint 4) vwb; lvar _one t_zsl vone; lvar _split t_zsl vsplit; gvars gv)
  SEP (data_at_ Tsh (tarray tint 4) vwb; sm_one gv vone o1 room z1 L1 ow1; data_at_ Tsh t_zsl vsplit;
       mem_mgr gv; zfuncs gv; tables_rep Ers gv; crc_table_at Ers gv; version_lit gv; si_hversion gv;
       malloc_token Ews (tarray tuchar (Zlength src)) inp;
       data_at Ews (tarray tuchar (Zlength src)) (bytes_rep src) inp;
       malloc_token Ews (tarray tuchar (Zlength src)) ins;
       data_at Ews (tarray tuchar (Zlength src)) (bytes_rep src) ins;
       malloc_token Ews (tarray tuchar room) o2; data_at_ Ews (tarray tuchar room) o2).

(* the invariant of the split's for(;;) at the head of its body: the split stream (z, L) read the first P bytes of
   the input and wrote O (Inv), next_in = input_split + P (inp: the split's copy of the input), next_out =
   out_split + |O|, total_out = |O|, out_split holds O and then undefined bytes; Fr: what the loop does not touch
   (window_bits, the one stream, the original input, the version literals) *)
Definition sm_inv (Inv: Z -> list Z -> Z -> Z -> list Z -> live -> Prop) (gv: globals) (vwb vone vsplit: val)
    (w: Z) (src: list Z) (room: Z) (inp o1 o2: val) (r1: Z) (Fr: mpred) : environ -> mpred :=
  EX P: Z, EX O: list Z, EX z: zfields, EX L: live,
  PROP (Inv w src room P O L; swfW (l_s L); 0 <= P <= Zlength src; Zlength O <= room;
        zf_ni z = offset_val P inp; zf_no z = offset_val (Zlength O) o2; zf_tout z = Zlength O)
  LOCAL (temp _input_len (Vlong (Int64.repr (Zlength src))); temp _room (Vlong (Int64.repr room));
         temp _input_split inp; temp _out_one o1; temp _out_split o2; temp _code_one (Vint (Int.repr r1));
         lvar _window_bits (tarray tint 4) vwb; lvar _one t_zsl vone; lvar _split t_zsl vsplit; gvars gv)
  SEP (istreamA gv Tsh vsplit z Vundef (Some L); head_opt (Some L);
       mem_mgr gv; zfuncs gv; tables_rep Ers gv; crc_table_at Ers gv;
       malloc_token Ews (tarray tuchar (Zlength src)) inp;
       data_at Ews (tarray tuchar (Zlength src)) (bytes_rep src) inp;
       malloc_token Ews (tarray tuchar room) o2; data_at Ews (tarray tuchar room) (sm_out O room) o2; Fr).

(* at the break of the for(;;): the split stopped where Max says, with code_split = code *)
Definition sm_brk (Max: Z -> list Z -> Z -> list Z -> option Z -> Prop) (gv: globals) (vwb vone vsplit: val)
    (w: Z) (src: list Z) (room: Z) (inp o1 o2: val) (r1: Z) (Fr: mpred) : environ -> mpred :=
  EX O: list Z, EX code: Z, EX z: zfields, EX L: live,
  PROP (Max w src room O (sm_stop code); -5 <= code <= 2; zf_tout z = Zlength O; Zlength O <= room)
  LOCAL (temp _code_split (Vint (Int.repr code));
         temp _input_len (Vlong (Int64.repr (Zlength src))); temp _room (Vlong (Int64.repr room));
         temp _input_split inp; temp _out_one o1; temp _out_split o2; temp _code_one (Vint (Int.repr r1));
         lvar _window_bits (tarray tint 4) vwb; lvar _one t_zsl vone; lvar _split t_zsl vsplit; gvars gv)
  SEP (istreamA gv Tsh vsplit z Vundef (Some L); head_opt (Some L);
       mem_mgr gv; zfuncs gv; tables_rep Ers gv; crc_table_at Ers gv;
       malloc_token Ews (tarray tuchar (Zlength src)) inp;
       data_at Ews (tarray tuchar (Zlength src)) (bytes_rep src) inp;
       malloc_token Ews (tarray tuchar room) o2; data_at Ews (tarray tuchar room) (sm_out O room) o2; Fr).

(* the frame Fr of the loop: window_bits, the one stream, the original input (the one call's), the version
   literals *)
Definition sm_fr (gv: globals) (vwb vone inp: val) (src: list Z) (o1: val) (room: Z) (z1: zfields) (L1: live)
    (ow1: list Z) : mpred :=
  data_at_ Tsh (tarray tint 4) vwb * sm_one gv vone o1 room z1 L1 ow1 *
  malloc_token Ews (tarray tuchar (Zlength src)) inp * data_at Ews (tarray tuchar (Zlength src)) (bytes_rep src) inp *
  version_lit gv * si_hversion gv.

Lemma sm_fr_frame gv vwb vone inp src o1 room z1 L1 ow1:
  sm_fr gv vwb vone inp src o1 room z1 L1 ow1 |-- data_at_ Tsh (tarray tint 4) vwb * data_at_ Tsh t_zsl vone * TT.
Proof. unfold sm_fr, sm_one. sep_apply sm_a_frame. cancel. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Tactics                                                                                         *)

(* a branch that cannot be taken *)
Ltac sm_infeas := exfalso; first [ match goal with H: ?a <> ?b |- _ => solve [apply H; reflexivity] end
                                 | match goal with H: _ |- _ => solve [discriminate H] end
                                 | contradiction
                                 | match goal with H: Int.repr _ = Int.repr _ |- _ =>
                                     apply repr_inj_signed in H; [lia | rep_lia | rep_lia] end
                                 | lia ].
(* right-associate the statement, so that `x = f(...)` is a call followed by a set: forward_call on a call of a
   function returning a pointer immediately followed by `x = t'` is very slow *)
Ltac sm_split_call := repeat match goal with |- semax _ _ (Ssequence (Ssequence _ _) _) _ => apply -> seq_assoc end.
(* isptr p from a data_at at p (at any compspecs) *)
Ltac sm_aptr p H := assert_PROP (isptr p) as H by (entailer;
  match goal with |- context [@data_at ?cs ?sh ?t ?c p] =>
    rewrite (@data_at_isptr cs sh t c p) end; normalize; try (apply prop_right; auto)).
