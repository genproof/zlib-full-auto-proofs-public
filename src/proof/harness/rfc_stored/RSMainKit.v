(* Law rfc_stored, main (RSMain.v): the kit shared by the segment lemmas of main's proof.
   - Gmain_k (= RSMain.Gmain), Delta_m (main's type context), POST_m (main's postcondition after start_function);
   - the segments of f_main's body: main's statements form one chain s1; (s2; (s3; ...)) (followed by the final
     `return 0`); rs_seg k is the suffix of the chain from its k-th statement. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.EnvBodies.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.SpecW.
Require Zlib.proof.adler32.Spec.
Require Zlib.proof.crc32.Spec.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rfc_stored.RSLawCS.
Require Import Zlib.proof.harness.rfc_stored.RSGlobals.
Require Import Zlib.proof.harness.rfc_stored.RSFacts.
Require Import Zlib.harness.rfc_stored.code.
Local Open Scope logic.

Definition Gmain_k : funspecs :=
  [inflateInit2__spec; inflate_specW; zcalloc_i; zcfree_i;
   Zlib.proof.adler32.Spec.adler32_z_spec; Zlib.proof.crc32.Spec.crc32_z_spec;
   upto_spec; clip_spec; any_bytes_spec; copy_of_spec; bytes_eq_spec; new_stream_spec;
   (_quickproof_malloc, malloc_spec'); nondet_u32_spec; gp_assert_spec; gp_assume_spec].

Definition Delta_m : tycontext := func_tycontext f_main (QPvarspecs p) Gmain_k nil.

(* main's postcondition after start_function (main_core_spec) *)
Definition POST_m : ret_assert :=
  frame_ret_assert (function_body_ret_assert tint (EX r : int, PROP () RETURN (Vint r) SEP (TT))%argsassert)
    (stackframe_of f_main).

(* ---------------------------------------------------------------------------------------------- *)
(* The segments of f_main's body                                                                 *)

(* drop the first n statements of a chain Ssequence s1 (Ssequence s2 ...) *)
Fixpoint rs_drop (n: nat) (s: statement) : statement :=
  match n, s with
  | O, _ => s
  | S n', Ssequence _ b => rs_drop n' b
  | _, _ => Sskip
  end.

(* the chain of main's statements (the body is `chain; return 0`) *)
Definition rs_chain (s: statement) : statement := match s with Ssequence a _ => a | _ => Sskip end.

Ltac rs_get_seg k :=
  let n := eval compute in (k - 1)%nat in
  let x := eval cbv beta iota zeta delta [rs_drop rs_chain f_main fn_body] in
    (rs_drop n (rs_chain (fn_body f_main))) in
  exact x.

(* main's statements: 1-5 the choices (upto), 6-10 head_len, trailer_len, stream_len, 11-12 the objects stream and
   data (alloc_any_bytes), 13 their NULL check, 14 expected = copy_of(data), 15 out = malloc, 16 the NULL check of
   expected and out, 17-18 the zlib / gzip header, 19-21 at, done and the block loop, 22-23 adler32_z, crc32_z, 24
   the trailer loop, 25 new_stream, 26-28 window_bits, 29 inflateInit2_ and its check, 30-31 next_in, next_out, 32
   the do-while of inflate() calls, 33 the final check, 34 `return 0` *)
Definition rs_seg1 : statement := ltac:(rs_get_seg 1%nat).
Definition rs_seg17 : statement := ltac:(rs_get_seg 17%nat).
Definition rs_seg19 : statement := ltac:(rs_get_seg 19%nat).
Definition rs_seg22 : statement := ltac:(rs_get_seg 22%nat).
Definition rs_seg25 : statement := ltac:(rs_get_seg 25%nat).
Definition rs_seg32 : statement := ltac:(rs_get_seg 32%nat).

(* main's body: the chain, then `return 0` (never reached: the chain ends with its own return) *)
Lemma rs_body_eq : fn_body f_main = Ssequence rs_seg1 (Sreturn (Some (Econst_int (Int.repr 0) tint))).
Proof. reflexivity. Qed.

(* the postcondition of every suffix of the chain: it never ends normally *)
Definition POST_B : ret_assert := overridePost FF POST_m.

(* ---------------------------------------------------------------------------------------------- *)
(* The assertions at the segments' boundaries                                                    *)

(* Ghost values: gv; vs, vwb (the local variables strm and window_bits); the choices n = data_len, nb = blocks,
   na = after, wr = wrapper, window; stp / s0: the stream object and its initial bytes (alloc_any_bytes,
   |s0| = stream_len); dp / d: the data object and its bytes; op: the output object (malloc, data_len bytes);
   ep: the copy of the data (copy_of, rs_copy); c: the zlib CINFO; lens: the lengths of the blocks. *)

(* after start_function (and zfuncs folded) *)
Definition rs_pre0 (gv: globals) (vs vwb: val) : environ -> mpred :=
  PROP ()
  LOCAL (lvar _window_bits (tarray tint 3) vwb; lvar _strm (Tstruct _z_stream_s noattr) vs; gvars gv)
  SEP (data_at_ Tsh (tarray tint 3) vwb; data_at_ Tsh (Tstruct _z_stream_s noattr) vs;
       mem_mgr gv; zfuncs gv; tables_rep Ers gv; Zlib.proof.crc32.Spec.crc_table_at Ers gv; version_lit gv;
       rs_hversion_lit gv).

(* the facts of the choices and the objects *)
Definition rs_A_facts (n nb na wr window: Z) (stp: val) (s0: list Z) (dp: val) (d: list Z) (op: val) : Prop :=
  0 <= n <= 2 ^ 60 /\ 1 <= nb <= 2 ^ 60 /\ 0 <= na <= 2 ^ 60 /\ 0 <= wr <= 2 /\ 8 <= window <= 15 /\
  Zlength s0 = rs_hl wr + 5 * nb + n + rs_tl wr + na /\ Zlength d = n /\ rs_bytes s0 /\ rs_bytes d /\
  isptr stp /\ isptr dp /\ isptr op.

(* the harness's constraints on the CINFO and on the lengths of the blocks *)
Definition rs_c_ok (wr window c: Z) : Prop := wr = 1 -> 0 <= c <= window - 8.
Definition rs_lens_ok (nb n: Z) (lens: list Z) : Prop :=
  lens <> [] /\ Zlength lens = nb /\ Forall (fun l => 0 <= l <= 65535) lens /\ fold_right Z.add 0 lens = n.

(* the copy of the data that main makes with copy_of before any zlib call (the object at ep, n bytes d) and
   compares the output with at the end; no statement between the copy and the final check touches it *)
Definition rs_copy (ep: val) (n: Z) (d: list Z) : mpred :=
  malloc_token Ews (tarray tuchar n) ep * data_at Ews (tarray tuchar n) (bytes_rep d) ep.

(* before statement 17 (the header): the three objects made, the stream holding s0 *)
Definition rs_A (gv: globals) (vs vwb: val) (n nb na wr window: Z) (stp: val) (s0: list Z) (dp: val) (d: list Z)
    (op ep: val) : environ -> mpred :=
  PROP ()
  LOCAL (temp _data_len (Vlong (Int64.repr n)); temp _blocks (Vlong (Int64.repr nb));
         temp _after (Vlong (Int64.repr na)); temp _wrapper (Vint (Int.repr wr));
         temp _window (Vint (Int.repr window)); temp _head_len (Vlong (Int64.repr (rs_hl wr)));
         temp _trailer_len (Vlong (Int64.repr (rs_tl wr))); temp _stream_len (Vlong (Int64.repr (Zlength s0)));
         temp _stream stp; temp _data dp; temp _out op; temp _expected ep;
         lvar _window_bits (tarray tint 3) vwb; lvar _strm (Tstruct _z_stream_s noattr) vs; gvars gv)
  SEP (data_at_ Tsh (tarray tint 3) vwb; data_at_ Tsh (Tstruct _z_stream_s noattr) vs;
       mem_mgr gv; zfuncs gv; tables_rep Ers gv; Zlib.proof.crc32.Spec.crc_table_at Ers gv; version_lit gv;
       rs_hversion_lit gv;
       malloc_token Ews (tarray tuchar (Zlength s0)) stp;
       data_at Ews (tarray tuchar (Zlength s0)) (bytes_rep s0) stp;
       malloc_token Ews (tarray tuchar n) dp; data_at Ews (tarray tuchar n) (bytes_rep d) dp;
       malloc_token Ews (tarray tuchar n) op; data_at_ Ews (tarray tuchar n) op; rs_copy ep n d).

(* before statement 19 (the blocks): the header written *)
Definition rs_B (gv: globals) (vs vwb: val) (n nb na wr window: Z) (stp: val) (s0: list Z) (dp: val) (d: list Z)
    (op ep: val) (c: Z) : environ -> mpred :=
  PROP ()
  LOCAL (temp _data_len (Vlong (Int64.repr n)); temp _blocks (Vlong (Int64.repr nb));
         temp _after (Vlong (Int64.repr na)); temp _wrapper (Vint (Int.repr wr));
         temp _window (Vint (Int.repr window)); temp _head_len (Vlong (Int64.repr (rs_hl wr)));
         temp _trailer_len (Vlong (Int64.repr (rs_tl wr))); temp _stream_len (Vlong (Int64.repr (Zlength s0)));
         temp _stream stp; temp _data dp; temp _out op; temp _expected ep;
         lvar _window_bits (tarray tint 3) vwb; lvar _strm (Tstruct _z_stream_s noattr) vs; gvars gv)
  SEP (data_at_ Tsh (tarray tint 3) vwb; data_at_ Tsh (Tstruct _z_stream_s noattr) vs;
       mem_mgr gv; zfuncs gv; tables_rep Ers gv; Zlib.proof.crc32.Spec.crc_table_at Ers gv; version_lit gv;
       rs_hversion_lit gv;
       malloc_token Ews (tarray tuchar (Zlength s0)) stp;
       data_at Ews (tarray tuchar (Zlength s0))
         (bytes_rep (rs_hdr wr c s0 ++ sublist (rs_hl wr) (Zlength s0) s0)) stp;
       malloc_token Ews (tarray tuchar n) dp; data_at Ews (tarray tuchar n) (bytes_rep d) dp;
       malloc_token Ews (tarray tuchar n) op; data_at_ Ews (tarray tuchar n) op; rs_copy ep n d).

(* before statement 22 (the checksums): the blocks written, at = the end of the blocks *)
Definition rs_C (gv: globals) (vs vwb: val) (n nb na wr window: Z) (stp: val) (s0: list Z) (dp: val) (d: list Z)
    (op ep: val) (c: Z) (lens: list Z) : environ -> mpred :=
  PROP ()
  LOCAL (temp _at (Vlong (Int64.repr (rs_hl wr + 5 * nb + n)));
         temp _data_len (Vlong (Int64.repr n)); temp _blocks (Vlong (Int64.repr nb));
         temp _after (Vlong (Int64.repr na)); temp _wrapper (Vint (Int.repr wr));
         temp _window (Vint (Int.repr window)); temp _head_len (Vlong (Int64.repr (rs_hl wr)));
         temp _trailer_len (Vlong (Int64.repr (rs_tl wr))); temp _stream_len (Vlong (Int64.repr (Zlength s0)));
         temp _stream stp; temp _data dp; temp _out op; temp _expected ep;
         lvar _window_bits (tarray tint 3) vwb; lvar _strm (Tstruct _z_stream_s noattr) vs; gvars gv)
  SEP (data_at_ Tsh (tarray tint 3) vwb; data_at_ Tsh (Tstruct _z_stream_s noattr) vs;
       mem_mgr gv; zfuncs gv; tables_rep Ers gv; Zlib.proof.crc32.Spec.crc_table_at Ers gv; version_lit gv;
       rs_hversion_lit gv;
       malloc_token Ews (tarray tuchar (Zlength s0)) stp;
       data_at Ews (tarray tuchar (Zlength s0))
         (bytes_rep (rs_hdr wr c s0 ++ rs_blocks (rs_pads wr s0 lens) lens d ++
                     sublist (rs_hl wr + 5 * nb + n) (Zlength s0) s0)) stp;
       malloc_token Ews (tarray tuchar n) dp; data_at Ews (tarray tuchar n) (bytes_rep d) dp;
       malloc_token Ews (tarray tuchar n) op; data_at_ Ews (tarray tuchar n) op; rs_copy ep n d).

(* before statement 25 (new_stream): the stream built, rs_src *)
Definition rs_D (gv: globals) (vs vwb: val) (n nb na wr window: Z) (stp: val) (s0: list Z) (dp: val) (d: list Z)
    (op ep: val) (c: Z) (lens: list Z) : environ -> mpred :=
  PROP ()
  LOCAL (temp _data_len (Vlong (Int64.repr n)); temp _blocks (Vlong (Int64.repr nb));
         temp _after (Vlong (Int64.repr na)); temp _wrapper (Vint (Int.repr wr));
         temp _window (Vint (Int.repr window)); temp _head_len (Vlong (Int64.repr (rs_hl wr)));
         temp _trailer_len (Vlong (Int64.repr (rs_tl wr))); temp _stream_len (Vlong (Int64.repr (Zlength s0)));
         temp _stream stp; temp _data dp; temp _out op; temp _expected ep;
         lvar _window_bits (tarray tint 3) vwb; lvar _strm (Tstruct _z_stream_s noattr) vs; gvars gv)
  SEP (data_at_ Tsh (tarray tint 3) vwb; data_at_ Tsh (Tstruct _z_stream_s noattr) vs;
       mem_mgr gv; zfuncs gv; tables_rep Ers gv; Zlib.proof.crc32.Spec.crc_table_at Ers gv; version_lit gv;
       rs_hversion_lit gv;
       malloc_token Ews (tarray tuchar (Zlength s0)) stp;
       data_at Ews (tarray tuchar (Zlength s0)) (bytes_rep (rs_src wr c s0 (rs_pads wr s0 lens) lens d)) stp;
       malloc_token Ews (tarray tuchar n) dp; data_at Ews (tarray tuchar n) (bytes_rep d) dp;
       malloc_token Ews (tarray tuchar n) op; data_at_ Ews (tarray tuchar n) op; rs_copy ep n d).

(* the invariant of the do-while (statement 32) at the head of its body: the buffer src, the data d, the input
   consumed pos (next_in = stream + pos), the output so far outv (next_out = out + |outv|, the output object holds
   outv and then undefined bytes), the stream (z, L) with P src d pos outv z L; avail_in / avail_out ai / ao (the
   values the previous call left; zf_ok z: z's own fields are in range, as RSFacts.rf_inflate needs);
   swfW of the live state (SpecW.inflate_specW takes it and gives it back); strm->adler of a raw stream
   undefined (new_stream does not set it, inflate() may leave any value) *)
Definition rs_inv (P: list Z -> list Z -> Z -> list Z -> zfields -> live -> Prop) (gv: globals) (vs vwb: val)
    (stp: val) (src: list Z) (dp: val) (d: list Z) (op ep: val) : environ -> mpred :=
  EX pos: Z, EX outv: list Z, EX z: zfields, EX L: live, EX ai: Z, EX ao: Z,
  PROP (P src d pos outv z L; zf_ok z; swfW (l_s L); 0 <= ai <= Int.max_unsigned; 0 <= ao <= Int.max_unsigned)
  LOCAL (temp _stream stp; temp _stream_len (Vlong (Int64.repr (Zlength src)));
         temp _data dp; temp _data_len (Vlong (Int64.repr (Zlength d))); temp _out op; temp _expected ep;
         lvar _window_bits (tarray tint 3) vwb; lvar _strm (Tstruct _z_stream_s noattr) vs; gvars gv)
  SEP (istreamA gv Tsh vs (rs_set_call z (offset_val pos stp) ai (offset_val (Zlength outv) op) ao) Vundef (Some L);
       data_at_ Tsh (tarray tint 3) vwb;
       mem_mgr gv; zfuncs gv; tables_rep Ers gv; Zlib.proof.crc32.Spec.crc_table_at Ers gv; version_lit gv;
       rs_hversion_lit gv;
       malloc_token Ews (tarray tuchar (Zlength src)) stp;
       data_at Ews (tarray tuchar (Zlength src)) (bytes_rep src) stp;
       malloc_token Ews (tarray tuchar (Zlength d)) dp;
       data_at Ews (tarray tuchar (Zlength d)) (bytes_rep d) dp;
       malloc_token Ews (tarray tuchar (Zlength d)) op;
       data_at Ews (tarray tuchar (Zlength d)) (bytes_rep outv ++ Zrepeat Vundef (Zlength d - Zlength outv)) op;
       rs_copy ep (Zlength d) d).

(* ---------------------------------------------------------------------------------------------- *)
(* Compspecs moves (the specs are at the units' CS, main at the law's CS)                          *)

Definition t_zsl : type := Tstruct _z_stream_s noattr.

(* the 14 members of struct z_stream *)
Definition rs_tuple : Type :=
  (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * val)))))))))))))%type.

Ltac rs_cs_tac CC := apply equal_f; apply (@data_at_change_composite _ _ CC); [apply JMeq_refl | reflexivity].

Lemma rs_strm_cs sh (v: rs_tuple) q:
  @data_at Zlib.units.Inflate.CS sh t_zsl v q = @data_at CS sh t_zsl v q.
Proof. rs_cs_tac CC_inflate. Qed.
Lemma rs_strm_cs_c sh (v: rs_tuple) q:
  @data_at Zlib.units.Compress.CS sh t_zsl v q = @data_at CS sh t_zsl v q.
Proof. rs_cs_tac CC_compress. Qed.
Lemma rs_bytes_a sh n (v: list val) q:
  @data_at Zlib.units.Adler32.CS sh (tarray tuchar n) v q = @data_at CS sh (tarray tuchar n) v q.
Proof. rs_cs_tac CC_adler32. Qed.
Lemma rs_bytes_c sh n (v: list val) q:
  @data_at Zlib.units.Crc32.CS sh (tarray tuchar n) v q = @data_at CS sh (tarray tuchar n) v q.
Proof. rs_cs_tac CC_crc32. Qed.
Lemma rs_bytes_i sh n (v: list val) q:
  @data_at Zlib.units.Inflate.CS sh (tarray tuchar n) v q = @data_at CS sh (tarray tuchar n) v q.
Proof. rs_cs_tac CC_inflate. Qed.
Lemma rs_tok_a sh n q:
  @malloc_token Zlib.units.Adler32.CS sh (tarray tuchar n) q = @malloc_token CS sh (tarray tuchar n) q.
Proof. apply equal_f; apply (@malloc_token_change_composite _ _ CC_adler32). reflexivity. Qed.
Lemma rs_tok_i sh n q:
  @malloc_token Zlib.units.Inflate.CS sh (tarray tuchar n) q = @malloc_token CS sh (tarray tuchar n) q.
Proof. apply equal_f; apply (@malloc_token_change_composite _ _ CC_inflate). reflexivity. Qed.

(* the local z_stream before new_stream() *)
Lemma rs_strm_undef sh q:
  @data_at_ CS sh t_zsl q =
  @data_at Zlib.units.Compress.CS sh t_zs
    (zs_val Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef) q.
Proof. unfold data_at_. change t_zs with t_zsl. unfold zs_val. rewrite rs_strm_cs_c. reflexivity. Qed.

(* the struct after new_stream() on it: inflateInit2_'s raw stream *)
Definition rs_ns_raw : rawf :=
  RF nullval (Vint (Int.repr 0)) Vundef nullval (Vint (Int.repr 0)) Vundef Vundef Vundef Vundef.

Lemma rs_ns_raw_eq gv q:
  @data_at Zlib.units.Compress.CS Tsh t_zs
    (zs_val nullval (Vint (Int.repr 0)) Vundef nullval (Vint (Int.repr 0)) Vundef Vundef Vundef nullval nullval
       nullval Vundef Vundef Vundef) q =
  raw_strm gv Tsh q rs_ns_raw Vundef Vundef nullval nullval nullval.
Proof.
  unfold raw_strm, rs_ns_raw, zs_val; simpl. change t_zs with t_zsl. change Rep.t_strm with t_zsl.
  rewrite rs_strm_cs, rs_strm_cs_c. reflexivity.
Qed.

(* at a `return`: the struct given back to the stack frame *)
Lemma rs_raw_frame gv sh q r m s za zf o: raw_strm gv sh q r m s za zf o |-- @data_at_ CS sh t_zsl q.
Proof. unfold raw_strm. change Rep.t_strm with t_zsl. rewrite rs_strm_cs. apply data_at_data_at_. Qed.
Lemma rs_c_frame sh (v: rs_tuple) q: @data_at Zlib.units.Compress.CS sh t_zs v q |-- @data_at_ CS sh t_zsl q.
Proof. change t_zs with t_zsl. rewrite rs_strm_cs_c. apply data_at_data_at_. Qed.

(* the stream as istreamA holds it, at the law's compspecs *)
Definition rs_tup (gv: globals) (z: zfields) (adv sp: val) : rs_tuple :=
  (zf_ni z, (Vint (Int.repr (zf_ai z)), (Vlong (Int64.repr (zf_tin z)), (zf_no z, (Vint (Int.repr (zf_ao z)),
   (Vlong (Int64.repr (zf_tout z)), (msg_val gv (zf_msg z), (sp, (gv Zlib.inflate.code._zcalloc,
   (gv Zlib.inflate.code._zcfree, (nullval, (Vint (Int.repr (zf_dt z)), (adv, zf_res z))))))))))))).

Lemma rs_istreamA_unfold gv shs vs z av L:
  istreamA gv shs vs z av (Some L) =
  (!! (zf_ok z /\ writable_share shs /\ live_ok L) &&
   (data_at shs t_zsl (rs_tup gv z (adler_v (raw_live (Some L)) z av) (l_sp L)) vs * state_mem gv vs L)).
Proof.
  unfold istreamA, zstrm_atA. change Rep.t_strm with t_zsl. rewrite rs_strm_cs.
  apply pred_ext; entailer!.
Qed.

Lemma rs_istreamA_fold gv shs vs z av L:
  zf_ok z -> writable_share shs -> live_ok L ->
  data_at shs t_zsl (rs_tup gv z (adler_v (raw_live (Some L)) z av) (l_sp L)) vs * state_mem gv vs L
  |-- istreamA gv shs vs z av (Some L).
Proof. intros. rewrite rs_istreamA_unfold. entailer!. Qed.

Lemma rs_a_frame gv shs vs z av L: istreamA gv shs vs z av (Some L) |-- data_at_ shs t_zsl vs * TT.
Proof. rewrite rs_istreamA_unfold. Intros. sep_apply (data_at_data_at_ shs t_zsl). cancel. Qed.

Lemma rs_istreamA_opt_ptr gv shs (vs: val) z av st:
  isptr vs -> istreamA_opt gv shs vs z av st = istreamA gv shs vs z av st.
Proof. intros Pv. unfold istreamA_opt. destruct (eq_dec vs nullval); [subst; contradiction | reflexivity]. Qed.

Lemma rs_is_live_ptr (vs: val) st: isptr vs -> is_live vs st = st.
Proof. intros Pv. unfold is_live. destruct (eq_dec vs nullval); [subst; contradiction | reflexivity]. Qed.

Lemma rs_head_none vs L: isptr vs -> i_head (l_s L) = false -> head_opt (is_live vs (Some L)) = emp.
Proof. intros Pv H. rewrite rs_is_live_ptr by auto. unfold head_opt, head_mem. rewrite H. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The stream after inflateInit2_ returned Z_OK                                                   *)

(* the fields: next_in/next_out NULL and avail_in/avail_out 0 (new_stream), totals 0, msg NULL, data_type 0,
   adler = wrap & 1 for a wrapped stream (0 in the model of a raw stream, whose member stays undefined) *)
Definition rs_z_init (L: live) : zfields :=
  ZF nullval 0 0 nullval 0 0 None 0 (if i_wrap (l_s L) =? 0 then 0 else Z.land (i_wrap (l_s L)) 1) Vundef.

Lemma rs_land1_range x: 0 <= Z.land x 1 <= 1.
Proof.
  change (Z.land x 1) with (Z.land x (Z.ones 1)). rewrite Z.land_ones by lia.
  pose proof (Z.mod_pos_bound x (2 ^ 1) ltac:(reflexivity)). simpl in *. lia.
Qed.

Lemma rs_z_init_ok L: zf_ok (rs_z_init L).
Proof.
  unfold zf_ok, rs_z_init; simpl. pose proof (rs_land1_range (i_wrap (l_s L))).
  destruct (i_wrap (l_s L) =? 0); rep_lia.
Qed.

Lemma rs_init_istreamA gv shs vs L:
  istream_raw gv shs vs (raw_after_init rs_ns_raw (l_s L)) L |-- istreamA gv shs vs (rs_z_init L) Vundef (Some L).
Proof.
  unfold istream_raw, istreamA, raw_strm, zstrm_atA, raw_after_init, rs_z_init, adler_v, raw_live, rs_ns_raw.
  Intros. simpl. pose proof (rs_land1_range (i_wrap (l_s L))).
  destruct (i_wrap (l_s L) =? 0) eqn:E; entailer!; unfold zf_ok; simpl; rep_lia.
Qed.

(* the state after inflateInit2_ is in mode HEAD: InvW.swfW holds *)
Lemma rs_init_swfW sp w: swfW (l_s (init_live sp w)).
Proof.
  assert (M: i_mode (l_s (init_live sp w)) = HEAD).
  { unfold init_live. destruct (reset2_wb w) as [[wrap wb] | ]; reflexivity. }
  unfold swfW. rewrite M. split; intros E; discriminate E.
Qed.

(* inflateInit2_(strm, w, "1.3.2", sizeof(z_stream)) on the local stream: what it returns *)
Lemma rs_init_ret vs w a: isptr vs ->
  init_ret vs 49 112 w a = if a then (if wbits_ok w then Z_OK else Z_STREAM_ERROR) else Z_MEM_ERROR.
Proof.
  intros Pv. unfold init_ret. simpl.
  destruct (EqDec_val vs nullval); [subst; contradiction | ]. destruct a; reflexivity.
Qed.

(* the harness's choices at the end of the stream's construction satisfy RSModel.rs_ok *)
Lemma rs_ok_of n nb na wr window stp s0 dp d op c lens:
  rs_A_facts n nb na wr window stp s0 dp d op -> rs_c_ok wr window c -> rs_lens_ok nb n lens ->
  rs_ok wr window c s0 lens d.
Proof.
  intros (Hn & Hnb & Hna & Hwr & Hw & Hs0 & Hd & Bs & Bd & _) Hc (Hne & Hl & Hf & Hsum).
  unfold rs_ok, rs_slen, rs_c_ok in *. rewrite Hl, Hd. split; [lia | ]. split; [lia | ].
  split; [intros E; apply Hc in E; lia | ]. repeat split; auto; try lia.
Qed.
