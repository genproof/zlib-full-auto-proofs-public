(* Law rj_far_back: main (harness/rj_far_back.c) against MainLib.main_core_spec R_fb, for the theory's facts
   (FBFacts.fb_theory_stmt), calling inflate.c's API through its shared specifications (inflateInit2_: Spec5.v;
   inflate: the wide SpecW.v, raw stream with strm->adler undefined), the helpers of harness/laws_common.h
   (laws_common/Spec.v) and the bit writer (BWSpec.v).  The proof is cut along main's statements into segments
   (fb_from n: the body from its n-th statement on): the inputs (fb_body_main), the writes (fb_seg_writes),
   new_stream and inflateInit2_ (fb_seg_init), the two inflate() calls (fb_seg_calls). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5 Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.bit_writer.BWSpec.
Require Import Zlib.proof.harness.bit_writer.FBFacts.
Require Import Zlib.proof.harness.bit_writer.BWLawCS Zlib.proof.harness.bit_writer.BWGlobals.
Require Zlib.harness.rj_far_back.code.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.crc32.Spec.
Import Zlib.harness.rj_far_back.code.

(* the specifications main calls *)
Definition Gmain_fb : funspecs :=
  [inflateInit2__spec; inflate_specW; zcalloc_i; zcfree_i;
   upto_spec; clip_spec; any_bytes_spec; copy_of_spec; offer_spec; new_stream_spec;
   put_bits_spec; put_literal_spec;
   (_quickproof_malloc, @malloc_spec' FB.CS); nondet_u8_spec; nondet_u32_spec; gp_assert_spec; gp_assume_spec].


#[local] Existing Instance FB.CS.
#[local] Existing Instances FB.CC_inflate FB.CC_adler32 FB.CC_crc32 FB.CC_zutil FB.CC_inffast FB.CC_inftrees
  FB.CC_compress.

(* ---------------------------------------------------------------------------------------------- *)
(* The kit: moves between the units' compspecs and the law's, the stream as main sees it          *)

Definition t_zsf : type := Tstruct _z_stream_s noattr.

(* the 14 members of struct z_stream as istreamA holds them *)
Definition fb_tuple : Type :=
  (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * val)))))))))))))%type.

Definition fb_tup (gv: globals) (z: zfields) (adv sp: val) : fb_tuple :=
  (zf_ni z, (Vint (Int.repr (zf_ai z)), (Vlong (Int64.repr (zf_tin z)), (zf_no z, (Vint (Int.repr (zf_ao z)),
   (Vlong (Int64.repr (zf_tout z)), (msg_val gv (zf_msg z), (sp, (gv Zlib.inflate.code._zcalloc,
   (gv Zlib.inflate.code._zcfree, (nullval, (Vint (Int.repr (zf_dt z)), (adv, zf_res z))))))))))))).

(* the fields of struct z_stream after new_stream() as inflateInit2_ takes them *)
Definition fb_ns_raw : rawf :=
  RF nullval (Vint (Int.repr 0)) Vundef nullval (Vint (Int.repr 0)) Vundef Vundef Vundef Vundef.

(* the harness's ZLIB_VERSION literal "1.3.2" *)
Definition fb_hv : list val := map (fun c => Vint (Int.repr c)) [49; 46; 51; 46; 50; 0].

(* the stream's fields after offer(strm, ni, ai, no, ao) *)
Definition offer_z (z: zfields) (ni: val) (ai: Z) (no: val) (ao: Z) : zfields :=
  ZF ni ai (zf_tin z) no ao (zf_tout z) (zf_msg z) (zf_dt z) (zf_adler z) (zf_res z).

(* the fields after inflateInit2_ returned Z_OK on a raw stream: next_in/next_out NULL and avail_in/avail_out 0
   (new_stream), totals 0, msg NULL, data_type 0 (strm->adler keeps its undefined value: istreamA's av) *)
Definition fb_z0 : zfields := ZF nullval 0 0 nullval 0 0 None 0 0 Vundef.

Ltac fb_cs_tac CC := apply equal_f; apply (@data_at_change_composite _ _ CC); [apply JMeq_refl | reflexivity].

Lemma fb_strm_cs sh (v: fb_tuple) q:
  @data_at Zlib.units.Inflate.CS sh t_zsf v q = @data_at FB.CS sh t_zsf v q.
Proof. fb_cs_tac FB.CC_inflate. Qed.
Lemma fb_strm_cs_c sh (v: fb_tuple) q:
  @data_at Zlib.units.Compress.CS sh t_zsf v q = @data_at FB.CS sh t_zsf v q.
Proof. fb_cs_tac FB.CC_compress. Qed.
Lemma fb_bytes_a sh n (v: list val) q:
  @data_at Zlib.units.Adler32.CS sh (tarray tuchar n) v q = @data_at FB.CS sh (tarray tuchar n) v q.
Proof. fb_cs_tac FB.CC_adler32. Qed.
Lemma fb_tok_a sh n q:
  @malloc_token Zlib.units.Adler32.CS sh (tarray tuchar n) q = @malloc_token FB.CS sh (tarray tuchar n) q.
Proof. apply equal_f; apply (@malloc_token_change_composite _ _ FB.CC_adler32). reflexivity. Qed.
Lemma fb_bytes_i sh n (v: list val) q:
  @data_at Zlib.units.Inflate.CS sh (tarray tuchar n) v q = @data_at FB.CS sh (tarray tuchar n) v q.
Proof. fb_cs_tac FB.CC_inflate. Qed.
Lemma fb_tok_i sh n q:
  @malloc_token Zlib.units.Inflate.CS sh (tarray tuchar n) q = @malloc_token FB.CS sh (tarray tuchar n) q.
Proof. apply equal_f; apply (@malloc_token_change_composite _ _ FB.CC_inflate). reflexivity. Qed.

(* the local z_stream before new_stream() *)
Lemma fb_strm_undef sh p:
  @data_at_ FB.CS sh t_zsf p =
  @data_at Zlib.units.Compress.CS sh t_zs
    (zs_val Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef) p.
Proof. unfold data_at_. change t_zs with t_zsf. unfold zs_val. rewrite fb_strm_cs_c. reflexivity. Qed.

(* after new_stream(): inflateInit2_'s raw stream *)
Lemma fb_ns_raw_eq gv p:
  @data_at Zlib.units.Compress.CS Tsh t_zs
    (zs_val nullval (Vint (Int.repr 0)) Vundef nullval (Vint (Int.repr 0)) Vundef Vundef Vundef nullval nullval
       nullval Vundef Vundef Vundef) p =
  raw_strm gv Tsh p fb_ns_raw Vundef Vundef nullval nullval nullval.
Proof.
  unfold raw_strm, fb_ns_raw, zs_val; simpl. change t_zs with t_zsf. change Rep.t_strm with t_zsf.
  rewrite fb_strm_cs, fb_strm_cs_c. reflexivity.
Qed.

(* at a `return`: the struct of the stream given back to the stack frame *)
Lemma fb_raw_frame gv sh p r m s za zf o: raw_strm gv sh p r m s za zf o |-- @data_at_ FB.CS sh t_zsf p.
Proof. unfold raw_strm. change Rep.t_strm with t_zsf. rewrite fb_strm_cs. apply data_at_data_at_. Qed.
Lemma fb_c_frame sh (v: fb_tuple) p: @data_at Zlib.units.Compress.CS sh t_zs v p |-- @data_at_ FB.CS sh t_zsf p.
Proof. change t_zs with t_zsf. rewrite fb_strm_cs_c. apply data_at_data_at_. Qed.

(* the harness's "1.3.2" as inflateInit2_ takes it *)
Lemma fb_hversion gv:
  @bw_hversion_at FB.CS ___stringlit_rj_far_back_1 gv =
  @data_at Zlib.units.Inflate.CS Ers (tarray tschar (Zlength fb_hv)) fb_hv (gv ___stringlit_rj_far_back_1).
Proof.
  unfold bw_hversion_at, fb_hv. change (Zlength _) with 6. symmetry.
  apply equal_f; apply (@data_at_change_composite _ _ FB.CC_inflate); [apply JMeq_refl | reflexivity].
Qed.

(* R_fb with the harness's version literal at the inflate unit's compspecs *)
Lemma fb_R_unfold gv:
  R_fb gv = (tables_rep Ers gv * crc_table_at Ers gv * version_lit gv *
             @data_at Zlib.units.Inflate.CS Ers (tarray tschar (Zlength fb_hv)) fb_hv
               (gv ___stringlit_rj_far_back_1))%logic.
Proof. unfold R_fb, bw_R. f_equal; apply fb_hversion. Qed.

Lemma fb_istreamA_opt_ptr gv shs (vs: val) z av st:
  isptr vs -> istreamA_opt gv shs vs z av st = istreamA gv shs vs z av st.
Proof. intros Pv. unfold istreamA_opt. destruct (eq_dec vs nullval); [subst; contradiction | reflexivity]. Qed.

Lemma fb_is_live_ptr (vs: val) st: isptr vs -> is_live vs st = st.
Proof. intros Pv. unfold is_live. destruct (eq_dec vs nullval); [subst; contradiction | reflexivity]. Qed.

(* a live stream: the struct at the law's compspecs and the memory behind strm->state *)
Lemma fb_istreamA_unfold gv shs vs z av L:
  istreamA gv shs vs z av (Some L) =
  (!! (zf_ok z /\ writable_share shs /\ live_ok L) &&
   (data_at shs t_zsf (fb_tup gv z (adler_v (raw_live (Some L)) z av) (l_sp L)) vs * state_mem gv vs L))%logic.
Proof.
  unfold istreamA, zstrm_atA.
  change Rep.t_strm with t_zsf. rewrite fb_strm_cs.
  apply pred_ext; entailer!.
Qed.

Lemma fb_istreamA_fold gv shs vs z av L:
  zf_ok z -> writable_share shs -> live_ok L ->
  (data_at shs t_zsf (fb_tup gv z (adler_v (raw_live (Some L)) z av) (l_sp L)) vs * state_mem gv vs L)%logic
  |-- istreamA gv shs vs z av (Some L).
Proof. intros. rewrite fb_istreamA_unfold. entailer!. Qed.

Lemma fb_a_frame gv shs vs z av L: istreamA gv shs vs z av (Some L) |-- (data_at_ shs t_zsf vs * TT)%logic.
Proof. rewrite fb_istreamA_unfold. Intros. sep_apply (data_at_data_at_ shs t_zsf). cancel. Qed.

Lemma fb_a_frame_opt gv shs vs z av st: isptr vs ->
  istreamA_opt gv shs vs z av st |-- (data_at_ shs t_zsf vs * TT)%logic.
Proof.
  intros Pv. rewrite fb_istreamA_opt_ptr by auto. destruct st as [L|]; [apply fb_a_frame | ].
  unfold istreamA, zstrm_atA. change Rep.t_strm with t_zsf. rewrite fb_strm_cs. Intros.
  sep_apply (data_at_data_at_ shs t_zsf). cancel.
Qed.

(* the stream after inflateInit2_(strm, w) returned Z_OK on a raw stream (-15 <= w <= -8) *)
Lemma fb_init_raw sp w: -15 <= w <= -8 -> i_wrap (l_s (init_live sp w)) = 0.
Proof.
  intros Hw. unfold init_live, reset2_wb. simpl.
  destruct (w <? 0) eqn:E; [ | apply Z.ltb_ge in E; lia].
  destruct (w <? -15) eqn:E1; [apply Z.ltb_lt in E1; lia | ].
  destruct (8 <=? - w) eqn:E2, (- w <=? 15) eqn:E3; rewrite ?Z.leb_le, ?Z.leb_gt in *; try lia; cbn [andb].
  (* wb = -w is not 0: inflateInit2_ keeps wrap 0 (bit 3 only when the header gives the window size) *)
  unfold init_s, reset2_s, reset_full_s, reset_hdr_s, reset2_wrap.
  destruct (Z.eqb_spec (- w) 0); [lia | ]. reflexivity.
Qed.

Lemma fb_init_istreamA gv shs vs sp w: -15 <= w <= -8 ->
  istream_raw gv shs vs (raw_after_init fb_ns_raw (l_s (init_live sp w))) (init_live sp w)
  |-- istreamA gv shs vs fb_z0 Vundef (Some (init_live sp w)).
Proof.
  intros Hw. pose proof (fb_init_raw sp w Hw) as R.
  unfold istream_raw, istreamA, raw_strm, zstrm_atA, raw_after_init, fb_z0, adler_v, raw_live, fb_ns_raw.
  rewrite R. Intros. simpl. entailer!. unfold zf_ok; simpl; rep_lia.
Qed.

(* the struct as offer() takes it *)
Lemma fb_istreamA_zs gv vs z av L:
  istreamA gv Tsh vs z av (Some L) |--
  (!! (zf_ok z /\ live_ok L) &&
   (@data_at Zlib.units.Compress.CS Tsh t_zs
      (zs_val (zf_ni z) (Vint (Int.repr (zf_ai z))) (Vlong (Int64.repr (zf_tin z))) (zf_no z)
         (Vint (Int.repr (zf_ao z))) (Vlong (Int64.repr (zf_tout z))) (msg_val gv (zf_msg z)) (l_sp L)
         (gv Zlib.inflate.code._zcalloc) (gv Zlib.inflate.code._zcfree) nullval (Vint (Int.repr (zf_dt z)))
         (adler_v (raw_live (Some L)) z av) (zf_res z)) vs * state_mem gv vs L))%logic.
Proof.
  rewrite fb_istreamA_unfold. Intros. change t_zs with t_zsf. rewrite fb_strm_cs_c. entailer!.
Qed.

Lemma fb_zf_ok_offer z ni ai no ao: zf_ok z -> 0 <= ai <= Int.max_unsigned -> 0 <= ao <= Int.max_unsigned ->
  zf_ok (offer_z z ni ai no ao).
Proof. unfold zf_ok, offer_z; simpl; intuition. Qed.

Lemma fb_head_none vs L: isptr vs -> i_head (l_s L) = false -> head_opt (is_live vs (Some L)) = emp.
Proof. intros Pv H. rewrite fb_is_live_ptr by auto. unfold head_opt, head_mem. rewrite H. reflexivity. Qed.

(* the input object of a call (copy_of: take bytes data) and the output object (malloc: room undefined bytes) *)
Definition fb_ib (piece: val) (take: Z) (data: list Z) : inbuf := InBuf Ews piece 0 take (bytes_rep data).
Definition fb_ob (outp: val) (room: Z) : outbuf := OutBuf Ews outp 0 room (Zrepeat Vundef room).

(* after offer(strm, piece, take, outp, room): the stream inflate() takes (no gz_header) *)
Lemma fb_offer_fold gv vs z av L piece take data outp room:
  isptr vs -> isptr piece -> isptr outp -> zf_ok z -> live_ok L -> i_head (l_s L) = false ->
  0 <= take <= Int.max_unsigned -> 0 <= room <= Int.max_unsigned ->
  (@data_at Zlib.units.Compress.CS Tsh t_zs
      (zs_val piece (Vint (Int.repr take)) (Vlong (Int64.repr (zf_tin z))) outp
         (Vint (Int.repr room)) (Vlong (Int64.repr (zf_tout z))) (msg_val gv (zf_msg z)) (l_sp L)
         (gv Zlib.inflate.code._zcalloc) (gv Zlib.inflate.code._zcfree) nullval (Vint (Int.repr (zf_dt z)))
         (adler_v (raw_live (Some L)) z av) (zf_res z)) vs * state_mem gv vs L)%logic
  |-- (istreamA_opt gv Tsh vs (offer_z z (in_ptr (fb_ib piece take data) 0) take (out_ptr (fb_ob outp room) 0) room)
         av (Some L) * head_opt (is_live vs (Some L)))%logic.
Proof.
  intros Pv Pp Po Zo Lo Hh Ht Hr.
  rewrite fb_head_none, fb_istreamA_opt_ptr by auto. rewrite sepcon_emp.
  eapply derives_trans;
    [ | apply (fb_istreamA_fold gv Tsh vs (offer_z z (in_ptr (fb_ib piece take data) 0) take
                                         (out_ptr (fb_ob outp room) 0) room) av L);
        [apply fb_zf_ok_offer; auto | auto | auto]].
  change t_zs with t_zsf. rewrite fb_strm_cs_c.
  unfold fb_tup, offer_z, adler_v, fb_ib, fb_ob, in_ptr, out_ptr; simpl.
  destruct piece; try contradiction. destruct outp; try contradiction. simpl.
  rewrite !Ptrofs.add_zero. apply derives_refl.
Qed.

Lemma fb_in_ok piece take data: isptr piece -> Zlength data = take -> take <= Ptrofs.max_unsigned ->
  is_bytes data -> in_ok (fb_ib piece take data) data.
Proof.
  intros Pp Hl Ht Hb. unfold in_ok, fb_ib. pose proof (Zlength_nonneg data).
  assert (Zlength (bytes_rep data) = take) by (unfold bytes_rep; rewrite Zlength_map; auto).
  repeat split; auto; try lia.
  rewrite Z.add_0_l, sublist_same by lia. reflexivity.
Qed.

Lemma fb_out_ok outp room: isptr outp -> 0 <= room <= Ptrofs.max_unsigned -> out_ok (fb_ob outp room) room.
Proof.
  intros Pp Hr. unfold out_ok, fb_ob. rewrite Zlength_Zrepeat by lia.
  split; [apply writable_Ews | ]. repeat split; auto; lia.
Qed.

(* the two new objects (copy_of's and malloc's, at the law's compspecs) as inflate()'s buffers *)
Lemma fb_bufs_pre vs L piece take data outp room:
  isptr vs -> 0 <= room ->
  (data_at Ews (tarray tuchar take) (bytes_rep data) piece * malloc_token Ews (tarray tuchar take) piece *
   data_at_ Ews (tarray tuchar room) outp * malloc_token Ews (tarray tuchar room) outp)%logic
  |-- bufs_opt (is_live vs (Some L)) (fb_ib piece take data) (Some (fb_ob outp room)) [] true true.
Proof.
  intros Pv Hr. rewrite fb_is_live_ptr by auto.
  unfold bufs_opt, in_rep, out_opt, out_rep, in_tok, out_tok, fb_ib, fb_ob.
  rewrite sublist_nil, Zlength_nil, Z.add_0_l, app_nil_l. unfold byte_vals. simpl map. rewrite app_nil_l.
  rewrite sublist_same by (rewrite ?Zlength_Zrepeat; lia).
  rewrite <- (fb_bytes_i Ews take (bytes_rep data) piece), <- (fb_tok_i Ews take piece), <- (fb_tok_i Ews room outp).
  unfold data_at_, default_val. simpl. rewrite (fb_bytes_i Ews room (Zrepeat Vundef room) outp). cancel.
Qed.

(* after the call: the input object and the output object holding what was written (any contents) *)
Lemma fb_bufs_post vs L piece take data outp room ow:
  isptr vs ->
  bufs_opt (is_live vs (Some L)) (fb_ib piece take data) (Some (fb_ob outp room)) ow true true
  |-- (data_at Ews (tarray tuchar take) (bytes_rep data) piece * malloc_token Ews (tarray tuchar take) piece *
       malloc_token Ews (tarray tuchar room) outp * TT)%logic.
Proof.
  intros Pv. rewrite fb_is_live_ptr by auto.
  unfold bufs_opt, in_rep, out_opt, out_rep, in_tok, out_tok, fb_ib, fb_ob.
  rewrite <- (fb_bytes_i Ews take (bytes_rep data) piece), <- (fb_tok_i Ews take piece), <- (fb_tok_i Ews room outp).
  cancel.
Qed.

(* read += take - avail_in without overflow *)
Lemma fb_read_step tin take ai:
  0 <= tin -> 0 <= ai <= take -> tin + take <= Int64.max_unsigned -> ai <= Int.max_unsigned ->
  Int64.add (Int64.repr tin) (Int64.sub (Int64.repr take) (Int64.repr (Int.unsigned (Int.repr ai)))) =
  Int64.repr (tin + (take - ai)).
Proof.
  intros H1 H2 H3 H4. rewrite Int.unsigned_repr by rep_lia.
  unfold Int64.add, Int64.sub.
  rewrite (Int64.unsigned_repr take), (Int64.unsigned_repr ai), (Int64.unsigned_repr (take - ai)),
    (Int64.unsigned_repr tin) by rep_lia.
  reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The segments of main: main's body from its n-th statement on (n counted along the sequence of its *)
(* statements), each proved from an assertion to the function's postcondition                       *)

Fixpoint fb_drop (n: nat) (s: statement) : statement :=
  match n, s with
  | O, _ => s
  | S n', Ssequence _ s2 => fb_drop n' s2
  | S _, _ => Sskip
  end.

(* main's body is `BIG; return 0;`: drop n statements of BIG, keep the final return *)
Definition fb_from (n: nat) : statement :=
  match fn_body f_main with Ssequence s r => Ssequence (fb_drop n s) r | s => s end.

Definition fb_Delta : tycontext := func_tycontext f_main (QPvarspecs FB.p) Gmain_fb nil.
Definition fb_POST : ret_assert :=
  frame_ret_assert (function_body_ret_assert tint (EX r : int, PROP () RETURN (Vint r) SEP (TT))%argsassert)
    (stackframe_of f_main).

(* The inputs main draws before the writes: window_bits = -8 - wb, the literals lits, length_code lc,
   distance_code dc, extra; then the stream of stream_len = |S0| arbitrary bytes S0 *)
Definition fb_inputs (wb: Z) (S0 lits: list Z) (lc dc extra: Z) : Prop :=
  0 <= wb <= 7 /\ is_bytes lits /\ Zlength lits <= 32767 /\ 257 <= lc <= 285 /\ 0 <= dc <= 29 /\
  0 <= extra <= Int.max_unsigned /\ Zlength lits < fb_dist dc extra /\
  is_bytes S0 /\ 6 + 2 * Zlength lits <= Zlength S0 <= Int64.max_signed.

(* ---------------------------------------------------------------------------------------------- *)
(* The two inflate() calls: what main's loop knows before each call                                *)

Require Zlib.proof.uncompr.URunFrame.

(* a run of inflate()'s model from a live stream keeps the input bytes, the output space and i_head: by
   URunFrame.run2_frame in the modes HEAD..BAD; in MEM and SYNC the first step returns at once *)
Lemma fb_run2_frame flush fx dx z L inp res:
  HEAD <= i_mode (l_s L) <= SYNC ->
  run2 flush fx dx (m_init z L inp) res ->
  m_inp (r_m res) = inp /\ m_aout (r_m res) = zf_ao z /\ i_head (m_s (r_m res)) = i_head (l_s L).
Proof.
  intros Hm R.
  assert (Hmi: HEAD <= i_mode (m_s (m_init z L inp)) <= SYNC /\
               (BAD < i_mode (l_s L) -> i_mode (m_s (m_init z L inp)) = i_mode (l_s L)) /\
               i_head (m_s (m_init z L inp)) = i_head (l_s L)).
  { unfold m_init. cbv zeta. simpl m_s.
    destruct (i_mode (l_s L) =? Zlib.proof.inflate.Model.TYPE) eqn:E; [apply Z.eqb_eq in E | ];
      unfold set_i_mode; simpl; rewrite ?E; cbv [HEAD SYNC BAD TYPEDO Zlib.proof.inflate.Model.TYPE] in *;
      repeat split; lia. }
  destruct Hmi as (Hb & Hk & Hh).
  destruct (Z_le_gt_dec (i_mode (m_s (m_init z L inp))) BAD) as [V|V].
  - destruct (URunFrame.run2_frame flush fx dx (m_init z L inp) res ltac:(unfold URunFrame.vmode; lia) R)
      as (A & B & _ & D & _).
    rewrite A, B, D, Hh. auto.
  - destruct R as (o & Lp & Ro).
    assert (E: stepf2 flush fx dx (m_init z L inp) =
               IRet (if i_mode (m_s (m_init z L inp)) =? MEM then Z_MEM_ERROR else Z_STREAM_ERROR)
                    (m_init z L inp)).
    { set (m0 := m_init z L inp) in *. clearbody m0. unfold stepf2, step2, m_mode.
      assert (Em: i_mode (m_s m0) = MEM \/ i_mode (m_s m0) = SYNC) by (cbv [HEAD SYNC BAD MEM] in *; lia).
      destruct Em as [Em|Em]; rewrite Em; reflexivity. }
    inversion Lp as [m r m' E1|m m' E1 Lv|m m' o' E1 Lv L']; subst;
      rewrite E in E1; try discriminate.
    inversion E1; subst. split; [reflexivity | split; [reflexivity | exact Hh]].
Qed.

(* the state after the first call: whatever the second call is offered (the rest of the stream from rd, room
   for the literals and one byte more, a flush other than Z_TREES), it returns Z_MEM_ERROR or Z_DATA_ERROR
   having written at most nlits - wr bytes *)
Definition fb_after1 (S: list Z) (nlits: Z) (L: live) (rd wr: Z) : Prop :=
  forall L' z' flush' res',
    l_s L' = l_s L -> live_ok L' -> zf_ok z' -> nlits + 1 <= zf_ao z' ->
    Int.min_signed <= flush' <= Int.max_signed -> flush' <> Z_TREES ->
    run2 flush' lenfix_list distfix_list
      (m_init z' L' (sublist rd (rd + Z.min (Zlength S - rd) Int.max_unsigned) S)) res' ->
    r_ret res' = Z_MEM_ERROR \/
    (r_ret res' = Z_DATA_ERROR /\ m_sow (r_m res') = Zlength (m_ow (r_m res')) /\
     wr + Zlength (m_ow (r_m res')) <= nlits).

(* the loop of main at `call = k` (k = 1, 2; 3 after the loop): the stream's fields z and live part L, read rd
   and written wr; S the stream bytes, nlits the number of literals, L0 the stream after inflateInit2_ *)
Definition fb_phase (S: list Z) (nlits: Z) (L0: live) (k: Z) (z: zfields) (L: live) (rd wr: Z) : Prop :=
  if k =? 1 then z = fb_z0 /\ L = L0 /\ rd = 0 /\ wr = 0
  else if k =? 2 then
    swfW (l_s L) /\ i_head (l_s L) = false /\ 0 <= rd <= Zlength S /\ 0 <= wr <= nlits /\
    fb_after1 S nlits L rd wr
  else True.

(* the call's arguments: the first takes any first part of the stream and any room, the second the rest
   (at most 2^32 - 1 bytes), room for the literals and one byte more and a flush other than Z_TREES *)
Definition fb_args (S: list Z) (nlits: Z) (k rd take room flush: Z) : Prop :=
  Int.min_signed <= flush <= Int.max_signed /\ 0 <= room <= Int.max_unsigned /\
  if k =? 1 then 0 <= take <= Z.min (Zlength S) Int.max_unsigned
  else take = Z.min (Zlength S - rd) Int.max_unsigned /\ nlits + 1 <= room /\ flush <> Z_TREES.

Lemma fb_init_head sp w: i_head (l_s (init_live sp w)) = false /\ i_mode (l_s (init_live sp w)) = HEAD.
Proof.
  unfold init_live. simpl. destruct (reset2_wb w) as [[a b]|]; unfold init_s, reset2_s; simpl; auto.
Qed.

(* one call of the loop: from the theory's facts, the call (not Z_MEM_ERROR) keeps the stream live, consumes
   n <= take bytes, writes ow (written + |ow| <= nlits), returns Z_DATA_ERROR the second time, and leaves the
   loop's facts for call k + 1 *)
Lemma fb_step S0 fin lits lc lx dc extra sp wb k z L rd wr take room flush vs piece outp r z' st' ow:
  fb_theory_stmt -> fb_ok S0 fin lits lc lx dc extra -> 0 <= wb <= 7 ->
  let S := fb_bytes S0 fin lits lc lx dc extra in
  Zlength S = Zlength S0 ->
  (k = 1 \/ k = 2) ->
  fb_phase S (Zlength lits) (init_live sp (-8 - wb)) k z L rd wr ->
  fb_args S (Zlength lits) k rd take room flush ->
  0 <= rd -> 0 <= take -> rd + take <= Zlength S ->
  zf_ok z -> live_ok L -> isptr vs ->
  inflate_rel flush vs (offer_z z (in_ptr (fb_ib piece take (sublist rd (rd + take) S)) 0) take
                          (out_ptr (fb_ob outp room) 0) room)
    (Some L) (fb_ib piece take (sublist rd (rd + take) S)) (sublist rd (rd + take) S)
    (Some (fb_ob outp room)) r z' st' ow ->
  r <> Z_MEM_ERROR ->
  exists L' n, st' = Some L' /\ 0 <= n <= take /\ zf_ai z' = take - n /\ zf_ao z' = room - Zlength ow /\
    (k = 2 -> r = Z_DATA_ERROR) /\ wr + Zlength ow <= Zlength lits /\ 0 <= Zlength ow /\
    (swfW (l_s L') -> fb_phase S (Zlength lits) (init_live sp (-8 - wb)) (k + 1) z' L' (rd + n) (wr + Zlength ow)).
Proof.
  intros TH OK Hwb S HS Hk Ph Ar Hrd Ht Hrt Zo Lo Pvs REL Hr.
  set (data := sublist rd (rd + take) S) in *.
  assert (Hdl: Zlength data = take) by (unfold data; rewrite Zlength_sublist; lia).
  destruct REL as [(Bad & _)|(_ & L1 & o & res & winp & E1 & E2 & RUN & Hsnx & Er & Eow & Ez & _ & Est)].
  { exfalso. unfold inflate_bad in Bad. rewrite fb_is_live_ptr in Bad by auto.
    destruct Bad as [B|[B|[B _]]]; discriminate. }
  inversion E1; subst L1. inversion E2; subst o. clear E1 E2.
  destruct (fb_run2_frame _ _ _ _ _ _ _ (sw_mode _ (proj1 (proj2 Lo))) RUN) as (Fi & Fa & Fh).
  simpl in Fa. rewrite Hdl in Hsnx.
  exists (Live (l_sp L) winp (m_s (r_m res)) (m_h (r_m res)) (l_headp L) (l_hsh L) (l_xb L) (l_nb L) (l_cb L)).
  exists (m_snx (r_m res)).
  assert (Ezai: zf_ai z' = take - m_snx (r_m res)) by (subst z'; unfold z_after; simpl; rewrite Fi, Hdl; reflexivity).
  unfold fb_phase, fb_args in *.
  destruct Hk as [Hk|Hk]; subst k; simpl in Ph, Ar |- *.
  - destruct Ph as (-> & -> & -> & ->). destruct Ar as (Hfl & Hroom & Htk).
    destruct (fb_init_head sp (-8 - wb)) as (Hh0 & Hm0).
    assert (Zo1: zf_ok (offer_z fb_z0 (in_ptr (fb_ib piece take data) 0) take (out_ptr (fb_ob outp room) 0) room))
      by (apply fb_zf_ok_offer; auto; rep_lia).
    replace data with (sublist 0 take S) in RUN by (unfold data; f_equal; lia).
    destruct (TH S0 fin lits lc lx dc extra (-8 - wb) sp (init_live sp (-8 - wb)) _ take flush res OK
                ltac:(lia) eq_refl Lo Zo1 Htk Hfl RUN) as [M|(Hw & Hsow & Hn & K)].
    { exfalso. apply Hr. subst r. exact M. }
    assert (Ezao: zf_ao z' = room - Zlength ow) by (subst z' ow; unfold z_after; simpl; rewrite Fa, Hsow; reflexivity).
    split; [exact Est | ]. split; [lia | ]. split; [exact Ezai | ]. split; [exact Ezao | ].
    split; [intro; discriminate | ]. subst ow. pose proof (Zlength_nonneg (m_ow (r_m res))).
    split; [lia | ]. split; [lia | ].
    intros Hsw. simpl. split; [exact Hsw | ]. split; [rewrite Fh; exact Hh0 | ].
    split; [lia | ]. split; [lia | ].
    intros L' z2 flush' res' HL' Lo' Zo' Hao Hfl' Htr RUN'.
    rewrite Z.add_0_l in *.
    destruct (K L' z2 flush' res' HL' Lo' Zo' Hao Hfl' Htr RUN') as [M'|(Hd & Hs' & Hw')]; [left; exact M' | ].
    right. split; [exact Hd | ]. split; [exact Hs' | ]. lia.
  - destruct Ph as (Hsw & Hh & Hrd' & Hwr & K). destruct Ar as (Hfl & Hroom & Htk & Hro & Htr).
    assert (Zo1: zf_ok (offer_z z (in_ptr (fb_ib piece take data) 0) take (out_ptr (fb_ob outp room) 0) room))
      by (apply fb_zf_ok_offer; auto; rep_lia).
    assert (Ed: data = sublist rd (rd + Z.min (Zlength S - rd) Int.max_unsigned) S) by (unfold data; rewrite Htk; reflexivity).
    rewrite Ed in RUN.
    destruct (K L _ flush res eq_refl Lo Zo1 ltac:(simpl; lia) Hfl Htr RUN) as [M|(Hd & Hsow & Hw)].
    { exfalso. apply Hr. subst r. exact M. }
    assert (Ezao: zf_ao z' = room - Zlength ow) by (subst z' ow; unfold z_after; simpl; rewrite Fa, Hsow; reflexivity).
    split; [exact Est | ]. split; [lia | ]. split; [exact Ezai | ]. split; [exact Ezao | ].
    split; [intros _; subst r; exact Hd | ]. subst ow. pose proof (Zlength_nonneg (m_ow (r_m res))).
    split; [lia | ]. split; [lia | ]. intros _. exact I.
Qed.

(* main's writes keep the stream's bytes bytes (BWModel's put_bits_m_ok, put_lits_ok) *)
Lemma fb_bytes_ok S0 fin lits lc lx dc extra:
  fb_ok S0 fin lits lc lx dc extra -> is_bytes (fb_bytes S0 fin lits lc lx dc extra).
Proof.
  intros (Hf & Hlb & Hln & Hlc & Hlx & Hdc & Hex & _ & HS0 & HS0n).
  pose proof (lits_len_bounds lits) as LB. pose proof (Zlength_nonneg lits).
  assert (HLB: 0 <= fb_lbits lc <= 5).
  { unfold fb_lbits. destruct (andb (265 <=? lc) (lc <=? 284)) eqn:E; [|lia].
    rewrite andb_true_iff, !Z.leb_le in E.
    assert ((lc - 261) / 4 < 6) by (apply Z.div_lt_upper_bound; lia).
    assert (0 <= (lc - 261) / 4) by (apply Z.div_pos; lia). lia. }
  assert (HDB: 0 <= fb_dbits dc <= 13).
  { unfold fb_dbits. destruct (4 <=? dc) eqn:E; [|lia]. rewrite Z.leb_le in E.
    assert (2 <= dc / 2) by (apply Z.div_le_lower_bound; lia).
    assert (dc / 2 < 15) by (apply Z.div_lt_upper_bound; lia). lia. }
  unfold fb_bytes. cbv zeta.
  destruct (put_bits_m_ok S0 0 fin 1 0 HS0 ltac:(lia) ltac:(lia) ltac:(lia)) as (L1 & B1).
  set (S1 := put_bits_m S0 0 fin 1 0) in *.
  destruct (put_bits_m_ok S1 1 1 2 0 B1 ltac:(lia) ltac:(lia) ltac:(lia)) as (L2 & B2).
  set (S2 := put_bits_m S1 1 1 2 0) in *.
  destruct (put_lits_ok lits S2 3 B2 ltac:(lia) ltac:(lia)) as (L3 & B3).
  set (S3 := put_lits S2 3 lits) in *.
  set (b := 3 + lits_len lits).
  assert (E4: exists S4, S4 = (if lc <? 280 then put_bits_m S3 b (lc - 256) 7 1 else put_bits_m S3 b (192 + lc - 280) 8 1)
                         /\ Zlength S4 = Zlength S0 /\ is_bytes S4).
  { eexists; split; [reflexivity | ]. destruct (lc <? 280).
    - destruct (put_bits_m_ok S3 b (lc - 256) 7 1 B3 ltac:(lia) ltac:(lia) ltac:(lia)) as (L4 & B4). split; [lia | auto].
    - destruct (put_bits_m_ok S3 b (192 + lc - 280) 8 1 B3 ltac:(lia) ltac:(lia) ltac:(lia)) as (L4 & B4).
      split; [lia | auto]. }
  destruct E4 as (S4 & <- & L4 & B4).
  set (b2 := b + (if lc <? 280 then 7 else 8)).
  assert (Hb2: b2 <= b + 8) by (unfold b2; destruct (lc <? 280); lia).
  destruct (put_bits_m_ok S4 b2 lx (fb_lbits lc) 0 B4 ltac:(unfold b2; destruct (lc <? 280); lia) ltac:(lia) ltac:(lia))
    as (L5 & B5).
  destruct (put_bits_m_ok (put_bits_m S4 b2 lx (fb_lbits lc) 0) (b2 + fb_lbits lc) dc 5 1 B5
              ltac:(unfold b2; destruct (lc <? 280); lia) ltac:(lia) ltac:(lia)) as (L6 & B6).
  destruct (put_bits_m_ok _ (b2 + fb_lbits lc + 5) extra (fb_dbits dc) 0 B6
              ltac:(unfold b2; destruct (lc <? 280); lia) ltac:(lia) ltac:(lia)) as (L7 & B7).
  exact B7.
Qed.

(* before a call: the stream's state is one inflate() takes (no gz_header, swfW) *)
Lemma fb_phase_call S nlits sp wb k z L rd wr:
  0 <= nlits -> (k = 1 \/ k = 2) -> fb_phase S nlits (init_live sp (-8 - wb)) k z L rd wr ->
  swfW (l_s L) /\ i_head (l_s L) = false /\ 0 <= rd <= Zlength S /\ 0 <= wr <= nlits.
Proof.
  intros Hn [-> | ->] Ph; unfold fb_phase in Ph; simpl in Ph.
  - destruct Ph as (_ & -> & -> & ->). destruct (fb_init_head sp (-8 - wb)) as (Hh & Hm).
    pose proof (Zlength_nonneg S).
    unfold swfW. rewrite Hm. split; [split; intro E; cbv in E; discriminate | ]. repeat split; auto; lia.
  - tauto.
Qed.

(* a branch that cannot be taken *)
Ltac fb_infeas := exfalso; first [ match goal with H: ?a <> ?b |- _ => solve [apply H; reflexivity] end
                                 | match goal with H: _ |- _ => solve [discriminate H] end
                                 | contradiction ].
(* forward_if whose join adds temp t = v to the current assertion *)
Ltac fb_ifpostv t v := match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx ?R))) _ _ =>
  forward_if (PROPx [] (LOCALx (temp t v :: Q) (SEPx R))) end.
(* right-associate, so that `x = f(...)` is a call followed by a set *)
Ltac fb_split_call := repeat match goal with |- semax _ _ (Ssequence (Ssequence _ _) _) _ => apply -> seq_assoc end.

(* main's loop at `call = c` with the facts of phase k (k = c at the loop head, c + 1 before `call++`): the
   stream, read and written, and the objects of the earlier calls (G) *)
Definition fb_inv (gv: globals) (vs vb strp: val) (S0 S: list Z) (nlits: Z) (L0: live) (Fr: mpred) (k c: Z)
    : environ -> mpred :=
  EX z: zfields, EX L: live, EX rd: Z, EX wr: Z, EX G: mpred,
  PROP (1 <= c <= 3; 1 <= k <= 3; fb_phase S nlits L0 k z L rd wr)
  LOCAL (temp _call (Vint (Int.repr c)); temp _read (Vlong (Int64.repr rd));
         temp _written (Vlong (Int64.repr wr)); temp _literals (Vlong (Int64.repr nlits));
         temp _stream_len (Vlong (Int64.repr (Zlength S0))); temp _stream strp;
         lvar _strm t_zsf vs; lvar _bit tulong vb; gvars gv)
  SEP (istreamA gv Tsh vs z Vundef (Some L); data_at_ Tsh tulong vb; mem_mgr gv; zfuncs gv;
       tables_rep Ers gv; crc_table_at Ers gv;
       malloc_token Ews (tarray tuchar (Zlength S0)) strp;
       data_at Ews (tarray tuchar (Zlength S0)) (bytes_rep S) strp; Fr; G).

(* Statements 25 to the end: read = 0, written = 0, the two inflate() calls, return 0.  The stream is
   inflateInit2_'s, at state init_live sp (-8 - wb); S its input bytes (main's writes into S0). *)
Lemma fb_seg_calls {Espec: OracleKind} gv vs vb strp sp wb S0 fin lits lc lx dc extra Fr :
  fb_theory_stmt -> fb_ok S0 fin lits lc lx dc extra -> 0 <= wb <= 7 ->
  live_ok (init_live sp (-8 - wb)) ->
  semax fb_Delta
    (PROP ()
     LOCAL (temp _literals (Vlong (Int64.repr (Zlength lits)));
            temp _stream_len (Vlong (Int64.repr (Zlength S0))); temp _stream strp;
            lvar _strm t_zsf vs; lvar _bit tulong vb; gvars gv)
     SEP (istreamA gv Tsh vs fb_z0 Vundef (Some (init_live sp (-8 - wb)));
          data_at_ Tsh tulong vb; mem_mgr gv; zfuncs gv; tables_rep Ers gv; crc_table_at Ers gv;
          malloc_token Ews (tarray tuchar (Zlength S0)) strp;
          data_at Ews (tarray tuchar (Zlength S0)) (bytes_rep (fb_bytes S0 fin lits lc lx dc extra)) strp; Fr))
    (fb_from 25) fb_POST.
Proof.
intros TH OK Hwb HL.
unfold fb_from. cbv [fb_drop f_main fn_body]. unfold fb_Delta, fb_POST. simplify_func_tycontext. abbreviate_semax.
set (S := fb_bytes S0 fin lits lc lx dc extra) in *.
set (L0 := init_live sp (-8 - wb)) in *.
assert_PROP (Zlength S = Zlength S0) as HS.
{ entailer!. match goal with H: Zlength (bytes_rep S) = _ |- _ => unfold bytes_rep in H; rewrite Zlength_map in H end.
  pose proof (Zlength_nonneg S0). lia. }
assert_PROP (isptr strp) as Pstrp.
{ entailer!. }
assert_PROP (isptr vs) as Pvs by entailer!.
assert (Hn: 0 <= Zlength lits <= 32767 /\ 6 + 2 * Zlength lits <= Zlength S0 <= Int64.max_signed)
  by (pose proof (Zlength_nonneg lits); unfold fb_ok in OK; tauto).
forward. forward. forward.
forward_loop (EX k: Z, fb_inv gv vs vb strp S0 S (Zlength lits) L0 Fr k k)
  continue: (EX k: Z, fb_inv gv vs vb strp S0 S (Zlength lits) L0 Fr (k + 1) k)
  break: (EX k: Z, fb_inv gv vs vb strp S0 S (Zlength lits) L0 Fr k k).
{ Exists 1. unfold fb_inv. Exists fb_z0 L0 0 0 emp. entailer!. unfold fb_phase; simpl; auto. }
{ Intros k. unfold fb_inv. Intros z L rd wr G.
  forward_if.
  2: { forward. Exists k. unfold fb_inv. Exists z L rd wr G. entailer!. }
  assert (Hk: k = 1 \/ k = 2) by lia.
  repeat match goal with |- semax _ _ (Ssequence (Ssequence _ _) _) _ => apply -> seq_assoc end.
  forward_call tt. Intros u. forward.
  assert (Eu: Int.repr u = Int.repr (Int.signed (Int.repr u))) by (rewrite Int.repr_signed; auto).
  rewrite Eu. clear Eu. set (fl := Int.signed (Int.repr u)).
  assert (Hfl: Int.min_signed <= fl <= Int.max_signed) by apply Int.signed_range. clearbody fl.
  (* the choices of the call: take, room (and flush <> Z_TREES the second time) *)
  match goal with |- semax _ (PROPx _ (LOCALx (_ :: _ :: ?Q) (SEPx ?R))) _ _ =>
    forward_if (EX take: Z, EX room: Z,
      PROPx [fb_args S (Zlength lits) k rd take room fl; 0 <= take; rd + take <= Zlength S]
        (LOCALx (temp _take (Vlong (Int64.repr take)) :: temp _room (Vlong (Int64.repr room)) ::
                 temp _flush (Vint (Int.repr fl)) :: Q) (SEPx R))) end.
  { (* call 1: take = upto(clip(stream_len)), room = upto(UINT_MAX) *)
    assert (k = 1) by (destruct Hk; subst; auto; discriminate). subst k.
    repeat match goal with |- semax _ _ (Ssequence (Ssequence _ _) _) _ => apply -> seq_assoc end.
    forward_call (Zlength S0).
    forward_call (Z.min (Zlength S0) Int.max_unsigned).
    Intros take. forward. forward_call tt. Intros room. forward. Exists take room.
    destruct H0 as (_ & _ & -> & _). entailer!. unfold fb_args; simpl.
    pose proof (Z.le_min_l (Zlength S0) Int.max_unsigned). rewrite HS. repeat split; lia. }
  { (* call 2: take = clip(stream_len - read), room = literals + 1 + upto(UINT_MAX - literals - 1),
       gp_assume(flush != Z_TREES) *)
    assert (k = 2).
    { destruct Hk as [E|E]; [subst k; exfalso | exact E].
      match goal with Hc: _ <> _ |- _ => apply Hc; reflexivity end. }
    subst k.
    assert (Hrd: 0 <= rd <= Zlength S) by (unfold fb_phase in H0; simpl in H0; tauto).
    repeat match goal with |- semax _ _ (Ssequence (Ssequence _ _) _) _ => apply -> seq_assoc end.
    forward_call (Zlength S0 - rd).
    forward. forward_call (Int.max_unsigned - Zlength lits - 1). Intros r19. forward.
    forward_call (if Int.eq (Int.repr fl) (Int.repr 6) then Int.zero else Int.one).
    { entailer!. simpl. unfold Int.notbool. destruct (Int.eq (Int.repr fl) (Int.repr 6)); reflexivity. }
    assert (Htr: fl <> Z_TREES).
    { intro E. rewrite E in *. match goal with Hc: _ <> Int.zero |- _ => apply Hc; reflexivity end. }
    assert (Hmn: 0 <= Z.min (Zlength S0 - rd) Int.max_unsigned <= Zlength S0 - rd /\
                 Z.min (Zlength S0 - rd) Int.max_unsigned <= Int.max_unsigned)
      by (pose proof (Z.le_min_l (Zlength S0 - rd) Int.max_unsigned);
          pose proof (Z.le_min_r (Zlength S0 - rd) Int.max_unsigned);
          pose proof (Z.min_glb (Zlength S0 - rd) Int.max_unsigned 0); rep_lia).
    rewrite Int.unsigned_repr by rep_lia. rewrite Int.signed_repr by rep_lia. rewrite !add64_repr.
    Exists (Z.min (Zlength S0 - rd) Int.max_unsigned) (Zlength lits + 1 + r19).
    entailer!. unfold fb_args; simpl. rewrite HS. repeat split; try lia; auto. }
  (* the common part: piece = copy_of(stream + read, take), out = malloc(room) *)
  Intros take room. clear u H2.
  match goal with Ha: fb_args _ _ _ _ _ _ _ |- _ => rename Ha into Har end.
  match goal with Ha: rd + take <= _ |- _ => rename Ha into Hrt end.
  set (data := sublist rd (rd + take) S).
  destruct (fb_phase_call S (Zlength lits) sp wb k z L rd wr ltac:(lia) Hk H0) as (Hsw & Hhd & Hrd & Hwr).
  assert (Hta: 0 <= take <= Int.max_unsigned /\ 0 <= room <= Int.max_unsigned).
  { pose proof Har as A'. unfold fb_args in A'. destruct A' as (_ & Hr & A). destruct (k =? 1).
    - pose proof (Z.le_min_r (Zlength S) Int.max_unsigned). lia.
    - destruct A as (-> & _). pose proof (Z.le_min_r (Zlength S - rd) Int.max_unsigned). lia. }
  assert (Hdl: Zlength data = take) by (unfold data; rewrite Zlength_sublist; lia).
  assert (Hdb: is_bytes data).
  { unfold data. apply Forall_sublist. apply fb_bytes_ok; auto. }
  fb_split_call.
  rewrite <- fb_bytes_a.
  forward_call (offset_val rd strp, Ews, strp, rd, Zlength S0, bytes_rep S, take, data, gv).
  { unfold cbuf_ok. repeat split; auto; try lia.
    unfold data, bytes_rep. rewrite sublist_map. reflexivity. }
  Intros piece.
  forward. fb_split_call.
  forward_call (tarray tuchar room, gv). { simpl. rep_lia. }
  Intros outp. rewrite !fb_bytes_a, !fb_tok_a. forward.
  (* if (piece == NULL || out == NULL) return 0 *)
  destruct (eq_dec piece nullval) as [NP|NP].
  { subst piece. fb_ifpostv _t'22 (Vint (Int.repr 1)); [forward; entailer! | fb_infeas | ].
    forward_if; [ | fb_infeas]. forward. Exists (Int.repr 0). sep_apply fb_a_frame. entailer!. }
  Intros. assert_PROP (isptr piece) as Ppiece by entailer!.
  destruct (eq_dec outp nullval) as [NO|NO].
  { subst outp. fb_ifpostv _t'22 (Vint (Int.repr 1)); [fb_infeas | forward; entailer! | ].
    forward_if; [ | fb_infeas]. forward. Exists (Int.repr 0). sep_apply fb_a_frame. entailer!. }
  Intros. assert_PROP (isptr outp) as Poutp by entailer!.
  fb_ifpostv _t'22 (Vint (Int.repr 0));
    [fb_infeas | forward; entailer!; destruct outp; try contradiction; reflexivity | ].
  forward_if; [fb_infeas | ].
  (* offer(&strm, piece, take, out, room) *)
  sep_apply (fb_istreamA_zs gv vs z Vundef L). Intros.
  assert (HLz: live_ok L) by assumption. assert (Zo: zf_ok z) by assumption.
  forward_call (vs, Tsh, piece, take, outp, room, zf_ni z, Vint (Int.repr (zf_ai z)), Vlong (Int64.repr (zf_tin z)),
                zf_no z, Vint (Int.repr (zf_ao z)), Vlong (Int64.repr (zf_tout z)), msg_val gv (zf_msg z), l_sp L,
                gv Zlib.inflate.code._zcalloc, gv Zlib.inflate.code._zcfree, nullval, Vint (Int.repr (zf_dt z)),
                adler_v (raw_live (Some L)) z Vundef, zf_res z).
  sep_apply (fb_offer_fold gv vs z Vundef L piece take data outp room); auto; try lia. Intros.
  sep_apply (fb_bufs_pre vs L piece take data outp room); auto; try lia.
  (* code = inflate(&strm, flush) *)
  assert (INOK: in_ok (fb_ib piece take data) data) by (apply fb_in_ok; auto; rep_lia).
  assert (OUTOK: out_ok (fb_ob outp room) room) by (apply fb_out_ok; auto; rep_lia).
  forward_call (gv, Tsh, vs, offer_z z (in_ptr (fb_ib piece take data) 0) take (out_ptr (fb_ob outp room) 0) room,
                Vundef, Some L, fb_ib piece take data, data, Some (fb_ob outp room), fl, Ers, Ers, true, true).
  { pose proof INOK as I'. pose proof OUTOK as O'. unfold in_ok, fb_ib in I'. unfold out_ok, fb_ob in O'.
    decompose [and] I'. decompose [and] O'. repeat split; auto; try discriminate; simpl; try lia. }
  Intros vret. destruct vret as [[[r z'] st'] ow]. simpl fst in *; simpl snd in *.
  match goal with H: inflate_rel _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H into REL end.
  match goal with H: match st' with Some _ => _ | None => _ end |- _ => rename H into Hsw' end.
  (* if (code == Z_MEM_ERROR) return 0 *)
  forward_if.
  { forward. Exists (Int.repr 0). sep_apply fb_a_frame_opt. entailer!. }
  assert (Hr: r <> Z_MEM_ERROR) by (intro E; subst r; contradiction).
  destruct (fb_step S0 fin lits lc lx dc extra sp wb k z L rd wr take room fl vs piece outp r z' st' ow
              TH OK Hwb HS Hk H0 Har ltac:(lia) H4 Hrt Zo HLz Pvs REL Hr)
    as (L' & n & Est & Hn' & Hai & Hao & Hd & Hw & How & Hph).
  subst st'. specialize (Hph Hsw').
  rewrite fb_istreamA_opt_ptr by auto.
  (* read += take - strm.avail_in; written += room - strm.avail_out *)
  rewrite (fb_istreamA_unfold gv Tsh vs z' Vundef L'). Intros.
  forward. forward. forward. forward.
  assert (Zo': zf_ok z') by assumption. pose proof Zo' as Zo2. unfold zf_ok in Zo2.
  rewrite (fb_read_step rd take (zf_ai z')) by rep_lia. rewrite (fb_read_step wr room (zf_ao z')) by rep_lia.
  replace (rd + (take - zf_ai z')) with (rd + n) by lia.
  replace (wr + (room - zf_ao z')) with (wr + Zlength ow) by lia.
  sep_apply (fb_istreamA_fold gv Tsh vs z' Vundef L'); auto.
  (* if (call == 2) gp_assert(code == Z_DATA_ERROR) *)
  match goal with |- semax _ ?Pre (Ssequence (Sifthenelse _ _ _) _) _ => forward_if Pre end.
  { pose proof (Hd ltac:(assumption)) as Er. subst r. forward_call Int.one. apply ENTAIL_refl. }
  { forward. apply ENTAIL_refl. }
  (* gp_assert(written <= literals) *)
  forward_call Int.one.
  { apply prop_right. simpl. unfold Int64.ltu. rewrite !Int64.unsigned_repr by rep_lia.
    rewrite zlt_false by lia. reflexivity. }
  Exists k. unfold fb_inv.
  Exists z' L' (rd + n) (wr + Zlength ow)
    (head_opt (is_live vs (Some L')) *
     bufs_opt (is_live vs (Some L)) (fb_ib piece take data) (Some (fb_ob outp room)) ow true true * G)%logic.
  entailer!. }
{ (* call++ *)
  Intros k. unfold fb_inv. Intros z L rd wr G. forward.
  Exists (k + 1). unfold fb_inv. Exists z L rd wr G. entailer!. }
(* return 0 *)
Intros k. unfold fb_inv. Intros z L rd wr G.
forward. Exists (Int.repr 0). sep_apply fb_a_frame. entailer!.
Qed.

(* the assertion after inflateInit2_ returned Z_OK rearranged as fb_seg_calls takes it (a lemma over abstract
   resources: the automatic cancellation compares the shares Ers / Ews and the compspecs of the items and is slow) *)
Lemma fb_perm_init P Q (A H V M Z B T C K D KL DL: mpred):
  PROPx P (LOCALx Q (SEPx [A; H; V; M; Z; B; T; C; K; D; KL; DL])) |--
  PROPx P (LOCALx Q (SEPx [A; B; M; Z; T; C; K; D; (V * H * KL * DL)%logic])).
Proof.
  apply andp_derives; [apply derives_refl | ]. apply andp_derives; [apply derives_refl | ].
  unfold SEPx. intro rho. simpl. cancel.
Qed.

(* Statements 23 and 24: new_stream(&strm), inflateInit2_(&strm, window_bits) (return 0 unless Z_OK) *)
Lemma fb_seg_init {Espec: OracleKind} gv vs vb strp lp wb S0 fin lits lc lx dc extra :
  fb_theory_stmt -> fb_ok S0 fin lits lc lx dc extra -> 0 <= wb <= 7 ->
  semax fb_Delta
    (PROP ()
     LOCAL (temp _window_bits (Vint (Int.repr (-8 - wb))); temp _literals (Vlong (Int64.repr (Zlength lits)));
            temp _stream_len (Vlong (Int64.repr (Zlength S0))); temp _stream strp;
            lvar _strm t_zsf vs; lvar _bit tulong vb; gvars gv)
     SEP (data_at_ Tsh t_zsf vs; data_at_ Tsh tulong vb; mem_mgr gv; zfuncs gv; R_fb gv;
          malloc_token Ews (tarray tuchar (Zlength S0)) strp;
          data_at Ews (tarray tuchar (Zlength S0)) (bytes_rep (fb_bytes S0 fin lits lc lx dc extra)) strp;
          malloc_token Ews (tarray tuchar (Zlength lits)) lp;
          data_at Ews (tarray tuchar (Zlength lits)) (bytes_rep lits) lp))
    (fb_from 23) fb_POST.
Proof.
  intros TH OK Hwb.
  unfold fb_from. cbv [fb_drop f_main fn_body]. unfold fb_Delta, fb_POST. simplify_func_tycontext. abbreviate_semax.
  assert (Hw: -15 <= -8 - wb <= -8) by lia.
  rewrite fb_strm_undef.
  forward_call (vs, Tsh, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef,
                Vundef, Vundef, Vundef, Vundef).
  rewrite (fb_ns_raw_eq gv vs).
  assert_PROP (isptr vs) as Pvs by entailer!.
  rewrite fb_R_unfold. flatten_sepcon_in_SEP.
  assert_PROP (isptr (gv ___stringlit_rj_far_back_1)) as Pver by entailer!.
  forward_call (gv, Tsh, vs, fb_ns_raw, Vundef, Vundef, nullval, -8 - wb, gv ___stringlit_rj_far_back_1, Ers,
                fb_hv, 49, 112).
  { rewrite if_false by (intro; subst; contradiction). cancel. }
  { change (Zlength fb_hv) with 6; repeat split; auto; rep_lia. }
  Intros vret. destruct vret as [alloc_ok sp]. simpl fst in *; simpl snd in *.
  assert (Ewb: wbits_ok (-8 - wb) = true).
  { unfold wbits_ok, reset2_wb.
    destruct (-8 - wb <? 0) eqn:E; [ | apply Z.ltb_ge in E; lia].
    destruct (-8 - wb <? -15) eqn:E1; [apply Z.ltb_lt in E1; lia | ].
    destruct (8 <=? - (-8 - wb)) eqn:E2, (- (-8 - wb) <=? 15) eqn:E3; rewrite ?Z.leb_le, ?Z.leb_gt in *;
      try lia; reflexivity. }
  assert (Eret: init_ret vs 49 112 (-8 - wb) alloc_ok = if alloc_ok then Z_OK else Z_MEM_ERROR).
  { unfold init_ret. simpl. rewrite if_false by (intro; subst; contradiction).
    destruct alloc_ok; simpl; rewrite ?Ewb; reflexivity. }
  rewrite Eret.
  destruct alloc_ok; unfold init_mem; rewrite if_false by (intro; subst; contradiction); simpl Z.eqb; cbv iota.
  2: { forward_if; [ | discriminate ].
       forward. Exists (Int.repr 0). entailer!. sep_apply fb_raw_frame. cancel. }
  forward_if; [ discriminate | ].
  assert_PROP (live_ok (init_live sp (-8 - wb))) as HL by (unfold istream_raw; entailer!).
  sep_apply (fb_init_istreamA gv Tsh vs sp (-8 - wb) Hw).
  drop_LOCAL 0%nat. drop_LOCAL 0%nat.
  eapply semax_pre; [ | apply (fb_seg_calls gv vs vb strp sp wb S0 fin lits lc lx dc extra
     (version_lit gv * @data_at Zlib.units.Inflate.CS Ers (tarray tschar (Zlength fb_hv)) fb_hv
        (gv ___stringlit_rj_far_back_1) * malloc_token Ews (tarray tuchar (Zlength lits)) lp *
      data_at Ews (tarray tuchar (Zlength lits)) (bytes_rep lits) lp)%logic TH OK Hwb HL) ].
  apply andp_left2. apply fb_perm_init.
Qed.

(* the bit position, a size_t object, at the bit writer's compspecs *)
Lemma fb_ulong_a sh v q: @data_at Zlib.units.Adler32.CS sh tulong v q = @data_at FB.CS sh tulong v q.
Proof. fb_cs_tac FB.CC_adler32. Qed.

(* [Q] without the binding of the temporary [t] *)
Ltac fb_rm_temp t Q :=
  lazymatch Q with
  | temp t _ :: ?Q' => Q'
  | ?a :: ?Q' => let r := fb_rm_temp t Q' in constr:(a :: r)
  | nil => constr:(@nil localdef)
  end.

(* the assertion after the writes rearranged as fb_seg_init takes it, the bit position given back as data_at_ (a
   lemma over abstract resources: the automatic cancellation is slow on main's resources) *)
Lemma fb_perm_writes P Q (DS B B' A M Z R TS TL DL: mpred): B |-- B' ->
  PROPx P (LOCALx Q (SEPx [DS; B; A; M; Z; R; TS; TL; DL])) |--
  PROPx P (LOCALx Q (SEPx [A; B'; M; Z; R; TS; DS; TL; DL])).
Proof.
  intros HB. apply andp_derives; [apply derives_refl | ]. apply andp_derives; [apply derives_refl | ].
  unfold SEPx. intro rho. simpl. sep_apply HB. cancel.
Qed.

(* Statements 13 to 22: bit = 0 and the writes (BFINAL = nondet_u8() & 1, BTYPE 01, the literals, the
   length code, its extra bits lx = nondet_u32(), the distance code, its extra bits): the stream holds
   fb_bytes S0 fin lits lc lx dc extra *)
Lemma fb_seg_writes {Espec: OracleKind} gv vs vb strp lp wb S0 lits lc dc extra :
  fb_theory_stmt -> fb_inputs wb S0 lits lc dc extra ->
  semax fb_Delta
    (PROP ()
     LOCAL (temp _window_bits (Vint (Int.repr (-8 - wb))); temp _literals (Vlong (Int64.repr (Zlength lits)));
            temp _length_code (Vint (Int.repr lc)); temp _distance_code (Vint (Int.repr dc));
            temp _extra (Vint (Int.repr extra)); temp _distance_bits (Vint (Int.repr (fb_dbits dc)));
            temp _stream_len (Vlong (Int64.repr (Zlength S0))); temp _stream strp; temp _literal lp;
            lvar _strm t_zsf vs; lvar _bit tulong vb; gvars gv)
     SEP (data_at_ Tsh t_zsf vs; data_at_ Tsh tulong vb; mem_mgr gv; zfuncs gv; R_fb gv;
          malloc_token Ews (tarray tuchar (Zlength S0)) strp;
          data_at Ews (tarray tuchar (Zlength S0)) (bytes_rep S0) strp;
          malloc_token Ews (tarray tuchar (Zlength lits)) lp;
          data_at Ews (tarray tuchar (Zlength lits)) (bytes_rep lits) lp))
    (fb_from 13) fb_POST.
Proof.
  intros TH IN.
  unfold fb_from. cbv [fb_drop f_main fn_body]. unfold fb_Delta, fb_POST. simplify_func_tycontext. abbreviate_semax.
  destruct IN as (Hwb & Blits & Llits & Hlc & Hdc & Hex & Hdist & BS0 & LS0).
  (* bit = 0; put_bits(stream, &bit, nondet_u8() & 1, 1, 0); *)
  forward. forward_call tt. Intros u.
  set (fin := Z.land u 1).
  assert (Hfin: 0 <= fin <= 1).
  { assert (E: Z.land u 1 = u mod 2) by (apply (Z.land_ones u 1); lia).
    unfold fin. rewrite E. pose proof (Z.mod_pos_bound u 2 ltac:(lia)). lia. }
  pose proof (lits_len_bounds lits) as Bl.
  pose proof (Zlength_nonneg lits) as Nl.
  rewrite Int.signed_repr by rep_lia.
  rewrite <- (fb_bytes_a Ews (Zlength S0) (bytes_rep S0) strp), <- (fb_ulong_a Tsh _ vb).
  forward_call (Ews, strp, Tsh, vb, S0, 0, fin, 1, 0).
  destruct (put_bits_m_ok S0 0 fin 1 0 BS0 ltac:(lia) ltac:(lia) ltac:(lia)) as [L1 B1].
  set (S1 := put_bits_m S0 0 fin 1 0) in *.
  (* put_bits(stream, &bit, 1, 2, 0); *)
  rewrite <- L1.
  forward_call (Ews, strp, Tsh, vb, S1, 0 + 1, 1, 2, 0).
  rewrite L1, fb_bytes_a, fb_ulong_a. change (0 + 1 + 2) with 3. change (0 + 1) with 1.
  destruct (put_bits_m_ok S1 1 1 2 0 B1 ltac:(lia) ltac:(lia) ltac:(lia)) as [L2 B2].
  set (S2 := put_bits_m S1 1 1 2 0) in *.
  (* for (i = 0; i < literals; i++) put_literal(stream, &bit, literal[i]); *)
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx (_ :: _ :: ?R)))) _ _ =>
    forward_for_simple_bound (Zlength lits)
      (EX i: Z, PROPx P (LOCALx Q (SEPx (
         data_at Ews (tarray tuchar (Zlength S0)) (bytes_rep (put_lits S2 3 (sublist 0 i lits))) strp ::
         data_at Tsh tulong (Vlong (Int64.repr (3 + lits_len (sublist 0 i lits)))) vb :: R))))
  end.
  { entailer!. }
  { assert (Hli: 0 <= Znth i lits <= 255) by (apply (is_bytes_Znth lits); auto; lia).
    forward; [entailer!; rewrite Znth_bytes_rep by lia; simpl; rewrite Int.unsigned_repr by rep_lia; rep_lia | ].
    rewrite Znth_bytes_rep by lia.
    set (Si := put_lits S2 3 (sublist 0 i lits)).
    pose proof (lits_len_bounds (sublist 0 i lits)) as Bi.
    pose proof (lits_len_bounds (sublist 0 (i + 1) lits)) as Bi1.
    rewrite !Zlength_sublist in Bi, Bi1 by lia.
    destruct (put_lits_snoc (sublist 0 i lits) (Znth i lits) S2 3) as [E1 E2].
    rewrite <- sublist_last_1 in E1, E2 by lia.
    destruct (put_lits_ok (sublist 0 i lits) S2 3 B2 ltac:(lia) ltac:(lia)) as [LSi BSi].
    fold Si in LSi, BSi, E1.
    rewrite <- L1, <- L2, <- LSi.
    rewrite <- (fb_bytes_a Ews (Zlength Si) (bytes_rep Si) strp), <- (fb_ulong_a Tsh _ vb).
    forward_call (Ews, strp, Tsh, vb, Si, 3 + lits_len (sublist 0 i lits), Znth i lits).
    rewrite fb_bytes_a, fb_ulong_a.
    entailer!. rewrite E1, E2, Z.add_assoc, LSi, L2, L1. cancel. }
  rewrite sublist_same by lia.
  Intros.
  destruct (put_lits_ok lits S2 3 B2 ltac:(lia) ltac:(lia)) as [L3 B3].
  set (S3 := put_lits S2 3 lits) in *.
  set (b := 3 + lits_len lits) in *.
  (* the length code: 7 bits from 0000000 for 256..279, 8 bits from 11000000 for 280..287 *)
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx (_ :: _ :: ?R)))) _ _ =>
    forward_if (PROPx P (LOCALx Q (SEPx (
         data_at Ews (tarray tuchar (Zlength S0))
           (bytes_rep (if lc <? 280 then put_bits_m S3 b (lc - 256) 7 1 else put_bits_m S3 b (192 + lc - 280) 8 1))
           strp ::
         data_at Tsh tulong (Vlong (Int64.repr (b + (if lc <? 280 then 7 else 8)))) vb :: R))))
  end.
  { rewrite <- L1, <- L2, <- L3.
    rewrite <- (fb_bytes_a Ews (Zlength S3) (bytes_rep S3) strp), <- (fb_ulong_a Tsh _ vb).
    forward_call (Ews, strp, Tsh, vb, S3, b, lc - 256, 7, 1).
    rewrite fb_bytes_a, fb_ulong_a.
    entailer!. destruct (Z.ltb_spec lc 280); [ | lia]. rewrite L3, L2, L1. cancel. }
  { rewrite <- L1, <- L2, <- L3.
    rewrite <- (fb_bytes_a Ews (Zlength S3) (bytes_rep S3) strp), <- (fb_ulong_a Tsh _ vb).
    forward_call (Ews, strp, Tsh, vb, S3, b, 192 + lc - 280, 8, 1).
    rewrite fb_bytes_a, fb_ulong_a.
    entailer!. destruct (Z.ltb_spec lc 280); [lia | ]. rewrite L3, L2, L1. cancel. }
  (* length_bits = 0; if (length_code >= 265 && length_code <= 284) length_bits = (length_code - 261) / 4; *)
  forward.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _t'11 (Vint (Int.repr (if andb (265 <=? lc) (lc <=? 284) then 1 else 0)))
                                   :: Q) (SEPx R)))
  end.
  { forward. entailer!. unfold bool2val.
    destruct (Z.leb_spec 265 lc), (Z.leb_spec lc 284), (zlt 284 lc); simpl; try lia; reflexivity. }
  { forward. entailer!. destruct (Z.leb_spec 265 lc); [lia | reflexivity]. }
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    let Q' := fb_rm_temp _length_bits Q in
    forward_if (PROPx P (LOCALx (temp _length_bits (Vint (Int.repr (fb_lbits lc))) :: Q') (SEPx R)))
  end.
  { forward. entailer!. unfold fb_lbits.
    destruct (Z.leb_spec 265 lc), (Z.leb_spec lc 284); simpl in *; try contradiction.
    unfold Int.divu. rewrite !Int.unsigned_repr by rep_lia. reflexivity. }
  { forward. entailer!. unfold fb_lbits.
    destruct ((265 <=? lc) && (lc <=? 284))%bool; [discriminate | reflexivity]. }
  assert (Hlb: 0 <= fb_lbits lc <= 5).
  { unfold fb_lbits. destruct (Z.leb_spec 265 lc), (Z.leb_spec lc 284); cbn [andb]; try lia.
    assert ((lc - 261) / 4 < 6) by (apply Z.div_lt_upper_bound; lia).
    assert (0 <= (lc - 261) / 4) by (apply Z.div_pos; lia). lia. }
  assert (Hdb: 0 <= fb_dbits dc <= 13).
  { unfold fb_dbits. destruct (Z.leb_spec 4 dc); try lia.
    assert (dc / 2 < 15) by (apply Z.div_lt_upper_bound; lia).
    assert (2 <= dc / 2) by (apply Z.div_le_lower_bound; lia). lia. }
  set (b4 := b + (if lc <? 280 then 7 else 8)).
  set (S4 := if lc <? 280 then put_bits_m S3 b (lc - 256) 7 1 else put_bits_m S3 b (192 + lc - 280) 8 1).
  assert (Hb4: b + 7 <= b4 <= b + 8) by (unfold b4; destruct (lc <? 280); lia).
  assert (L4B4: Zlength S4 = Zlength S3 /\ is_bytes S4)
    by (unfold S4; destruct (lc <? 280); apply put_bits_m_ok; auto; lia).
  destruct L4B4 as [L4 B4].
  (* put_bits(stream, &bit, nondet_u32(), length_bits, 0); *)
  forward_call tt. Intros lx.
  rewrite <- L1, <- L2, <- L3, <- L4.
  rewrite <- (fb_bytes_a Ews (Zlength S4) (bytes_rep S4) strp), <- (fb_ulong_a Tsh _ vb).
  forward_call (Ews, strp, Tsh, vb, S4, b4, lx, fb_lbits lc, 0).
  rewrite fb_bytes_a, fb_ulong_a.
  set (S5 := put_bits_m S4 b4 lx (fb_lbits lc) 0).
  destruct (put_bits_m_ok S4 b4 lx (fb_lbits lc) 0 B4 ltac:(lia) ltac:(lia) ltac:(lia)) as [L5 B5].
  fold S5 in L5, B5.
  (* put_bits(stream, &bit, distance_code, 5, 1); *)
  rewrite <- L5.
  rewrite <- (fb_bytes_a Ews (Zlength S5) (bytes_rep S5) strp), <- (fb_ulong_a Tsh _ vb).
  forward_call (Ews, strp, Tsh, vb, S5, b4 + fb_lbits lc, dc, 5, 1).
  rewrite fb_bytes_a, fb_ulong_a.
  set (S6 := put_bits_m S5 (b4 + fb_lbits lc) dc 5 1).
  destruct (put_bits_m_ok S5 (b4 + fb_lbits lc) dc 5 1 B5 ltac:(lia) ltac:(lia) ltac:(lia)) as [L6 B6].
  fold S6 in L6, B6.
  (* put_bits(stream, &bit, extra, distance_bits, 0); *)
  rewrite <- L6.
  rewrite <- (fb_bytes_a Ews (Zlength S6) (bytes_rep S6) strp), <- (fb_ulong_a Tsh _ vb).
  forward_call (Ews, strp, Tsh, vb, S6, b4 + fb_lbits lc + 5, extra, fb_dbits dc, 0).
  rewrite fb_bytes_a, fb_ulong_a.
  rewrite L6, L5, L4, L3, L2, L1.
  (* the stream holds fb_bytes: on to statement 23 *)
  change (put_bits_m S6 (b4 + fb_lbits lc + 5) extra (fb_dbits dc) 0)
    with (fb_bytes S0 fin lits lc lx dc extra).
  assert (OK: fb_ok S0 fin lits lc lx dc extra) by (unfold fb_ok; repeat split; auto; lia).
  clearbody S1 S2 S3 S4 S5 S6.
  drop_LOCAL 0%nat. drop_LOCAL 0%nat. drop_LOCAL 0%nat. drop_LOCAL 0%nat. drop_LOCAL 0%nat.
  drop_LOCAL 2%nat. drop_LOCAL 2%nat. drop_LOCAL 2%nat. drop_LOCAL 2%nat. drop_LOCAL 4%nat.
  eapply semax_pre; [ | apply (fb_seg_init gv vs vb strp lp wb S0 fin lits lc lx dc extra TH OK Hwb) ].
  apply andp_left2. apply fb_perm_writes. apply data_at_data_at_.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The distance computation of main in 32-bit unsigned arithmetic is FBFacts.fb_dist               *)

Lemma fb_dbits_range dc: 4 <= dc <= 29 -> 1 <= fb_dbits dc <= 13.
Proof.
  intros H. unfold fb_dbits. rewrite (proj2 (Z.leb_le 4 dc)) by lia.
  pose proof (Z.div_le_mono 4 dc 2). pose proof (Z.div_le_mono dc 29 2).
  change (4 / 2) with 2 in *. change (29 / 2) with 14 in *. lia.
Qed.

Lemma fb_dbits_int dc: 4 <= dc <= 29 ->
  Int.sub (Int.divu (Int.repr dc) (Int.repr 2)) (Int.repr 1) = Int.repr (fb_dbits dc).
Proof.
  intros H. unfold Int.divu. rewrite !Int.unsigned_repr by rep_lia. rewrite sub_repr.
  unfold fb_dbits. rewrite (proj2 (Z.leb_le 4 dc)) by lia. reflexivity.
Qed.

Lemma fb_shl_repr a k: 0 <= a <= Int.max_unsigned -> 0 <= k <= Int.max_unsigned ->
  Int.shl (Int.repr a) (Int.repr k) = Int.repr (Z.shiftl a k).
Proof. intros. unfold Int.shl. rewrite !Int.unsigned_repr by lia. reflexivity. Qed.

Lemma fb_dist_range dc extra: 0 <= dc <= 29 -> 0 <= extra -> 1 <= fb_dist dc extra <= 32768.
Proof.
  intros Hd He. unfold fb_dist. destruct (Z.leb_spec 4 dc); [ | lia].
  pose proof (fb_dbits_range dc ltac:(lia)) as Hk. set (k := fb_dbits dc) in *.
  assert (Hl: Z.land dc 1 = 0 \/ Z.land dc 1 = 1).
  { change (Z.land dc 1) with (Z.land dc (Z.ones 1)). rewrite Z.land_ones by lia.
    pose proof (Z.mod_pos_bound dc (2 ^ 1) ltac:(reflexivity)). simpl in *. lia. }
  assert (Ho: 2 <= Z.lor 2 (Z.land dc 1) <= 3) by (destruct Hl as [E|E]; rewrite E; simpl; lia).
  assert (Hp: 2 <= 2 ^ k <= 2 ^ 13) by (split; [change 2 with (2 ^ 1) at 1 | ]; apply Z.pow_le_mono_r; lia).
  assert (Hm: 0 <= Z.land extra (2 ^ k - 1) < 2 ^ k).
  { replace (2 ^ k - 1) with (Z.ones k) by (rewrite Z.ones_equiv; lia). rewrite Z.land_ones by lia.
    apply Z.mod_pos_bound; lia. }
  rewrite Z.shiftl_mul_pow2 by lia.
  assert (Z.lor 2 (Z.land dc 1) * 2 ^ k <= 3 * 2 ^ 13) by (apply Z.mul_le_mono_nonneg; lia).
  change (2 ^ 13) with 8192 in *.
  (* the largest distance code 29 has 13 extra bits: (3 << 13) + 1 + 8191 = 32768 *)
  assert (Z.lor 2 (Z.land dc 1) * 2 ^ k + 2 ^ k <= 32768).
  { destruct (Z.eq_dec k 13).
    - rewrite e. change (2 ^ 13) with 8192. lia.
    - assert (2 ^ k <= 2 ^ 12) by (apply Z.pow_le_mono_r; lia). change (2 ^ 12) with 4096 in *.
      assert (Z.lor 2 (Z.land dc 1) * 2 ^ k <= 3 * 4096) by (apply Z.mul_le_mono_nonneg; lia). lia. }
  lia.
Qed.

Lemma fb_dist_int dc extra: 4 <= dc <= 29 -> 0 <= extra <= Int.max_unsigned ->
  Int.unsigned (Int.add (Int.add (Int.shl (Int.or (Int.repr 2) (Int.and (Int.repr dc) (Int.repr 1)))
                                          (Int.repr (fb_dbits dc))) (Int.repr 1))
                        (Int.and (Int.repr extra)
                                 (Int.sub (Int.shl (Int.repr 1) (Int.repr (fb_dbits dc))) (Int.repr 1)))) =
  fb_dist dc extra.
Proof.
  intros Hd He. pose proof (fb_dbits_range dc Hd) as Hk. set (k := fb_dbits dc) in *.
  assert (Hl: Z.land dc 1 = 0 \/ Z.land dc 1 = 1).
  { change (Z.land dc 1) with (Z.land dc (Z.ones 1)). rewrite Z.land_ones by lia.
    pose proof (Z.mod_pos_bound dc (2 ^ 1) ltac:(reflexivity)). simpl in *. lia. }
  assert (Ho: 2 <= Z.lor 2 (Z.land dc 1) <= 3) by (destruct Hl as [E|E]; rewrite E; simpl; lia).
  assert (Hp: 2 <= 2 ^ k <= 2 ^ 13) by (split; [change 2 with (2 ^ 1) at 1 | ]; apply Z.pow_le_mono_r; lia).
  assert (Hm: 0 <= Z.land extra (2 ^ k - 1) < 2 ^ k).
  { replace (2 ^ k - 1) with (Z.ones k) by (rewrite Z.ones_equiv; lia). rewrite Z.land_ones by lia.
    apply Z.mod_pos_bound; lia. }
  assert (Hs: Z.shiftl (Z.lor 2 (Z.land dc 1)) k = Z.lor 2 (Z.land dc 1) * 2 ^ k) by (apply Z.shiftl_mul_pow2; lia).
  rewrite and_repr, or_repr, !fb_shl_repr by rep_lia.
  rewrite Z.shiftl_1_l, sub_repr, and_repr, !add_repr.
  assert (Z.lor 2 (Z.land dc 1) * 2 ^ k <= 3 * 2 ^ 13) by (apply Z.mul_le_mono_nonneg; lia).
  change (2 ^ 13) with 8192 in *.
  rewrite Int.unsigned_repr by (rewrite Hs; rep_lia).
  unfold fb_dist. rewrite (proj2 (Z.leb_le 4 dc)) by lia. fold k. reflexivity.
Qed.

Lemma fb_body_main : fb_theory_stmt ->
  @semax_body (QPvarspecs FB.p) Gmain_fb FB.CS Zlib.harness.rj_far_back.code.f_main
    (Zlib.harness.rj_far_back.code._main, main_core_spec R_fb).
Proof.
  intros TH.
  start_function.
  make_func_ptr Zlib.inflate.code._zcalloc. make_func_ptr Zlib.inflate.code._zcfree.
  gather_SEP (func_ptr' _ (gv Zlib.inflate.code._zcalloc)) (func_ptr' _ (gv Zlib.inflate.code._zcfree)).
  fold (zfuncs gv).
  forward_call 7. Intros wb.
  forward.
  { entailer!. rewrite Int64.Z_mod_modulus_eq, Z.mod_small, Int.signed_repr by rep_lia. rep_lia. }
  forward_call 32767. Intros n.
  forward_call 28. Intros lcv.
  forward.
  fb_split_call.
  forward_call 29. Intros dc.
  forward.
  forward_call tt. Intros extra.
  forward. forward.
  match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx ?R))) _ _ =>
    apply semax_pre with
      (PROP () LOCAL (temp _distance (Vlong (Int64.repr (dc + 1))); temp _distance_bits (Vint (Int.repr 0));
         temp _extra (Vint (Int.repr extra)); temp _distance_code (Vint (Int.repr dc));
         temp _length_code (Vint (Int.repr (257 + lcv))); temp _literals (Vlong (Int64.repr n));
         temp _window_bits (Vint (Int.repr (-8 - wb)));
         lvar _strm (Tstruct _z_stream_s noattr) v_strm; lvar _bit tulong v_bit; gvars gv) (SEPx R));
    [ | forward_if (PROP () LOCAL (temp _distance (Vlong (Int64.repr (fb_dist dc extra)));
         temp _distance_bits (Vint (Int.repr (fb_dbits dc)));
         temp _extra (Vint (Int.repr extra)); temp _distance_code (Vint (Int.repr dc));
         temp _length_code (Vint (Int.repr (257 + lcv))); temp _literals (Vlong (Int64.repr n));
         temp _window_bits (Vint (Int.repr (-8 - wb)));
         lvar _strm (Tstruct _z_stream_s noattr) v_strm; lvar _bit tulong v_bit; gvars gv) (SEPx R)) ] end.
  { entailer!. }
  { assert (Hd: 4 <= dc <= 29) by lia.
    pose proof (Z.div_le_mono 4 dc 2 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_mono dc 29 2 ltac:(lia) ltac:(lia)).
    change (4 / 2) with 2 in *. change (29 / 2) with 14 in *.
    forward. forward.
    { entailer!. change (Int.unsigned Int.iwordsize) with 32. lia. }
    rewrite (fb_dbits_int dc Hd), (fb_dist_int dc extra Hd) by lia. apply ENTAIL_refl. }
  { forward. entailer!.
    unfold fb_dist, fb_dbits. rewrite (proj2 (Z.leb_gt 4 dc)) by lia. auto. }
  pose proof (fb_dist_range dc extra ltac:(lia) ltac:(lia)) as Hdist.
  forward_call (Int.repr (if n <? fb_dist dc extra then 1 else 0)).
  { entailer!. unfold Int64.ltu. rewrite !Int64.unsigned_repr by rep_lia.
    destruct (zlt n (fb_dist dc extra)), (Z.ltb_spec n (fb_dist dc extra)); try lia; reflexivity. }
  match goal with H: Int.repr (if _ then _ else _) <> Int.zero |- _ => rename H into Hgt end.
  assert (Hlt: n < fb_dist dc extra).
  { destruct (Z.ltb_spec n (fb_dist dc extra)); auto. exfalso; apply Hgt; reflexivity. }
  clear Hgt.
  forward_call (Int64.max_signed - 6 - 2 * n). Intros t6.
  forward.
  fb_split_call.
  forward_call (6 + 2 * n + t6, gv).
  Intros vret. destruct vret as [strp S0]. simpl fst in *; simpl snd in *.
  forward.
  fb_split_call.
  forward_call (n, gv).
  Intros vret. destruct vret as [lp lits]. simpl fst in *; simpl snd in *.
  forward.
  rewrite !fb_bytes_a, !fb_tok_a.
  destruct (eq_dec strp nullval) as [N1|N1].
  { subst strp. fb_ifpostv _t'9 (Vint (Int.repr 1)); [forward; entailer! | exfalso; auto | ].
    forward_if; [ | discriminate]. forward. Exists (Int.repr 0). entailer!. }
  Intros. assert_PROP (isptr strp) as Pstrp by entailer!.
  destruct (eq_dec lp nullval) as [N2|N2].
  { subst lp. fb_ifpostv _t'9 (Vint (Int.repr 1)); [clear TH; exfalso; first [congruence | auto] | forward; entailer! | ].
    forward_if; [ | discriminate]. forward. Exists (Int.repr 0). entailer!. }
  Intros. assert_PROP (isptr lp) as Plp by entailer!.
  fb_ifpostv _t'9 (Vint (Int.repr 0)); [clear TH; exfalso; first [congruence | auto] | forward; entailer!; destruct lp; try (exfalso; exact Plp); reflexivity | ].
  forward_if; [exfalso; match goal with H: Int.repr 0 <> Int.zero |- _ => apply H; reflexivity end | ].
  subst n. rewrite <- H5.
  assert (Esl: Int64.add (Int64.add (Int64.repr (Int.signed (Int.repr 6)))
                 (Int64.mul (Int64.repr (Int.signed (Int.repr 2))) (Int64.repr (Zlength lits)))) (Int64.repr t6) =
               Int64.repr (Zlength S0)).
  { rewrite H5, !Int.signed_repr by rep_lia. rewrite mul64_repr, !add64_repr. f_equal; lia. }
  rewrite Esl.
  eapply semax_pre; [ | apply (fb_seg_writes gv v_strm v_bit strp lp wb S0 lits (257 + lcv) dc extra TH) ].
  2: { unfold fb_inputs. repeat split; auto; try lia. }
  entailer!.
Qed.
