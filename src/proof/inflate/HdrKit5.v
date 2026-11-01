(* A view of loop_state for the gzip header cases (FLAGS, TIME, OS, ...) in Delta_cases5: the state fields
   mode, wrap, flags, check, head apart (state_rep_h: the 30 others), the head part, the stream, the crc
   table and the stack variables as separate SEP items, the rest of the memory one opaque item (mem_rep_h,
   unchanged by the updates of these cases).  And INITBITS(). *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Export Zlib.proof.inflate.ModeKit5.
Require Import Zlib.proof.crc32.Spec.

#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Definition state_rep_h (gv: globals) (sp strmp winp: val) (s: istate) : mpred :=
  field_at Ews t_state (DOT _strm) strmp sp *
  field_at Ews t_state (DOT _last) (zv (i_last s)) sp *
  field_at Ews t_state (DOT _havedict) (zv (i_havedict s)) sp *
  field_at Ews t_state (DOT _dmax) (zv (i_dmax s)) sp *
  field_at Ews t_state (DOT _total) (lv (i_total s)) sp *
  field_at Ews t_state (DOT _wbits) (zv (i_wbits s)) sp *
  field_at Ews t_state (DOT _wsize) (zv (i_wsize s)) sp *
  field_at Ews t_state (DOT _whave) (zv (i_whave s)) sp *
  field_at Ews t_state (DOT _wnext) (zv (i_wnext s)) sp *
  field_at Ews t_state (DOT _window) (if i_win s then winp else nullval) sp *
  field_at Ews t_state (DOT _hold) (lv (i_hold s)) sp *
  field_at Ews t_state (DOT _bits) (zv (i_bits s)) sp *
  field_at Ews t_state (DOT _length) (zv (i_length s)) sp *
  field_at Ews t_state (DOT _offset) (zv (i_offset s)) sp *
  field_at Ews t_state (DOT _extra) (zv (i_extra s)) sp *
  field_at Ews t_state (DOT _lencode) (tref_val gv sp (i_lencode s)) sp *
  field_at Ews t_state (DOT _distcode) (tref_val gv sp (i_distcode s)) sp *
  field_at Ews t_state (DOT _lenbits) (zv (i_lenbits s)) sp *
  field_at Ews t_state (DOT _distbits) (zv (i_distbits s)) sp *
  field_at Ews t_state (DOT _ncode) (zv (i_ncode s)) sp *
  field_at Ews t_state (DOT _nlen) (zv (i_nlen s)) sp *
  field_at Ews t_state (DOT _ndist) (zv (i_ndist s)) sp *
  field_at Ews t_state (DOT _have) (zv (i_have s)) sp *
  field_at Ews t_state (DOT _next) (codes_at sp (i_next s)) sp *
  field_at Ews t_state (DOT _lens) (map (fun z => Vint (Int.repr z)) (i_lens s)) sp *
  field_at_ Ews t_state (DOT _work) sp *
  field_at Ews t_state (DOT _codes) (map ent (i_codes s)) sp *
  field_at Ews t_state (DOT _sane) (zv (i_sane s)) sp *
  field_at Ews t_state (DOT _back) (zv (i_back s)) sp *
  field_at Ews t_state (DOT _was) (zv (i_was s)) sp.

(* the conjuncts 2, 4, 6, 8, 10 of 35 to the front (on variables: a cheap proof term) *)
Lemma sepcon_h_35: forall a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35: mpred,
  a1 * a2 * a3 * a4 * a5 * a6 * a7 * a8 * a9 * a10 * a11 * a12 * a13 * a14 * a15 * a16 * a17 * a18 * a19 * a20 * a21 * a22 * a23 * a24 * a25 * a26 * a27 * a28 * a29 * a30 * a31 * a32 * a33 * a34 * a35 =
  a2 * a4 * a6 * a8 * a10 * (a1 * a3 * a5 * a7 * a9 * a11 * a12 * a13 * a14 * a15 * a16 * a17 * a18 * a19 * a20 * a21 * a22 * a23 * a24 * a25 * a26 * a27 * a28 * a29 * a30 * a31 * a32 * a33 * a34 * a35).
Proof. intros. apply pred_ext; cancel. Qed.

Lemma state_rep_hsplit: forall gv sp strmp headp winp s,
  state_rep gv sp strmp headp winp s =
  field_at Ews t_state (DOT _mode) (zv (i_mode s)) sp *
  field_at Ews t_state (DOT _wrap) (zv (i_wrap s)) sp *
  field_at Ews t_state (DOT _flags) (zv (i_flags s)) sp *
  field_at Ews t_state (DOT _check) (lv (i_check s)) sp *
  field_at Ews t_state (DOT _head) (if i_head s then headp else nullval) sp *
  state_rep_h gv sp strmp winp s.
Proof. intros. unfold state_rep, state_rep_h. apply sepcon_h_35. Qed.

(* the memory but the five fields, the head part, the stream and the crc table *)
Definition mem_rep_h (F: frame) (m: mst) : mpred :=
  state_rep_h (f_gv F) (f_sp F) (f_strmp F) (f_winp F) (m_s m) *
  win_rep (f_winp F) (m_s m) *
  in_rep (f_ib F) *
  out_rep (f_ob F) (m_ow m) *
  tables_rep (f_gsh F) (f_gv F).

Definition strm_part (F: frame) (m: mst) : mpred :=
  strm_rep (f_gv F) (f_shs F) (f_strmp F)
    (in_ptr (f_ib F) (m_snx m)) (zv (Zlength (m_inp m) - m_snx m)) (m_tin m)
    (out_ptr (f_ob F) (m_sow m)) (zv (m_aout m - m_sow m)) (m_tout m)
    (msg_val (f_gv F) (m_msg m)) (f_sp F) (f_dt F) (m_adler m) (f_vres F).

Lemma mem_rep_hsplit: forall F m,
  mem_rep F m =
  field_at Ews t_state (DOT _mode) (zv (i_mode (m_s m))) (f_sp F) *
  field_at Ews t_state (DOT _wrap) (zv (i_wrap (m_s m))) (f_sp F) *
  field_at Ews t_state (DOT _flags) (zv (i_flags (m_s m))) (f_sp F) *
  field_at Ews t_state (DOT _check) (lv (i_check (m_s m))) (f_sp F) *
  field_at Ews t_state (DOT _head) (if i_head (m_s m) then f_headp F else nullval) (f_sp F) *
  head_part F m * strm_part F m * crc_table_at (f_tsh F) (f_gv F) * mem_rep_h F m.
Proof.
  intros. unfold mem_rep, mem_rep_h, strm_part. rewrite state_rep_hsplit.
  apply pred_ext; cancel.
Qed.

(* loop_state with these parts apart *)
Definition loop_state_h (F: frame) (m: mst) : environ -> mpred :=
  PROP (in_ok (f_ib F) (m_inp m); out_ok (f_ob F) (m_aout m))
  LOCAL (temp _strm (f_strmp F); temp _flush (zv (f_flush F)); temp _state (f_sp F);
         temp _next (in_ptr (f_ib F) (m_nx m)); temp _put (out_ptr (f_ob F) (Zlength (m_ow m)));
         temp _have (zv (m_have m)); temp _left (zv (m_left m)); temp _hold (lv (m_hold m));
         temp _bits (zv (m_bits m)); temp _in (zv (m_in m)); temp _out (zv (m_out m));
         temp _ret (zv (m_ret m)); temp _leave (zv (m_leave m));
         lvar _here t_code (f_vhere F); lvar _last t_code (f_vlast F);
         lvar _hbuf (tarray tuchar 4) (f_vhbuf F); gvars (f_gv F))
  SEP (field_at Ews t_state (DOT _mode) (zv (i_mode (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _wrap) (zv (i_wrap (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _flags) (zv (i_flags (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _check) (lv (i_check (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _head) (if i_head (m_s m) then f_headp F else nullval) (f_sp F);
       head_part F m; strm_part F m; crc_table_at (f_tsh F) (f_gv F);
       data_at_ Tsh (tarray tuchar 4) (f_vhbuf F);
       data_at_ Tsh t_code (f_vhere F); data_at_ Tsh t_code (f_vlast F); mem_rep_h F m).

Lemma loop_state_hsplit: forall F m, loop_state F m = loop_state_h F m.
Proof.
  intros. unfold loop_state, loop_state_h, locals_rep. rewrite mem_rep_hsplit.
  f_equal. unfold SEPx. simpl. f_equal. extensionality rho. apply pred_ext; cancel.
Qed.

(* INITBITS(): do { hold = 0; bits = 0; } while (0) *)
Lemma semax_initbits5 {Espec: OracleKind} (F: frame) (m: mst):
  semax Delta_cases5 (loop_state F m)
    (Sloop (Ssequence (Sset _hold (Ecast (Econst_int (Int.repr 0) tint) tulong))
                      (Sset _bits (Econst_int (Int.repr 0) tint))) Sbreak)
    (normal_ret_assert (loop_state F (initbits m))).
Proof.
  apply semax_loop with (Q' := loop_state F (initbits m)).
  - unfold loop_state. abbreviate_semax. forward. forward.
    unfold loop1_ret_assert. simpl RA_normal. entailer!. apply derives_refl.
  - eapply semax_pre; [ | apply semax_break]. simpl RA_break. unfold loop2_ret_assert. simpl RA_break.
    apply andp_left2. apply derives_refl.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* pure facts of the header cases                                                                 *)

Require Import Zlib.proof.crc32.Combine.
Require Import Zlib.proof.inflate.MwfLemmas.

Lemma hk_byte_mod: forall x, 0 <= x mod 256 <= Byte.max_unsigned.
Proof. intros x. pose proof (Z.mod_pos_bound x 256 ltac:(lia)). rep_lia. Qed.

Lemma hk_hbytes2_bytes: forall h, is_bytes (hbytes2 h).
Proof. intros h. unfold hbytes2. repeat constructor; apply hk_byte_mod. Qed.

Lemma hk_hbytes4_bytes: forall h, is_bytes (hbytes4 h).
Proof. intros h. unfold hbytes4. repeat constructor; apply hk_byte_mod. Qed.

Lemma hk_ref_crc32_lrange: forall c d, is_bytes d -> lrange (ref_crc32 c d).
Proof. intros c d B. pose proof (ref_crc32_range c d B). unfold is32 in *. unfold lrange. rep_lia. Qed.

Lemma hk_s32_range: forall x, srange (s32 x).
Proof.
  intros x. unfold s32, srange. pose proof (Z.mod_pos_bound x (2^32) ltac:(lia)).
  destruct (Z.ltb_spec (x mod 2^32) (2^31)); rep_lia.
Qed.

Lemma hk_land_range: forall a b, 0 <= b -> 0 <= Z.land a b <= b.
Proof.
  intros a b H. split.
  - apply Z.land_nonneg; auto.
  - apply Zbits.Ztestbit_le; auto. intros i _ T. rewrite Z.land_spec in T. apply andb_prop in T. tauto.
Qed.

(* crc_if keeps mwf *)
Lemma mwf_crc_if: forall m d, mwf m -> is_bytes d -> mwf (crc_if m d).
Proof.
  intros m d W B. unfold crc_if.
  destruct (andb _ _); [ | exact W].
  pose proof (hk_ref_crc32_lrange (i_check (m_s m)) d B) as R.
  destruct W as [MD S H]; constructor; auto; cbn [upd_s set_m_s m_s m_h m_inp m_aout m_nx m_ow m_hold m_bits
    m_in m_out m_ret m_leave m_adler m_tin m_tout m_snx m_sow m_mode] in *; auto.
  - destruct MD; constructor; auto.
  - destruct S; constructor; auto.
Qed.

Lemma mwf_upd_h: forall m f, mwf m -> hwf (f (m_h m)) -> mwf (upd_h m f).
Proof. intros m f W HW. destruct W; constructor; auto. Qed.

Lemma hwf_set_time: forall h v, hwf h -> lrange v -> hwf (set_h_time h v).
Proof. intros h v H R. destruct H; constructor; auto. Qed.
Lemma hwf_set_text: forall h v, hwf h -> srange v -> hwf (set_h_text h v).
Proof. intros h v H R. destruct H; constructor; auto. Qed.
Lemma hwf_set_xflags_os: forall h v w, hwf h -> srange v -> srange w -> hwf (set_h_os (set_h_xflags h v) w).
Proof. intros h v w H R1 R2. destruct H; constructor; auto. Qed.

(* the mode change at the end of a header case: to a mode of FLAGS .. TYPEDO, from a header mode *)
Lemma mwf3_set_mode_hdr: forall m md,
  mwf m -> HEAD <= m_mode m <= TYPEDO -> FLAGS <= md <= TYPEDO -> mwf3 (set_mode m md).
Proof.
  intros m md W HM Hmd. split.
  - apply mwf_set_mode_plain; [exact W | unfold HEAD, FLAGS, TYPEDO, SYNC in *; lia
      | unfold LENLENS, FLAGS, TYPEDO in *; lia | unfold CODELENS, FLAGS, TYPEDO in *; lia
      | unfold decode_mode, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT, FLAGS, TYPEDO in *; lia | ].
    left. apply mwf_out_eq; [exact W | ..]; unfold HEAD, TYPEDO, LENGTH, DONE, BAD in *; lia.
  - constructor; cbn [set_mode upd_s set_m_s m_s set_i_mode i_mode];
      unfold decode_mode, HEAD, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT, FLAGS, TYPEDO in *; intros; lia.
Qed.

(* do { body } while (0) *)
Lemma semax_dowhile0 {Espec: OracleKind} {cs: compspecs} (Delta: tycontext) (P Q: environ -> mpred)
    (body: statement):
  semax Delta P body (normal_ret_assert Q) ->
  semax Delta P (Sloop body Sbreak) (normal_ret_assert Q).
Proof.
  intros H.
  apply semax_loop with (Q' := Q).
  - eapply semax_post; [ | | | | exact H]; unfold loop1_ret_assert, normal_ret_assert; simpl; intros;
      try (apply andp_left2; apply derives_refl); try (apply andp_left2; apply FF_left).
  - eapply semax_pre; [ | apply semax_break]. unfold loop2_ret_assert. simpl RA_break.
    apply andp_left2. apply derives_refl.
Qed.

(* the bit tests of int fields *)
Lemma hk_and_repr: forall a b, Int.and (Int.repr a) (Int.repr b) = Int.repr (Z.land a b).
Proof.
  intros. apply Int.same_bits_eq; intros i Hi.
  rewrite Int.bits_and by auto. rewrite !Int.testbit_repr by auto. rewrite Z.land_spec. reflexivity.
Qed.

Lemma hk_land_small: forall a b, 0 <= b <= Int.max_signed -> 0 <= Z.land a b <= Int.max_signed.
Proof. intros a b H. pose proof (hk_land_range a b ltac:(lia)). lia. Qed.

Lemma hk_flagbit: forall a b, Int.and (Int.repr a) (Int.repr b) <> Int.zero -> (Z.land a b =? 0) = false.
Proof.
  intros a b H. rewrite hk_and_repr in H. apply Z.eqb_neq. intro E. rewrite E in H. apply H. reflexivity.
Qed.

Lemma hk_flagbit0: forall a b, Int.and (Int.repr a) (Int.repr b) = Int.zero -> 0 <= b <= Int.max_signed ->
  (Z.land a b =? 0) = true.
Proof.
  intros a b H Hb. rewrite hk_and_repr in H. apply Z.eqb_eq.
  pose proof (hk_land_range a b ltac:(lia)).
  apply (f_equal Int.unsigned) in H. rewrite Int.unsigned_repr in H by rep_lia. exact H.
Qed.

Lemma hk_tbool: forall x, 0 <= x <= Int.max_signed ->
  Vint (if Int.eq (Int.repr x) Int.zero then Int.zero else Int.one) = Vint (Int.repr (if x =? 0 then 0 else 1)).
Proof.
  intros x H. destruct (Z.eqb_spec x 0).
  - subst. reflexivity.
  - rewrite Int.eq_false; [reflexivity | ]. intro E. apply (f_equal Int.unsigned) in E.
    rewrite Int.unsigned_repr in E by rep_lia. apply n. exact E.
Qed.

(* what the header updates keep *)
Lemma hk_needbits_f_s: forall k n m, m_s (needbits_f k n m) = m_s m.
Proof.
  induction k; intros n m; simpl; auto.
  destruct (m_bits m <? n); auto. destruct (m_have m =? 0); auto. rewrite IHk. reflexivity.
Qed.

Lemma hk_needbits_mode: forall n m, m_mode (needbits n m) = m_mode m.
Proof. intros. unfold m_mode, needbits. rewrite hk_needbits_f_s. reflexivity. Qed.

Lemma hk_crc_if_mode: forall m d, m_mode (crc_if m d) = m_mode m.
Proof. intros. unfold crc_if. destruct (andb _ _); reflexivity. Qed.

Lemma hk_crc_if_leave: forall m d, m_leave (crc_if m d) = m_leave m.
Proof. intros. unfold crc_if. destruct (andb _ _); reflexivity. Qed.

Lemma mem_rep_h_check: forall F m d,
  mem_rep_h F (upd_s m (fun s => set_i_check s (ref_crc32 (i_check s) d))) = mem_rep_h F m.
Proof. reflexivity. Qed.
Lemma head_part_check: forall F m d,
  head_part F (upd_s m (fun s => set_i_check s (ref_crc32 (i_check s) d))) = head_part F m.
Proof. reflexivity. Qed.
Lemma strm_part_check: forall F m d,
  strm_part F (upd_s m (fun s => set_i_check s (ref_crc32 (i_check s) d))) = strm_part F m.
Proof. reflexivity. Qed.
