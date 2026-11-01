(* A view of loop_state for the trailer cases CHECK and LENGTH in Delta_cases5: the state fields mode, wrap,
   flags, check, total apart (state_rep_k: the 30 others), the stream, the output object, the crc table and
   the stack variables as separate SEP items, the rest of the memory one opaque item (mem_rep_k, unchanged by
   the updates of these cases).  INITBITS(), the BAD block, and small int facts.  (After HdrKit5.v.) *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Export Zlib.proof.inflate.ModeKit5.
Require Import Zlib.proof.crc32.Spec.

#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Definition state_rep_k (gv: globals) (sp strmp headp winp: val) (s: istate) : mpred :=
  field_at Ews t_state (DOT _strm) strmp sp *
  field_at Ews t_state (DOT _last) (zv (i_last s)) sp *
  field_at Ews t_state (DOT _havedict) (zv (i_havedict s)) sp *
  field_at Ews t_state (DOT _dmax) (zv (i_dmax s)) sp *
  field_at Ews t_state (DOT _head) (if i_head s then headp else nullval) sp *
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

(* the conjuncts 2, 4, 6, 8, 9 of 35 to the front (on variables: a cheap proof term) *)
Lemma sepcon_k_35: forall a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35: mpred,
  a1 * a2 * a3 * a4 * a5 * a6 * a7 * a8 * a9 * a10 * a11 * a12 * a13 * a14 * a15 * a16 * a17 * a18 * a19 * a20 * a21 * a22 * a23 * a24 * a25 * a26 * a27 * a28 * a29 * a30 * a31 * a32 * a33 * a34 * a35 =
  a2 * a4 * a6 * a8 * a9 * (a1 * a3 * a5 * a7 * a10 * a11 * a12 * a13 * a14 * a15 * a16 * a17 * a18 * a19 * a20 * a21 * a22 * a23 * a24 * a25 * a26 * a27 * a28 * a29 * a30 * a31 * a32 * a33 * a34 * a35).
Proof. intros. apply pred_ext; cancel. Qed.

Lemma state_rep_ksplit: forall gv sp strmp headp winp s,
  state_rep gv sp strmp headp winp s =
  field_at Ews t_state (DOT _mode) (zv (i_mode s)) sp *
  field_at Ews t_state (DOT _wrap) (zv (i_wrap s)) sp *
  field_at Ews t_state (DOT _flags) (zv (i_flags s)) sp *
  field_at Ews t_state (DOT _check) (lv (i_check s)) sp *
  field_at Ews t_state (DOT _total) (lv (i_total s)) sp *
  state_rep_k gv sp strmp headp winp s.
Proof. intros. unfold state_rep, state_rep_k. apply sepcon_k_35. Qed.

(* the memory but the five fields, the stream, the output object and the crc table *)
Definition mem_rep_k (F: frame) (m: mst) : mpred :=
  state_rep_k (f_gv F) (f_sp F) (f_strmp F) (f_headp F) (f_winp F) (m_s m) *
  win_rep (f_winp F) (m_s m) *
  head_part F m *
  in_rep (f_ib F) *
  tables_rep (f_gsh F) (f_gv F).

Definition strm_k (F: frame) (m: mst) : mpred :=
  strm_rep (f_gv F) (f_shs F) (f_strmp F)
    (in_ptr (f_ib F) (m_snx m)) (zv (Zlength (m_inp m) - m_snx m)) (m_tin m)
    (out_ptr (f_ob F) (m_sow m)) (zv (m_aout m - m_sow m)) (m_tout m)
    (msg_val (f_gv F) (m_msg m)) (f_sp F) (f_dt F) (m_adler m) (f_vres F).

Lemma mem_rep_ksplit: forall F m,
  mem_rep F m =
  field_at Ews t_state (DOT _mode) (zv (i_mode (m_s m))) (f_sp F) *
  field_at Ews t_state (DOT _wrap) (zv (i_wrap (m_s m))) (f_sp F) *
  field_at Ews t_state (DOT _flags) (zv (i_flags (m_s m))) (f_sp F) *
  field_at Ews t_state (DOT _check) (lv (i_check (m_s m))) (f_sp F) *
  field_at Ews t_state (DOT _total) (lv (i_total (m_s m))) (f_sp F) *
  strm_k F m * out_rep (f_ob F) (m_ow m) * crc_table_at (f_tsh F) (f_gv F) * mem_rep_k F m.
Proof.
  intros. unfold mem_rep, mem_rep_k, strm_k. rewrite state_rep_ksplit.
  apply pred_ext; cancel.
Qed.

(* loop_state with these parts apart *)
Definition loop_state_k (F: frame) (m: mst) : environ -> mpred :=
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
       field_at Ews t_state (DOT _total) (lv (i_total (m_s m))) (f_sp F);
       strm_k F m; out_rep (f_ob F) (m_ow m); crc_table_at (f_tsh F) (f_gv F);
       data_at_ Tsh (tarray tuchar 4) (f_vhbuf F);
       data_at_ Tsh t_code (f_vhere F); data_at_ Tsh t_code (f_vlast F); mem_rep_k F m).

Lemma loop_state_ksplit: forall F m, loop_state F m = loop_state_k F m.
Proof.
  intros. unfold loop_state, loop_state_k, locals_rep. rewrite mem_rep_ksplit.
  f_equal. unfold SEPx. simpl. f_equal. extensionality rho. apply pred_ext; cancel.
Qed.

(* INITBITS(): do { hold = 0; bits = 0; } while (0) *)
Lemma semax_initbits_k {Espec: OracleKind} (F: frame) (m: mst):
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
(* strm->msg = (char * )<msg>; state->mode = BAD; break;                                           *)

Definition bad_block_k (id: ident) (n: Z) : statement :=
  (Ssequence (Sassign (Efield (Ederef (Etempvar _strm (tptr (Tstruct _z_stream_s noattr))) (Tstruct _z_stream_s noattr)) _msg (tptr tschar)) (Ecast (Evar id (tarray tschar n)) (tptr tschar))) (Ssequence (Sassign (Efield (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr))) (Tstruct _inflate_state noattr)) _mode tint) (Econst_int (Int.repr 16209) tint)) Sbreak)).

Definition bad_okk {Espec: OracleKind} (F: frame) (e: msgid) (n: Z) : Prop :=
  forall (m m0: mst) (R: ret_assert),
    RA_break R = RA_normal (case_post2 F m0) ->
    stepf2 (f_flush F) lenfix_list distfix_list m0 = IBrk (set_bad m e) ->
    semax Delta_cases5 (loop_state F m) (bad_block_k (msg_ident e) n) R.

Lemma mem_rep_k_bad: forall F m e, mem_rep_k F (set_bad m e) = mem_rep_k F m.
Proof. reflexivity. Qed.

Ltac bad_tac F e :=
  let HWS := fresh "HWS" in let m := fresh "m" in let m0 := fresh "m0" in let R := fresh "R" in
  let HR := fresh "HR" in let HS := fresh "HS" in let zca := fresh "zca" in let zcf := fresh "zcf" in
  let Hzca := fresh "Hzca" in let Hzcf := fresh "Hzcf" in
  intros HWS m m0 R HR HS;
  unfold bad_block_k; cbn [msg_ident];
  rewrite loop_state_ksplit; unfold loop_state_k, strm_k, strm_rep;
  abbreviate_semax;
  remember (f_gv F _zcalloc) as zca eqn:Hzca; remember (f_gv F _zcfree) as zcf eqn:Hzcf;
  forward; forward; forward;
  rewrite HR; unfold case_post2, RA_normal; Exists (set_bad m e);
  rewrite loop_state_ksplit; unfold loop_state_k, strm_k, strm_rep;
  rewrite (mem_rep_k_bad F m e);
  cbn [set_bad set_mode upd_s set_m_s set_m_msg m_s m_msg i_mode set_i_mode i_wrap i_flags i_check i_total
       i_head m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave m_snx m_sow m_tin m_tout m_adler
       m_have m_left msg_val];
  rewrite <- Hzca, <- Hzcf; entailer!.

Lemma bad_okk_dcheck {Espec: OracleKind} (F: frame) : writable_share (f_shs F) -> bad_okk F M_dcheck 21.
Proof. bad_tac F M_dcheck. Qed.

Lemma bad_okk_lcheck {Espec: OracleKind} (F: frame) : writable_share (f_shs F) -> bad_okk F M_lcheck 23.
Proof. bad_tac F M_lcheck. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* small int facts                                                                                 *)

Lemma ck_land_range: forall a b, 0 <= b -> 0 <= Z.land a b <= b.
Proof.
  intros a b H. split.
  - apply Z.land_nonneg; auto.
  - apply Zbits.Ztestbit_le; auto. intros i _ T. rewrite Z.land_spec in T. apply andb_prop in T. tauto.
Qed.

Lemma ck_and_repr: forall a b, Int.and (Int.repr a) (Int.repr b) = Int.repr (Z.land a b).
Proof.
  intros. apply Int.same_bits_eq; intros i Hi.
  rewrite Int.bits_and by auto. rewrite !Int.testbit_repr by auto. rewrite Z.land_spec. reflexivity.
Qed.

Lemma ck_flagbit: forall a b, Int.and (Int.repr a) (Int.repr b) <> Int.zero -> (Z.land a b =? 0) = false.
Proof.
  intros a b H. rewrite ck_and_repr in H. apply Z.eqb_neq. intro E. rewrite E in H. apply H. reflexivity.
Qed.

Lemma ck_flagbit0: forall a b, Int.and (Int.repr a) (Int.repr b) = Int.zero -> 0 <= b <= Int.max_signed ->
  (Z.land a b =? 0) = true.
Proof.
  intros a b H Hb. rewrite ck_and_repr in H. apply Z.eqb_eq.
  pose proof (ck_land_range a b ltac:(lia)).
  apply (f_equal Int.unsigned) in H. rewrite Int.unsigned_repr in H by rep_lia. exact H.
Qed.

Lemma ck_int_zero: forall x, Int.min_signed <= x <= Int.max_signed -> Int.repr x = Int.zero -> x = 0.
Proof.
  intros x R H. apply (f_equal Int.signed) in H. rewrite Int.signed_repr in H by rep_lia. exact H.
Qed.

Lemma ck_int_nzero: forall x, x <> 0 -> Int.min_signed <= x <= Int.max_signed -> Int.repr x <> Int.zero.
Proof. intros x N R H. apply N. apply ck_int_zero; auto. Qed.

(* (_Bool) of an int / unsigned in range *)
Lemma ck_tbool: forall x, 0 <= x <= Int.max_unsigned ->
  Vint (if Int.eq (Int.repr x) Int.zero then Int.zero else Int.one) = Vint (Int.repr (if x =? 0 then 0 else 1)).
Proof.
  intros x H. destruct (Z.eqb_spec x 0).
  - subst. reflexivity.
  - rewrite Int.eq_false; [reflexivity | ]. intro E. apply (f_equal Int.unsigned) in E.
    rewrite Int.unsigned_repr in E by rep_lia. apply n. exact E.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* NEEDBITS keeps everything but the input position, hold, bits and leave                          *)

Lemma ck_needbits_f_keep: forall k n m,
  m_s (needbits_f k n m) = m_s m /\ m_h (needbits_f k n m) = m_h m /\ m_inp (needbits_f k n m) = m_inp m /\
  m_aout (needbits_f k n m) = m_aout m /\ m_ow (needbits_f k n m) = m_ow m /\
  m_in (needbits_f k n m) = m_in m /\ m_out (needbits_f k n m) = m_out m /\ m_ret (needbits_f k n m) = m_ret m /\
  m_adler (needbits_f k n m) = m_adler m /\ m_msg (needbits_f k n m) = m_msg m /\
  m_tin (needbits_f k n m) = m_tin m /\ m_tout (needbits_f k n m) = m_tout m /\
  m_snx (needbits_f k n m) = m_snx m /\ m_sow (needbits_f k n m) = m_sow m.
Proof.
  induction k; intros n m; simpl; [repeat split; reflexivity | ].
  destruct (m_bits m <? n); [ | repeat split; reflexivity].
  destruct (m_have m =? 0); [repeat split; reflexivity | ].
  destruct (IHk n (pull m)) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14).
  rewrite A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14. repeat split; reflexivity.
Qed.

Lemma ck_needbits_mode: forall n m, m_mode (needbits n m) = m_mode m.
Proof. intros. unfold m_mode, needbits. rewrite (proj1 (ck_needbits_f_keep 4 n m)). reflexivity. Qed.
