(* inflate(), the switch cases TYPE, TYPEDO (11-12), version 5 (Delta_cases5, case_post2 over Model2.v, mwf3; header cases
   FLAGS .. COMMENT with the header buffers' tokens: CaseHyps5.v, CaseKitT5.v) *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate.CaseHyps5.
Require Import Zlib.proof.inflate.NeedKit5 Zlib.proof.inflate.NeedBits Zlib.proof.inflate.NeedBits2_5.
Require Import Zlib.proof.inflate.Model2 Zlib.proof.inflate.Steps2 Zlib.proof.inflate.MwfLemmas.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* ---------------------------------------------------------------------------------------------- *)
(* the fields TYPEDO writes (mode, last, lencode, distcode, lenbits, distbits) and the z_stream apart
   from the rest of the memory (one opaque SEP item), as in Cases3_HEAD *)

Definition state_rest_ty (gv: globals) (sp strmp headp winp: val) (s: istate) : mpred :=
  field_at Ews t_state (DOT _strm) strmp sp *
  field_at Ews t_state (DOT _wrap) (zv (i_wrap s)) sp *
  field_at Ews t_state (DOT _havedict) (zv (i_havedict s)) sp *
  field_at Ews t_state (DOT _flags) (zv (i_flags s)) sp *
  field_at Ews t_state (DOT _dmax) (zv (i_dmax s)) sp *
  field_at Ews t_state (DOT _check) (lv (i_check s)) sp *
  field_at Ews t_state (DOT _total) (lv (i_total s)) sp *
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

Lemma sepcon_ty_35: forall a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35: mpred,
  a1 * a2 * a3 * a4 * a5 * a6 * a7 * a8 * a9 * a10 * a11 * a12 * a13 * a14 * a15 * a16 * a17 * a18 * a19 * a20 * a21 * a22 * a23 * a24 * a25 * a26 * a27 * a28 * a29 * a30 * a31 * a32 * a33 * a34 * a35 =
  a2 * a3 * a21 * a22 * a23 * a24 * (a1 * a4 * a5 * a6 * a7 * a8 * a9 * a10 * a11 * a12 * a13 * a14 * a15 * a16 * a17 * a18 * a19 * a20 * a25 * a26 * a27 * a28 * a29 * a30 * a31 * a32 * a33 * a34 * a35).
Proof. intros. apply pred_ext; cancel. Qed.

Lemma state_rep_ty: forall gv sp strmp headp winp s,
  state_rep gv sp strmp headp winp s =
  field_at Ews t_state (DOT _mode) (zv (i_mode s)) sp *
  field_at Ews t_state (DOT _last) (zv (i_last s)) sp *
  field_at Ews t_state (DOT _lencode) (tref_val gv sp (i_lencode s)) sp *
  field_at Ews t_state (DOT _distcode) (tref_val gv sp (i_distcode s)) sp *
  field_at Ews t_state (DOT _lenbits) (zv (i_lenbits s)) sp *
  field_at Ews t_state (DOT _distbits) (zv (i_distbits s)) sp *
  state_rest_ty gv sp strmp headp winp s.
Proof. intros. unfold state_rep, state_rest_ty. apply sepcon_ty_35. Qed.

(* the memory but those six fields and the z_stream *)
Definition mem_rest_ty (F: frame) (m: mst) : mpred :=
  state_rest_ty (f_gv F) (f_sp F) (f_strmp F) (f_headp F) (f_winp F) (m_s m) *
  win_rep (f_winp F) (m_s m) *
  head_part F m *
  in_rep (f_ib F) *
  out_rep (f_ob F) (m_ow m) *
  tables_rep (f_gsh F) (f_gv F) *
  crc_table_at (f_tsh F) (f_gv F).

Definition loop_state_ty (F: frame) (m: mst) : environ -> mpred :=
  PROP (in_ok (f_ib F) (m_inp m); out_ok (f_ob F) (m_aout m))
  LOCAL (temp _strm (f_strmp F); temp _flush (zv (f_flush F)); temp _state (f_sp F);
         temp _next (in_ptr (f_ib F) (m_nx m)); temp _put (out_ptr (f_ob F) (Zlength (m_ow m)));
         temp _have (zv (m_have m)); temp _left (zv (m_left m)); temp _hold (lv (m_hold m));
         temp _bits (zv (m_bits m)); temp _in (zv (m_in m)); temp _out (zv (m_out m));
         temp _ret (zv (m_ret m)); temp _leave (zv (m_leave m));
         lvar _here t_code (f_vhere F); lvar _last t_code (f_vlast F);
         lvar _hbuf (tarray tuchar 4) (f_vhbuf F); gvars (f_gv F))
  SEP (field_at Ews t_state (DOT _mode) (zv (i_mode (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _last) (zv (i_last (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _lencode) (tref_val (f_gv F) (f_sp F) (i_lencode (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _distcode) (tref_val (f_gv F) (f_sp F) (i_distcode (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _lenbits) (zv (i_lenbits (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _distbits) (zv (i_distbits (m_s m))) (f_sp F);
       strm_rep (f_gv F) (f_shs F) (f_strmp F)
         (in_ptr (f_ib F) (m_snx m)) (zv (Zlength (m_inp m) - m_snx m)) (m_tin m)
         (out_ptr (f_ob F) (m_sow m)) (zv (m_aout m - m_sow m)) (m_tout m)
         (msg_val (f_gv F) (m_msg m)) (f_sp F) (f_dt F) (m_adler m) (f_vres F);
       mem_rest_ty F m;
       locals_rep F).

Lemma mem_rest_ty_bits: forall F m b, mem_rest_ty F (set_m_bits m b) = mem_rest_ty F m.
Proof. reflexivity. Qed.
Lemma mem_rest_ty_hold: forall F m h, mem_rest_ty F (set_m_hold m h) = mem_rest_ty F m.
Proof. reflexivity. Qed.
Lemma mem_rest_ty_leave: forall F m l, mem_rest_ty F (set_m_leave m l) = mem_rest_ty F m.
Proof. reflexivity. Qed.
Lemma mem_rest_ty_msg: forall F m e, mem_rest_ty F (set_m_msg m e) = mem_rest_ty F m.
Proof. reflexivity. Qed.
Lemma mem_rest_ty_mode: forall F m md, mem_rest_ty F (set_mode m md) = mem_rest_ty F m.
Proof. reflexivity. Qed.
Lemma mem_rest_ty_last: forall F m v, mem_rest_ty F (upd_s m (fun s => set_i_last s v)) = mem_rest_ty F m.
Proof. reflexivity. Qed.
Lemma mem_rest_ty_tables: forall F m,
  mem_rest_ty F (upd_s m (fun s =>
    set_i_distbits (set_i_distcode (set_i_lenbits (set_i_lencode s TLenfix) 9) TDistfix) 5)) = mem_rest_ty F m.
Proof. reflexivity. Qed.

Definition ty_locals (F: frame) (m: mst) : list localdef :=
  [temp _strm (f_strmp F); temp _flush (zv (f_flush F)); temp _state (f_sp F);
   temp _next (in_ptr (f_ib F) (m_nx m)); temp _put (out_ptr (f_ob F) (Zlength (m_ow m)));
   temp _have (zv (m_have m)); temp _left (zv (m_left m)); temp _hold (lv (m_hold m));
   temp _bits (zv (m_bits m)); temp _in (zv (m_in m)); temp _out (zv (m_out m));
   temp _ret (zv (m_ret m)); temp _leave (zv (m_leave m));
   lvar _here t_code (f_vhere F); lvar _last t_code (f_vlast F);
   lvar _hbuf (tarray tuchar 4) (f_vhbuf F); gvars (f_gv F)].

Lemma loop_state_ty_eq: forall F m, loop_state F m = loop_state_ty F m.
Proof.
  intros. unfold loop_state, loop_state_ty, mem_rep, mem_rest_ty. rewrite state_rep_ty.
  f_equal. f_equal. unfold SEPx. extensionality rho. simpl. apply pred_ext; cancel.
Qed.

(* do { c } while (0) followed by rest *)
Lemma semax_dowhile0 {Espec: OracleKind} (Delta: tycontext) (P Q: environ -> mpred) (c rest: statement)
    (R: ret_assert):
  semax Delta P c (normal_ret_assert Q) -> semax Delta Q rest R ->
  semax Delta P (Ssequence (Sloop c Sbreak) rest) R.
Proof.
  intros H1 H2. apply semax_seq with Q; [ | exact H2].
  apply semax_loop with (Q' := Q).
  - destruct R. eapply semax_post; [ | | | | exact H1]; intros; simpl_ret_assert;
      first [apply andp_left2, derives_refl | apply andp_left2, FF_left].
  - eapply semax_pre; [ | apply semax_break]. destruct R. simpl_ret_assert. apply andp_left2, derives_refl.
Qed.

Lemma semax_switch_post {Espec: OracleKind} (Delta: tycontext) (P Q: environ -> mpred) (c: statement)
    (R: ret_assert):
  semax Delta P c (switch_ret_assert (normal_ret_assert Q)) ->
  semax Delta P c (switch_ret_assert (overridePost Q R)).
Proof.
  intros H. destruct R. eapply semax_post; [ | | | | exact H]; intros; simpl_ret_assert;
    first [apply andp_left2, derives_refl | apply andp_left2, FF_left].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the model of TYPEDO, cut along the code                                                        *)

Definition ty_m2 (m1: mst) : mst := dropbits 1 (upd_s m1 (fun s => set_i_last s (bitsn m1 1))).
Definition ty_fixed (m: mst) : mst :=
  set_mode (upd_s m (fun s =>
    set_i_distbits (set_i_distcode (set_i_lenbits (set_i_lencode s TLenfix) 9) TDistfix) 5)) LEN_.

(* the machine after the inner switch (before `if (leave) break; DROPBITS(2);`) *)
Definition ty_sw (fl: Z) (m2: mst) : mst :=
  let bt := bitsn m2 2 in
  if bt =? 0 then set_mode m2 STORED
  else if bt =? 1 then (if fl =? Z_TREES then set_leave (dropbits 2 (ty_fixed m2)) else ty_fixed m2)
  else if bt =? 2 then set_mode m2 TABLE
  else set_bad m2 M_btype.

Definition ty_out (m3: mst) : iout := if m_leave m3 =? 1 then IBrk m3 else IBrk (dropbits 2 m3).

Lemma ty_sw_leave: forall fl m2, m_leave m2 = 0 -> m_leave (ty_sw fl m2) = 0 \/ m_leave (ty_sw fl m2) = 1.
Proof.
  intros fl m2 L. unfold ty_sw.
  destruct (bitsn m2 2 =? 0); [left; exact L | ].
  destruct (bitsn m2 2 =? 1); [destruct (fl =? Z_TREES); [right; reflexivity | left; exact L] | ].
  destruct (bitsn m2 2 =? 2); left; exact L.
Qed.

Lemma ty_sw_hold: forall fl m2, 0 <= m_hold m2 <= Int64.max_unsigned ->
  0 <= m_hold (ty_sw fl m2) <= Int64.max_unsigned.
Proof.
  intros fl m2 L. unfold ty_sw.
  destruct (bitsn m2 2 =? 0); [exact L | ].
  destruct (bitsn m2 2 =? 1); [destruct (fl =? Z_TREES); [ | exact L] | ].
  - cbn [m_hold set_leave set_m_leave dropbits set_m_bits set_m_hold]. apply Zshiftr_range; [exact L | lia].
  - destruct (bitsn m2 2 =? 2); exact L.
Qed.

Lemma c_TYPEDO_eq: forall fl m, m_leave m = 0 ->
  c_TYPEDO fl m =
  if negb (i_last (m_s m) =? 0) then IBrk (set_mode (bytebits m) CHECK) else
  let m1 := needbits 3 m in
  if m_leave m1 =? 1 then IBrk m1 else ty_out (ty_sw fl (ty_m2 m1)).
Proof.
  intros fl m HL. unfold c_TYPEDO, ty_out, ty_sw, ty_m2, ty_fixed.
  destruct (negb (i_last (m_s m) =? 0)); [reflexivity | ].
  cbv zeta. destruct (m_leave (needbits 3 m) =? 1) eqn:L1; [reflexivity | ].
  set (m2 := dropbits 1 _).
  assert (Lm2: m_leave m2 = m_leave (needbits 3 m)) by reflexivity.
  destruct (bitsn m2 2 =? 0); [cbn [m_leave set_mode upd_s set_m_s]; rewrite Lm2, L1; reflexivity | ].
  destruct (bitsn m2 2 =? 1).
  - destruct (fl =? Z_TREES); [reflexivity | ]. cbn [m_leave set_mode upd_s set_m_s]. rewrite Lm2, L1.
    reflexivity.
  - destruct (bitsn m2 2 =? 2); [cbn [m_leave set_mode upd_s set_m_s]; rewrite Lm2, L1; reflexivity | ].
    cbn [m_leave set_bad set_mode upd_s set_m_s set_m_msg]. rewrite Lm2, L1. reflexivity.
Qed.

(* the bit operations of BITS / DROPBITS / BYTEBITS *)
Lemma int_and_ones: forall b k, 0 <= b -> 0 <= k <= 32 ->
  Int.and (Int.repr b) (Int.repr (2 ^ k - 1)) = Int.repr (b mod 2 ^ k).
Proof.
  intros b k Hb Hk. unfold Int.and.
  rewrite (Int.unsigned_repr_eq b).
  rewrite (Int.unsigned_repr (2 ^ k - 1)).
  - f_equal. replace (2 ^ k - 1) with (Z.ones k) by (rewrite Z.ones_equiv; lia). rewrite Z.land_ones by lia.
    change Int.modulus with (2 ^ 32). symmetry. apply Znumtheory.Zmod_div_mod.
    + apply Z.pow_pos_nonneg; lia.
    + lia.
    + exists (2 ^ (32 - k)). rewrite <- Z.pow_add_r by lia. f_equal. lia.
  - split; [ | change Int.max_unsigned with (2 ^ 32 - 1)].
    + assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia). lia.
    + assert (2 ^ k <= 2 ^ 32) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

Lemma int_and7: forall b, 0 <= b <= Int.max_unsigned ->
  Int.and (Int.repr b) (Int.repr 7) = Int.repr (b mod 8).
Proof. intros. apply (int_and_ones b 3); lia. Qed.

Lemma int_and1: forall b, 0 <= b -> Int.and (Int.repr b) (Int.repr 1) = Int.repr (b mod 2).
Proof. intros. apply (int_and_ones b 1); lia. Qed.
Lemma int_and3: forall b, 0 <= b -> Int.and (Int.repr b) (Int.repr 3) = Int.repr (b mod 4).
Proof. intros. apply (int_and_ones b 2); lia. Qed.

Lemma land7: forall b, Z.land b 7 = b mod 8.
Proof. intros. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma long_shru_eq: forall h n, 0 <= h <= Int64.max_unsigned -> 0 <= n < 64 ->
  Int64.shru (Int64.repr h) (Int64.repr n) = Int64.repr (Z.shiftr h n).
Proof.
  intros h n Hh Hn. unfold Int64.shru.
  rewrite (Int64.unsigned_repr h) by lia. rewrite (Int64.unsigned_repr n) by rep_lia. reflexivity.
Qed.

Lemma u32_repr: forall x, Int.repr (u32 x) = Int.repr x.
Proof.
  intros. unfold u32. apply Int.eqm_samerepr. unfold Int.eqm. apply Zbits.eqmod_sym, Zbits.eqmod_mod.
  reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* TYPEDO's statements for any machine m (of mode TYPE or TYPEDO) whose pass m0 is c_TYPEDO m      *)

Lemma typedo5 {Espec: OracleKind} (F: frame) (m0 m: mst):
  frame_ok F -> Int.min_signed <= f_flush F <= Int.max_signed -> m_leave m = 0 -> mwf m ->
  stepf2 (f_flush F) lenfix_list distfix_list m0 = c_TYPEDO (f_flush F) m ->
  semax Delta_cases5 (loop_state F m) (seq_of_labeled_statement (ls_drop 12 inflate_LS))
    (switch_ret_assert (case_post2 F m0)).
Proof.
  intros HF Hfl HL W E0.
  rewrite c_TYPEDO_eq in E0 by exact HL.
  rewrite seq_split by lia. eapply semax_seq; [ | apply semax_ff].
  case_body_stmt.
  pose proof (mw_bits _ W) as WB. pose proof (mw_hold _ W) as WH. unfold lrange in WH.
  destruct (Z.eq_dec (i_last (m_s m)) 0) as [L0|L0].
  2:{ rewrite (proj2 (Z.eqb_neq _ _) L0) in E0. cbn [negb] in E0.
  apply semax_seq with (Q := FF); [ | apply semax_ff].
  rewrite loop_state_ty_eq. unfold loop_state_ty.
  abbreviate_semax.
  forward. forward_if.
  2:{ exfalso. pose proof (sw_last _ (mw_s _ W)). assert (X: i_last (m_s m) = 1) by lia. rewrite X in H1. discriminate. }
  unfold abbreviate in MORE_COMMANDS. subst MORE_COMMANDS.
  apply semax_dowhile0 with (Q := loop_state_ty F (bytebits m)).
  - unfold loop_state_ty. abbreviate_semax.
    pose proof (Z.mod_pos_bound (m_bits m) 8 ltac:(lia)) as B8.
    freeze [0;1;2;3;4;5;6;7;8] FR.
    forward.
    { entailer!. rewrite land7. rewrite Int.unsigned_repr by rep_lia. change (Int.unsigned Int64.iwordsize') with 64. lia. }
    rewrite int_and7 by rep_lia. rewrite Int.unsigned_repr by rep_lia.
    rewrite long_shru_eq by lia.
    forward.
    thaw FR. unfold bytebits. rewrite mem_rest_ty_bits, mem_rest_ty_hold. mnorm_goal. entailer!.
    rewrite land7. reflexivity.
  - unfold loop_state_ty. abbreviate_semax. freeze [1;2;3;4;5;6;7;8] FR. forward. forward.
    unfold switch_ret_assert, case_post2. cbn [RA_break RA_normal].
    Exists (set_mode (bytebits m) CHECK).
    apply andp_right; [apply prop_right; exact E0 | ].
    thaw FR. rewrite loop_state_ty_eq. unfold loop_state_ty. rewrite mem_rest_ty_mode.
    unfold bytebits. mnorm_goal. entailer!. }
  rewrite (proj2 (Z.eqb_eq _ _) L0) in E0. cbn [negb] in E0.
  apply semax_seq with (Q := loop_state F m).
  { rewrite !loop_state_ty_eq. unfold loop_state_ty. abbreviate_semax.
    freeze [0;2;3;4;5;6;7;8] FR.
    forward. forward_if; [contradiction | ].
    forward. thaw FR. unfold switch_ret_assert, case_post2. cbn [RA_normal]. entailer!. }
  eapply (semax_needbits_seq_r5 F m0 m 3).
  - apply semax_needbits_TYPEDO5; [exact W | exact HL | lia].
  - exact W.
  - lia.
  - reflexivity.
  - intro E. rewrite E0. cbv zeta. rewrite E. reflexivity.
  - apply semax_extract_prop; intros HL1.
    pose proof (mwf_needbits 3 m W ltac:(lia)) as W1.
    assert (E1: stepf2 (f_flush F) lenfix_list distfix_list m0 = ty_out (ty_sw (f_flush F) (ty_m2 (needbits 3 m)))).
    { rewrite E0. cbv zeta. rewrite HL1. reflexivity. }
    clear E0.
    set (m1 := needbits 3 m) in *. clearbody m1.
    clear WB WH. pose proof (mw_bits _ W1) as WB. pose proof (mw_hold _ W1) as WH. unfold lrange in WH.
    rewrite loop_state_ty_eq. unfold loop_state_ty. abbreviate_semax.
    freeze [0;2;3;4;5;6;7;8] FR.
    forward.
    replace (Int64.Z_mod_modulus (m_hold m1)) with (m_hold m1)
      by (rewrite Int64.Z_mod_modulus_eq, Z.mod_small; rep_lia).
    change (Int.sub (Int.shl (Int.repr 1) (Int.repr 1)) (Int.repr 1)) with (Int.repr 1).
    rewrite int_and1 by lia.
    unfold abbreviate in MORE_COMMANDS. subst MORE_COMMANDS.
    apply semax_dowhile0 with (Q := loop_state_ty F (ty_m2 m1)).
    { forward. forward. thaw FR. unfold loop_state_ty, ty_m2, dropbits, bitsn.
      rewrite mem_rest_ty_bits, mem_rest_ty_hold, mem_rest_ty_last. unfold m_have, m_left. mnorm_goal.
      change (Int.unsigned (Int.repr 1)) with 1.
      rewrite long_shru_eq by lia. rewrite u32_repr. change (2 ^ 1) with 2.
      entailer!. }
    set (m2 := ty_m2 m1) in *.
    assert (HL2: m_leave m2 = 0) by exact HL1.
    assert (WH2: 0 <= m_hold m2 <= Int64.max_unsigned) 
      by (unfold m2, ty_m2, dropbits; cbn [m_hold set_m_bits set_m_hold upd_s set_m_s];
          apply Zshiftr_range; lia).
    clearbody m2. clear FR.
    unfold loop_state_ty. abbreviate_semax.
    freeze [1;7;8] FR.
    assert (BT: 0 <= bitsn m2 2 < 4) by (unfold bitsn; apply Z.mod_pos_bound; lia).
    apply semax_seq with (Q := loop_state_ty F (ty_sw (f_flush F) m2)).
    apply (semax_switch_PQR (bitsn m2 2)); [reflexivity | entailer! | | ].
    { entailer!. rewrite Int64.Z_mod_modulus_eq, Z.mod_small by rep_lia.
      change (Int.sub (Int.shl (Int.repr 1) (Int.repr 2)) (Int.repr 1)) with (Int.repr 3).
      rewrite int_and3 by lia. reflexivity. }
    rewrite Int.unsigned_repr by rep_lia.
    apply semax_switch_post.
    assert (Hc: bitsn m2 2 = 0 \/ bitsn m2 2 = 1 \/ bitsn m2 2 = 2 \/ bitsn m2 2 = 3) by lia.
    destruct Hc as [X|[X|[X|X]]]; rewrite X; simpl select_switch; simpl seq_of_labeled_statement.
    + forward. forward.
      unfold ty_sw. rewrite X. cbn [Z.eqb Pos.eqb]. unfold loop_state_ty. rewrite mem_rest_ty_mode.
      thaw FR. unfold m_have, m_left. mnorm_goal. entailer!.
    + forward_call (f_sp F, f_gv F, tref_val (f_gv F) (f_sp F) (i_lencode (m_s m2)), zv (i_lenbits (m_s m2)),
                    tref_val (f_gv F) (f_sp F) (i_distcode (m_s m2)), zv (i_distbits (m_s m2))).
      freeze [0;1;2;3] FR2.
      forward.
      apply semax_seq with (Q := FF); [ | apply semax_ff].
      forward_if.
      * apply semax_seq with (Q := FF); [ | apply semax_ff].
        match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx ?S))) _ _ =>
          apply semax_dowhile0 with (Q := PROPx [] (LOCALx (ty_locals F (dropbits 2 m2)) (SEPx S))) end.
        { unfold ty_locals. forward. forward.
          unfold dropbits, m_have, m_left. mnorm_goal.
          change (Int.unsigned (Int.repr 2)) with 2.
          rewrite long_shru_eq by lia. rewrite u32_repr.
          entailer!. }
        unfold ty_locals. forward. forward.
        unfold ty_sw. rewrite X, H3. change (1 =? 0) with false. change (1 =? 1) with true.
        change (6 =? Z_TREES) with true. cbv iota.
        unfold loop_state_ty, set_leave, ty_fixed, dropbits.
        rewrite mem_rest_ty_leave, mem_rest_ty_bits, mem_rest_ty_hold, mem_rest_ty_mode, mem_rest_ty_tables.
        unfold m_have, m_left. mnorm_goal. cbn [tref_val].
        thaw FR2. thaw FR.
        remember (f_gv F g_lenfix) as lf eqn:Elf. remember (f_gv F g_distfix) as df eqn:Edf.
        entailer!.
      * forward.
        unfold ty_sw. rewrite X. change (1 =? 0) with false. change (1 =? 1) with true.
        unfold Z_TREES. rewrite (proj2 (Z.eqb_neq _ _) H3). cbv iota.
        unfold loop_state_ty, ty_fixed.
        rewrite mem_rest_ty_mode, mem_rest_ty_tables.
        unfold m_have, m_left. mnorm_goal. cbn [tref_val].
        thaw FR2. thaw FR.
        remember (f_gv F g_lenfix) as lf eqn:Elf. remember (f_gv F g_distfix) as df eqn:Edf.
        entailer!.
    + forward. forward.
      unfold ty_sw. rewrite X. cbn [Z.eqb Pos.eqb]. unfold loop_state_ty. rewrite mem_rest_ty_mode.
      thaw FR. unfold m_have, m_left. mnorm_goal. entailer!.
    + destruct HF as (Hshs & Hhsh & Hgsh & Htsh).
      unfold strm_rep. remember (f_gv F _zcalloc) as za eqn:Eza. remember (f_gv F _zcfree) as zf eqn:Ezf.
      forward. forward. forward.
      unfold ty_sw. rewrite X. cbn [Z.eqb Pos.eqb].
      unfold loop_state_ty, set_bad. rewrite mem_rest_ty_mode, mem_rest_ty_msg.
      unfold strm_rep, m_have, m_left. mnorm_goal. cbn [msg_val msg_ident]. rewrite <- Eza, <- Ezf.
      thaw FR. entailer!.
    + pose proof (ty_sw_leave (f_flush F) m2 HL2) as HL3.
      pose proof (ty_sw_hold (f_flush F) m2 WH2) as WH3.
      set (m3 := ty_sw (f_flush F) m2) in *. clearbody m3. clear FR.
      unfold loop_state_ty. abbreviate_semax.
      freeze [0;1;2;3;4;5;6;7;8] FR.
      forward_if.
      * forward.
        assert (L1: m_leave m3 = 1) by lia.
        unfold switch_ret_assert, case_post2. cbn [RA_break RA_normal].
        Exists m3. apply andp_right; [apply prop_right; rewrite E1; unfold ty_out; rewrite L1; reflexivity | ].
        thaw FR. rewrite loop_state_ty_eq. unfold loop_state_ty. entailer!.
      * assert (L1: m_leave m3 = 0) by (destruct HL3 as [L | L]; [exact L | ];
          match goal with X: Int.repr (m_leave m3) = Int.zero |- _ => rewrite L in X; discriminate end).
        match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx ?S))) _ _ =>
          apply semax_dowhile0 with (Q := PROPx [] (LOCALx (ty_locals F (dropbits 2 m3)) (SEPx S))) end.
        { unfold ty_locals. forward. forward.
          unfold dropbits, m_have, m_left. mnorm_goal.
          change (Int.unsigned (Int.repr 2)) with 2.
          rewrite long_shru_eq by lia. rewrite u32_repr.
          entailer!. }
        unfold ty_locals. abbreviate_semax. forward.
        unfold switch_ret_assert, case_post2. cbn [RA_break RA_normal].
        Exists (dropbits 2 m3).
        apply andp_right; [apply prop_right; rewrite E1; unfold ty_out; rewrite L1; reflexivity | ].
        thaw FR. rewrite loop_state_ty_eq. unfold loop_state_ty, dropbits.
        rewrite mem_rest_ty_bits, mem_rest_ty_hold.
        unfold m_have, m_left. mnorm_goal. entailer!.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* TYPE: flush Z_BLOCK / Z_TREES -> leave; else TYPEDO's statements with the mode still TYPE      *)

Lemma type5 {Espec: OracleKind} (F: frame) :
  frame_ok F -> Int.min_signed <= f_flush F <= Int.max_signed ->
  case_ok5 F Zlib.proof.inflate.Model.TYPE 11.
Proof.
  intros HF Hfl m HM HL [W W3].
  pose proof (stepf2_TYPE (f_flush F) lenfix_list distfix_list m HM) as E0.
  unfold c_TYPE in E0.
  set (b := orb (f_flush F =? Z_BLOCK) (f_flush F =? Z_TREES)) in E0.
  rewrite seq_split by lia.
  apply semax_seq with (Q := PROPx [b = false; in_ok (f_ib F) (m_inp m); out_ok (f_ob F) (m_aout m)]
                               (LOCALx (ty_locals F m) (SEPx [mem_rep F m; locals_rep F]))).
  - case_body_stmt.
    unfold loop_state. abbreviate_semax.
    forward_if (PROPx [in_ok (f_ib F) (m_inp m); out_ok (f_ob F) (m_aout m)] (LOCALx (temp _t'53 (Vint (Int.repr (Z.b2z b))) :: ty_locals F m)
                 (SEPx [mem_rep F m; locals_rep F]))).
    + forward. unfold switch_ret_assert, case_post2, ty_locals. cbn [RA_normal].
      entailer!. unfold b, Z_BLOCK. rewrite H. reflexivity.
    + forward. unfold switch_ret_assert, case_post2, ty_locals. cbn [RA_normal].
      entailer!. unfold b, Z_BLOCK, Z_TREES.
      rewrite (proj2 (Z.eqb_neq _ _) H). cbn [orb].
      destruct (Z.eq_dec (f_flush F) 6) as [E6 | E6].
      * rewrite E6. reflexivity.
      * rewrite (proj2 (Z.eqb_neq _ _) E6).
        destruct (zeq (Int.unsigned (Int.repr (f_flush F))) (Int.unsigned (Int.repr 6))) as [Z6 | Z6];
          [ | unfold Int.eq; rewrite zeq_false by exact Z6; reflexivity].
        exfalso. apply E6. apply repr_inj_signed; [rep_lia | rep_lia | ].
        rewrite <- (Int.repr_unsigned (Int.repr (f_flush F))), Z6, Int.repr_unsigned. reflexivity.
    + unfold ty_locals. forward_if.
      * destruct b; [ | discriminate].
        forward. forward.
        unfold switch_ret_assert, case_post2. cbn [RA_break RA_normal].
        Exists (set_leave m). apply andp_right; [apply prop_right; exact E0 | ].
        unfold loop_state. change (mem_rep F (set_leave m)) with (mem_rep F m).
        unfold set_leave. mnorm_goal. unfold m_have, m_left. entailer!.
      * forward. destruct b; [discriminate | ].
        unfold switch_ret_assert, case_post2, ty_locals. cbn [RA_normal].
        entailer!.
  - apply semax_extract_PROP. intros Hb. rewrite Hb in E0.
    apply (typedo5 F m m HF Hfl HL W E0).
Qed.

Lemma cases5_TY {Espec: OracleKind} (F: frame) : frame_ok5 F -> fixed_ok5 ->
  case_ok5 F Zlib.proof.inflate.Model.TYPE 11 /\ case_ok5 F TYPEDO 12.
Proof.
  intros [HF Hfl] _. split; [apply type5; auto | ].
  intros m HM HL [W W3]. apply (typedo5 F m m HF Hfl HL W).
  apply stepf2_TYPEDO; exact HM.
Qed.
