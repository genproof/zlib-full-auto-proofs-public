(* case DISTEXT: offset += BITS(extra); DROPBITS(extra); back += extra; (dx_rest_ok), with the fields extra, offset,
   back apart from the rest of the memory (loop_state_dx) *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate.DmKit5.
Require Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Definition state_rep_dx (gv: globals) (sp strmp headp winp: val) (s: istate) : mpred :=
  field_at Ews t_state (DOT _strm) strmp sp *
  field_at Ews t_state (DOT _mode) (zv (i_mode s)) sp *
  field_at Ews t_state (DOT _last) (zv (i_last s)) sp *
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
  field_at Ews t_state (DOT _was) (zv (i_was s)) sp.

Lemma sepcon_dx_35: forall a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35: mpred,
  a1 * a2 * a3 * a4 * a5 * a6 * a7 * a8 * a9 * a10 * a11 * a12 * a13 * a14 * a15 * a16 * a17 * a18 * a19 * a20 * a21 * a22 * a23 * a24 * a25 * a26 * a27 * a28 * a29 * a30 * a31 * a32 * a33 * a34 * a35 =
  a20 * a19 * a34 * (a1 * a2 * a3 * a4 * a5 * a6 * a7 * a8 * a9 * a10 * a11 * a12 * a13 * a14 * a15 * a16 * a17 * a18 * a21 * a22 * a23 * a24 * a25 * a26 * a27 * a28 * a29 * a30 * a31 * a32 * a33 * a35).
Proof. intros. apply pred_ext; cancel. Qed.

Lemma state_rep_dxsplit: forall gv sp strmp headp winp s,
  state_rep gv sp strmp headp winp s =
  field_at Ews t_state (DOT _extra) (zv (i_extra s)) sp * field_at Ews t_state (DOT _offset) (zv (i_offset s)) sp *
  field_at Ews t_state (DOT _back) (zv (i_back s)) sp * state_rep_dx gv sp strmp headp winp s.
Proof. intros. unfold state_rep, state_rep_dx. apply sepcon_dx_35. Qed.

Definition mem_rep_dx (F: frame) (m: mst) : mpred :=
  state_rep_dx (f_gv F) (f_sp F) (f_strmp F) (f_headp F) (f_winp F) (m_s m) *
  win_rep (f_winp F) (m_s m) *
  head_part F m *
  strm_rep (f_gv F) (f_shs F) (f_strmp F)
    (in_ptr (f_ib F) (m_snx m)) (zv (Zlength (m_inp m) - m_snx m)) (m_tin m)
    (out_ptr (f_ob F) (m_sow m)) (zv (m_aout m - m_sow m)) (m_tout m)
    (msg_val (f_gv F) (m_msg m)) (f_sp F) (f_dt F) (m_adler m) (f_vres F) *
  in_rep (f_ib F) *
  out_rep (f_ob F) (m_ow m) *
  tables_rep (f_gsh F) (f_gv F) *
  Zlib.proof.crc32.Spec.crc_table_at (f_tsh F) (f_gv F).

Definition loop_state_dx (F: frame) (m: mst) : environ -> mpred :=
  PROP (in_ok (f_ib F) (m_inp m); out_ok (f_ob F) (m_aout m))
  LOCAL (temp _strm (f_strmp F); temp _flush (zv (f_flush F)); temp _state (f_sp F);
         temp _next (in_ptr (f_ib F) (m_nx m)); temp _put (out_ptr (f_ob F) (Zlength (m_ow m)));
         temp _have (zv (m_have m)); temp _left (zv (m_left m)); temp _hold (lv (m_hold m));
         temp _bits (zv (m_bits m)); temp _in (zv (m_in m)); temp _out (zv (m_out m));
         temp _ret (zv (m_ret m)); temp _leave (zv (m_leave m));
         lvar _here t_code (f_vhere F); lvar _last t_code (f_vlast F);
         lvar _hbuf (tarray tuchar 4) (f_vhbuf F); gvars (f_gv F))
  SEP (field_at Ews t_state (DOT _extra) (zv (i_extra (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _offset) (zv (i_offset (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _back) (zv (i_back (m_s m))) (f_sp F);
       mem_rep_dx F m; locals_rep F).

Lemma loop_state_dx_eq: forall F m, loop_state F m = loop_state_dx F m.
Proof.
  intros. unfold loop_state, loop_state_dx. f_equal. f_equal.
  unfold SEPx. extensionality rho. cbn [fold_right_sepcon].
  unfold mem_rep. rewrite state_rep_dxsplit. unfold mem_rep_dx.
  generalize (field_at Ews t_state (DOT _extra) (zv (i_extra (m_s m))) (f_sp F)),
    (field_at Ews t_state (DOT _offset) (zv (i_offset (m_s m))) (f_sp F)),
    (field_at Ews t_state (DOT _back) (zv (i_back (m_s m))) (f_sp F)),
    (state_rep_dx (f_gv F) (f_sp F) (f_strmp F) (f_headp F) (f_winp F) (m_s m)).
  intros. apply pred_ext; cancel.
Qed.

(* the bit operations (as in CaseSTORED5.v) *)
Lemma dx_int_and_ones: forall b k, 0 <= b -> 0 <= k <= 32 ->
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

Lemma dx_long_shru_eq: forall h n, 0 <= h <= Int64.max_unsigned -> 0 <= n < 64 ->
  Int64.shru (Int64.repr h) (Int64.repr n) = Int64.repr (Z.shiftr h n).
Proof.
  intros h n Hh Hn. unfold Int64.shru.
  rewrite (Int64.unsigned_repr h) by lia. rewrite (Int64.unsigned_repr n) by rep_lia. reflexivity.
Qed.

Lemma dx_shl1: forall k, 0 <= k < 32 -> Int.shl (Int.repr 1) (Int.repr k) = Int.repr (2 ^ k).
Proof.
  intros k Hk. rewrite Int.shl_mul_two_p. rewrite Int.unsigned_repr by rep_lia.
  rewrite two_p_equiv. rewrite Int.mul_commut, Int.mul_one. reflexivity.
Qed.

(* do { c } while (0) followed by rest *)
Lemma dx_semax_dowhile0 {Espec: OracleKind} (Delta: tycontext) (P Q: environ -> mpred) (c rest: statement)
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

(* the machine after state->offset += BITS(extra); DROPBITS(extra); state->back += extra; *)
Definition dx_m (m: mst) : mst :=
  let ex := i_extra (m_s m) in
  let off := u32 (i_offset (m_s m) + bitsn m ex) in
  dropbits ex (upd_s m (fun s => set_i_offset (set_i_back s (i_back s + ex)) off)).

Lemma dx_rest_ok {Espec: OracleKind} (F: frame) (m: mst):
  mwf m -> m_mode m = DISTEXT -> i_extra (m_s m) <= m_bits m -> i_offset (m_s m) <= 32768 ->
  semax Delta_cases5 (loop_state F m) dx_rest (normal_ret_assert (loop_state F (dx_m m))).
Proof.
  intros W HM HB HO.
  pose proof (md_distext _ (mw_md _ W) HM) as HX. pose proof (sw_extra _ (mw_s _ W)) as HX0.
  pose proof (proj2 (proj2 (md_back _ (mw_md _ W))) HM) as HBK. pose proof (sw_back _ (mw_s _ W)) as HBK0.
  pose proof (sw_offset _ (mw_s _ W)) as HO0. pose proof (mw_hold _ W) as HH. pose proof (mw_bits _ W) as HB0.
  unfold urange, lrange in *.
  set (ex := i_extra (m_s m)) in *.
  assert (P13: 2 ^ ex <= 2 ^ 13) by (apply Z.pow_le_mono_r; lia). change (2 ^ 13) with 8192 in P13.
  assert (P0: 0 < 2 ^ ex) by (apply Z.pow_pos_nonneg; lia).
  pose proof (Z.mod_pos_bound (m_hold m) (2 ^ ex) P0) as HMOD.
  rewrite !loop_state_dx_eq. unfold loop_state_dx.
  destruct F as [gv shs strmp sp headp winp hsh xb nb cb ib ob gsh tsh dt vres vhere vlast vhbuf flush].
  frame_simpl.
  cbv beta iota zeta delta [dx_rest dx_ext dx_head dx_body case_body inflate_LS find_switch f_inflate fn_body ls_drop].
  abbreviate_semax.
  assert (OV: Int.add (Int.repr (i_offset (m_s m)))
                (Int.and (Int.repr (Int64.Z_mod_modulus (m_hold m)))
                   (Int.sub (Int.shl (Int.repr 1) (Int.repr ex)) (Int.repr 1)))
              = Int.repr (u32 (i_offset (m_s m) + bitsn m ex))).
  { rewrite Int64.Z_mod_modulus_eq, Z.mod_small by rep_lia.
    rewrite dx_shl1 by lia. rewrite sub_repr. rewrite dx_int_and_ones by lia. rewrite add_repr.
    unfold u32, bitsn. rewrite (Z.mod_small (_ + _)) by rep_lia. reflexivity. }
  assert (MR: mem_rep_dx (Fr gv shs strmp sp headp winp hsh xb nb cb ib ob gsh tsh dt vres vhere vlast vhbuf flush)
                (dx_m m) =
              mem_rep_dx (Fr gv shs strmp sp headp winp hsh xb nb cb ib ob gsh tsh dt vres vhere vlast vhbuf flush) m)
    by reflexivity.
  forward. forward.
  forward.
  { entailer!. change (Int.unsigned Int.iwordsize) with 32. lia. }
  fold ex. rewrite OV.
  apply dx_semax_dowhile0 with
    (Q := loop_state_dx (Fr gv shs strmp sp headp winp hsh xb nb cb ib ob gsh tsh dt vres vhere vlast vhbuf flush)
            (dropbits ex (upd_s m (fun s => set_i_offset s (u32 (i_offset (m_s m) + bitsn m ex)))))).
  { forward. forward.
    { entailer!. change (Int.unsigned Int64.iwordsize') with 64. lia. }
    forward. forward.
    unfold loop_state_dx, dropbits, upd_s. frame_simpl.
    cbn [m_s set_m_s set_m_hold set_m_bits m_hold m_bits m_nx m_ow m_inp
      m_aout m_in m_out m_ret m_leave i_extra i_offset i_back set_i_offset].
    rewrite Int.unsigned_repr by rep_lia. rewrite dx_long_shru_eq by lia.
    rewrite sub_repr.
    entailer!.
    all: try (unfold u32; rewrite (Z.mod_small (m_bits m - ex)) by lia; reflexivity).
    all: try apply derives_refl. }
  unfold loop_state_dx, dropbits, upd_s. frame_simpl.
  cbn [m_s set_m_s set_m_hold set_m_bits m_hold m_bits m_nx m_ow m_inp
      m_aout m_in m_out m_ret m_leave i_extra i_offset i_back set_i_offset].
  abbreviate_semax.
  forward. forward. forward.
  unfold dx_m, dropbits, upd_s. cbn [m_s set_m_s set_m_hold set_m_bits m_hold m_bits m_nx m_ow m_inp
    m_aout m_in m_out m_ret m_leave i_extra i_offset i_back set_i_offset set_i_back].
  entailer!. apply derives_refl.
Qed.
