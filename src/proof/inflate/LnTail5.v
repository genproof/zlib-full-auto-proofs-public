(* case LEN (LnKit5.v): DROPBITS(here.bits), back, length and the outcomes LIT / TYPE / BAD / LENEXT (ln_tail_stmt) *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate.LnKit5.
Require Import Zlib.proof.inflate.MwfLemmas.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* ---------------------------------------------------------------------------------------------- *)
(* the model                                                                                      *)

(* after DROPBITS(here.bits), back += here.bits, length = here.val *)
Definition tl_m1 (h: entry) (m: mst) : mst :=
  upd_s (dropbits (e_bits h) (upd_s m (fun s => set_i_back s (i_back s + e_bits h))))
    (fun s => set_i_length s (e_val h)).

(* the machine entering LENEXT *)
Definition tl_lenext (h: entry) (m: mst) : mst :=
  set_mode (upd_s (tl_m1 h m) (fun s => set_i_extra s (Z.land (e_op h) 15))) LENEXT.

Lemma tl_lit: forall h m, e_op h = 0 -> ln_tail_m h m = IBrk (set_mode (tl_m1 h m) LIT).
Proof. intros h m E. unfold ln_tail_m. rewrite E. reflexivity. Qed.

Lemma tl_type: forall h m, e_op h <> 0 -> Z.land (e_op h) 32 <> 0 ->
  ln_tail_m h m = IBrk (set_mode (upd_s (tl_m1 h m) (fun s => set_i_back s (-1))) Model.TYPE).
Proof.
  intros h m E1 E2. unfold ln_tail_m. cbv zeta.
  rewrite (proj2 (Z.eqb_neq _ _) E1), (proj2 (Z.eqb_neq _ _) E2). reflexivity.
Qed.

Lemma tl_bad: forall h m, e_op h <> 0 -> Z.land (e_op h) 32 = 0 -> Z.land (e_op h) 64 <> 0 ->
  ln_tail_m h m = IBrk (set_bad (tl_m1 h m) M_ll_code).
Proof.
  intros h m E1 E2 E3. unfold ln_tail_m. cbv zeta.
  rewrite (proj2 (Z.eqb_neq _ _) E1), E2, (proj2 (Z.eqb_neq _ _) E3). reflexivity.
Qed.

Lemma tl_ext: forall h m, e_op h <> 0 -> Z.land (e_op h) 32 = 0 -> Z.land (e_op h) 64 = 0 ->
  ln_tail_m h m = c_LENEXT lenfix_list distfix_list (tl_lenext h m).
Proof.
  intros h m E1 E2 E3. unfold ln_tail_m. cbv zeta.
  rewrite (proj2 (Z.eqb_neq _ _) E1), E2, E3. reflexivity.
Qed.

(* a final LENS entry that is neither a literal, an end of block nor invalid: a length *)
Lemma tl_len_entry: forall h, final_ok LENS h -> e_op h <> 0 -> Z.land (e_op h) 32 = 0 -> Z.land (e_op h) 64 = 0 ->
  16 <= e_op h <= 21 /\ 3 <= e_val h <= 258.
Proof.
  intros h F E1 E2 E3.
  assert (F': (e_op h = 0 /\ 0 <= e_val h <= 255) \/ (16 <= e_op h <= 21 /\ 3 <= e_val h <= 258) \/
              e_op h = 96 \/ (Z.land (e_op h) 64 <> 0 /\ Z.land (e_op h) 48 = 0)) by exact F.
  destruct F' as [[? ?] | [? | [O96 | [C _]]]]; [lia | exact H | | congruence].
  rewrite O96 in E2. discriminate.
Qed.

Lemma tl_land15: forall x, 16 <= x <= 31 -> Z.land x 15 = x - 16.
Proof.
  intros x H. change 15 with (Z.ones 4). rewrite Z.land_ones by lia.
  symmetry. apply Z.mod_unique with (q := 1); [left; simpl; lia | simpl; lia].
Qed.

(* the fields length, extra, back written in mode LEN *)
Lemma mwf_upd_lbe: forall m x y z, mwf m -> m_mode m = LEN ->
  urange x -> 0 <= y <= 15 -> -1 <= z <= 1000 ->
  mwf (upd_s m (fun s => set_i_extra (set_i_length (set_i_back s z) x) y)).
Proof.
  intros m x y z W HM Hx Hy Hz.
  assert (Hne: forall P: Prop, i_mode (m_s m) = LENLENS \/ i_mode (m_s m) = CODELENS \/
               i_mode (m_s m) = LENEXT \/ i_mode (m_s m) = DISTEXT \/
               i_mode (m_s m) = MATCH \/ i_mode (m_s m) = DIST -> P).
  { intros P X. exfalso. unfold m_mode in HM. rewrite HM in X.
    unfold LENLENS, CODELENS, LEN, LENEXT, DIST, DISTEXT, MATCH in *. lia. }
  destruct W as [MD SW HW A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16].
  constructor; cbn [upd_s set_m_s m_s m_h m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave
                    m_adler m_msg m_tin m_tout m_snx m_sow]; try assumption.
  - destruct MD as [M1 M2 M3 M4 M5 M6 M7 M8 M9].
    constructor; cbn [i_mode set_i_length set_i_extra set_i_back]; try (intros X; apply Hne; tauto).
    + intros X. exact (M3 X).
    + repeat split; intros X; apply Hne; tauto.
  - destruct SW; constructor; cbn [set_i_length set_i_extra set_i_back i_mode i_last i_wrap i_havedict i_flags
      i_dmax i_check i_total i_head i_wbits i_wsize i_whave i_wnext i_win i_wdata i_hold i_bits i_length i_offset
      i_extra i_lencode i_distcode i_lenbits i_distbits i_ncode i_nlen i_ndist i_have i_next i_lens i_codes i_sane
      i_back i_was]; try assumption.
Qed.

Lemma tl_lenext_eq: forall h m,
  tl_lenext h m =
  set_mode (upd_s (dropbits (e_bits h) m)
    (fun s => set_i_extra (set_i_length (set_i_back s (i_back (m_s m) + e_bits h)) (e_val h)) (Z.land (e_op h) 15)))
    LENEXT.
Proof. reflexivity. Qed.

Lemma mwf3_tl_lenext: forall h m,
  mwf3 m -> m_mode m = LEN -> entry_ok h -> 0 <= i_back (m_s m) -> i_back (m_s m) + e_bits h <= 15 ->
  e_bits h <= m_bits m -> 16 <= e_op h <= 21 -> 3 <= e_val h <= 258 ->
  mwf3 (tl_lenext h m).
Proof.
  intros h m [W W3] HM EO B0 B1 B2 OP VL.
  destruct EO as (EO1 & EO2 & EO3).
  assert (D: decode_mode (i_mode (m_s m))).
  { change (i_mode (m_s m)) with (m_mode m). rewrite HM. unfold decode_mode. auto. }
  destruct (md_tables _ (mw_md _ W) D) as [TL TD].
  pose proof (s3_len _ W3 D) as XL.
  assert (O: m_out m = m_aout m).
  { apply mwf_out_eq; [exact W | | | ]; rewrite HM; unfold LEN, LENGTH, DONE, BAD; lia. }
  assert (Wd: mwf (dropbits (e_bits h) m)) by (apply mwf_dropbits; [exact W | lia]).
  assert (Wu: mwf (upd_s (dropbits (e_bits h) m)
    (fun s => set_i_extra (set_i_length (set_i_back s (i_back (m_s m) + e_bits h)) (e_val h)) (Z.land (e_op h) 15)))).
  { apply mwf_upd_lbe; [exact Wd | exact HM | unfold urange; rep_lia | | lia].
    rewrite tl_land15 by lia. lia. }
  rewrite tl_lenext_eq. split.
  - apply (mwf_set_mode _ LENEXT Wu); cbn [upd_s set_m_s m_s dropbits set_m_hold set_m_bits
      set_i_extra set_i_length set_i_back i_ncode i_have i_nlen i_ndist i_lens i_lencode i_lenbits i_distcode
      i_distbits i_extra i_length i_offset i_back].
    + unfold HEAD, SYNC, LENEXT; lia.
    + intros X; unfold LENEXT, LENLENS in X; lia.
    + intros X; unfold LENEXT, CODELENS in X; lia.
    + intros _. split; [exact TL | exact TD].
    + intros _. rewrite tl_land15 by lia. lia.
    + intros X; unfold LENEXT, DISTEXT in X; lia.
    + intros X; unfold LENEXT, MATCH in X; lia.
    + intros _. lia.
    + intros [X | X]; unfold LENEXT, DISTEXT, MATCH in X; lia.
    + intros _. lia.
    + intros X; unfold LENEXT, DIST in X; lia.
    + intros X; unfold LENEXT, DISTEXT in X; lia.
    + left. exact O.
  - constructor; cbn [upd_s set_m_s m_s dropbits set_m_hold set_m_bits set_mode
      set_i_mode set_i_extra set_i_length set_i_back i_mode i_length i_offset i_lencode i_lenbits].
    + intros X; unfold LENEXT, HEAD in X; lia.
    + intros _. exact XL.
    + intros _. lia.
    + intros X; unfold LENEXT, DISTEXT in X; lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the memory with the fields mode, length, extra, back and the stream apart                      *)

Definition state_rest4 (gv: globals) (sp strmp headp winp: val) (s: istate) : mpred :=
  field_at Ews t_state (DOT _strm) strmp sp *
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
  field_at Ews t_state (DOT _offset) (zv (i_offset s)) sp *
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

Lemma pull4_35: forall a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35: mpred,
  a1 * a2 * a3 * a4 * a5 * a6 * a7 * a8 * a9 * a10 * a11 * a12 * a13 * a14 * a15 * a16 * a17 * a18 * a19 * a20 * a21 * a22 * a23 * a24 * a25 * a26 * a27 * a28 * a29 * a30 * a31 * a32 * a33 * a34 * a35 = a2 * a18 * a20 * a34 * (a1 * a3 * a4 * a5 * a6 * a7 * a8 * a9 * a10 * a11 * a12 * a13 * a14 * a15 * a16 * a17 * a19 * a21 * a22 * a23 * a24 * a25 * a26 * a27 * a28 * a29 * a30 * a31 * a32 * a33 * a35).
Proof. intros. apply pred_ext; cancel. Qed.

Lemma state_rep_pull4: forall gv sp strmp headp winp s,
  state_rep gv sp strmp headp winp s =
  field_at Ews t_state (DOT _mode) (zv (i_mode s)) sp * field_at Ews t_state (DOT _length) (zv (i_length s)) sp *
  field_at Ews t_state (DOT _extra) (zv (i_extra s)) sp * field_at Ews t_state (DOT _back) (zv (i_back s)) sp *
  state_rest4 gv sp strmp headp winp s.
Proof. intros. unfold state_rep, state_rest4. apply pull4_35. Qed.

Definition tl_strm (F: frame) (m: mst) (msg: val) : mpred :=
  strm_rep (f_gv F) (f_shs F) (f_strmp F)
    (in_ptr (f_ib F) (m_snx m)) (zv (Zlength (m_inp m) - m_snx m)) (m_tin m)
    (out_ptr (f_ob F) (m_sow m)) (zv (m_aout m - m_sow m)) (m_tout m)
    msg (f_sp F) (f_dt F) (m_adler m) (f_vres F).

Definition mem_rep_t (F: frame) (m: mst) : mpred :=
  state_rest4 (f_gv F) (f_sp F) (f_strmp F) (f_headp F) (f_winp F) (m_s m) *
  win_rep (f_winp F) (m_s m) *
  head_part F m *
  in_rep (f_ib F) *
  out_rep (f_ob F) (m_ow m) *
  tables_rep (f_gsh F) (f_gv F) *
  crc_table_at (f_tsh F) (f_gv F).

Lemma mem_rep_tsplit: forall F m,
  mem_rep F m =
  field_at Ews t_state (DOT _mode) (zv (i_mode (m_s m))) (f_sp F) *
  field_at Ews t_state (DOT _length) (zv (i_length (m_s m))) (f_sp F) *
  field_at Ews t_state (DOT _extra) (zv (i_extra (m_s m))) (f_sp F) *
  field_at Ews t_state (DOT _back) (zv (i_back (m_s m))) (f_sp F) *
  tl_strm F m (msg_val (f_gv F) (m_msg m)) * mem_rep_t F m.
Proof.
  intros. unfold mem_rep, mem_rep_t, tl_strm. rewrite state_rep_pull4.
  apply pred_ext; cancel.
Qed.

(* ls_hl with the locals of m, the memory of mb but the four fields and the message *)
Definition ls_t (F: frame) (m mb: mst) (vmd vln vex vbk vmsg: val) (hv lv: reptype t_code) : environ -> mpred :=
  PROPx [in_ok (f_ib F) (m_inp m); out_ok (f_ob F) (m_aout m)]
  (LOCALx (ln_locals F m)
  (SEPx [field_at Ews t_state (DOT _mode) vmd (f_sp F); field_at Ews t_state (DOT _length) vln (f_sp F);
         field_at Ews t_state (DOT _extra) vex (f_sp F); field_at Ews t_state (DOT _back) vbk (f_sp F);
         tl_strm F mb vmsg; mem_rep_t F mb;
         data_at Tsh t_code hv (f_vhere F); data_at Tsh t_code lv (f_vlast F);
         data_at_ Tsh (tarray tuchar 4) (f_vhbuf F)])).

Lemma ls_hl_t: forall F m hv lv,
  ls_hl F m hv lv = ls_t F m m (zv (i_mode (m_s m))) (zv (i_length (m_s m))) (zv (i_extra (m_s m)))
                      (zv (i_back (m_s m))) (msg_val (f_gv F) (m_msg m)) hv lv.
Proof.
  intros. unfold ls_hl, ls_t. f_equal. f_equal.
  unfold SEPx. extensionality rho. cbn [fold_right_sepcon]. rewrite mem_rep_tsplit.
  rewrite !sepcon_emp, !sepcon_assoc. reflexivity.
Qed.

Lemma tl_semax_dowhile0 {Espec: OracleKind} (Delta: tycontext) (P Q: environ -> mpred) (c rest: statement)
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

Lemma tl_long_shru_eq: forall h n, 0 <= h <= Int64.max_unsigned -> 0 <= n < 64 ->
  Int64.shru (Int64.repr h) (Int64.repr n) = Int64.repr (Z.shiftr h n).
Proof.
  intros h n Hh Hn. unfold Int64.shru.
  rewrite (Int64.unsigned_repr h) by lia. rewrite (Int64.unsigned_repr n) by rep_lia. reflexivity.
Qed.

Lemma tl_u32_repr: forall x, Int.repr (u32 x) = Int.repr x.
Proof.
  intros. unfold u32. apply Int.eqm_samerepr. unfold Int.eqm. apply Zbits.eqmod_sym, Zbits.eqmod_mod.
  reflexivity.
Qed.

Lemma ls_t_loop_state: forall F m hv lv,
  ls_t F m m (zv (i_mode (m_s m))) (zv (i_length (m_s m))) (zv (i_extra (m_s m)))
    (zv (i_back (m_s m))) (msg_val (f_gv F) (m_msg m)) hv lv |-- loop_state F m.
Proof. intros. rewrite <- ls_hl_t. apply ls_hl_loop_state. Qed.

Ltac fix_break R HR :=
  match goal with |- context [RA_break ?X] =>
    replace (RA_break X) with (RA_break R) by (destruct R; reflexivity) end;
  rewrite HR.

Lemma tl_land_range: forall a b, 0 <= a <= 255 -> 0 <= b -> 0 <= Z.land a b <= 255.
Proof.
  intros a b Ha Hb. assert (N: 0 <= Z.land a b) by (apply Z.land_nonneg; lia). split; [exact N | ].
  destruct (Z.eq_dec (Z.land a b) 0) as [Z0 | Z0]; [lia | ].
  destruct (Z.eq_dec a 0) as [A0 | A0]; [subst a; rewrite Z.land_0_l in Z0; congruence | ].
  pose proof (Z.log2_land a b ltac:(lia) ltac:(lia)) as L.
  assert (La: Z.log2 a < 8) by (apply Z.log2_lt_pow2; [lia | simpl; lia]).
  assert (Z.land a b < 2 ^ 8) by (apply Z.log2_lt_pow2; lia).
  simpl in *; lia.
Qed.

Lemma tl_and_repr: forall a b, 0 <= a <= 255 -> 0 <= b <= 255 ->
  Int.and (Int.repr a) (Int.repr b) = Int.repr (Z.land a b).
Proof.
  intros a b Ha Hb. unfold Int.and. rewrite !Int.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma tl_and_zero: forall a b, 0 <= a <= 255 -> 0 <= b <= 255 ->
  (Int.and (Int.repr a) (Int.repr b) = Int.zero <-> Z.land a b = 0).
Proof.
  intros a b Ha Hb. rewrite tl_and_repr by lia. pose proof (tl_land_range a b Ha ltac:(lia)).
  split; intro X; [ | rewrite X; reflexivity].
  apply repr_inj_unsigned in X; rep_lia.
Qed.

Ltac tl_unfold := cbv beta iota zeta delta [ln_tail ln_s3 ln_s2 ln_s1 ln_slow ln_body case_body inflate_LS
  find_switch f_inflate fn_body ls_drop].

Lemma ln_tail_ok : ln_tail_stmt.
Proof.
  intros Espec F m0 m h lv R HF W3 HM HL EO FO B0 B1 B2 E HR HN.
  destruct HF as [[Hshs [Hhsh [Hgsh Htsh]]] Hfl].
  pose proof (mwf3_mwf _ W3) as W.
  pose proof (mw_bits _ W) as WB. pose proof (mw_hold _ W) as WH. unfold lrange in WH.
  pose proof (sw_back _ (mw_s _ W)) as WK.
  pose proof EO as (EO1 & EO2 & EO3).
  rewrite ls_hl_t. tl_unfold. unfold ls_t. abbreviate_semax.
  match goal with |- semax _ (PROPx ?P (LOCALx _ (SEPx ?S))) _ _ =>
    apply tl_semax_dowhile0 with (Q := PROPx P (LOCALx (ln_locals F (dropbits (e_bits h) m)) (SEPx S))) end.
  { unfold ln_locals, ent. forward. { entailer!. rep_lia. }
    forward. { entailer!. change (Int.unsigned Int64.iwordsize') with 64. lia. }
    forward. forward.
    unfold dropbits, m_have, m_left. mnorm_goal.
    entailer!. split; [rewrite tl_long_shru_eq by rep_lia; reflexivity | rewrite tl_u32_repr; reflexivity]. }
  unfold ln_locals, ent. abbreviate_semax.
  Ltac tl_fw := forward; try (entailer!; rep_lia).
  tl_fw. tl_fw. tl_fw. tl_fw. tl_fw. tl_fw.
  rewrite add_repr.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?S))) _ _ =>
    forward_if (PROPx (@cons Prop (e_op h <> 0) P) (LOCALx Q (SEPx S))) end.
  { forward. forward.
    fix_break R HR. unfold case_post2, RA_normal.
    Exists (set_mode (tl_m1 h m) LIT).
    apply andp_right; [apply prop_right; rewrite E; apply tl_lit; exact H1 | ].
    eapply derives_trans; [ | apply ls_t_loop_state]. unfold ls_t.
    change (mem_rep_t F (set_mode (tl_m1 h m) LIT)) with (mem_rep_t F m).
    change (tl_strm F (set_mode (tl_m1 h m) LIT)) with (tl_strm F m).
    unfold ln_locals, tl_m1, LIT. mnorm_goal. entailer!. }
  { forward. destruct R as [r1 r2 r3 r4]. cbn [RA_normal]. entailer!. }
  Intros. rename H1 into O0. abbreviate_semax.
  tl_fw.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?S))) _ _ =>
    forward_if (PROPx (@cons Prop (Z.land (e_op h) 32 = 0) P) (LOCALx Q (SEPx S))) end.
  { forward. forward. forward.
    fix_break R HR. unfold case_post2, RA_normal.
    Exists (set_mode (upd_s (tl_m1 h m) (fun s => set_i_back s (-1))) Model.TYPE).
    rewrite !Int.unsigned_repr in H1' by rep_lia.
    apply andp_right; [apply prop_right; rewrite E; apply tl_type; assumption | ].
    eapply derives_trans; [ | apply ls_t_loop_state]. unfold ls_t.
    change (mem_rep_t F (set_mode (upd_s (tl_m1 h m) (fun s => set_i_back s (-1))) Model.TYPE)) with (mem_rep_t F m).
    change (tl_strm F (set_mode (upd_s (tl_m1 h m) (fun s => set_i_back s (-1))) Model.TYPE)) with (tl_strm F m).
    change (Int.neg (Int.repr 1)) with (Int.repr (-1)).
    unfold ln_locals, tl_m1, Model.TYPE. mnorm_goal. entailer!. }
  { forward. destruct R as [r1 r2 r3 r4]. cbn [RA_normal]. entailer!.
    first [apply (tl_and_zero (e_op h) 32); [lia | lia | assumption]
          | rewrite !Int.unsigned_repr in * by rep_lia; assumption]. }
  Intros. rename H1 into O32. abbreviate_semax.
  tl_fw.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?S))) _ _ =>
    forward_if (PROPx (@cons Prop (Z.land (e_op h) 64 = 0) P) (LOCALx Q (SEPx S))) end.
  { unfold tl_strm, strm_rep.
    remember (f_gv F _zcalloc) as zca eqn:Hzca. remember (f_gv F _zcfree) as zcf eqn:Hzcf.
    forward. forward. forward.
    rewrite !Int.unsigned_repr in H1' by rep_lia.
    fix_break R HR. unfold case_post2, RA_normal.
    Exists (set_bad (tl_m1 h m) M_ll_code).
    apply andp_right; [apply prop_right; rewrite E; apply tl_bad; assumption | ].
    eapply derives_trans; [ | apply ls_t_loop_state]. unfold ls_t.
    change (mem_rep_t F (set_bad (tl_m1 h m) M_ll_code)) with (mem_rep_t F m).
    unfold tl_strm, strm_rep. rewrite <- Hzca, <- Hzcf.
    unfold ln_locals, tl_m1, BAD. mnorm_goal. cbn [msg_val msg_ident]. entailer!. }
  { forward. destruct R as [r1 r2 r3 r4]. cbn [RA_normal]. entailer!.
    first [apply (tl_and_zero (e_op h) 64); [lia | lia | assumption]
          | rewrite !Int.unsigned_repr in * by rep_lia; assumption]. }
  Intros. rename H1 into O64. abbreviate_semax.
  destruct (tl_len_entry h FO O0 O32 O64) as [OP VL].
  tl_fw. tl_fw.
  unfold abbreviate in POSTCONDITION; subst POSTCONDITION.
  eapply semax_post_flipped'; [forward; apply andp_left2, derives_refl | ].
  rewrite HN. unfold fall_post5.
  Exists (tl_lenext h m).
  rewrite tl_and_repr by lia.
  apply andp_right.
  { apply prop_right. split; [ | split; [reflexivity | split; [exact HL | ]]].
    - rewrite E, tl_ext by assumption. symmetry. apply stepf2_LENEXT. reflexivity.
    - apply mwf3_tl_lenext; auto. }
  eapply derives_trans; [ | apply ls_t_loop_state]. unfold ls_t.
  change (mem_rep_t F (tl_lenext h m)) with (mem_rep_t F m).
  change (tl_strm F (tl_lenext h m)) with (tl_strm F m).
  unfold ln_locals, tl_lenext, tl_m1, LENEXT. mnorm_goal. entailer!.
Qed.
