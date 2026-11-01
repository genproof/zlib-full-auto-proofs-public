(* DIST: the tail (DROPBITS(here.bits), back, BAD, offset, extra, DISTEXT) (part of the cases LENEXT/DIST, Cases5_LD.v; definitions and statements in LdKit5.v) *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate.LdKit5.
Require Import Zlib.proof.inflate.MwfLemmas.
Require Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* ---------------------------------------------------------------------------------------------- *)
(* the model                                                                                      *)

(* after DROPBITS(here.bits), back += here.bits *)
Definition dt_m1 (h: entry) (m: mst) : mst :=
  dropbits (e_bits h) (upd_s m (fun s => set_i_back s (i_back s + e_bits h))).

(* the machine entering DISTEXT *)
Definition dt_distext (h: entry) (m: mst) : mst :=
  set_mode (upd_s (dt_m1 h m) (fun s => set_i_extra (set_i_offset s (e_val h)) (Z.land (e_op h) 15))) DISTEXT.

Lemma dt_bad: forall h m, Z.land (e_op h) 64 <> 0 ->
  ds_tail_m h m = IBrk (set_bad (dt_m1 h m) M_d_code).
Proof.
  intros h m E. unfold ds_tail_m. cbv zeta. rewrite (proj2 (Z.eqb_neq _ _) E). reflexivity.
Qed.

Lemma dt_ext: forall h m, Z.land (e_op h) 64 = 0 ->
  ds_tail_m h m = c_DISTEXT (dt_distext h m).
Proof. intros h m E. unfold ds_tail_m. cbv zeta. rewrite E. reflexivity. Qed.

(* a final DISTS entry that is not invalid: a distance *)
Lemma dt_dist_entry: forall h, final_ok DISTS h -> Z.land (e_op h) 64 = 0 ->
  16 <= e_op h <= 29 /\ 1 <= e_val h <= 32768.
Proof.
  intros h F E.
  assert (F': (16 <= e_op h <= 29 /\ 1 <= e_val h <= 32768) \/
              (Z.land (e_op h) 64 <> 0 /\ Z.land (e_op h) 48 = 0)) by exact F.
  destruct F' as [H | [C _]]; [exact H | congruence].
Qed.

Lemma dt_land15: forall x, 16 <= x <= 31 -> Z.land x 15 = x - 16.
Proof.
  intros x H. change 15 with (Z.ones 4). rewrite Z.land_ones by lia.
  symmetry. apply Z.mod_unique with (q := 1); [left; simpl; lia | simpl; lia].
Qed.

(* the fields offset, extra, back written in mode DIST, then mode DISTEXT *)
Lemma mwf3_upd_dext: forall m x y z, mwf3 m -> m_mode m = DIST ->
  1 <= x <= 32768 -> 0 <= y <= 13 -> -1 <= z <= 35 ->
  mwf3 (set_mode (upd_s m (fun s => set_i_extra (set_i_offset (set_i_back s z) x) y)) DISTEXT).
Proof.
  intros m x y z [W W3] HM Hx Hy Hz.
  assert (D: decode_mode (i_mode (m_s m))).
  { change (i_mode (m_s m)) with (m_mode m). rewrite HM. unfold decode_mode. auto 10. }
  assert (O: m_out m = m_aout m).
  { apply mwf_out_eq; [exact W | | | ]; rewrite HM; unfold DIST, LENGTH, DONE, BAD; lia. }
  pose proof (md_length _ (mw_md _ W) (or_intror (or_introl HM))) as LN.
  destruct W as [MD SW HW A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16].
  pose proof (md_tables _ MD D) as TB.
  pose proof (s3_len _ W3 D) as XL.
  split.
  - constructor; cbn [upd_s set_mode set_m_s m_s m_h m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret
                      m_leave m_adler m_msg m_tin m_tout m_snx m_sow m_mode]; try assumption.
    + destruct MD as [M1 M2 M3 M4 M5 M6 M7 M8 M9].
      constructor; cbn [i_mode set_i_mode set_i_offset set_i_extra set_i_back i_extra i_offset i_back i_length];
        try (intros X; unfold DISTEXT, LENLENS, CODELENS, LENEXT, MATCH, DIST in X; lia).
      all: first [intros _; exact TB | intros _; exact LN | intros _; lia
                 | repeat split; intros X; unfold DISTEXT, LENEXT, DIST in X; lia].
    + destruct SW; constructor; cbn [set_i_mode set_i_offset set_i_extra set_i_back i_mode i_last i_wrap
        i_havedict i_flags i_dmax i_check i_total i_head i_wbits i_wsize i_whave i_wnext i_win i_wdata i_hold
        i_bits i_length i_offset i_extra i_lencode i_distcode i_lenbits i_distbits i_ncode i_nlen i_ndist i_have
        i_next i_lens i_codes i_sane i_back i_was]; try assumption; try (unfold urange; rep_lia); try lia.
      unfold DISTEXT, HEAD, SYNC; lia.
    + left. exact O.
  - constructor; cbn [upd_s set_mode set_m_s m_s set_i_mode set_i_offset set_i_extra set_i_back i_mode i_offset
      i_lencode i_lenbits].
    + intros X; unfold DISTEXT, HEAD in X; lia.
    + intros _. exact XL.
    + intros X; unfold DISTEXT, LENEXT in X; lia.
    + intros _. lia.
Qed.

Lemma dt_distext_eq: forall h b1 M,
  dt_distext h (ds_drop b1 M) =
  set_mode (upd_s (dropbits (e_bits h) (dropbits b1 M))
    (fun s => set_i_extra (set_i_offset (set_i_back s (i_back (m_s M) + b1 + e_bits h)) (e_val h))
                (Z.land (e_op h) 15))) DISTEXT.
Proof. reflexivity. Qed.

Lemma dt_u32_small: forall x, 0 <= x <= 39 -> u32 x = x.
Proof. intros x H. unfold u32. apply Z.mod_small. lia. Qed.

Lemma mwf3_dt_distext: forall h b1 M,
  mwf3 M -> m_mode M = DIST -> 0 <= b1 -> entry_ok h -> b1 + e_bits h <= 15 -> b1 + e_bits h <= m_bits M ->
  16 <= e_op h <= 29 -> 1 <= e_val h <= 32768 ->
  mwf3 (dt_distext h (ds_drop b1 M)).
Proof.
  intros h b1 M [W W3] HM B0 EO B1 B2 OP VL.
  destruct EO as (EO1 & EO2 & EO3).
  pose proof (mw_bits _ W) as WB.
  pose proof (sw_back _ (mw_s _ W)) as WK.
  pose proof (proj1 (proj2 (md_back _ (mw_md _ W))) HM) as BK.
  assert (W1: mwf (dropbits b1 M)) by (apply mwf_dropbits; [exact W | lia]).
  assert (W2: mwf (dropbits (e_bits h) (dropbits b1 M))).
  { apply mwf_dropbits; [exact W1 | ]. cbn [dropbits m_bits set_m_bits set_m_hold].
    rewrite dt_u32_small by lia. lia. }
  rewrite dt_distext_eq. apply mwf3_upd_dext.
  - split; [exact W2 | exact W3].
  - exact HM.
  - exact VL.
  - rewrite dt_land15 by lia. lia.
  - lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the memory with the fields mode, offset, extra, back and the stream apart                      *)

Definition state_restd (gv: globals) (sp strmp headp winp: val) (s: istate) : mpred :=
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

Lemma dt_pull4_35: forall a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35: mpred,
  a1 * a2 * a3 * a4 * a5 * a6 * a7 * a8 * a9 * a10 * a11 * a12 * a13 * a14 * a15 * a16 * a17 * a18 * a19 * a20 * a21 * a22 * a23 * a24 * a25 * a26 * a27 * a28 * a29 * a30 * a31 * a32 * a33 * a34 * a35 = a2 * a19 * a20 * a34 * (a1 * a3 * a4 * a5 * a6 * a7 * a8 * a9 * a10 * a11 * a12 * a13 * a14 * a15 * a16 * a17 * a18 * a21 * a22 * a23 * a24 * a25 * a26 * a27 * a28 * a29 * a30 * a31 * a32 * a33 * a35).
Proof. intros. apply pred_ext; cancel. Qed.

Lemma state_rep_pulld: forall gv sp strmp headp winp s,
  state_rep gv sp strmp headp winp s =
  field_at Ews t_state (DOT _mode) (zv (i_mode s)) sp * field_at Ews t_state (DOT _offset) (zv (i_offset s)) sp *
  field_at Ews t_state (DOT _extra) (zv (i_extra s)) sp * field_at Ews t_state (DOT _back) (zv (i_back s)) sp *
  state_restd gv sp strmp headp winp s.
Proof. intros. unfold state_rep, state_restd. apply dt_pull4_35. Qed.

Definition dt_strm (F: frame) (m: mst) (msg: val) : mpred :=
  strm_rep (f_gv F) (f_shs F) (f_strmp F)
    (in_ptr (f_ib F) (m_snx m)) (zv (Zlength (m_inp m) - m_snx m)) (m_tin m)
    (out_ptr (f_ob F) (m_sow m)) (zv (m_aout m - m_sow m)) (m_tout m)
    msg (f_sp F) (f_dt F) (m_adler m) (f_vres F).

Definition mem_rep_d (F: frame) (m: mst) : mpred :=
  state_restd (f_gv F) (f_sp F) (f_strmp F) (f_headp F) (f_winp F) (m_s m) *
  win_rep (f_winp F) (m_s m) *
  head_part F m *
  in_rep (f_ib F) *
  out_rep (f_ob F) (m_ow m) *
  tables_rep (f_gsh F) (f_gv F) *
  Zlib.proof.crc32.Spec.crc_table_at (f_tsh F) (f_gv F).

Lemma mem_rep_dsplit: forall F m,
  mem_rep F m =
  field_at Ews t_state (DOT _mode) (zv (i_mode (m_s m))) (f_sp F) *
  field_at Ews t_state (DOT _offset) (zv (i_offset (m_s m))) (f_sp F) *
  field_at Ews t_state (DOT _extra) (zv (i_extra (m_s m))) (f_sp F) *
  field_at Ews t_state (DOT _back) (zv (i_back (m_s m))) (f_sp F) *
  dt_strm F m (msg_val (f_gv F) (m_msg m)) * mem_rep_d F m.
Proof.
  intros. unfold mem_rep, mem_rep_d, dt_strm. rewrite state_rep_pulld.
  apply pred_ext; cancel.
Qed.

(* ld_hl with the locals of m, the memory of mb but the four fields and the message *)
Definition ld_t (F: frame) (m mb: mst) (vmd vof vex vbk vmsg: val) (hv lv: reptype t_code) : environ -> mpred :=
  PROPx [in_ok (f_ib F) (m_inp m); out_ok (f_ob F) (m_aout m)]
  (LOCALx (ld_locals F m)
  (SEPx [field_at Ews t_state (DOT _mode) vmd (f_sp F); field_at Ews t_state (DOT _offset) vof (f_sp F);
         field_at Ews t_state (DOT _extra) vex (f_sp F); field_at Ews t_state (DOT _back) vbk (f_sp F);
         dt_strm F mb vmsg; mem_rep_d F mb;
         data_at Tsh t_code hv (f_vhere F); data_at Tsh t_code lv (f_vlast F);
         data_at_ Tsh (tarray tuchar 4) (f_vhbuf F)])).

Lemma ld_hl_t: forall F m hv lv,
  ld_hl F m hv lv = ld_t F m m (zv (i_mode (m_s m))) (zv (i_offset (m_s m))) (zv (i_extra (m_s m)))
                      (zv (i_back (m_s m))) (msg_val (f_gv F) (m_msg m)) hv lv.
Proof.
  intros. unfold ld_hl, ld_t. f_equal. f_equal.
  unfold SEPx. extensionality rho. cbn [fold_right_sepcon]. rewrite mem_rep_dsplit.
  rewrite !sepcon_emp, !sepcon_assoc. reflexivity.
Qed.

Lemma ld_t_loop_state: forall F m hv lv,
  ld_t F m m (zv (i_mode (m_s m))) (zv (i_offset (m_s m))) (zv (i_extra (m_s m)))
    (zv (i_back (m_s m))) (msg_val (f_gv F) (m_msg m)) hv lv |-- loop_state F m.
Proof. intros. rewrite <- ld_hl_t. apply ld_hl_loop_state. Qed.

Lemma dt_semax_dowhile0 {Espec: OracleKind} (Delta: tycontext) (P Q: environ -> mpred) (c rest: statement)
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

Lemma dt_long_shru_eq: forall h n, 0 <= h <= Int64.max_unsigned -> 0 <= n < 64 ->
  Int64.shru (Int64.repr h) (Int64.repr n) = Int64.repr (Z.shiftr h n).
Proof.
  intros h n Hh Hn. unfold Int64.shru.
  rewrite (Int64.unsigned_repr h) by lia. rewrite (Int64.unsigned_repr n) by rep_lia. reflexivity.
Qed.

Lemma dt_u32_repr: forall x, Int.repr (u32 x) = Int.repr x.
Proof.
  intros. unfold u32. apply Int.eqm_samerepr. unfold Int.eqm. apply Zbits.eqmod_sym, Zbits.eqmod_mod.
  reflexivity.
Qed.

Ltac dt_fix_break R HR :=
  match goal with |- context [RA_break ?X] =>
    replace (RA_break X) with (RA_break R) by (destruct R; reflexivity) end;
  rewrite HR.

Lemma dt_land_range: forall a b, 0 <= a <= 255 -> 0 <= b -> 0 <= Z.land a b <= 255.
Proof.
  intros a b Ha Hb. assert (N: 0 <= Z.land a b) by (apply Z.land_nonneg; lia). split; [exact N | ].
  destruct (Z.eq_dec (Z.land a b) 0) as [Z0 | Z0]; [lia | ].
  destruct (Z.eq_dec a 0) as [A0 | A0]; [subst a; rewrite Z.land_0_l in Z0; congruence | ].
  pose proof (Z.log2_land a b ltac:(lia) ltac:(lia)) as L.
  assert (La: Z.log2 a < 8) by (apply Z.log2_lt_pow2; [lia | simpl; lia]).
  assert (Z.land a b < 2 ^ 8) by (apply Z.log2_lt_pow2; lia).
  simpl in *; lia.
Qed.

Lemma dt_and_repr: forall a b, 0 <= a <= 255 -> 0 <= b <= 255 ->
  Int.and (Int.repr a) (Int.repr b) = Int.repr (Z.land a b).
Proof.
  intros a b Ha Hb. unfold Int.and. rewrite !Int.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma dt_and_zero: forall a b, 0 <= a <= 255 -> 0 <= b <= 255 ->
  (Int.and (Int.repr a) (Int.repr b) = Int.zero <-> Z.land a b = 0).
Proof.
  intros a b Ha Hb. rewrite dt_and_repr by lia. pose proof (dt_land_range a b Ha ltac:(lia)).
  split; intro X; [ | rewrite X; reflexivity].
  apply repr_inj_unsigned in X; rep_lia.
Qed.

Ltac dt_unfold := cbv beta iota zeta delta [ds_tail ds_s2 ds_s1 ds_body case_body inflate_LS
  find_switch f_inflate fn_body ls_drop].

(* the tail from any machine m whose bit buffer holds here.bits *)
Lemma ds_tail_gen {Espec: OracleKind} (F: frame) (m0 m: mst) (h: entry) (lv: reptype t_code) (R: ret_assert):
  frame_ok5 F -> 0 <= m_bits m <= 39 -> lrange (m_hold m) -> -1 <= i_back (m_s m) ->
  i_back (m_s m) + e_bits h <= 35 -> m_leave m = 0 ->
  entry_ok h -> final_ok DISTS h -> e_bits h <= m_bits m ->
  (Z.land (e_op h) 64 = 0 -> mwf3 (dt_distext h m)) ->
  stepf2 (f_flush F) lenfix_list distfix_list m0 = ds_tail_m h m ->
  RA_break R = RA_normal (case_post2 F m0) ->
  RA_normal R = fall_post5 F m0 DISTEXT ->
  semax Delta_cases5 (ld_hl F m (ent h) lv) ds_tail R.
Proof.
  intros HF WB WH WK1 WK2 HL EO FO B2 WX E HR HN.
  destruct HF as [[Hshs [Hhsh [Hgsh Htsh]]] Hfl].
  unfold lrange in WH.
  pose proof EO as (EO1 & EO2 & EO3).
  rewrite ld_hl_t. dt_unfold. unfold ld_t. abbreviate_semax.
  match goal with |- semax _ (PROPx ?P (LOCALx _ (SEPx ?S))) _ _ =>
    apply dt_semax_dowhile0 with (Q := PROPx P (LOCALx (ld_locals F (dropbits (e_bits h) m)) (SEPx S))) end.
  { unfold ld_locals, ent. forward. { entailer!. rep_lia. }
    forward. { entailer!. change (Int.unsigned Int64.iwordsize') with 64. lia. }
    forward. forward.
    unfold dropbits, m_have, m_left. mnorm_goal.
    entailer!. split; [rewrite dt_long_shru_eq by rep_lia; reflexivity | rewrite dt_u32_repr; reflexivity]. }
  unfold ld_locals, ent. abbreviate_semax.
  Ltac dt_fw := forward; try (entailer!; rep_lia).
  dt_fw. dt_fw. dt_fw. dt_fw.
  rewrite add_repr.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?S))) _ _ =>
    forward_if (PROPx (@cons Prop (Z.land (e_op h) 64 = 0) P) (LOCALx Q (SEPx S))) end.
  { unfold dt_strm, strm_rep.
    remember (f_gv F _zcalloc) as zca eqn:Hzca. remember (f_gv F _zcfree) as zcf eqn:Hzcf.
    forward. forward. forward.
    rewrite !Int.unsigned_repr in H1' by rep_lia.
    dt_fix_break R HR. unfold case_post2, RA_normal.
    Exists (set_bad (dt_m1 h m) M_d_code).
    apply andp_right; [apply prop_right; rewrite E; apply dt_bad; assumption | ].
    eapply derives_trans; [ | apply ld_t_loop_state]. unfold ld_t.
    change (mem_rep_d F (set_bad (dt_m1 h m) M_d_code)) with (mem_rep_d F m).
    unfold dt_strm, strm_rep. rewrite <- Hzca, <- Hzcf.
    unfold ld_locals, dt_m1, BAD. mnorm_goal. cbn [msg_val msg_ident]. entailer!. }
  { forward. destruct R as [r1 r2 r3 r4]. cbn [RA_normal]. entailer!.
    first [apply (dt_and_zero (e_op h) 64); [lia | lia | assumption]
          | rewrite !Int.unsigned_repr in * by rep_lia; assumption]. }
  Intros. rename H1 into O64. abbreviate_semax.
  destruct (dt_dist_entry h FO O64) as [OP VL].
  dt_fw. dt_fw. dt_fw. dt_fw.
  unfold abbreviate in POSTCONDITION; subst POSTCONDITION.
  eapply semax_post_flipped'; [forward; apply andp_left2, derives_refl | ].
  rewrite HN. unfold fall_post5.
  Exists (dt_distext h m).
  rewrite dt_and_repr by lia.
  apply andp_right.
  { apply prop_right. split; [ | split; [reflexivity | split; [exact HL | exact (WX O64)]]].
    rewrite E, dt_ext by assumption. symmetry. apply stepf2_DISTEXT. reflexivity. }
  eapply derives_trans; [ | apply ld_t_loop_state]. unfold ld_t.
  change (mem_rep_d F (dt_distext h m)) with (mem_rep_d F m).
  change (dt_strm F (dt_distext h m)) with (dt_strm F m).
  unfold ld_locals, dt_distext, dt_m1, DISTEXT. mnorm_goal. entailer!.
Qed.

Lemma ds_tail_ok : ds_tail_stmt.
Proof.
  intros Espec F m0 M b1 h lv R HF W3 HM HL B0 EO FO B1 B2 E HR HN.
  pose proof (mwf3_mwf _ W3) as W.
  pose proof (mw_bits _ W) as WB. pose proof (mw_hold _ W) as WH.
  pose proof (sw_back _ (mw_s _ W)) as WK.
  pose proof (proj1 (proj2 (md_back _ (mw_md _ W))) HM) as BK.
  pose proof EO as (EO1 & EO2 & EO3).
  assert (MB: m_bits (ds_drop b1 M) = m_bits M - b1).
  { cbn [ds_drop dropbits upd_s m_bits set_m_bits set_m_hold set_m_s]. apply dt_u32_small. lia. }
  apply (ds_tail_gen F m0 (ds_drop b1 M) h lv R HF); auto.
  - rewrite MB. lia.
  - cbn [ds_drop dropbits upd_s m_hold set_m_bits set_m_hold set_m_s]. apply Zshiftr_range; [exact WH | lia].
  - cbn [ds_drop dropbits upd_s m_s set_m_bits set_m_hold set_m_s set_i_back i_back]. lia.
  - cbn [ds_drop dropbits upd_s m_s set_m_bits set_m_hold set_m_s set_i_back i_back]. lia.
  - rewrite MB. lia.
  - intros O64. destruct (dt_dist_entry h FO O64) as [OP VL].
    apply mwf3_dt_distext; auto.
Qed.
