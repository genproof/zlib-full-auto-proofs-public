(* inflate(), case STORED (13) in Delta_cases5: BYTEBITS, NEEDBITS(32), the length/complement check (-> BAD),
   state->length, INITBITS, mode COPY_, leave on Z_TREES, else falls into COPY_ (Model.v c_STORED). *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate.CaseHyps5.
Require Import Zlib.proof.inflate.NeedKit5 Zlib.proof.inflate.NeedBits Zlib.proof.inflate.NeedBits2_5.
Require Import Zlib.proof.inflate.Steps2 Zlib.proof.inflate.MwfLemmas Zlib.proof.inflate.STKit5.
Require Import Zlib.proof.inflate.CaseCOPY5.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* ---------------------------------------------------------------------------------------------- *)
(* pure facts                                                                                     *)

Lemma st_needbits_f_s: forall k n m, m_s (needbits_f k n m) = m_s m.
Proof.
  induction k; intros n m; simpl; auto.
  destruct (m_bits m <? n); auto. destruct (m_have m =? 0); auto. rewrite IHk. reflexivity.
Qed.

(* the machine entering COPY_ *)
Definition st_m2 (m1: mst) : mst :=
  set_mode (initbits (upd_s m1 (fun s => set_i_length s (m_hold m1 mod 65536)))) COPY_.

Lemma c_STORED_eq: forall fl m,
  c_STORED fl m =
  let m1 := needbits 32 (bytebits m) in
  if m_leave m1 =? 1 then IBrk m1 else
  if negb (Z.land (m_hold m1) 65535 =? Z.lxor (Z.shiftr (m_hold m1) 16) 65535)
  then IBrk (set_bad m1 M_stored) else
  if fl =? Z_TREES then IBrk (set_leave (st_m2 m1)) else c_COPY_ (st_m2 m1).
Proof. reflexivity. Qed.

Lemma mwf_set_length_stored: forall m x,
  mwf m -> m_mode m = STORED -> 0 <= x <= Int.max_unsigned -> mwf (upd_s m (fun s => set_i_length s x)).
Proof.
  intros m x W HM Hx.
  assert (Hne: forall P: Prop, i_mode (m_s m) = LENLENS \/ i_mode (m_s m) = CODELENS \/
               decode_mode (i_mode (m_s m)) \/ i_mode (m_s m) = LENEXT \/ i_mode (m_s m) = DISTEXT \/
               i_mode (m_s m) = MATCH \/ i_mode (m_s m) = DIST -> P).
  { intros P X. exfalso. unfold m_mode in HM. rewrite HM in X. unfold decode_mode in X.
    unfold STORED, LENLENS, CODELENS, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT in *. lia. }
  destruct W as [MD SW HW A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16].
  constructor; cbn [upd_s set_m_s m_s m_h m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave
                    m_adler m_msg m_tin m_tout m_snx m_sow]; try assumption.
  - constructor; cbn [i_mode set_i_length]; try (intros X; apply Hne; tauto).
    repeat split; intros X; apply Hne; tauto.
  - destruct SW; constructor; cbn [set_i_length i_mode i_last i_wrap i_havedict i_flags i_dmax i_check i_total
      i_head i_wbits i_wsize i_whave i_wnext i_win i_wdata i_hold i_bits i_length i_offset i_extra i_lencode
      i_distcode i_lenbits i_distbits i_ncode i_nlen i_ndist i_have i_next i_lens i_codes i_sane i_back i_was];
      try assumption.
Qed.

Lemma mwf3_st_m2: forall m1, mwf m1 -> m_mode m1 = STORED -> mwf3 (st_m2 m1).
Proof.
  intros m1 W HM. pose proof (mw_hold _ W) as Hh. unfold lrange in Hh.
  unfold st_m2. apply mwf3_set_mode_stored; [ | unfold m_mode in *; cbn; rewrite HM; unfold STORED, LENGTH, DONE, BAD; lia ..
                                             | left; reflexivity].
  split.
  - apply mwf_initbits. apply mwf_set_length_stored; [exact W | exact HM | ].
    pose proof (Z.mod_pos_bound (m_hold m1) 65536 ltac:(lia)). rep_lia.
  - unfold m_mode in HM.
    constructor; cbn [initbits upd_s set_m_s set_m_hold set_m_bits m_s set_i_length i_mode]; rewrite HM;
      intros X; exfalso; try (unfold decode_mode in X);
      unfold STORED, HEAD, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT in *; lia.
Qed.

(* the bit operations *)
Lemma st_int_and_ones: forall b k, 0 <= b -> 0 <= k <= 32 ->
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

Lemma st_int_and7: forall b, 0 <= b ->
  Int.and (Int.repr b) (Int.repr 7) = Int.repr (b mod 8).
Proof. intros. apply (st_int_and_ones b 3); lia. Qed.

Lemma st_land7: forall b, Z.land b 7 = b mod 8.
Proof. intros. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma st_long_shru_eq: forall h n, 0 <= h <= Int64.max_unsigned -> 0 <= n < 64 ->
  Int64.shru (Int64.repr h) (Int64.repr n) = Int64.repr (Z.shiftr h n).
Proof.
  intros h n Hh Hn. unfold Int64.shru.
  rewrite (Int64.unsigned_repr h) by lia. rewrite (Int64.unsigned_repr n) by rep_lia. reflexivity.
Qed.

(* the length/complement test *)
Lemma st_test: forall h, 0 <= h <= Int64.max_unsigned ->
  (Int64.and (Int64.repr h) (Int64.repr 65535) =
   Int64.xor (Int64.shru (Int64.repr h) (Int64.repr (Int.unsigned (Int.repr 16)))) (Int64.repr 65535)) <->
  Z.land h 65535 = Z.lxor (Z.shiftr h 16) 65535.
Proof.
  intros h Hh. change (Int.unsigned (Int.repr 16)) with 16.
  rewrite st_long_shru_eq by lia.
  assert (S1: 0 <= Z.shiftr h 16 <= h).
  { rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]. }
  assert (S2: 0 <= Z.land h 65535 <= 65535).
  { change 65535 with (Z.ones 16). rewrite Z.land_ones by lia.
    pose proof (Z.mod_pos_bound h (2 ^ 16) ltac:(lia)). change (2 ^ 16) with 65536 in *. change (Z.ones 16) with 65535. lia. }
  assert (S3: 0 <= Z.lxor (Z.shiftr h 16) 65535 <= Int64.max_unsigned).
  { split; [apply Z.lxor_nonneg; lia | ].
    destruct (Z.eq_dec (Z.lxor (Z.shiftr h 16) 65535) 0) as [Z0 | Z0]; [rewrite Z0; rep_lia | ].
    assert (P: 0 < Z.lxor (Z.shiftr h 16) 65535) by (pose proof (Z.lxor_nonneg (Z.shiftr h 16) 65535); lia).
    pose proof (Z.log2_lxor (Z.shiftr h 16) 65535 ltac:(lia) ltac:(lia)) as L.
    assert (L1: Z.log2 (Z.shiftr h 16) < 64).
    { destruct (Z.eq_dec (Z.shiftr h 16) 0) as [E|E]; [rewrite E; simpl; lia | ].
      apply Z.log2_lt_pow2; [lia | ]. rep_lia. }
    assert (L2: Z.log2 65535 < 64) by (simpl; lia).
    assert (Z.lxor (Z.shiftr h 16) 65535 < 2 ^ 64)
      by (apply Z.log2_lt_pow2; [lia | eapply Z.le_lt_trans; [exact L | apply Z.max_lub_lt; assumption]]).
    rep_lia. }
  unfold Int64.and, Int64.xor.
  rewrite !Int64.unsigned_repr by rep_lia.
  split; intro E.
  - apply repr_inj_unsigned64 in E; [exact E | rep_lia | rep_lia].
  - rewrite E. reflexivity.
Qed.

(* do { c } while (0) followed by rest *)
Lemma st_semax_dowhile0 {Espec: OracleKind} (Delta: tycontext) (P Q: environ -> mpred) (c rest: statement)
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

(* ---------------------------------------------------------------------------------------------- *)
(* the pieces of the body (separate lemmas keep each Qed small)                                    *)

Definition st_bb : statement :=
  match case_body 13 with Ssequence (Sloop c _) _ => c | _ => Sskip end.
Definition st_c : statement :=
  match case_body 13 with Ssequence _ (Ssequence _ (Ssequence _ c)) => c | _ => Sskip end.
Definition st_nb : statement :=
  match case_body 13 with Ssequence _ (Ssequence nb _) => nb | _ => Sskip end.
Definition st_cond : expr :=
  match st_c with Ssequence (Sifthenelse e _ _) _ => e | _ => Etempvar _leave tint end.
Definition st_bad : statement :=
  match st_c with Ssequence (Sifthenelse _ b _) _ => b | _ => Sskip end.
Definition st_tail : statement :=
  match st_c with Ssequence _ t => t | _ => Sskip end.

Lemma case_body13_eq: case_body 13 =
  Ssequence (Sloop st_bb Sbreak)
    (Ssequence st_nb (Ssequence (Sifthenelse (Etempvar _leave tint) Sbreak Sskip) st_c)).
Proof. reflexivity. Qed.

Lemma st_c_eq: st_c = Ssequence (Sifthenelse st_cond st_bad Sskip) st_tail.
Proof. reflexivity. Qed.

Lemma st_nb_eq: st_nb = needbits_stmt 32 _t'55 _t'338.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the case                                                                                       *)

Ltac st_unfold := cbv beta iota zeta delta [st_bb st_c st_bad st_tail st_cond st_nb case_body inflate_LS
  find_switch f_inflate fn_body ls_drop].

Ltac fix_post :=
  match goal with |- context [RA_normal (match ?R with _ => _ end)] => destruct R; simpl RA_normal end.

Ltac fix_break R HR :=
  match goal with |- context [RA_break ?X] =>
    replace (RA_break X) with (RA_break R) by (destruct R; reflexivity) end;
  rewrite HR.

(* BYTEBITS *)
Lemma st_bb_ok {Espec: OracleKind} (F: frame) (m: mst) :
  mwf m -> semax Delta_cases5 (loop_state F m) st_bb (normal_ret_assert (loop_state F (bytebits m))).
Proof.
  intros W. pose proof (mw_bits _ W) as WB. pose proof (mw_hold _ W) as WH. unfold lrange in WH.
  st_unfold.
  unfold loop_state. abbreviate_semax.
  pose proof (Z.mod_pos_bound (m_bits m) 8 ltac:(lia)) as B8.
  forward.
  { entailer!. rewrite st_land7. rewrite Int.unsigned_repr by rep_lia.
    change (Int.unsigned Int64.iwordsize') with 64. lia. }
  rewrite (st_int_and7 (m_bits m)) by lia. rewrite Int.unsigned_repr by rep_lia.
  rewrite st_long_shru_eq by lia.
  forward.
  change (mem_rep F (bytebits m)) with (mem_rep F m).
  unfold bytebits. mnorm_goal. entailer!.
  rewrite st_land7. reflexivity.
Qed.

(* the length/complement check fails: BAD *)
Lemma st_bad_ok {Espec: OracleKind} (F: frame) (m m1: mst) (R: ret_assert) :
  frame_ok F ->
  RA_break R = RA_normal (case_post2 F m) ->
  stepf2 (f_flush F) lenfix_list distfix_list m = IBrk (set_bad m1 M_stored) ->
  semax Delta_cases5 (loop_state_st F m1 (zv (m_mode m1)) (zv (i_length (m_s m1)))) st_bad R.
Proof.
  intros HF HR E.
  st_unfold. unfold loop_state_st. Intros.
  destruct HF as (Hshs & Hhsh & Hgsh & Htsh).
  unfold mem_rep_io, strm_rep.
  destruct F as [gv shs strmp sp headp winp hsh xb nb cb ib ob gsh tsh dt vres vhere vlast vhbuf flush].
  frame_simpl. Intros.
  remember (gv _zcalloc) as zca eqn:Hzca. remember (gv _zcfree) as zcf eqn:Hzcf.
  forward. forward. forward.
  fix_break R HR. unfold case_post2, RA_normal.
  Exists (set_bad m1 M_stored).
  apply andp_right; [apply prop_right; exact E | ].
  rewrite loop_state_split_st. unfold loop_state_st, mem_rep_io, strm_rep. frame_simpl_goal.
  rewrite <- Hzca, <- Hzcf.
  mnorm_goal. cbn [msg_val msg_ident].
  entailer!. apply derives_refl.
Qed.

(* the check passes: length, INITBITS, mode COPY_, leave on Z_TREES or fall into COPY_ *)
Lemma st_tail_ok {Espec: OracleKind} (F: frame) (m m1: mst) (R: ret_assert) :
  Int.min_signed <= f_flush F <= Int.max_signed ->
  m_leave m1 = 0 -> mwf m1 -> m_mode m1 = STORED ->
  RA_break R = RA_normal (case_post2 F m) ->
  RA_normal R = fall_post5 F m COPY_ ->
  stepf2 (f_flush F) lenfix_list distfix_list m =
    (if f_flush F =? Z_TREES then IBrk (set_leave (st_m2 m1)) else c_COPY_ (st_m2 m1)) ->
  semax Delta_cases5 (loop_state_st F m1 (zv (m_mode m1)) (zv (i_length (m_s m1)))) st_tail R.
Proof.
  intros Hfl HL1 W1 HM1 HR HN E2.
  pose proof (mw_hold _ W1) as WH. unfold lrange in WH.
  st_unfold. unfold loop_state_st. abbreviate_semax. Intros.
  assert (HLm: 0 <= m_hold m1 mod 65536 < 65536) by (apply Z.mod_pos_bound; lia).
  forward.
  apply st_semax_dowhile0 with
    (Q := loop_state_st F (initbits (upd_s m1 (fun s => set_i_length s (m_hold m1 mod 65536))))
            (zv (m_mode m1)) (zv (m_hold m1 mod 65536))).
  { unfold loop_state_st. forward. forward.
    change (mem_rep_io F (initbits (upd_s m1 (fun s => set_i_length s (m_hold m1 mod 65536)))))
      with (mem_rep_io F m1).
    unfold initbits. mnorm_goal. entailer!.
    rewrite Int64.Z_mod_modulus_eq, Z.mod_small by rep_lia.
    change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. change (2 ^ 16) with 65536.
    apply derives_refl. }
  pose proof (mwf3_st_m2 m1 W1 HM1) as W2.
  unfold loop_state_st.
  change (mem_rep_io F (initbits (upd_s m1 (fun s => set_i_length s (m_hold m1 mod 65536)))))
    with (mem_rep_io F m1).
  abbreviate_semax. Intros.
  forward.
  forward_if.
  * assert (Fl: f_flush F = Z_TREES).
    { exact H3. }
    forward. forward.
    fix_break R HR. unfold case_post2, RA_normal.
    Exists (set_leave (st_m2 m1)).
    apply andp_right; [apply prop_right; rewrite E2, Fl; reflexivity | ].
    rewrite loop_state_split_st. unfold loop_state_st.
    change (mem_rep_io F (set_leave (st_m2 m1))) with (mem_rep_io F m1).
    unfold st_m2. mnorm_goal. entailer!.
  * assert (Fl: f_flush F <> Z_TREES) by (intro X; apply H3; rewrite X; reflexivity).
    forward.
    rewrite HN. unfold fall_post5.
    Exists (st_m2 m1).
    apply andp_right.
    { apply prop_right. split; [ | split; [reflexivity | split; [exact HL1 | exact W2]]].
      rewrite E2, (proj2 (Z.eqb_neq _ _) Fl). symmetry.
      exact (stepf2_COPY_ (f_flush F) lenfix_list distfix_list (st_m2 m1) eq_refl). }
    rewrite loop_state_split_st. unfold loop_state_st.
    change (mem_rep_io F (st_m2 m1)) with (mem_rep_io F m1).
    unfold st_m2. mnorm_goal. entailer!.
Qed.

Lemma stored_body5 {Espec: OracleKind} (F: frame) (m: mst) (R: ret_assert) :
  frame_ok F -> Int.min_signed <= f_flush F <= Int.max_signed ->
  m_mode m = STORED -> m_leave m = 0 -> mwf m ->
  RA_break R = RA_normal (case_post2 F m) ->
  RA_normal R = fall_post5 F m COPY_ ->
  semax Delta_cases5 (loop_state F m) (case_body 13) R.
Proof.
  intros HF Hfl HM HL W HR HN.
  pose proof (stepf2_STORED (f_flush F) lenfix_list distfix_list m HM) as E0.
  rewrite c_STORED_eq in E0.
  rewrite case_body13_eq.
  apply st_semax_dowhile0 with (Q := loop_state F (bytebits m)); [apply st_bb_ok; exact W | ].
  pose proof (mwf_bytebits m W) as Wb.
  rewrite st_nb_eq.
  eapply (semax_needbits_seq_r5 F m (bytebits m) 32).
  - apply semax_needbits_STORED5; [exact Wb | exact HL | lia].
  - exact Wb.
  - lia.
  - exact HR.
  - intro E. rewrite E0. cbv zeta. rewrite E. reflexivity.
  - apply semax_extract_prop; intros HL1.
    pose proof (mwf_needbits 32 (bytebits m) Wb ltac:(lia)) as W1.
    assert (HM1: m_mode (needbits 32 (bytebits m)) = STORED)
      by (unfold m_mode, needbits; rewrite st_needbits_f_s; exact HM).
    cbv zeta in E0. rewrite HL1 in E0. change (0 =? 1) with false in E0. cbv iota in E0.
    set (m1 := needbits 32 (bytebits m)) in *. clearbody m1.
    pose proof (mw_hold _ W1) as WH. unfold lrange in WH.
    rewrite loop_state_split_st, st_c_eq.
    cbv beta iota zeta delta [st_cond st_c case_body inflate_LS find_switch f_inflate fn_body ls_drop].
    unfold loop_state_st. abbreviate_semax. Intros.
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROPx (@cons Prop (Z.land (m_hold m1) 65535 = Z.lxor (Z.shiftr (m_hold m1) 16) 65535) P)
                   (LOCALx Q (SEPx R))) end.
    + assert (T: Z.land (m_hold m1) 65535 <> Z.lxor (Z.shiftr (m_hold m1) 16) 65535)
        by (intro X; apply H1; apply st_test; auto).
      assert (E: stepf2 (f_flush F) lenfix_list distfix_list m = IBrk (set_bad m1 M_stored))
        by (rewrite E0, (proj2 (Z.eqb_neq _ _) T); reflexivity).
      eapply semax_pre; [ | apply (st_bad_ok F m m1 _ HF); [destruct R; exact HR | exact E]].
      unfold loop_state_st. entailer!.
    + forward. try fix_post. entailer!.
      apply st_test; auto.
      apply Int64.same_if_eq in H1. rewrite <- H1. unfold Int64.and.
      rewrite (Int64.unsigned_repr (m_hold m1)) by lia. reflexivity.
    + apply semax_extract_PROP; intro HT.
      assert (E2: stepf2 (f_flush F) lenfix_list distfix_list m =
                  if f_flush F =? Z_TREES then IBrk (set_leave (st_m2 m1)) else c_COPY_ (st_m2 m1))
        by (rewrite E0, HT, Z.eqb_refl; reflexivity).
      eapply semax_pre; [ | apply (st_tail_ok F m m1 R Hfl HL1 W1 HM1 HR HN E2)].
      unfold loop_state_st. entailer!.
Qed.

Lemma case_STORED5 {Espec: OracleKind} (F: frame) : frame_ok5 F -> case_ok5 F COPY_ 14 -> case_ok5 F STORED 13.
Proof.
  intros [HF Hfl] HY m HM HL [W W3].
  apply (case_fallthrough5 F m COPY_ 13); [lia | exact HY | ].
  apply stored_body5; auto.
Qed.
