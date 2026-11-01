(* case LEN (20) from its parts (LnKit5.v): the F4 test, the fast path, state->back = 0, the root lookup,
   the link test and the sub-table part (last = here, the sub-table lookup, DROPBITS(last.bits), back), the tail. *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate.LnKit5.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Definition vb (b: bool) : val := Vint (if b then Int.one else Int.zero).

(* ---------------------------------------------------------------------------------------------- *)
(* pure facts                                                                                     *)

Lemma mwf3_set_back: forall m x, mwf3 m -> m_mode m = LEN -> -1 <= x <= 1000 ->
  mwf3 (upd_s m (fun s => set_i_back s x)).
Proof.
  intros m x [W X] HM Hx. unfold m_mode in HM.
  destruct W as [MD SW HW INP AOUT NX OW HOLD BITS IN OUT RET LEAVE ADLER TIN TOUT SNX SOW OUTEQ].
  split.
  - constructor; cbn [upd_s set_m_s m_s m_h m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave
      m_adler m_tin m_tout m_snx m_sow].
    all: try assumption.
    + destruct MD; constructor; cbn [set_i_back i_mode i_back i_have i_ncode i_nlen i_ndist i_lens i_lencode
        i_lenbits i_distcode i_distbits i_extra i_length i_offset]; try assumption.
      rewrite HM. unfold LEN, LENEXT, DIST, DISTEXT. repeat split; intros; lia.
    + destruct SW; constructor; cbn [set_i_back i_mode i_last i_wrap i_havedict i_flags i_dmax i_check i_total
        i_wbits i_wsize i_whave i_wnext i_wdata i_win i_hold i_bits i_length i_offset i_extra i_lencode
        i_distcode i_lenbits i_distbits i_ncode i_nlen i_ndist i_have i_next i_lens i_codes i_sane i_back
        i_was]; try assumption.
  - destruct X; constructor; cbn [set_i_back i_mode i_wbits i_wrap i_wsize i_win i_length i_offset i_lencode
      i_lenbits upd_s set_m_s m_s]; try assumption.
Qed.

Lemma mwf3_intro: forall m m', mwf3 m -> mwf m' -> m_s m' = m_s m -> mwf3 m'.
Proof. intros m m' [W X] W' E. split; [exact W'|]. rewrite E. exact X. Qed.

Lemma islink_lens: forall op, islink LENS op = andb (negb (op =? 0)) (Z.land op 240 =? 0).
Proof. reflexivity. Qed.

(* after the root lookup *)
Lemma ln_after1: forall m0 here m1, mwf3 m0 -> m_mode m0 = LEN -> m_leave m0 = 0 ->
  lookup1 lenfix_list distfix_list (i_lencode (m_s m0)) (i_lenbits (m_s m0)) m0 = (here, m1, true) ->
  mwf3 m1 /\ m_s m1 = m_s m0 /\ m_leave m1 = 0 /\ e_bits here <= m_bits m1 /\ entry_ok here /\
  (islink LENS (e_op here) = true -> exists sz, sz <= tab_size (i_lencode (m_s m0)) /\
     sub_ok LENS (tab_entry lenfix_list distfix_list (m_s m0) (i_lencode (m_s m0))) (i_lenbits (m_s m0)) sz here) /\
  (islink LENS (e_op here) = false -> e_bits here <= i_lenbits (m_s m0) /\ final_ok LENS here).
Proof.
  intros m0 here m1 W3 HM HL E1. pose proof W3 as [W X].
  assert (D: decode_mode (i_mode (m_s m0))) by (change (i_mode (m_s m0)) with (m_mode m0); rewrite HM; unfold decode_mode; auto 10).
  destruct (md_tables _ (mw_md _ W) D) as [(sz & SZ & TV) _].
  pose proof (tv_rb _ _ _ _ TV) as RB.
  pose proof (lookup1_ok lenfix_list distfix_list (i_lencode (m_s m0)) (i_lenbits (m_s m0)) m0 W HL ltac:(lia)
                (fun i Hi => proj2 (proj1 (tv_root_bits _ _ _ _ i TV Hi)))) as LK.
  rewrite E1 in LK. destruct LK as (W1 & S1 & OK1 & _).
  destruct (OK1 eq_refl) as (L1 & B1 & i & Hi & Eh).
  pose proof (tv_root_bits _ _ _ _ i TV Hi) as [RBh EOh]. rewrite <- Eh in EOh.
  split; [apply (mwf3_intro m0); auto|]. split; [exact S1|]. split; [exact L1|]. split; [exact B1|].
  split; [exact EOh|]. split.
  - intro ISL. rewrite Eh in ISL. pose proof (tv_sub _ _ _ _ i TV Hi ISL) as SO. rewrite <- Eh in SO.
    exists sz. split; [exact SZ | exact SO].
  - intro ISL. rewrite Eh in ISL. destruct (tv_final _ _ _ _ i TV Hi ISL) as [FB FF]. rewrite <- Eh in FB, FF.
    split; [exact FB | exact FF].
Qed.

(* after the sub-table lookup *)
Lemma ln_after2: forall m1 here sz h2 m2, mwf m1 -> m_leave m1 = 0 -> e_bits here <= m_bits m1 ->
  sub_ok LENS (tab_entry lenfix_list distfix_list (m_s m1) (i_lencode (m_s m1))) (i_lenbits (m_s m1)) sz here ->
  lookup2 lenfix_list distfix_list (i_lencode (m_s m1)) here m1 = (h2, m2, true) ->
  mwf m2 /\ m_s m2 = m_s m1 /\ m_leave m2 = 0 /\ e_bits here + e_bits h2 <= m_bits m2 /\ entry_ok h2 /\
  final_ok LENS h2 /\ e_bits here + e_bits h2 <= 15 /\ e_bits here = i_lenbits (m_s m1) /\ 0 <= e_bits h2.
Proof.
  intros m1 here sz h2 m2 W L B SO E2.
  destruct SO as (SB & SO1 & SO2 & SBT).
  assert (SB2: forall j, 0 <= j < 2 ^ e_op here ->
    e_bits here + e_bits (tab_entry lenfix_list distfix_list (m_s m1) (i_lencode (m_s m1)) (e_val here + j)) <= 15).
  { intros j Hj. destruct (SBT j Hj) as (_ & _ & _ & A & _). lia. }
  assert (B0: 0 <= e_bits here) by (pose proof (proj1 (mw_s _ W).(sw_lenbits _)); lia).
  pose proof (lookup2_ok lenfix_list distfix_list (i_lencode (m_s m1)) here m1 W L ltac:(lia) ltac:(lia) SB2) as LK2.
  rewrite E2 in LK2. destruct LK2 as (W2 & S2 & OK2 & _).
  destruct (OK2 eq_refl) as (L2 & B2 & j & Hj & Eh2).
  destruct (SBT j Hj) as (_ & EO2 & _ & A2 & F2). cbv zeta in EO2, A2, F2. rewrite <- Eh2 in EO2, A2, F2.
  pose proof (proj1 (proj2 EO2)) as BH2.
  split; [exact W2|]. split; [exact S2|]. split; [exact L2|]. split; [exact B2|]. split; [exact EO2|].
  split; [exact F2|]. split; [lia|]. split; [exact SB | lia].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the field state->back apart (ModeKit.v's pattern)                                              *)

Definition state_rep_nb (gv: globals) (sp strmp headp winp: val) (s: istate) : mpred :=
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
  field_at Ews t_state (DOT _was) (zv (i_was s)) sp.

Lemma sepcon_34th_35: forall a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35: mpred,
  a1 * a2 * a3 * a4 * a5 * a6 * a7 * a8 * a9 * a10 * a11 * a12 * a13 * a14 * a15 * a16 * a17 * a18 * a19 * a20 * a21 * a22 * a23 * a24 * a25 * a26 * a27 * a28 * a29 * a30 * a31 * a32 * a33 * a34 * a35 =
  a34 * (a1 * a2 * a3 * a4 * a5 * a6 * a7 * a8 * a9 * a10 * a11 * a12 * a13 * a14 * a15 * a16 * a17 * a18 * a19 * a20 * a21 * a22 * a23 * a24 * a25 * a26 * a27 * a28 * a29 * a30 * a31 * a32 * a33 * a35).
Proof. intros. apply pred_ext; cancel. Qed.

Lemma state_rep_split_b: forall gv sp strmp headp winp s,
  state_rep gv sp strmp headp winp s =
  field_at Ews t_state (DOT _back) (zv (i_back s)) sp * state_rep_nb gv sp strmp headp winp s.
Proof. intros. unfold state_rep, state_rep_nb. apply sepcon_34th_35. Qed.

Definition mem_rep_nb (F: frame) (m: mst) : mpred :=
  state_rep_nb (f_gv F) (f_sp F) (f_strmp F) (f_headp F) (f_winp F) (m_s m) *
  win_rep (f_winp F) (m_s m) *
  head_part F m *
  strm_rep (f_gv F) (f_shs F) (f_strmp F)
    (in_ptr (f_ib F) (m_snx m)) (zv (Zlength (m_inp m) - m_snx m)) (m_tin m)
    (out_ptr (f_ob F) (m_sow m)) (zv (m_aout m - m_sow m)) (m_tout m)
    (msg_val (f_gv F) (m_msg m)) (f_sp F) (f_dt F) (m_adler m) (f_vres F) *
  in_rep (f_ib F) *
  out_rep (f_ob F) (m_ow m) *
  tables_rep (f_gsh F) (f_gv F) *
  crc_table_at (f_tsh F) (f_gv F).

Lemma sepcon_first_8: forall a b1 b2 b3 b4 b5 b6 b7 b8: mpred,
  (a * b1) * b2 * b3 * b4 * b5 * b6 * b7 * b8 = a * (b1 * b2 * b3 * b4 * b5 * b6 * b7 * b8).
Proof. intros. apply pred_ext; cancel. Qed.

Lemma mem_rep_split_b: forall F m,
  mem_rep F m = field_at Ews t_state (DOT _back) (zv (i_back (m_s m))) (f_sp F) * mem_rep_nb F m.
Proof. intros. unfold mem_rep, mem_rep_nb. rewrite state_rep_split_b. apply sepcon_first_8. Qed.

(* ls_hl with more temps, and with the back field apart *)
Definition ls_hlx (F: frame) (m: mst) (hv lv: reptype t_code) (extra: list localdef) : environ -> mpred :=
  PROPx [in_ok (f_ib F) (m_inp m); out_ok (f_ob F) (m_aout m)]
  (LOCALx (extra ++ ln_locals F m)
  (SEPx [mem_rep F m; data_at Tsh t_code hv (f_vhere F); data_at Tsh t_code lv (f_vlast F);
         data_at_ Tsh (tarray tuchar 4) (f_vhbuf F)])).

Definition ls_hlb (F: frame) (m: mst) (hv lv: reptype t_code) (v: val) : environ -> mpred :=
  PROPx [in_ok (f_ib F) (m_inp m); out_ok (f_ob F) (m_aout m)]
  (LOCALx (ln_locals F m)
  (SEPx [field_at Ews t_state (DOT _back) v (f_sp F); mem_rep_nb F m;
         data_at Tsh t_code hv (f_vhere F); data_at Tsh t_code lv (f_vlast F);
         data_at_ Tsh (tarray tuchar 4) (f_vhbuf F)])).

Lemma ls_hl_split_b: forall F m hv lv, ls_hl F m hv lv = ls_hlb F m hv lv (zv (i_back (m_s m))).
Proof.
  intros. unfold ls_hl, ls_hlb. rewrite mem_rep_split_b. f_equal. f_equal.
  unfold SEPx. extensionality rho. cbn [fold_right_sepcon]. rewrite !sepcon_assoc. reflexivity.
Qed.

Lemma ls_hlb_set_back: forall F m hv lv v x,
  ls_hlb F (upd_s m (fun s => set_i_back s x)) hv lv v = ls_hlb F m hv lv v.
Proof. reflexivity. Qed.

Lemma ls_hl_set_back: forall F m hv lv x,
  ls_hl F (upd_s m (fun s => set_i_back s x)) hv lv = ls_hlb F m hv lv (zv x).
Proof. intros. rewrite ls_hl_split_b. reflexivity. Qed.

Lemma tuchar_true: forall z, 0 <= z <= 255 -> typed_true tuchar (Vint (Int.repr z)) -> z <> 0.
Proof. intros z R T E. subst z. inversion T. Qed.

Lemma tuchar_false: forall z, 0 <= z <= 255 -> typed_false tuchar (Vint (Int.repr z)) -> z = 0.
Proof.
  intros z R T. unfold typed_false, strict_bool_val in T. simpl in T.
  destruct (Int.eq (Int.repr z) Int.zero) eqn:Q; [ | inversion T].
  apply int_eq_e in Q. apply (f_equal Int.unsigned) in Q. rewrite Int.unsigned_repr in Q by rep_lia. exact Q.
Qed.

Lemma land240_range: forall op, 0 <= op <= 255 -> 0 <= Z.land op 240 <= 240.
Proof.
  intros op R.
  assert (A: forallb (fun n => andb (0 <=? Z.land (Z.of_nat n) 240) (Z.land (Z.of_nat n) 240 <=? 240))
               (seq 0 256) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in A. specialize (A (Z.to_nat op)).
  rewrite Z2Nat.id in A by lia. destruct (andb_prop _ _ (A ltac:(apply in_seq; lia))) as [A1 A2].
  apply Z.leb_le in A1. apply Z.leb_le in A2. lia.
Qed.

Lemma ln_link_val: forall op, 0 <= op <= 255 -> op <> 0 ->
  vb (islink LENS op) = bool2val (Int.eq (Int.repr (Z.land op 240)) (Int.repr 0)).
Proof.
  intros op R N. rewrite islink_lens. destruct (Z.eqb_spec op 0); [lia|]. cbn [negb andb].
  pose proof (land240_range op R) as LR.
  unfold vb, bool2val. destruct (Z.eqb_spec (Z.land op 240) 0) as [E|E].
  - rewrite E. reflexivity.
  - rewrite Int.eq_false; [reflexivity|]. intro C. apply E.
    apply (f_equal Int.unsigned) in C. rewrite !Int.unsigned_repr in C by rep_lia. exact C.
Qed.

Lemma ln_after1_false: forall m0 here m1, mwf m0 -> m_mode m0 = LEN -> m_leave m0 = 0 ->
  lookup1 lenfix_list distfix_list (i_lencode (m_s m0)) (i_lenbits (m_s m0)) m0 = (here, m1, false) ->
  m_leave m1 = 1.
Proof.
  intros m0 here m1 W HM HL E1.
  assert (D: decode_mode (i_mode (m_s m0))) by (change (i_mode (m_s m0)) with (m_mode m0); rewrite HM; unfold decode_mode; auto 10).
  destruct (md_tables _ (mw_md _ W) D) as [(sz & SZ & TV) _].
  pose proof (tv_rb _ _ _ _ TV) as RB.
  pose proof (lookup1_ok lenfix_list distfix_list (i_lencode (m_s m0)) (i_lenbits (m_s m0)) m0 W HL ltac:(lia)
                (fun i Hi => proj2 (proj1 (tv_root_bits _ _ _ _ i TV Hi)))) as LK.
  rewrite E1 in LK. destruct LK as (_ & _ & _ & NOK). apply NOK; reflexivity.
Qed.

Lemma ln_after2_false: forall m1 here sz h2 m2, mwf m1 -> m_leave m1 = 0 -> e_bits here <= m_bits m1 ->
  sub_ok LENS (tab_entry lenfix_list distfix_list (m_s m1) (i_lencode (m_s m1))) (i_lenbits (m_s m1)) sz here ->
  lookup2 lenfix_list distfix_list (i_lencode (m_s m1)) here m1 = (h2, m2, false) ->
  m_leave m2 = 1.
Proof.
  intros m1 here sz h2 m2 W L B SO E2.
  destruct SO as (SB & SO1 & SO2 & SBT).
  assert (SB2: forall j, 0 <= j < 2 ^ e_op here ->
    e_bits here + e_bits (tab_entry lenfix_list distfix_list (m_s m1) (i_lencode (m_s m1)) (e_val here + j)) <= 15).
  { intros j Hj. destruct (SBT j Hj) as (_ & _ & _ & A & _). lia. }
  assert (B0: 0 <= e_bits here) by (pose proof (proj1 (mw_s _ W).(sw_lenbits _)); lia).
  pose proof (lookup2_ok lenfix_list distfix_list (i_lencode (m_s m1)) here m1 W L ltac:(lia) ltac:(lia) SB2) as LK2.
  rewrite E2 in LK2. destruct LK2 as (_ & _ & _ & NOK). apply NOK; reflexivity.
Qed.

Lemma ln_link_post: forall m0 m1 m2 here h2,
  mwf3 m1 -> m_s m1 = m_s m0 -> i_back (m_s m0) = 0 -> m_mode m1 = LEN -> mwf m2 -> m_s m2 = m_s m1 ->
  m_leave m2 = 0 -> e_bits here + e_bits h2 <= m_bits m2 -> 0 <= e_bits h2 -> e_bits here + e_bits h2 <= 15 ->
  0 <= e_bits here ->
  let m3 := dropbits (e_bits here) (upd_s m2 (fun s => set_i_back s (i_back s + e_bits here))) in
  mwf3 m3 /\ m_mode m3 = LEN /\ m_leave m3 = 0 /\ 0 <= i_back (m_s m3) /\ i_back (m_s m3) + e_bits h2 <= 15 /\
  e_bits h2 <= m_bits m3.
Proof.
  intros m0 m1 m2 here h2 W1 S1 B0 HM1 W2 S2 L2 B2 BH2 BB BH. cbv zeta.
  assert (W32: mwf3 m2) by (apply (mwf3_intro m1); auto).
  assert (HM2: m_mode m2 = LEN) by (unfold m_mode; rewrite S2; exact HM1).
  assert (BK2: i_back (m_s m2) = 0) by (rewrite S2, S1; exact B0).
  assert (W4: mwf3 (upd_s m2 (fun s => set_i_back s (i_back (m_s m2) + e_bits here))))
    by (apply mwf3_set_back; auto; lia).
  pose proof (mw_bits _ W2) as WB.
  change (upd_s m2 (fun s => set_i_back s (i_back s + e_bits here)))
    with (upd_s m2 (fun s => set_i_back s (i_back (m_s m2) + e_bits here))).
  split; [ | split; [exact HM2 | split; [exact L2 | ]]].
  - apply (mwf3_intro _ _ W4); [ | reflexivity]. apply mwf_dropbits; [apply W4 | cbn; lia].
  - cbn [dropbits set_m_bits set_m_hold upd_s set_m_s m_s set_i_back i_back]. rewrite BK2.
    split; [lia | split; [lia | ]].
    unfold dropbits, upd_s. cbn [m_bits set_m_bits set_m_hold set_m_s]. unfold u32.
    rewrite Z.mod_small by lia. lia.
Qed.

(* loop_state with more temps *)
Definition ls_t (F: frame) (m: mst) (extra: list localdef) : environ -> mpred :=
  PROPx [in_ok (f_ib F) (m_inp m); out_ok (f_ob F) (m_aout m)]
  (LOCALx (extra ++ ln_locals F m) (SEPx [mem_rep F m; locals_rep F])).


(* state->back = 0; *)
Lemma ln_back0_ok {Espec: OracleKind} (F: frame) (m: mst):
  semax Delta_cases5 (loop_state F m) ln_back0
    (normal_ret_assert (ls_hl F (upd_s m (fun s => set_i_back s 0)) (default_val t_code) (default_val t_code))).
Proof.
  rewrite loop_state_hl, ls_hl_set_back, ls_hl_split_b. unfold ls_hlb, ln_locals.
  unfold ln_back0, ln_slow. cbv beta iota zeta delta [ln_body case_body inflate_LS find_switch f_inflate fn_body ls_drop].
  abbreviate_semax. forward. entailer!.
Qed.

(* if (leave) break; with leave = 1: the pass ends with m1 *)
Lemma ln_leave_brk {Espec: OracleKind} (F: frame) (m0 m1: mst) (hv lv: reptype t_code) (c: statement)
    (R: ret_assert):
  m_leave m1 = 1 -> stepf2 (f_flush F) lenfix_list distfix_list m0 = IBrk m1 ->
  RA_break R = RA_normal (case_post2 F m0) ->
  semax Delta_cases5 (ls_hl F m1 hv lv) (Ssequence ifleave_stmt c) R.
Proof.
  intros L1 E HR.
  apply semax_seq with (Q := FF); [ | apply semax_pre with FF; [apply andp_left2, derives_refl | apply semax_ff]].
  pose proof (ls_hl_loop_state F m1 hv lv) as LS.
  eapply semax_pre; [apply andp_left2, LS | ].
  unfold loop_state, ifleave_stmt. abbreviate_semax.
  rewrite L1. forward_if.
  - forward.
    match goal with |- _ |-- RA_break ?X => replace (RA_break X) with (RA_break R) by (destruct R; reflexivity) end.
    rewrite HR.
    unfold case_post2. cbv [RA_normal]. Exists m1. unfold loop_state. rewrite L1. entailer!.
  - match goal with H: Int.repr 1 = Int.zero |- _ => apply Int.one_not_zero in H; contradiction end.
Qed.

(* if (leave) break; with leave = 0 *)
Lemma ln_leave_go {Espec: OracleKind} (F: frame) (m1: mst) (hv lv: reptype t_code) (c: statement)
    (R: ret_assert):
  m_leave m1 = 0 -> semax Delta_cases5 (ls_hl F m1 hv lv) c R ->
  semax Delta_cases5 (ls_hl F m1 hv lv) (Ssequence ifleave_stmt c) R.
Proof.
  intros L1 HC.
  eapply semax_seq'; [ | exact HC].
  unfold ls_hl, ln_locals, ifleave_stmt. abbreviate_semax.
  rewrite L1. forward_if.
  - match goal with H: Int.repr 0 <> Int.zero |- _ => exfalso; apply H; reflexivity end.
  - forward. rewrite L1. entailer!.
Qed.

(* the link test: _t'76 = here.op && (here.op & 0xf0) == 0 *)
Lemma ln_ltest_ok {Espec: OracleKind} (F: frame) (m: mst) (h: entry) (lv: reptype t_code):
  entry_ok h ->
  semax Delta_cases5 (ls_hl F m (ent h) lv) ln_ltest
    (normal_ret_assert (ls_hlx F m (ent h) lv [temp _t'76 (vb (islink LENS (e_op h)))])).
Proof.
  intros EO. destruct EO as (EO1 & EO2 & EO3).
  unfold ls_hl, ls_hlx, ln_locals, ent. cbn [app].
  unfold ln_ltest, ln_lif, ln_s3, ln_s2, ln_s1, ln_slow.
  cbv beta iota zeta delta [ln_body case_body inflate_LS find_switch f_inflate fn_body ls_drop].
  abbreviate_semax.
  forward. { entailer!. rep_lia. }
  forward_if ltac:(let x := eval cbv [ls_hlx ln_locals app ent] in
                     (ls_hlx F m (ent h) lv [temp _t'76 (vb (islink LENS (e_op h)))]) in exact x).
  - forward. forward. unfold ln_locals, ent. entailer!.
    apply ln_link_val; [lia | exact (tuchar_true _ EO1 H1)].
  - forward. unfold ln_locals, ent. entailer!.
    rewrite (tuchar_false _ EO1 H1). reflexivity.
Qed.

Lemma ln_dowhile0 {Espec: OracleKind} (Delta: tycontext) (P Q: environ -> mpred) (c rest: statement)
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

Lemma long_shru_eq: forall h n, 0 <= h <= Int64.max_unsigned -> 0 <= n < 64 ->
  Int64.shru (Int64.repr h) (Int64.repr n) = Int64.repr (Z.shiftr h n).
Proof.
  intros h n Hh Hn. unfold Int64.shru.
  rewrite (Int64.unsigned_repr h) by lia. rewrite (Int64.unsigned_repr n) by rep_lia. reflexivity.
Qed.

(* DROPBITS(last.bits); state->back += last.bits; *)
Lemma ln_dropback_ok {Espec: OracleKind} (F: frame) (m: mst) (hv: reptype t_code) (l: entry):
  mwf m -> entry_ok l -> e_bits l <= m_bits m ->
  semax Delta_cases5 (ls_hl F m hv (ent l)) (Ssequence ln_dropl ln_backl)
    (normal_ret_assert (ls_hl F (dropbits (e_bits l) (upd_s m (fun s => set_i_back s (i_back s + e_bits l)))) hv (ent l))).
Proof.
  intros W EO B. destruct EO as (EO1 & EO2 & EO3).
  pose proof (mw_bits _ W) as WB. pose proof (mw_hold _ W) as WH. pose proof (sw_back _ (mw_s _ W)) as BK.
  unfold ln_dropl, ln_backl, ln_l3, ln_l2, ln_l1, ln_link, ln_lif, ln_s3, ln_s2, ln_s1, ln_slow.
  cbv beta iota zeta delta [ln_body case_body inflate_LS find_switch f_inflate fn_body ls_drop].
  apply ln_dowhile0 with (Q := ls_hl F (dropbits (e_bits l) m) hv (ent l)).
  - unfold ls_hl, ln_locals, ent. abbreviate_semax.
    forward. { entailer!. rep_lia. }
    forward. { entailer!. change (Int.unsigned Int64.iwordsize') with 64; lia. }
    forward. forward. entailer!.
    + unfold dropbits; cbn [m_hold m_bits set_m_bits set_m_hold].
      rewrite long_shru_eq by (unfold lrange in WH; lia). split; [reflexivity|].
      unfold u32. rewrite Z.mod_small by lia. reflexivity.
    + unfold dropbits. apply derives_refl.
  - change (dropbits (e_bits l) (upd_s m (fun s => set_i_back s (i_back s + e_bits l))))
      with (upd_s (dropbits (e_bits l) m) (fun s => set_i_back s (i_back (m_s m) + e_bits l))).
    rewrite ls_hl_set_back, ls_hl_split_b. unfold ls_hlb, ln_locals, ent. abbreviate_semax.
    forward. forward. { entailer!. rep_lia. } forward. entailer!.
Qed.

(* last = here; (op, bits, val) *)
Lemma ln_copy_ok {Espec: OracleKind} (F: frame) (m: mst) (h: entry) (lv: reptype t_code) (X: statement)
    (R: ret_assert):
  entry_ok h ->
  semax Delta_cases5 (ls_hl F m (ent h) (ent h)) X R ->
  semax Delta_cases5 (ls_hl F m (ent h) lv) (Ssequence ln_c1 (Ssequence ln_c2 (Ssequence ln_c3 X))) R.
Proof.
  intros EO HX. destruct EO as (EO1 & EO2 & EO3).
  unfold ln_c1, ln_c2, ln_c3, ln_link, ln_lif, ln_s3, ln_s2, ln_s1, ln_slow.
  cbv beta iota zeta delta [ln_body case_body inflate_LS find_switch f_inflate fn_body ls_drop].
  unfold ls_hl at 1. unfold ln_locals, ent. abbreviate_semax.
  forward. { entailer!. rep_lia. } forward.
  forward. { entailer!. rep_lia. } forward.
  forward. { entailer!. rep_lia. } forward.
  rewrite !zero_ext_inrange by (rewrite Int.unsigned_repr by rep_lia; simpl; rep_lia).
  eapply semax_pre; [ | exact HX].
  unfold ls_hl, ln_locals, ent. entailer!.
Qed.

Lemma semax_normal_override {Espec: OracleKind} (Delta: tycontext) (P P' Q: environ -> mpred) (c: statement)
    (R: ret_assert):
  semax Delta P c (normal_ret_assert P') -> P' |-- Q -> semax Delta P c (overridePost Q R).
Proof.
  intros H E. eapply semax_post; [ | | | | exact H]; intros; destruct R; simpl_ret_assert;
    first [apply andp_left2; exact E | apply andp_left2, FF_left | intros; apply andp_left2, FF_left].
Qed.

Lemma ln_if_true {Espec: OracleKind} (F: frame) (m: mst) (hv lv: reptype t_code) (c1 c2: statement)
    (R: ret_assert):
  semax Delta_cases5 (ls_hl F m hv lv) c1 R ->
  semax Delta_cases5 (ls_hlx F m hv lv [temp _t'76 (vb true)]) (Sifthenelse (Etempvar _t'76 tint) c1 c2) R.
Proof.
  intros H. unfold ls_hlx, ln_locals, vb. cbn [app]. abbreviate_semax.
  forward_if.
  - eapply semax_pre; [ | exact H]. unfold ls_hl, ln_locals. entailer!.
  - exfalso. apply Int.one_not_zero. assumption.
Qed.

Lemma ln_if_false {Espec: OracleKind} (F: frame) (m: mst) (hv lv: reptype t_code) (c1 c2: statement)
    (R: ret_assert):
  semax Delta_cases5 (ls_hl F m hv lv) c2 R ->
  semax Delta_cases5 (ls_hlx F m hv lv [temp _t'76 (vb false)]) (Sifthenelse (Etempvar _t'76 tint) c1 c2) R.
Proof.
  intros H. unfold ls_hlx, ln_locals, vb. cbn [app]. abbreviate_semax.
  forward_if.
  - match goal with H: Int.repr 0 <> Int.zero |- _ => exfalso; apply H; reflexivity end.
  - eapply semax_pre; [ | exact H]. unfold ls_hl, ln_locals. entailer!.
Qed.

Lemma ln_case {Espec: OracleKind} (F: frame) : frame_ok5 F ->
  ln_fast_stmt -> ln_loop1_stmt -> ln_loop2_stmt -> ln_tail_stmt ->
  case_ok5 F LENEXT 21 -> case_ok5 F LEN 20.
Proof.
  intros FO HF HL1 HL2 HT HY m HM HL W3.
  pose proof W3 as [W WS].
  apply (case_fallthrough5 F m LENEXT 20); [lia | exact HY | ].
  change (case_body 20) with ln_body. rewrite ln_body_eq.
  set (R := overridePost (fall_post5 F m LENEXT) (switch_ret_assert (case_post2 F m))).
  apply semax_seq with (Q := !! (ln_fastc m = false) && loop_state F m).
  - (* the F4 test and the fast path *)
    unfold ln_cond, ln_head. cbv beta iota zeta delta [ln_body case_body inflate_LS find_switch f_inflate fn_body ls_drop].
    pose proof (mwf_have m W) as HH. pose proof (mwf_left m W) as HLF. pose proof (mw_bits _ W) as HB.
    replace (loop_state F m) with (ls_t F m []) by reflexivity.
    apply semax_seq' with (P' := ls_t F m [temp _t'73 (vb (ln_fastc m))]).
    + unfold ls_t, ln_locals. cbn [app]. abbreviate_semax.
      forward_if (ls_t F m [temp _t'72 (vb (andb (6 <=? m_have m) (258 <=? m_left m)))]).
      * forward. unfold ls_t, ln_locals. cbn [app]. entailer!.
        unfold vb; destruct (Z.leb_spec 6 (m_have m)); destruct (Z.leb_spec 258 (m_left m));
          destruct (zlt (m_left m) 258); simpl; try reflexivity; lia.
      * forward. unfold ls_t, ln_locals. cbn [app]. entailer!.
        unfold vb; destruct (Z.leb_spec 6 (m_have m)); simpl; try reflexivity; lia.
      * unfold ls_t, ln_locals. cbn [app]. abbreviate_semax.
        forward_if.
        -- forward. entailer!.
           unfold vb, ln_fastc in *; destruct (Z.leb_spec 6 (m_have m)); destruct (Z.leb_spec 258 (m_left m));
             destruct (Z.ltb_spec (m_bits m) 8); destruct (zlt (m_bits m) 8); cbn [andb] in *;
             try reflexivity; try lia; try contradiction; try (apply Int.one_not_zero in H; contradiction).
        -- forward. entailer!.
           unfold vb, ln_fastc in *; destruct (Z.leb_spec 6 (m_have m)); destruct (Z.leb_spec 258 (m_left m));
             cbn [andb] in *; try reflexivity; try lia; try contradiction;
             try (apply Int.one_not_zero in H; contradiction).
    +       unfold ls_t, ln_locals. cbn [app]. abbreviate_semax.
      forward_if.
      * assert (EF: ln_fastc m = true) by (unfold vb in *; destruct (ln_fastc m); [reflexivity | contradiction]).
        unfold ln_fastc in EF. destruct (andb_prop _ _ EF) as [EF1 E3]. destruct (andb_prop _ _ EF1) as [E1 E2].
        apply Z.leb_le in E1. apply Z.leb_le in E2. apply Z.ltb_lt in E3.
        eapply semax_pre; [ | apply (HF _ F m); try assumption; reflexivity ].
        unfold loop_state. entailer!.
      * eapply ConseqFacts.semax_post''; [ | apply semax_skip].
        unfold R. cbv [overridePost switch_ret_assert case_post2 RA_normal normal_ret_assert].
        unfold loop_state. entailer!.
        unfold vb in *; destruct (ln_fastc m); [ | reflexivity]. apply Int.one_not_zero in H; contradiction.
  - apply semax_extract_prop; intro EF.
    assert (E0: stepf2 (f_flush F) lenfix_list distfix_list m = ln_slow_m (upd_s m (fun s => set_i_back s 0))).
    { rewrite (stepf2_LEN _ _ _ m HM). apply c_LEN_slow_eq; exact EF. }
    assert (W0: mwf3 (upd_s m (fun s => set_i_back s 0))) by (apply mwf3_set_back; auto; lia).
    eapply semax_seq'; [ apply ln_back0_ok | ].
    set (m0 := upd_s m (fun s => set_i_back s 0)) in *.
    assert (HM0: m_mode m0 = LEN) by exact HM. assert (HL0: m_leave m0 = 0) by exact HL.
    assert (B0: i_back (m_s m0) = 0) by reflexivity.
    clearbody m0.
    assert (HRb: RA_break R = RA_normal (case_post2 F m)) by reflexivity.
    assert (HRn: RA_normal R = fall_post5 F m LENEXT) by reflexivity.
    clearbody R.
    eapply semax_seq'; [ apply (HL1 _ F m0); auto; apply W0 | ].
    apply extract_exists_pre; intro here. apply extract_exists_pre; intro m1. apply extract_exists_pre; intro ok.
    apply semax_extract_prop; intro E1.
    pose proof (sw_lenbits _ (mw_s _ (proj1 W0))) as LB.
    destruct ok.
    + destruct (ln_after1 m0 here m1 W0 HM0 HL0 E1) as (W1 & S1 & L1 & B1 & EO & LK & NLK).
      assert (HM1: m_mode m1 = LEN) by (unfold m_mode; rewrite S1; exact HM0).
      apply ln_leave_go; [exact L1 | ].
      apply semax_seq with (Q := EX h2: entry, EX m2: mst, EX lv2: reptype t_code,
         !! (mwf3 m2 /\ m_mode m2 = LEN /\ m_leave m2 = 0 /\ entry_ok h2 /\ final_ok LENS h2 /\
             0 <= i_back (m_s m2) /\ i_back (m_s m2) + e_bits h2 <= 15 /\ e_bits h2 <= m_bits m2 /\
             stepf2 (f_flush F) lenfix_list distfix_list m = ln_tail_m h2 m2) && ls_hl F m2 (ent h2) lv2).
      * eapply semax_seq'; [ apply ln_ltest_ok; exact EO | ].
        destruct (islink LENS (e_op here)) eqn:ISL.
        -- (* a link: the sub-table *)
           destruct (LK eq_refl) as (sz & SZ & SO).
           apply ln_if_true. rewrite ln_link_eq. apply ln_copy_ok; [exact EO | ].
           rewrite <- S1 in SO, SZ.
           eapply semax_seq'; [ apply (HL2 _ F m1 here (ent here) sz); auto; apply W1 | ].
           apply extract_exists_pre; intro h2. apply extract_exists_pre; intro m2.
           apply extract_exists_pre; intro ok2. apply semax_extract_prop; intro E2.
           assert (EL: stepf2 (f_flush F) lenfix_list distfix_list m =
             match lookup2 lenfix_list distfix_list (i_lencode (m_s m1)) here m1 with
             | (h2, m2, false) => IBrk m2
             | (h2, m2, true) =>
                 ln_tail_m h2 (dropbits (e_bits here) (upd_s m2 (fun s => set_i_back s (i_back s + e_bits here))))
             end).
           { rewrite E0. unfold ln_slow_m. cbv zeta. rewrite E1. rewrite islink_lens in ISL. rewrite ISL.
             rewrite S1. reflexivity. }
           rewrite E2 in EL.
           destruct ok2.
           ++ destruct (ln_after2 m1 here sz h2 m2 (proj1 W1) L1 B1 SO E2)
                as (W2 & S2 & L2 & B2 & EO2 & F2 & BB & SB & BH2).
              apply ln_leave_go; [exact L2 | ].
              eapply semax_normal_override; [ apply ln_dropback_ok; auto; lia | ].
              destruct (ln_link_post m0 m1 m2 here h2 W1 S1 B0 HM1 W2 S2 L2 B2 BH2 BB ltac:(destruct EO; lia))
                as (W3' & HM3 & L3 & BK3 & BK4 & B3).
              Exists h2 (dropbits (e_bits here) (upd_s m2 (fun s => set_i_back s (i_back s + e_bits here))))
                (ent here).
              apply andp_right; [ | apply derives_refl]. apply prop_right.
              split; [exact W3'|]. split; [exact HM3|]. split; [exact L3|]. split; [exact EO2|].
              split; [exact F2|]. split; [exact BK3|]. split; [exact BK4|]. split; [exact B3|]. exact EL.
           ++ apply (ln_leave_brk F m m2); [ | exact EL | rewrite <- HRb; destruct R; reflexivity].
              exact (ln_after2_false m1 here sz h2 m2 (proj1 W1) L1 B1 SO E2).
        -- (* final *)
           apply ln_if_false.
           eapply semax_normal_override; [ apply semax_skip | ].
           destruct (NLK eq_refl) as [FB FF].
           Exists here m1 (default_val t_code).
           apply andp_right; [ | apply derives_refl]. apply prop_right.
           assert (BK1: i_back (m_s m1) = 0) by (rewrite S1; exact B0).
           split; [exact W1|]. split; [exact HM1|]. split; [exact L1|]. split; [exact EO|].
           split; [exact FF|]. split; [lia|]. split; [lia|]. split; [exact B1|].
           rewrite E0. unfold ln_slow_m. cbv zeta. rewrite E1. rewrite islink_lens in ISL. rewrite ISL. reflexivity.
      * apply extract_exists_pre; intro h2. apply extract_exists_pre; intro m2.
        apply extract_exists_pre; intro lv2. apply semax_extract_prop; intros (W2 & HM2 & L2 & EO2 & F2 & BK1 & BK2 & B2 & ET).
        eapply HT; eauto.
    + apply (ln_leave_brk F m m1 _ _ _ R); [ | | exact HRb].
      * exact (ln_after1_false m0 here m1 (proj1 W0) HM0 HL0 E1).
      * rewrite E0. unfold ln_slow_m. cbv zeta. rewrite E1. reflexivity.
Qed.
