(* DIST: the sub-table part (last = here, loop2, DROPBITS(last.bits), back) (part of the cases LENEXT/DIST, Cases5_LD.v; definitions and statements in LdKit5.v) *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate.LdKit5.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* ---------------------------------------------------------------------------------------------- *)
(* the field state->back apart (ModeKit.v's pattern; as in LnCase5.v of the case LEN)             *)

Definition dsl_state_rep_nb (gv: globals) (sp strmp headp winp: val) (s: istate) : mpred :=
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

Lemma dsl_sepcon_34th_35: forall a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35: mpred,
  a1 * a2 * a3 * a4 * a5 * a6 * a7 * a8 * a9 * a10 * a11 * a12 * a13 * a14 * a15 * a16 * a17 * a18 * a19 * a20 * a21 * a22 * a23 * a24 * a25 * a26 * a27 * a28 * a29 * a30 * a31 * a32 * a33 * a34 * a35 =
  a34 * (a1 * a2 * a3 * a4 * a5 * a6 * a7 * a8 * a9 * a10 * a11 * a12 * a13 * a14 * a15 * a16 * a17 * a18 * a19 * a20 * a21 * a22 * a23 * a24 * a25 * a26 * a27 * a28 * a29 * a30 * a31 * a32 * a33 * a35).
Proof. intros. apply pred_ext; cancel. Qed.

Lemma dsl_state_rep_split_b: forall gv sp strmp headp winp s,
  state_rep gv sp strmp headp winp s =
  field_at Ews t_state (DOT _back) (zv (i_back s)) sp * dsl_state_rep_nb gv sp strmp headp winp s.
Proof. intros. unfold state_rep, dsl_state_rep_nb. apply dsl_sepcon_34th_35. Qed.

Definition dsl_mem_rep_nb (F: frame) (m: mst) : mpred :=
  dsl_state_rep_nb (f_gv F) (f_sp F) (f_strmp F) (f_headp F) (f_winp F) (m_s m) *
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

Lemma dsl_sepcon_first_8: forall a b1 b2 b3 b4 b5 b6 b7 b8: mpred,
  (a * b1) * b2 * b3 * b4 * b5 * b6 * b7 * b8 = a * (b1 * b2 * b3 * b4 * b5 * b6 * b7 * b8).
Proof. intros. apply pred_ext; cancel. Qed.

Lemma dsl_mem_rep_split_b: forall F m,
  mem_rep F m = field_at Ews t_state (DOT _back) (zv (i_back (m_s m))) (f_sp F) * dsl_mem_rep_nb F m.
Proof. intros. unfold mem_rep, dsl_mem_rep_nb. rewrite dsl_state_rep_split_b. apply dsl_sepcon_first_8. Qed.

(* ld_hl with the back field apart *)
Definition ld_hlb (F: frame) (m: mst) (hv lv: reptype t_code) (v: val) : environ -> mpred :=
  PROPx [in_ok (f_ib F) (m_inp m); out_ok (f_ob F) (m_aout m)]
  (LOCALx (ld_locals F m)
  (SEPx [field_at Ews t_state (DOT _back) v (f_sp F); dsl_mem_rep_nb F m;
         data_at Tsh t_code hv (f_vhere F); data_at Tsh t_code lv (f_vlast F);
         data_at_ Tsh (tarray tuchar 4) (f_vhbuf F)])).

Lemma ld_hl_split_b: forall F m hv lv, ld_hl F m hv lv = ld_hlb F m hv lv (zv (i_back (m_s m))).
Proof.
  intros. unfold ld_hl, ld_hlb. rewrite dsl_mem_rep_split_b. f_equal. f_equal.
  unfold SEPx. extensionality rho. cbn [fold_right_sepcon]. rewrite !sepcon_assoc. reflexivity.
Qed.

Lemma ld_hl_set_back: forall F m hv lv x,
  ld_hl F (upd_s m (fun s => set_i_back s x)) hv lv = ld_hlb F m hv lv (zv x).
Proof. intros. rewrite ld_hl_split_b. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the statements                                                                                 *)

(* if (leave) break; with leave = 1: the pass ends with m1 *)
Lemma dsl_leave_brk {Espec: OracleKind} (F: frame) (m0 m1: mst) (hv lv: reptype t_code) (c: statement)
    (R: ret_assert):
  m_leave m1 = 1 -> stepf2 (f_flush F) lenfix_list distfix_list m0 = IBrk m1 ->
  RA_break R = RA_normal (case_post2 F m0) ->
  semax Delta_cases5 (ld_hl F m1 hv lv) (Ssequence ld_ifleave c) R.
Proof.
  intros L1 E HR.
  apply semax_seq with (Q := FF); [ | apply semax_pre with FF; [apply andp_left2, derives_refl | apply semax_ff]].
  pose proof (ld_hl_loop_state F m1 hv lv) as LS.
  eapply semax_pre; [apply andp_left2, LS | ].
  unfold loop_state, ld_ifleave. abbreviate_semax.
  rewrite L1. forward_if.
  - forward.
    match goal with |- _ |-- RA_break ?X => replace (RA_break X) with (RA_break R) by (destruct R; reflexivity) end.
    rewrite HR.
    unfold case_post2. cbv [RA_normal]. Exists m1. unfold loop_state. rewrite L1. entailer!.
  - match goal with H: Int.repr 1 = Int.zero |- _ => apply Int.one_not_zero in H; contradiction end.
Qed.

(* if (leave) break; with leave = 0 *)
Lemma dsl_leave_go {Espec: OracleKind} (F: frame) (m1: mst) (hv lv: reptype t_code) (c: statement)
    (R: ret_assert):
  m_leave m1 = 0 -> semax Delta_cases5 (ld_hl F m1 hv lv) c R ->
  semax Delta_cases5 (ld_hl F m1 hv lv) (Ssequence ld_ifleave c) R.
Proof.
  intros L1 HC.
  eapply semax_seq'; [ | exact HC].
  unfold ld_hl, ld_locals, ld_ifleave. abbreviate_semax.
  rewrite L1. forward_if.
  - match goal with H: Int.repr 0 <> Int.zero |- _ => exfalso; apply H; reflexivity end.
  - forward. rewrite L1. entailer!.
Qed.

Lemma dsl_dowhile0 {Espec: OracleKind} (Delta: tycontext) (P Q: environ -> mpred) (c rest: statement)
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

Lemma dsl_long_shru_eq: forall h n, 0 <= h <= Int64.max_unsigned -> 0 <= n < 64 ->
  Int64.shru (Int64.repr h) (Int64.repr n) = Int64.repr (Z.shiftr h n).
Proof.
  intros h n Hh Hn. unfold Int64.shru.
  rewrite (Int64.unsigned_repr h) by lia. rewrite (Int64.unsigned_repr n) by rep_lia. reflexivity.
Qed.

(* DROPBITS(last.bits); state->back += last.bits; *)
Lemma dsl_dropback_ok {Espec: OracleKind} (F: frame) (m: mst) (hv: reptype t_code) (l: entry):
  mwf m -> entry_ok l -> e_bits l <= m_bits m ->
  semax Delta_cases5 (ld_hl F m hv (ent l)) (Ssequence ds_dropl ds_backl)
    (normal_ret_assert (ld_hl F (ds_drop (e_bits l) m) hv (ent l))).
Proof.
  intros W EO B. destruct EO as (EO1 & EO2 & EO3).
  pose proof (mw_bits _ W) as WB. pose proof (mw_hold _ W) as WH. pose proof (sw_back _ (mw_s _ W)) as BK.
  unfold ds_drop.
  unfold ds_dropl, ds_backl, ds_l3, ds_l2, ds_l1, ds_link, ds_lif, ds_s2, ds_s1.
  cbv beta iota zeta delta [ds_body case_body inflate_LS find_switch f_inflate fn_body ls_drop].
  apply dsl_dowhile0 with (Q := ld_hl F (dropbits (e_bits l) m) hv (ent l)).
  - unfold ld_hl, ld_locals, ent. abbreviate_semax.
    forward. { entailer!. rep_lia. }
    forward. { entailer!. change (Int.unsigned Int64.iwordsize') with 64; lia. }
    forward. forward. entailer!.
    + unfold dropbits; cbn [m_hold m_bits set_m_bits set_m_hold].
      rewrite dsl_long_shru_eq by (unfold lrange in WH; lia). split; [reflexivity|].
      unfold u32. rewrite Z.mod_small by lia. reflexivity.
    + unfold dropbits. apply derives_refl.
  - change (dropbits (e_bits l) (upd_s m (fun s => set_i_back s (i_back s + e_bits l))))
      with (upd_s (dropbits (e_bits l) m) (fun s => set_i_back s (i_back (m_s m) + e_bits l))).
    rewrite ld_hl_set_back, ld_hl_split_b. unfold ld_hlb, ld_locals, ent. abbreviate_semax.
    forward. forward. { entailer!. rep_lia. } forward. entailer!.
Qed.

(* last = here; (op, bits, val) *)
Lemma dsl_copy_ok {Espec: OracleKind} (F: frame) (m: mst) (h: entry) (lv: reptype t_code) (X: statement)
    (R: ret_assert):
  entry_ok h ->
  semax Delta_cases5 (ld_hl F m (ent h) (ent h)) X R ->
  semax Delta_cases5 (ld_hl F m (ent h) lv) (Ssequence ds_c1 (Ssequence ds_c2 (Ssequence ds_c3 X))) R.
Proof.
  intros EO HX. destruct EO as (EO1 & EO2 & EO3).
  unfold ds_c1, ds_c2, ds_c3, ds_link, ds_lif, ds_s2, ds_s1.
  cbv beta iota zeta delta [ds_body case_body inflate_LS find_switch f_inflate fn_body ls_drop].
  unfold ld_hl at 1. unfold ld_locals, ent. abbreviate_semax.
  forward. { entailer!. rep_lia. } forward.
  forward. { entailer!. rep_lia. } forward.
  forward. { entailer!. rep_lia. } forward.
  rewrite !zero_ext_inrange by (rewrite Int.unsigned_repr by rep_lia; simpl; rep_lia).
  eapply semax_pre; [ | exact HX].
  unfold ld_hl, ld_locals, ent. entailer!.
Qed.

Lemma dsl_normal_override {Espec: OracleKind} (Delta: tycontext) (P P' Q: environ -> mpred) (c: statement)
    (R: ret_assert):
  semax Delta P c (normal_ret_assert P') -> P' |-- Q -> semax Delta P c (overridePost Q R).
Proof.
  intros H E. eapply semax_post; [ | | | | exact H]; intros; destruct R; simpl_ret_assert;
    first [apply andp_left2; exact E | apply andp_left2, FF_left | intros; apply andp_left2, FF_left].
Qed.

(* after the sub-table lookup *)
Lemma dsl_after2: forall m here sz h2 m2 ok, mwf m -> m_leave m = 0 -> e_bits here <= m_bits m ->
  sub_ok DISTS (tab_entry lenfix_list distfix_list (m_s m) (i_distcode (m_s m))) (i_distbits (m_s m)) sz here ->
  lookup2 lenfix_list distfix_list (i_distcode (m_s m)) here m = (h2, m2, ok) ->
  mwf m2 /\ (ok = true -> m_leave m2 = 0 /\ e_bits here + e_bits h2 <= m_bits m2 /\ 0 <= e_bits h2) /\
  (ok = false -> m_leave m2 = 1).
Proof.
  intros m here sz h2 m2 ok W L B SO E2.
  destruct SO as (SB & SO1 & SO2 & SBT).
  assert (SB2: forall j, 0 <= j < 2 ^ e_op here ->
    e_bits here + e_bits (tab_entry lenfix_list distfix_list (m_s m) (i_distcode (m_s m)) (e_val here + j)) <= 15).
  { intros j Hj. destruct (SBT j Hj) as (_ & _ & _ & A & _). lia. }
  assert (B0: 0 <= e_bits here) by (pose proof (proj1 (mw_s _ W).(sw_distbits _)); lia).
  pose proof (lookup2_ok lenfix_list distfix_list (i_distcode (m_s m)) here m W L ltac:(lia) ltac:(lia) SB2) as LK2.
  rewrite E2 in LK2. destruct LK2 as (W2 & S2 & OK2 & NOK).
  split; [exact W2|]. split.
  - intro T. subst ok. destruct (OK2 eq_refl) as (L2 & B2 & j & Hj & Eh2).
    destruct (SBT j Hj) as (_ & EO2 & _). cbv zeta in EO2. rewrite <- Eh2 in EO2.
    pose proof (proj1 (proj2 EO2)) as BH2.
    split; [exact L2 | split; [exact B2 | lia]].
  - intro T. subst ok. apply NOK; reflexivity.
Qed.

Lemma ds_link_ok : ds_loop2_stmt -> ds_link_stmt.
Proof.
  intros HL2. unfold ds_link_stmt.
  intros Espec F m0 m here lv sz R HF W HM HL Hsz SO EO B HR HBRK.
  rewrite ds_link_eq. apply dsl_copy_ok; [exact EO | ].
  eapply semax_seq'; [ apply (HL2 _ F m here (ent here) sz); auto | ].
  apply extract_exists_pre; intro h2. apply extract_exists_pre; intro m2.
  apply extract_exists_pre; intro ok2. apply semax_extract_prop; intro E2.
  destruct (dsl_after2 m here sz h2 m2 ok2 W HL B SO E2) as (W2 & OK2 & NOK2).
  destruct ok2.
  - destruct (OK2 eq_refl) as (L2 & B2 & BH2).
    apply dsl_leave_go; [exact L2 | ].
    eapply dsl_normal_override; [ apply dsl_dropback_ok; auto; lia | ].
    Exists h2 m2. apply andp_right; [ | apply derives_refl]. apply prop_right. exact E2.
  - apply (dsl_leave_brk F m0 m2); [ exact (NOK2 eq_refl) | exact (HBRK _ _ E2) | rewrite <- HR; destruct R; reflexivity ].
Qed.
