(* case LEN (LnKit5.v): the decoding table and the lookup memory apart (ln_tab_stmt) *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate.LnKit5.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Lemma ln_tab_entry: forall s t i, tref_ok t -> Zlength (i_codes s) = ENOUGH_CODES -> 0 <= i ->
  tab_entry lenfix_list distfix_list s t i = Znth i (tab_list s t).
Proof.
  intros s t i Ht HL Hi. destruct t; simpl; auto.
  simpl in Ht. unfold ENOUGH_CODES in *.
  destruct (Z_lt_dec i (1444 - k)).
  - rewrite Znth_sublist by lia. f_equal; lia.
  - rewrite !Znth_overflow; auto; rewrite ?Zlength_sublist; lia.
Qed.

Lemma ln_tab_len: forall s t, tref_ok t -> Zlength (i_codes s) = ENOUGH_CODES -> Zlength (tab_list s t) = tab_size t.
Proof.
  intros s t Ht HL. destruct t; simpl.
  - reflexivity.
  - reflexivity.
  - simpl in Ht. rewrite Zlength_sublist; unfold ENOUGH_CODES in *; lia.
Qed.

Lemma codes_split: forall sp (codes: list entry) k, Zlength codes = ENOUGH_CODES -> 0 <= k <= ENOUGH_CODES ->
  field_at Ews t_state (DOT _codes) (map ent codes) sp =
  array_at Ews t_state (DOT _codes) 0 k (map ent (sublist 0 k codes)) sp *
  data_at Ews (tarray t_code (ENOUGH_CODES - k)) (map ent (sublist k ENOUGH_CODES codes)) (codes_at sp k).
Proof.
  intros sp codes k HL Hk. unfold ENOUGH_CODES in *.
  assert (legal_nested_field t_state (DOT _codes)) by (apply compute_legal_nested_field_spec'; repeat constructor).
  erewrite field_at_Tarray with (t0 := t_code) (n := 1444) (a := noattr); [ | auto | reflexivity | lia | apply JMeq_refl].
  rewrite (split2_array_at _ _ _ 0 k 1444) by (rewrite ?Zlength_map; lia).
  rewrite Zlength_map, HL, Z.sub_0_r, !sublist_map.
  f_equal.
  erewrite array_at_data_at''' by (first [reflexivity | lia]).
  reflexivity.
Qed.

Lemma pull35: forall a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35: mpred,
  a1 * a2 * a3 * a4 * a5 * a6 * a7 * a8 * a9 * a10 * a11 * a12 * a13 * a14 * a15 * a16 * a17 * a18 * a19 * a20 * a21 * a22 * a23 * a24 * a25 * a26 * a27 * a28 * a29 * a30 * a31 * a32 * a33 * a34 * a35 = a21 * a23 * a32 * (a1 * a2 * a3 * a4 * a5 * a6 * a7 * a8 * a9 * a10 * a11 * a12 * a13 * a14 * a15 * a16 * a17 * a18 * a19 * a20 * a22 * a24 * a25 * a26 * a27 * a28 * a29 * a30 * a31 * a33 * a34 * a35).
Proof. intros. apply pred_ext; cancel. Qed.

(* the 32 fields of state_rep but lencode, lenbits, codes *)
Definition state_rest (gv: globals) (sp strmp headp winp: val) (s: istate) : mpred :=
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
  field_at Ews t_state (DOT _distcode) (tref_val gv sp (i_distcode s)) sp *
  field_at Ews t_state (DOT _distbits) (zv (i_distbits s)) sp *
  field_at Ews t_state (DOT _ncode) (zv (i_ncode s)) sp *
  field_at Ews t_state (DOT _nlen) (zv (i_nlen s)) sp *
  field_at Ews t_state (DOT _ndist) (zv (i_ndist s)) sp *
  field_at Ews t_state (DOT _have) (zv (i_have s)) sp *
  field_at Ews t_state (DOT _next) (codes_at sp (i_next s)) sp *
  field_at Ews t_state (DOT _lens) (map (fun z => Vint (Int.repr z)) (i_lens s)) sp *
  field_at_ Ews t_state (DOT _work) sp *
  field_at Ews t_state (DOT _sane) (zv (i_sane s)) sp *
  field_at Ews t_state (DOT _back) (zv (i_back s)) sp *
  field_at Ews t_state (DOT _was) (zv (i_was s)) sp.

Lemma state_rep_pull: forall gv sp strmp headp winp s,
  state_rep gv sp strmp headp winp s =
  field_at Ews t_state (DOT _lencode) (tref_val gv sp (i_lencode s)) sp *
  field_at Ews t_state (DOT _lenbits) (zv (i_lenbits s)) sp *
  field_at Ews t_state (DOT _codes) (map ent (i_codes s)) sp *
  state_rest gv sp strmp headp winp s.
Proof. intros. unfold state_rep, state_rest. apply pull35. Qed.

Lemma wand_of_eq: forall P V: mpred, (exists R, P = V * R) -> P |-- V * (V -* P).
Proof.
  intros P V [R E]. rewrite E at 1. apply sepcon_derives; [apply derives_refl|].
  apply wand_sepcon_adjoint. rewrite sepcon_comm, E. apply derives_refl.
Qed.

Lemma rearr_lf: forall L B Cf Rs w h st I o lf df od it c: mpred,
  (L * B * Cf * Rs) * w * h * st * I * o * (lf * df * od * it) * c =
  (L * B * lf * I) * (Cf * Rs * w * h * st * o * df * od * it * c).
Proof. intros. apply pred_ext; cancel. Qed.

Lemma rearr_df: forall L B Cf Rs w h st I o lf df od it c: mpred,
  (L * B * Cf * Rs) * w * h * st * I * o * (lf * df * od * it) * c =
  (L * B * df * I) * (Cf * Rs * w * h * st * o * lf * od * it * c).
Proof. intros. apply pred_ext; cancel. Qed.

Lemma rearr_codes: forall L B pre C Rs w h st I o T c: mpred,
  (L * B * (pre * C) * Rs) * w * h * st * I * o * T * c =
  (L * B * C * I) * (pre * Rs * w * h * st * o * T * c).
Proof. intros. apply pred_ext; cancel. Qed.

Lemma ln_tab_mem: forall F m, tref_ok (i_lencode (m_s m)) -> Zlength (i_codes (m_s m)) = ENOUGH_CODES ->
  mem_rep F m |-- ln_view F m * (ln_view F m -* mem_rep F m).
Proof.
  intros F m Ht HL. apply wand_of_eq.
  unfold mem_rep, ln_view, tab_arr. rewrite state_rep_pull. unfold tables_rep.
  destruct (i_lencode (m_s m)) eqn:E; cbn [tab_sh tab_list tref_val tab_size].
  - eexists. apply rearr_lf.
  - eexists. apply rearr_df.
  - cbn in Ht. rewrite (codes_split _ _ k HL Ht). eexists. apply rearr_codes.
Qed.

Lemma ln_tab_ok : ln_tab_stmt.
Proof.
  split; [exact ln_tab_entry | split; [exact ln_tab_len | exact ln_tab_mem]].
Qed.
