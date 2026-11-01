(* case LEN (LnKit5.v): the fast path RESTORE / inflate_fast / LOAD / back (ln_fast_stmt) *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate.LnKit5.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* ---------------------------------------------------------------------------------------------- *)
(* the model: what inflate_fast keeps                                                             *)

Definition fkey (m: mst) : list Z * Z * Z * Z * Z * Z :=
  (m_inp m, m_aout m, m_in m, m_out m, m_ret m, m_leave m).

Definition fk (m0 m: mst) : Prop :=
  fkey m = fkey m0 /\ (m_mode m = m_mode m0 \/ m_mode m = Model.TYPE \/ m_mode m = BAD).

Lemma fk_refl: forall m, fk m m.
Proof. intros. split; auto. Qed.

Lemma fk_trans: forall m0 m1 m2, fk m0 m1 -> fk m1 m2 -> fk m0 m2.
Proof.
  intros m0 m1 m2 [A B] [C D]. split; [congruence|].
  destruct D as [D|D]; [rewrite D; exact B | right; exact D].
Qed.

Lemma fk_pull: forall m0 m, fk m0 m -> fk m0 (pull m).
Proof. intros. exact H. Qed.
Lemma fk_ow: forall m0 m o, fk m0 m -> fk m0 (set_m_ow m o).
Proof. intros. exact H. Qed.
Lemma fk_hold: forall m0 m o, fk m0 m -> fk m0 (set_m_hold m o).
Proof. intros. exact H. Qed.
Lemma fk_bits: forall m0 m o, fk m0 m -> fk m0 (set_m_bits m o).
Proof. intros. exact H. Qed.
Lemma fk_nx: forall m0 m o, fk m0 m -> fk m0 (set_m_nx m o).
Proof. intros. exact H. Qed.
Lemma fk_restore: forall m0 m, fk m0 m -> fk m0 (restore m).
Proof. intros. exact H. Qed.
Lemma fk_type: forall m0 m, fk m0 m -> fk m0 (set_mode m Model.TYPE).
Proof. intros m0 m [A _]. split; [exact A | right; left; reflexivity]. Qed.
Lemma fk_bad: forall m0 m e, fk m0 m -> fk m0 (set_bad m e).
Proof. intros m0 m e [A _]. split; [exact A | right; right; reflexivity]. Qed.

Lemma fk_fwalk: forall k l t e m h m1 m0,
  fwalk_f lenfix_list distfix_list k l t e m = (h, m1) -> fk m0 m -> fk m0 m1.
Proof.
  induction k; intros l t e m h m1 m0 E H; simpl in E.
  - inversion E; subst. exact H.
  - destruct (l (e_op e)).
    + eapply IHk; [exact E | exact H].
    + inversion E; subst. exact H.
Qed.

Lemma fk_if: forall (b: bool) m0 m1 m2, fk m0 m1 -> fk m0 m2 -> fk m0 (if b then m1 else m2).
Proof. intros. destruct b; auto. Qed.

Lemma fk_fpull: forall m0 m, fk m0 m -> fk m0 (fpull m).
Proof. intros. exact H. Qed.

Ltac fkt := repeat match goal with
  | H: fk ?a ?b |- fk ?a ?b => exact H
  | |- fk _ (pull _) => apply fk_pull
  | |- fk _ (fpull _) => apply fk_fpull
  | |- fk _ (set_m_ow _ _) => apply fk_ow
  | |- fk _ (set_m_hold _ _) => apply fk_hold
  | |- fk _ (set_m_bits _ _) => apply fk_bits
  | |- fk _ (set_m_nx _ _) => apply fk_nx
  | |- fk _ (restore _) => apply fk_restore
  | |- fk _ (set_mode _ Model.TYPE) => apply fk_type
  | |- fk _ (set_bad _ _) => apply fk_bad
  | |- fk _ (if _ then _ else _) => apply fk_if
  | E: fwalk_f _ _ _ _ _ _ _ = (_, ?mm) |- fk _ ?mm => apply (fk_fwalk _ _ _ _ _ _ _ _ E)
  end.

Lemma fk_iter: forall m0 m, fk m0 m -> fk m0 (snd (fast_iter lenfix_list distfix_list m)).
Proof.
  intros m0 m H. unfold fast_iter. cbv beta iota zeta.
  repeat match goal with
  | |- fk _ (snd (if ?b then _ else _)) => destruct b
  | |- fk _ (snd (match ?p with (_, _) => _ end)) => destruct p as [?x ?y] eqn:?
  end; cbn [snd].
  all: repeat match goal with
  | E: (if ?b then _ else _) = (_, _) |- _ => destruct b; injection E; clear E; intros; subst
  end.
  all: fkt.
Qed.

Lemma fk_loop: forall k m0 m, fk m0 m -> fk m0 (fast_loop lenfix_list distfix_list k m).
Proof.
  induction k; intros m0 m H; simpl; [exact H|].
  pose proof (fk_iter m0 m H) as H1.
  destruct (fast_iter lenfix_list distfix_list m) as [g m1]. cbn [snd] in H1.
  destruct (_ && _)%bool; [apply IHk; exact H1 | exact H1].
Qed.

Lemma fk_fast: forall m0 m, fk m0 m -> fk m0 (fast lenfix_list distfix_list m).
Proof.
  intros m0 m H. unfold fast. cbv beta zeta.
  apply fk_restore, fk_bits, fk_hold, fk_nx, fk_loop, H.
Qed.

Lemma restore_facts: forall x,
  m_snx (restore x) = m_nx (restore x) /\ m_sow (restore x) = Zlength (m_ow (restore x)) /\
  i_hold (m_s (restore x)) = m_hold (restore x) /\ i_bits (m_s (restore x)) = m_bits (restore x).
Proof. intros. repeat split. Qed.

Lemma fast_restored: forall x, let y := fast lenfix_list distfix_list x in
  m_snx y = m_nx y /\ m_sow y = Zlength (m_ow y) /\ i_hold (m_s y) = m_hold y /\ i_bits (m_s y) = m_bits y.
Proof. intros. unfold y, fast. cbv beta zeta. apply restore_facts. Qed.

Lemma mwf_restore: forall m, mwf m -> mwf (restore m).
Proof.
  intros m W. pose proof (mw_hold _ W) as WH. pose proof (mw_bits _ W) as WB. pose proof (mw_nx _ W) as WN.
  destruct W. constructor; cbn [restore upd_s set_m_s set_m_sow set_m_snx m_s m_h m_inp m_aout m_nx m_ow m_hold
    m_bits m_in m_out m_ret m_leave m_adler m_msg m_tin m_tout m_snx m_sow m_mode]; auto.
  - destruct mw_md; constructor; assumption.
  - destruct mw_s; constructor; cbn [set_i_bits set_i_hold i_mode i_last i_wrap i_havedict i_flags i_dmax i_check
      i_total i_head i_wbits i_wsize i_whave i_wnext i_win i_wdata i_hold i_bits i_length i_offset i_extra
      i_lencode i_distcode i_lenbits i_distbits i_ncode i_nlen i_ndist i_have i_next i_lens i_codes i_sane
      i_back i_was]; auto.
  - pose proof (Zlength_nonneg (m_ow m)). lia.
Qed.

Lemma fast_ok_restore: forall m, mwf3 m -> m_mode m = LEN -> fast_ok (restore m).
Proof.
  intros m [W S] HM. split; [apply mwf_restore; exact W|].
  destruct S. exact (s3_len ltac:(unfold decode_mode; right; left; exact HM)).
Qed.

Lemma ln_fast_model: forall fl m, m_mode m = LEN -> 6 <= m_have m -> 258 <= m_left m -> m_bits m < 8 ->
  stepf2 fl lenfix_list distfix_list m =
  IBrk (let m' := fast lenfix_list distfix_list (restore m) in
        if m_mode m' =? Model.TYPE then upd_s m' (fun s => set_i_back s (-1)) else m').
Proof.
  intros fl m HM H1 H2 H3. rewrite (stepf2_LEN _ _ _ m HM). unfold c_LEN.
  replace ((6 <=? m_have m) && (258 <=? m_left m) && (m_bits m <? 8))%bool with true; [reflexivity|].
  symmetry. apply andb_true_intro; split; [apply andb_true_intro; split|]; [apply Z.leb_le | apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the memory with the fields the fast path touches apart: mode, hold, bits, back, the stream      *)

Definition state_rest (gv: globals) (sp strmp headp winp: val) (s: istate) : mpred :=
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

Lemma sep_pull4_35: forall a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35: mpred,
  a1 * a2 * a3 * a4 * a5 * a6 * a7 * a8 * a9 * a10 * a11 * a12 * a13 * a14 * a15 * a16 * a17 * a18 * a19 * a20 * a21 * a22 * a23 * a24 * a25 * a26 * a27 * a28 * a29 * a30 * a31 * a32 * a33 * a34 * a35 =
  a2 * a16 * a17 * a34 * (a1 * a3 * a4 * a5 * a6 * a7 * a8 * a9 * a10 * a11 * a12 * a13 * a14 * a15 * a18 * a19 * a20 * a21 * a22 * a23 * a24 * a25 * a26 * a27 * a28 * a29 * a30 * a31 * a32 * a33 * a35).
Proof. intros. apply pred_ext; cancel. Qed.

Lemma state_rep_split4: forall gv sp strmp headp winp s,
  state_rep gv sp strmp headp winp s =
  field_at Ews t_state (DOT _mode) (zv (i_mode s)) sp * field_at Ews t_state (DOT _hold) (lv (i_hold s)) sp *
  field_at Ews t_state (DOT _bits) (zv (i_bits s)) sp * field_at Ews t_state (DOT _back) (zv (i_back s)) sp *
  state_rest gv sp strmp headp winp s.
Proof. intros. unfold state_rep, state_rest. apply sep_pull4_35. Qed.

Definition strm_m (F: frame) (m: mst) : mpred :=
  strm_rep (f_gv F) (f_shs F) (f_strmp F)
    (in_ptr (f_ib F) (m_snx m)) (zv (Zlength (m_inp m) - m_snx m)) (m_tin m)
    (out_ptr (f_ob F) (m_sow m)) (zv (m_aout m - m_sow m)) (m_tout m)
    (msg_val (f_gv F) (m_msg m)) (f_sp F) (f_dt F) (m_adler m) (f_vres F).

Definition mem_rest (F: frame) (m: mst) : mpred :=
  state_rest (f_gv F) (f_sp F) (f_strmp F) (f_headp F) (f_winp F) (m_s m) *
  win_rep (f_winp F) (m_s m) *
  head_part F m *
  in_rep (f_ib F) *
  out_rep (f_ob F) (m_ow m) *
  tables_rep (f_gsh F) (f_gv F) *
  crc_table_at (f_tsh F) (f_gv F).

Lemma mem_rep_split4: forall F m,
  mem_rep F m =
  field_at Ews t_state (DOT _mode) (zv (m_mode m)) (f_sp F) *
  field_at Ews t_state (DOT _hold) (lv (i_hold (m_s m))) (f_sp F) *
  field_at Ews t_state (DOT _bits) (zv (i_bits (m_s m))) (f_sp F) *
  field_at Ews t_state (DOT _back) (zv (i_back (m_s m))) (f_sp F) *
  strm_m F m * mem_rest F m.
Proof.
  intros. unfold mem_rep, mem_rest, strm_m. rewrite state_rep_split4. unfold m_mode.
  apply pred_ext; cancel.
Qed.

Lemma mem_rest_restore: forall F m, mem_rest F (restore m) = mem_rest F m.
Proof. reflexivity. Qed.

Lemma mem_rest_back: forall F m v, mem_rest F (upd_s m (fun s => set_i_back s v)) = mem_rest F m.
Proof. reflexivity. Qed.

Lemma strm_m_back: forall F m v, strm_m F (upd_s m (fun s => set_i_back s v)) = strm_m F m.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the Clight of the fast path                                                                    *)

Definition lf_restore : statement := match ln_fast with Ssequence r _ => r | _ => Sskip end.
Definition lf_call : statement := match ln_fast with Ssequence _ (Ssequence c _) => c | _ => Sskip end.
Definition lf_load : statement := match ln_fast with Ssequence _ (Ssequence _ (Ssequence l _)) => l | _ => Sskip end.
Definition lf_tail : statement := match ln_fast with Ssequence _ (Ssequence _ (Ssequence _ t)) => t | _ => Sskip end.

Lemma ln_fast_eq: ln_fast = Ssequence lf_restore (Ssequence lf_call (Ssequence lf_load lf_tail)).
Proof. reflexivity. Qed.

Ltac lf_stmt := cbv beta iota zeta delta [lf_restore lf_call lf_load lf_tail ln_fast ln_head ln_body
  case_body inflate_LS find_switch f_inflate fn_body ls_drop].

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

Lemma mem_rep_restore_eq: forall F m,
  mem_rep F (restore m) =
  field_at Ews t_state (DOT _mode) (zv (m_mode m)) (f_sp F) *
  field_at Ews t_state (DOT _hold) (lv (m_hold m)) (f_sp F) *
  field_at Ews t_state (DOT _bits) (zv (m_bits m)) (f_sp F) *
  field_at Ews t_state (DOT _back) (zv (i_back (m_s m))) (f_sp F) *
  strm_rep (f_gv F) (f_shs F) (f_strmp F)
    (in_ptr (f_ib F) (m_nx m)) (zv (m_have m)) (m_tin m)
    (out_ptr (f_ob F) (Zlength (m_ow m))) (zv (m_left m)) (m_tout m)
    (msg_val (f_gv F) (m_msg m)) (f_sp F) (f_dt F) (m_adler m) (f_vres F) *
  mem_rest F m.
Proof. intros. rewrite mem_rep_split4, mem_rest_restore. reflexivity. Qed.

(* RESTORE() *)
Lemma lf_restore_ok {Espec: OracleKind} (F: frame) (m: mst) :
  frame_ok5 F ->
  semax Delta_cases5 (loop_state F m) lf_restore
    (normal_ret_assert (PROPx [in_ok (f_ib F) (m_inp m); out_ok (f_ob F) (m_aout m)]
      (LOCALx (ln_locals F m) (SEPx [mem_rep F (restore m); locals_rep F])))).
Proof.
  cbv beta iota zeta delta [lf_restore ln_fast ln_head ln_body case_body inflate_LS find_switch f_inflate fn_body ls_drop].
  intros [[HS _] _].
  apply semax_dowhile0.
  unfold loop_state, ln_locals. rewrite mem_rep_split4, mem_rep_restore_eq. unfold strm_m, strm_rep.
  remember (f_gv F _zcalloc) as zca eqn:Hzca. remember (f_gv F _zcfree) as zcf eqn:Hzcf.
  abbreviate_semax. Intros.
  forward. forward. forward. forward. forward. forward.
  entailer!.
Qed.

(* inflate_fast(strm, out) *)
Lemma lf_call_ok {Espec: OracleKind} (F: frame) (m: mst) :
  frame_ok5 F -> mwf3 m -> m_mode m = LEN -> 6 <= m_have m -> 258 <= m_left m -> m_bits m < 8 ->
  semax Delta_cases5
    (PROPx [in_ok (f_ib F) (m_inp m); out_ok (f_ob F) (m_aout m)]
      (LOCALx (ln_locals F m) (SEPx [mem_rep F (restore m); locals_rep F])))
    lf_call
    (normal_ret_assert (PROPx [in_ok (f_ib F) (m_inp m); out_ok (f_ob F) (m_aout m)]
      (LOCALx (ln_locals F m) (SEPx [mem_rep F (fast lenfix_list distfix_list (restore m)); locals_rep F])))).
Proof.
  intros [[HS1 [HS2 [HS3 HS4]]] _] W HM H6 H258 H8.
  pose proof (fast_ok_restore m W HM) as FO.
  pose proof (mwf_out_eq m (mwf3_mwf m W)) as HO.
  rewrite HM in HO. specialize (HO ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)).
  cbv beta iota zeta delta [lf_call ln_fast ln_head ln_body case_body inflate_LS find_switch f_inflate fn_body ls_drop].
  unfold ln_locals. abbreviate_semax. Intros.
  forward_call (F, restore m).
  entailer!.
Qed.

(* a machine after RESTORE: the stream and state fields are the locals *)
Lemma mem_rep_restored_eq: forall F m,
  m_snx m = m_nx m -> m_sow m = Zlength (m_ow m) -> i_hold (m_s m) = m_hold m -> i_bits (m_s m) = m_bits m ->
  mem_rep F m =
  field_at Ews t_state (DOT _mode) (zv (m_mode m)) (f_sp F) *
  field_at Ews t_state (DOT _hold) (lv (m_hold m)) (f_sp F) *
  field_at Ews t_state (DOT _bits) (zv (m_bits m)) (f_sp F) *
  field_at Ews t_state (DOT _back) (zv (i_back (m_s m))) (f_sp F) *
  strm_rep (f_gv F) (f_shs F) (f_strmp F)
    (in_ptr (f_ib F) (m_nx m)) (zv (m_have m)) (m_tin m)
    (out_ptr (f_ob F) (Zlength (m_ow m))) (zv (m_left m)) (m_tout m)
    (msg_val (f_gv F) (m_msg m)) (f_sp F) (f_dt F) (m_adler m) (f_vres F) *
  mem_rest F m.
Proof.
  intros F m A B C D. rewrite mem_rep_split4. unfold strm_m, m_have, m_left. rewrite A, B, C, D. reflexivity.
Qed.

Lemma out_ptr_tc: forall ob a k, out_ok ob a -> tc_val (tptr tuchar) (out_ptr ob k).
Proof. intros [sh p lo n c] a k (_ & P & _). destruct p; try contradiction. exact I. Qed.

Lemma in_ptr_tc: forall ib inp k, in_ok ib inp -> tc_val (tptr tuchar) (in_ptr ib k).
Proof.
  intros [|sh p lo n c] inp k H; simpl.
  - reflexivity.
  - destruct H as (_ & P & _). destruct p; try contradiction. exact I.
Qed.

(* LOAD() *)
Lemma lf_load_ok {Espec: OracleKind} (F: frame) (m m': mst) :
  frame_ok5 F ->
  m_snx m' = m_nx m' -> m_sow m' = Zlength (m_ow m') -> i_hold (m_s m') = m_hold m' -> i_bits (m_s m') = m_bits m' ->
  fkey m' = fkey m ->
  semax Delta_cases5
    (PROPx [in_ok (f_ib F) (m_inp m); out_ok (f_ob F) (m_aout m)]
      (LOCALx (ln_locals F m) (SEPx [mem_rep F m'; locals_rep F])))
    lf_load (normal_ret_assert (loop_state F m')).
Proof.
  intros [[HS _] _] A B C D K. unfold fkey in K.
  injection K as K1 K2 K3 K4 K5 K6. unfold ln_locals. rewrite <- K1, <- K2, <- K3, <- K4, <- K5, <- K6.
  cbv beta iota zeta delta [lf_load ln_fast ln_head ln_body case_body inflate_LS find_switch f_inflate fn_body ls_drop].
  apply semax_dowhile0.
  unfold loop_state, ln_locals. rewrite (mem_rep_restored_eq F m' A B C D). unfold strm_rep.
  remember (f_gv F _zcalloc) as zca eqn:Hzca. remember (f_gv F _zcfree) as zcf eqn:Hzcf.
  abbreviate_semax. Intros.
  pose proof (out_ptr_tc (f_ob F) _ (Zlength (m_ow m')) H0) as T1.
  pose proof (in_ptr_tc (f_ib F) _ (m_nx m') H) as T2.
  forward. forward. forward. forward. forward. forward.
  entailer!.
Qed.

(* if (state->mode == TYPE) state->back = -1; break; *)
Lemma lf_tail_ok {Espec: OracleKind} (F: frame) (m0 m': mst) (R: ret_assert) :
  (m_mode m' = LEN \/ m_mode m' = Model.TYPE \/ m_mode m' = BAD) ->
  stepf2 (f_flush F) lenfix_list distfix_list m0 =
    IBrk (if m_mode m' =? Model.TYPE then upd_s m' (fun s => set_i_back s (-1)) else m') ->
  RA_break R = RA_normal (case_post2 F m0) ->
  semax Delta_cases5 (loop_state F m') lf_tail R.
Proof.
  intros HMd Hst HR.
  cbv beta iota zeta delta [lf_tail ln_fast ln_head ln_body case_body inflate_LS find_switch f_inflate fn_body ls_drop].
  unfold loop_state. rewrite mem_rep_split4.
  destruct HMd as [E|[E|E]]; rewrite E in Hst |- *.
  - change (LEN =? Model.TYPE) with false in Hst. cbv beta iota in Hst.
    abbreviate_semax. Intros. forward. apply semax_if_seq. forward_if.
    + exfalso. apply (f_equal Int.unsigned) in H1. rewrite !Int.unsigned_repr in H1 by (unfold LEN; rep_lia).
      unfold LEN in H1. lia.
    + eapply semax_pre; [ | apply semax_break]. rewrite HR. unfold case_post2. cbn [RA_normal].
      Exists m'. apply andp_right; [apply prop_right; exact Hst|].
      unfold loop_state. rewrite mem_rep_split4, E. entailer!.
  - change (Model.TYPE =? Model.TYPE) with true in Hst. cbv beta iota in Hst.
    abbreviate_semax. Intros. forward. apply semax_if_seq. forward_if.
    + forward. eapply semax_pre; [ | apply semax_break]. rewrite HR. unfold case_post2. cbn [RA_normal].
      Exists (upd_s m' (fun s => set_i_back s (-1))). apply andp_right; [apply prop_right; exact Hst|].
      unfold loop_state. rewrite mem_rep_split4, strm_m_back, mem_rest_back.
      unfold m_mode in E |- *. cbn [upd_s set_m_s m_s set_i_back i_mode i_hold i_bits i_back m_inp m_aout m_nx m_ow
        m_have m_left m_hold m_bits m_in m_out m_ret m_leave].
      rewrite E. entailer!.
    + exfalso. apply H1. reflexivity.
  - change (BAD =? Model.TYPE) with false in Hst. cbv beta iota in Hst.
    abbreviate_semax. Intros. forward. apply semax_if_seq. forward_if.
    + exfalso. apply (f_equal Int.unsigned) in H1. rewrite !Int.unsigned_repr in H1 by (unfold BAD; rep_lia).
      unfold BAD in H1. lia.
    + eapply semax_pre; [ | apply semax_break]. rewrite HR. unfold case_post2. cbn [RA_normal].
      Exists m'. apply andp_right; [apply prop_right; exact Hst|].
      unfold loop_state. rewrite mem_rep_split4, E. entailer!.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the fast path                                                                                  *)

Lemma ln_fast_ok : ln_fast_stmt.
Proof.
  intros Espec F m R HF W HM HL H6 H258 H8 HR.
  pose proof (ln_fast_model (f_flush F) m HM H6 H258 H8) as Hst. cbv zeta in Hst.
  pose proof (fast_restored (restore m)) as (A & B & C & D). cbv zeta in A, B, C, D.
  pose proof (fk_fast (restore m) (restore m) (fk_refl _)) as [K Md].
  change (m_mode (restore m)) with (m_mode m) in Md. rewrite HM in Md.
  change (fkey (restore m)) with (fkey m) in K.
  rewrite ln_fast_eq.
  eapply semax_seq'; [exact (lf_restore_ok F m HF)|].
  eapply semax_seq'; [exact (lf_call_ok F m HF W HM H6 H258 H8)|].
  eapply semax_seq'; [exact (lf_load_ok F m _ HF A B C D K)|].
  exact (lf_tail_ok F m _ R Md Hst HR).
Qed.
