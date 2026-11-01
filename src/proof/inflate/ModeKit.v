(* The mode field of inflate()'s state alone: state_rep = field_at mode * state_rep_nm (the 33 other
   fields), so that `state->mode = X;` changes one field_at and the rest of the memory stays one opaque
   SEP item (mem_rep_nm, unchanged by set_mode).  semax_store_mode: the store, for any mode value. *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Export Zlib.proof.inflate.CaseCommon.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.inflate.MwfLemmas.

#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Definition state_rep_nm (gv: globals) (sp strmp headp winp: val) (s: istate) : mpred :=
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

(* the second of 35 separating conjuncts to the front (on variables: a cheap proof term) *)
Lemma sepcon_second_35: forall a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35: mpred,
  a1 * a2 * a3 * a4 * a5 * a6 * a7 * a8 * a9 * a10 * a11 * a12 * a13 * a14 * a15 * a16 * a17 * a18 * a19 * a20 * a21 * a22 * a23 * a24 * a25 * a26 * a27 * a28 * a29 * a30 * a31 * a32 * a33 * a34 * a35 =
  a2 * (a1 * a3 * a4 * a5 * a6 * a7 * a8 * a9 * a10 * a11 * a12 * a13 * a14 * a15 * a16 * a17 * a18 * a19 * a20 * a21 * a22 * a23 * a24 * a25 * a26 * a27 * a28 * a29 * a30 * a31 * a32 * a33 * a34 * a35).
Proof.
  intros. rewrite !sepcon_assoc. rewrite <- (sepcon_assoc a1), (sepcon_comm a1 a2), sepcon_assoc. reflexivity.
Qed.

Lemma state_rep_split: forall gv sp strmp headp winp s,
  state_rep gv sp strmp headp winp s =
  field_at Ews t_state (DOT _mode) (zv (i_mode s)) sp * state_rep_nm gv sp strmp headp winp s.
Proof.
  (* not by cancel: its proof term on 35 field_ats takes the kernel 73 s *)
  intros. unfold state_rep, state_rep_nm. apply sepcon_second_35.
Qed.

Definition mem_rep_nm (F: frame) (m: mst) : mpred :=
  state_rep_nm (f_gv F) (f_sp F) (f_strmp F) (f_headp F) (f_winp F) (m_s m) *
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

Lemma mem_rep_split: forall F m,
  mem_rep F m = field_at Ews t_state (DOT _mode) (zv (m_mode m)) (f_sp F) * mem_rep_nm F m.
Proof.
  intros. unfold mem_rep, mem_rep_nm. rewrite state_rep_split. unfold m_mode.
  apply pred_ext; cancel.
Qed.

Lemma mem_rep_nm_set_mode: forall F m md, mem_rep_nm F (set_mode m md) = mem_rep_nm F m.
Proof. reflexivity. Qed.

(* loop_state with the mode field (value v) apart *)
Definition loop_state_m (F: frame) (m: mst) (v: val) : environ -> mpred :=
  PROP (in_ok (f_ib F) (m_inp m); out_ok (f_ob F) (m_aout m))
  LOCAL (temp _strm (f_strmp F); temp _flush (zv (f_flush F)); temp _state (f_sp F);
         temp _next (in_ptr (f_ib F) (m_nx m)); temp _put (out_ptr (f_ob F) (Zlength (m_ow m)));
         temp _have (zv (m_have m)); temp _left (zv (m_left m)); temp _hold (lv (m_hold m));
         temp _bits (zv (m_bits m)); temp _in (zv (m_in m)); temp _out (zv (m_out m));
         temp _ret (zv (m_ret m)); temp _leave (zv (m_leave m));
         lvar _here t_code (f_vhere F); lvar _last t_code (f_vlast F);
         lvar _hbuf (tarray tuchar 4) (f_vhbuf F); gvars (f_gv F))
  SEP (field_at Ews t_state (DOT _mode) v (f_sp F); mem_rep_nm F m; locals_rep F).

Lemma loop_state_split: forall F m, loop_state F m = loop_state_m F m (zv (m_mode m)).
Proof.
  intros. unfold loop_state, loop_state_m. rewrite mem_rep_split.
  f_equal. unfold SEPx. simpl. rewrite !sepcon_assoc. reflexivity.
Qed.

Lemma loop_state_set_mode: forall F m md, loop_state F (set_mode m md) = loop_state_m F m (zv md).
Proof. intros. rewrite loop_state_split. reflexivity. Qed.

(* state->mode = md; *)
Lemma semax_store_mode {Espec: OracleKind} (F: frame) (m: mst) (md: Z):
  semax Delta_inflate (loop_state F m)
    (Sassign (Efield (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                       (Tstruct _inflate_state noattr)) _mode tint)
       (Econst_int (Int.repr md) tint))
    (normal_ret_assert (loop_state F (set_mode m md))).
Proof.
  rewrite loop_state_set_mode, loop_state_split. unfold loop_state_m.
  abbreviate_semax.
  forward.
  entailer!.
Qed.

(* mwf after a change between the modes that need only the decoding tables (LEN_, LEN, LIT), from a
   decoding mode.  Do not prove such side goals with `apply mwf_set_mode; auto`: it took > 5 min. *)
Lemma mwf_set_mode_tables: forall m md,
  mwf m -> decode_mode (m_mode m) -> md = LEN_ \/ md = LEN \/ md = LIT -> mwf (set_mode m md).
Proof.
  intros m md W D Hmd.
  assert (Hr: HEAD <= md <= SYNC) by (unfold HEAD, SYNC, LEN_, LEN, LIT in *; lia).
  pose proof (md_tables _ (mw_md _ W) D) as T.
  assert (Hne: forall P: Prop,
    md = LENLENS \/ md = CODELENS \/ md = LENEXT \/ md = DIST \/ md = DISTEXT \/ md = MATCH -> P).
  { intros P H. exfalso. unfold LENLENS, CODELENS, LENEXT, DIST, DISTEXT, MATCH, LEN_, LEN, LIT in *. lia. }
  assert (O: m_out m = m_aout m).
  { apply mwf_out_eq; [exact W | | | ]; intro E; rewrite E in D;
      unfold decode_mode, LENGTH, DONE, BAD, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT in D; lia. }
  apply (mwf_set_mode m md W Hr);
    [ intro; apply Hne; tauto | intro; apply Hne; tauto | intros _; exact T
    | intro; apply Hne; tauto | intro; apply Hne; tauto | intro; apply Hne; tauto
    | intro; apply Hne; tauto | intro; apply Hne; tauto | intro; apply Hne; tauto
    | intro; apply Hne; tauto | intro; apply Hne; tauto | left; exact O ].
Qed.
