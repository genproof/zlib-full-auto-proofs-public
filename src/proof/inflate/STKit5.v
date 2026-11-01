(* Kit of the cases STORED, COPY_, COPY (Cases5_ST.v): loop_state with the fields mode and length of the
   state, the input object and the output object apart, the rest of the memory one opaque SEP item
   (mem_rep_io), so that these cases see 7 SEP items (which keeps the cost of Qed low). *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Export Zlib.proof.inflate.ModeKit5.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Definition state_rep_nml (gv: globals) (sp strmp headp winp: val) (s: istate) : mpred :=
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

Lemma sepcon_17th_34: forall a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34: mpred,
  a1 * a2 * a3 * a4 * a5 * a6 * a7 * a8 * a9 * a10 * a11 * a12 * a13 * a14 * a15 * a16 * a17 * a18 * a19 * a20 * a21 * a22 * a23 * a24 * a25 * a26 * a27 * a28 * a29 * a30 * a31 * a32 * a33 * a34 =
  a17 * (a1 * a2 * a3 * a4 * a5 * a6 * a7 * a8 * a9 * a10 * a11 * a12 * a13 * a14 * a15 * a16 * a18 * a19 * a20 * a21 * a22 * a23 * a24 * a25 * a26 * a27 * a28 * a29 * a30 * a31 * a32 * a33 * a34).
Proof. intros. apply pred_ext; cancel. Qed.

Lemma state_rep_nm_split_l: forall gv sp strmp headp winp s,
  state_rep_nm gv sp strmp headp winp s =
  field_at Ews t_state (DOT _length) (zv (i_length s)) sp * state_rep_nml gv sp strmp headp winp s.
Proof. intros. unfold state_rep_nm, state_rep_nml. apply sepcon_17th_34. Qed.

(* the memory but the fields mode and length, the input and the output objects *)
Definition mem_rep_io (F: frame) (m: mst) : mpred :=
  state_rep_nml (f_gv F) (f_sp F) (f_strmp F) (f_headp F) (f_winp F) (m_s m) *
  win_rep (f_winp F) (m_s m) *
  head_part F m *
  strm_rep (f_gv F) (f_shs F) (f_strmp F)
    (in_ptr (f_ib F) (m_snx m)) (zv (Zlength (m_inp m) - m_snx m)) (m_tin m)
    (out_ptr (f_ob F) (m_sow m)) (zv (m_aout m - m_sow m)) (m_tout m)
    (msg_val (f_gv F) (m_msg m)) (f_sp F) (f_dt F) (m_adler m) (f_vres F) *
  tables_rep (f_gsh F) (f_gv F) *
  crc_table_at (f_tsh F) (f_gv F).

Lemma mem_rep_nm_split_io: forall F m,
  mem_rep_nm F m = field_at Ews t_state (DOT _length) (zv (i_length (m_s m))) (f_sp F) *
    in_rep (f_ib F) * out_rep (f_ob F) (m_ow m) * mem_rep_io F m.
Proof.
  intros. unfold mem_rep_nm, mem_rep_io. rewrite state_rep_nm_split_l.
  apply pred_ext; cancel.
Qed.

(* loop_state with the mode (value v) and length (value l) fields, the input and output objects apart *)
Definition loop_state_st (F: frame) (m: mst) (v l: val) : environ -> mpred :=
  PROP (in_ok (f_ib F) (m_inp m); out_ok (f_ob F) (m_aout m))
  LOCAL (temp _strm (f_strmp F); temp _flush (zv (f_flush F)); temp _state (f_sp F);
         temp _next (in_ptr (f_ib F) (m_nx m)); temp _put (out_ptr (f_ob F) (Zlength (m_ow m)));
         temp _have (zv (m_have m)); temp _left (zv (m_left m)); temp _hold (lv (m_hold m));
         temp _bits (zv (m_bits m)); temp _in (zv (m_in m)); temp _out (zv (m_out m));
         temp _ret (zv (m_ret m)); temp _leave (zv (m_leave m));
         lvar _here t_code (f_vhere F); lvar _last t_code (f_vlast F);
         lvar _hbuf (tarray tuchar 4) (f_vhbuf F); gvars (f_gv F))
  SEP (field_at Ews t_state (DOT _mode) v (f_sp F);
       field_at Ews t_state (DOT _length) l (f_sp F);
       in_rep (f_ib F); out_rep (f_ob F) (m_ow m);
       mem_rep_io F m; locals_rep F).

Lemma loop_state_split_st: forall F m,
  loop_state F m = loop_state_st F m (zv (m_mode m)) (zv (i_length (m_s m))).
Proof.
  intros. rewrite loop_state_split. unfold loop_state_m, loop_state_st. rewrite mem_rep_nm_split_io.
  f_equal. unfold SEPx. simpl. rewrite !sepcon_assoc. reflexivity.
Qed.

(* mem_rep_io does not see mode, length, the output bytes, the input position, hold, bits, leave *)
Lemma mem_rep_io_set_mode: forall F m md, mem_rep_io F (set_mode m md) = mem_rep_io F m.
Proof. reflexivity. Qed.
Lemma mem_rep_io_set_length: forall F m x,
  mem_rep_io F (upd_s m (fun s => set_i_length s x)) = mem_rep_io F m.
Proof. reflexivity. Qed.
Lemma mem_rep_io_set_ow: forall F m x, mem_rep_io F (set_m_ow m x) = mem_rep_io F m.
Proof. reflexivity. Qed.
Lemma mem_rep_io_set_nx: forall F m x, mem_rep_io F (set_m_nx m x) = mem_rep_io F m.
Proof. reflexivity. Qed.
Lemma mem_rep_io_initbits: forall F m, mem_rep_io F (initbits m) = mem_rep_io F m.
Proof. reflexivity. Qed.
Lemma mem_rep_io_set_leave: forall F m, mem_rep_io F (set_leave m) = mem_rep_io F m.
Proof. reflexivity. Qed.
