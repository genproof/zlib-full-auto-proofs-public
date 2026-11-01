(* The cases TABLE and LENLENS (Cases5_TL.v): the fields they touch (mode, lencode, distcode, lenbits, ncode,
   nlen, ndist, have, next, lens, work, codes), the z_stream and the static tables apart from the rest of the
   memory (one opaque SEP item), as in Cases5_TY.v; and the bit-operation / do-while(0) lemmas of Cases5_TY.v. *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate.CaseHyps5.
Require Import Zlib.proof.inflate.Model2.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Definition state_rest_tl (gv: globals) (sp strmp headp winp: val) (s: istate) : mpred :=
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
  field_at Ews t_state (DOT _distbits) (zv (i_distbits s)) sp *
  field_at Ews t_state (DOT _sane) (zv (i_sane s)) sp *
  field_at Ews t_state (DOT _back) (zv (i_back s)) sp *
  field_at Ews t_state (DOT _was) (zv (i_was s)) sp.

Lemma sepcon_tl_35: forall a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35: mpred,
  a1 * a2 * a3 * a4 * a5 * a6 * a7 * a8 * a9 * a10 * a11 * a12 * a13 * a14 * a15 * a16 * a17 * a18 * a19 * a20 * a21 * a22 * a23 * a24 * a25 * a26 * a27 * a28 * a29 * a30 * a31 * a32 * a33 * a34 * a35 =
  a2 * a26 * a27 * a25 * a28 * a30 * a29 * a21 * a22 * a23 * a32 * a31 *
  (a1 * a3 * a4 * a5 * a6 * a7 * a8 * a9 * a10 * a11 * a12 * a13 * a14 * a15 * a16 * a17 * a18 * a19 * a20 * a24 * a33 * a34 * a35).
Proof. intros. apply pred_ext; cancel. Qed.

Lemma state_rep_tl: forall gv sp strmp headp winp s,
  state_rep gv sp strmp headp winp s =
  field_at Ews t_state (DOT _mode) (zv (i_mode s)) sp *
  field_at Ews t_state (DOT _nlen) (zv (i_nlen s)) sp *
  field_at Ews t_state (DOT _ndist) (zv (i_ndist s)) sp *
  field_at Ews t_state (DOT _ncode) (zv (i_ncode s)) sp *
  field_at Ews t_state (DOT _have) (zv (i_have s)) sp *
  field_at Ews t_state (DOT _lens) (map (fun z => Vint (Int.repr z)) (i_lens s)) sp *
  field_at Ews t_state (DOT _next) (codes_at sp (i_next s)) sp *
  field_at Ews t_state (DOT _lencode) (tref_val gv sp (i_lencode s)) sp *
  field_at Ews t_state (DOT _distcode) (tref_val gv sp (i_distcode s)) sp *
  field_at Ews t_state (DOT _lenbits) (zv (i_lenbits s)) sp *
  field_at Ews t_state (DOT _codes) (map ent (i_codes s)) sp *
  field_at_ Ews t_state (DOT _work) sp *
  state_rest_tl gv sp strmp headp winp s.
Proof. intros. unfold state_rep, state_rest_tl. apply sepcon_tl_35. Qed.

(* the memory but those twelve fields, the z_stream and the static tables *)
Definition mem_rest_tl (F: frame) (m: mst) : mpred :=
  state_rest_tl (f_gv F) (f_sp F) (f_strmp F) (f_headp F) (f_winp F) (m_s m) *
  win_rep (f_winp F) (m_s m) *
  head_part F m *
  in_rep (f_ib F) *
  out_rep (f_ob F) (m_ow m) *
  crc_table_at (f_tsh F) (f_gv F).

Definition tl_locals (F: frame) (m: mst) : list localdef :=
  [temp _strm (f_strmp F); temp _flush (zv (f_flush F)); temp _state (f_sp F);
   temp _next (in_ptr (f_ib F) (m_nx m)); temp _put (out_ptr (f_ob F) (Zlength (m_ow m)));
   temp _have (zv (m_have m)); temp _left (zv (m_left m)); temp _hold (lv (m_hold m));
   temp _bits (zv (m_bits m)); temp _in (zv (m_in m)); temp _out (zv (m_out m));
   temp _ret (zv (m_ret m)); temp _leave (zv (m_leave m));
   lvar _here t_code (f_vhere F); lvar _last t_code (f_vlast F);
   lvar _hbuf (tarray tuchar 4) (f_vhbuf F); gvars (f_gv F)].

Definition tl_strm (F: frame) (m: mst) : mpred :=
  strm_rep (f_gv F) (f_shs F) (f_strmp F)
    (in_ptr (f_ib F) (m_snx m)) (zv (Zlength (m_inp m) - m_snx m)) (m_tin m)
    (out_ptr (f_ob F) (m_sow m)) (zv (m_aout m - m_sow m)) (m_tout m)
    (msg_val (f_gv F) (m_msg m)) (f_sp F) (f_dt F) (m_adler m) (f_vres F).

Definition tl_sep (F: frame) (m: mst) : list mpred :=
  let s := m_s m in let sp := f_sp F in
  [field_at Ews t_state (DOT _mode) (zv (i_mode s)) sp;
   field_at Ews t_state (DOT _nlen) (zv (i_nlen s)) sp;
   field_at Ews t_state (DOT _ndist) (zv (i_ndist s)) sp;
   field_at Ews t_state (DOT _ncode) (zv (i_ncode s)) sp;
   field_at Ews t_state (DOT _have) (zv (i_have s)) sp;
   field_at Ews t_state (DOT _lens) (map (fun z => Vint (Int.repr z)) (i_lens s)) sp;
   field_at Ews t_state (DOT _next) (codes_at sp (i_next s)) sp;
   field_at Ews t_state (DOT _lencode) (tref_val (f_gv F) sp (i_lencode s)) sp;
   field_at Ews t_state (DOT _distcode) (tref_val (f_gv F) sp (i_distcode s)) sp;
   field_at Ews t_state (DOT _lenbits) (zv (i_lenbits s)) sp;
   field_at Ews t_state (DOT _codes) (map ent (i_codes s)) sp;
   field_at_ Ews t_state (DOT _work) sp;
   tl_strm F m;
   tables_rep (f_gsh F) (f_gv F);
   mem_rest_tl F m;
   locals_rep F].

Definition loop_state_tl (F: frame) (m: mst) : environ -> mpred :=
  PROPx [in_ok (f_ib F) (m_inp m); out_ok (f_ob F) (m_aout m)]
  (LOCALx (tl_locals F m) (SEPx (tl_sep F m))).

Lemma loop_state_tl_eq: forall F m, loop_state F m = loop_state_tl F m.
Proof.
  intros. unfold loop_state, loop_state_tl, tl_locals, tl_sep, tl_strm, mem_rep, mem_rest_tl. rewrite state_rep_tl.
  f_equal. f_equal. unfold SEPx. extensionality rho. simpl. apply pred_ext; cancel.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Cases5_TY.v's helpers                                                                          *)

Lemma semax_dowhile0 {Espec: OracleKind} (Delta: tycontext) (P Q: environ -> mpred) (c rest: statement)
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

Lemma int_and_ones: forall b k, 0 <= b -> 0 <= k <= 32 ->
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

Lemma long_shru_eq: forall h n, 0 <= h <= Int64.max_unsigned -> 0 <= n < 64 ->
  Int64.shru (Int64.repr h) (Int64.repr n) = Int64.repr (Z.shiftr h n).
Proof.
  intros h n Hh Hn. unfold Int64.shru.
  rewrite (Int64.unsigned_repr h) by lia. rewrite (Int64.unsigned_repr n) by rep_lia. reflexivity.
Qed.

Lemma u32_repr: forall x, Int.repr (u32 x) = Int.repr x.
Proof.
  intros. unfold u32. apply Int.eqm_samerepr. unfold Int.eqm. apply Zbits.eqmod_sym, Zbits.eqmod_mod.
  reflexivity.
Qed.

(* BITS(k)'s mask (1U << k) - 1 *)
Ltac mask_simpl :=
  repeat match goal with |- context [Int.sub (Int.shl (Int.repr 1) (Int.repr ?k)) (Int.repr 1)] =>
    change (Int.sub (Int.shl (Int.repr 1) (Int.repr k)) (Int.repr 1)) with (Int.repr (2 ^ k - 1)) end.
