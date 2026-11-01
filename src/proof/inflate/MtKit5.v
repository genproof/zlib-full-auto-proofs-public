(* case MATCH (24) v5: the model in pieces (mt_src: where the bytes come from, None = BAD; mt_fin: the copy and
   the new length/mode) and the memory with the fields MATCH touches apart (loop_state_mt). *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate.DmKit5.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* ---------------------------------------------------------------------------------------------- *)
(* the model                                                                                      *)

Definition mt_src (m: mst) : option (src * Z) :=
  let s := m_s m in
  let copy0 := u32 (m_out m - m_left m) in
  if copy0 <? i_offset s then
    let copy := i_offset s - copy0 in
    if andb (i_whave s <? copy) (negb (i_sane s =? 0)) then None else
    let '(sr, copy) := if i_wnext s <? copy then (SWin (i_wsize s - (copy - i_wnext s)), copy - i_wnext s)
                       else (SWin (i_wnext s - copy), copy) in
    Some (sr, Z.min copy (i_length s))
  else Some (SOut (Zlength (m_ow m) - i_offset s), i_length s).

Definition mt_fin (m: mst) (sr: src) (cp: Z) : mst :=
  let copy := Z.min cp (m_left m) in
  let ow' := fst (copy_bytes (i_wdata (m_s m)) sr copy (m_ow m)) in
  let len' := i_length (m_s m) - copy in
  let m := upd_s (set_m_ow m ow') (fun s => set_i_length s len') in
  if len' =? 0 then set_mode m LEN else m.

Lemma c_MATCH_eq: forall m, m_left m <> 0 ->
  c_MATCH m = match mt_src m with None => IBrk (set_bad m M_far) | Some (sr, cp) => IBrk (mt_fin m sr cp) end.
Proof.
  intros m L. unfold c_MATCH, mt_src, mt_fin.
  rewrite (proj2 (Z.eqb_neq _ _) L).
  destruct (u32 (m_out m - m_left m) <? i_offset (m_s m)).
  - destruct (andb (i_whave (m_s m) <? i_offset (m_s m) - u32 (m_out m - m_left m)) (negb (i_sane (m_s m) =? 0)));
      [reflexivity | ].
    destruct (i_wnext (m_s m) <? i_offset (m_s m) - u32 (m_out m - m_left m));
      destruct (copy_bytes _ _ _ _); reflexivity.
  - destruct (copy_bytes _ _ _ _); reflexivity.
Qed.

Lemma copy_f_len: forall n w sr ow, Zlength (fst (copy_f n w sr ow)) = Zlength ow + Z.of_nat n.
Proof.
  induction n; intros; simpl; [lia | ].
  destruct sr; rewrite IHn, Zlength_app, Zlength_cons, Zlength_nil; lia.
Qed.

Lemma copy_bytes_len: forall w sr c ow, 0 <= c -> Zlength (fst (copy_bytes w sr c ow)) = Zlength ow + c.
Proof. intros. unfold copy_bytes. rewrite copy_f_len. lia. Qed.

Lemma copy_f_bytes: forall n w sr ow, bytes_ok w -> bytes_ok ow ->
  (forall i, sr = SWin i -> 0 <= i /\ i + Z.of_nat n <= Zlength w) ->
  (forall i, sr = SOut i -> 0 <= i < Zlength ow) ->
  bytes_ok (fst (copy_f n w sr ow)).
Proof.
  induction n; intros w sr ow BW BO HW HO; simpl; [exact BO | ].
  destruct sr as [i | i].
  - destruct (HW i eq_refl) as [A B].
    apply IHn; auto.
    + unfold bytes_ok. apply Forall_app. split; [exact BO | ]. constructor; [ | constructor].
      apply (proj1 (Forall_Znth _ _) BW); lia.
    + intros j E. inversion E; subst. lia.
    + intros j E. discriminate.
  - destruct (HO i eq_refl) as [A B].
    apply IHn; auto.
    + unfold bytes_ok. apply Forall_app. split; [exact BO | ]. constructor; [ | constructor].
      apply (proj1 (Forall_Znth _ _) BO); lia.
    + intros j E. discriminate.
    + intros j E. inversion E; subst. rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the memory with MATCH's fields apart                                                           *)

(* the 27 fields MATCH does not touch *)
Definition state_rep_mt (gv: globals) (sp strmp headp: val) (s: istate) : mpred :=
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
  field_at Ews t_state (DOT _hold) (lv (i_hold s)) sp *
  field_at Ews t_state (DOT _bits) (zv (i_bits s)) sp *
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
  field_at Ews t_state (DOT _back) (zv (i_back s)) sp *
  field_at Ews t_state (DOT _was) (zv (i_was s)) sp.

(* the rest of the memory, untouched by MATCH *)
Definition mem_rep_mt (F: frame) (m: mst) : mpred :=
  state_rep_mt (f_gv F) (f_sp F) (f_strmp F) (f_headp F) (m_s m) *
  head_part F m * in_rep (f_ib F) * tables_rep (f_gsh F) (f_gv F) * crc_table_at (f_tsh F) (f_gv F).

Definition mt_strm (F: frame) (m: mst) : mpred :=
  strm_rep (f_gv F) (f_shs F) (f_strmp F)
    (in_ptr (f_ib F) (m_snx m)) (zv (Zlength (m_inp m) - m_snx m)) (m_tin m)
    (out_ptr (f_ob F) (m_sow m)) (zv (m_aout m - m_sow m)) (m_tout m)
    (msg_val (f_gv F) (m_msg m)) (f_sp F) (f_dt F) (m_adler m) (f_vres F).

Definition mt_locals (F: frame) (m: mst) : list localdef :=
  [temp _strm (f_strmp F); temp _flush (zv (f_flush F)); temp _state (f_sp F);
   temp _next (in_ptr (f_ib F) (m_nx m)); temp _put (out_ptr (f_ob F) (Zlength (m_ow m)));
   temp _have (zv (m_have m)); temp _left (zv (m_left m)); temp _hold (lv (m_hold m));
   temp _bits (zv (m_bits m)); temp _in (zv (m_in m)); temp _out (zv (m_out m));
   temp _ret (zv (m_ret m)); temp _leave (zv (m_leave m));
   lvar _here t_code (f_vhere F); lvar _last t_code (f_vlast F);
   lvar _hbuf (tarray tuchar 4) (f_vhbuf F); gvars (f_gv F)].

Definition mt_seps (F: frame) (m: mst) : list mpred :=
  [field_at Ews t_state (DOT _mode) (zv (i_mode (m_s m))) (f_sp F);
   field_at Ews t_state (DOT _wsize) (zv (i_wsize (m_s m))) (f_sp F);
   field_at Ews t_state (DOT _whave) (zv (i_whave (m_s m))) (f_sp F);
   field_at Ews t_state (DOT _wnext) (zv (i_wnext (m_s m))) (f_sp F);
   field_at Ews t_state (DOT _window) (if i_win (m_s m) then f_winp F else nullval) (f_sp F);
   field_at Ews t_state (DOT _length) (zv (i_length (m_s m))) (f_sp F);
   field_at Ews t_state (DOT _offset) (zv (i_offset (m_s m))) (f_sp F);
   field_at Ews t_state (DOT _sane) (zv (i_sane (m_s m))) (f_sp F);
   win_rep (f_winp F) (m_s m); mt_strm F m; out_rep (f_ob F) (m_ow m); mem_rep_mt F m; locals_rep F].

Definition loop_state_mt (F: frame) (m: mst) : environ -> mpred :=
  PROPx [in_ok (f_ib F) (m_inp m); out_ok (f_ob F) (m_aout m)] (LOCALx (mt_locals F m) (SEPx (mt_seps F m))).

(* where the copy reads *)
Definition src_ptr (F: frame) (sr: src) : val :=
  match sr with SWin i => offset_val i (f_winp F) | SOut i => out_ptr (f_ob F) i end.

(* after the source selection: from, copy *)
Definition mt_selq (F: frame) (m: mst) (sr: src) (cp: Z) : environ -> mpred :=
  PROPx [in_ok (f_ib F) (m_inp m); out_ok (f_ob F) (m_aout m)]
  (LOCALx (temp _from (src_ptr F sr) :: temp _copy (zv cp) :: mt_locals F m) (SEPx (mt_seps F m))).

Lemma sepcon_mt_35: forall a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35: mpred,
  a1 * a2 * a3 * a4 * a5 * a6 * a7 * a8 * a9 * a10 * a11 * a12 * a13 * a14 * a15 * a16 * a17 * a18 * a19 * a20 * a21 * a22 * a23 * a24 * a25 * a26 * a27 * a28 * a29 * a30 * a31 * a32 * a33 * a34 * a35 =
  a2 * a12 * a13 * a14 * a15 * a18 * a19 * a33 *
  (a1 * a3 * a4 * a5 * a6 * a7 * a8 * a9 * a10 * a11 * a16 * a17 * a20 * a21 * a22 * a23 * a24 * a25 * a26 * a27 * a28 * a29 * a30 * a31 * a32 * a34 * a35).
Proof. intros. apply pred_ext; cancel. Qed.

Lemma state_rep_mt_split: forall gv sp strmp headp winp s,
  state_rep gv sp strmp headp winp s =
  field_at Ews t_state (DOT _mode) (zv (i_mode s)) sp *
  field_at Ews t_state (DOT _wsize) (zv (i_wsize s)) sp *
  field_at Ews t_state (DOT _whave) (zv (i_whave s)) sp *
  field_at Ews t_state (DOT _wnext) (zv (i_wnext s)) sp *
  field_at Ews t_state (DOT _window) (if i_win s then winp else nullval) sp *
  field_at Ews t_state (DOT _length) (zv (i_length s)) sp *
  field_at Ews t_state (DOT _offset) (zv (i_offset s)) sp *
  field_at Ews t_state (DOT _sane) (zv (i_sane s)) sp *
  state_rep_mt gv sp strmp headp s.
Proof. intros. unfold state_rep, state_rep_mt. apply sepcon_mt_35. Qed.

Lemma loop_state_mt_eq: forall F m, loop_state F m = loop_state_mt F m.
Proof.
  intros. unfold loop_state, loop_state_mt, mt_locals, mt_seps. f_equal. f_equal.
  unfold SEPx. extensionality rho. cbn [fold_right_sepcon].
  unfold mem_rep. rewrite state_rep_mt_split.
  fold (mt_strm F m). unfold mem_rep_mt.
  generalize (field_at Ews t_state (DOT _mode) (zv (i_mode (m_s m))) (f_sp F)),
    (field_at Ews t_state (DOT _wsize) (zv (i_wsize (m_s m))) (f_sp F)),
    (field_at Ews t_state (DOT _whave) (zv (i_whave (m_s m))) (f_sp F)),
    (field_at Ews t_state (DOT _wnext) (zv (i_wnext (m_s m))) (f_sp F)),
    (field_at Ews t_state (DOT _window) (if i_win (m_s m) then f_winp F else nullval) (f_sp F)),
    (field_at Ews t_state (DOT _length) (zv (i_length (m_s m))) (f_sp F)),
    (field_at Ews t_state (DOT _offset) (zv (i_offset (m_s m))) (f_sp F)),
    (field_at Ews t_state (DOT _sane) (zv (i_sane (m_s m))) (f_sp F)),
    (state_rep_mt (f_gv F) (f_sp F) (f_strmp F) (f_headp F) (m_s m)), (win_rep (f_winp F) (m_s m)),
    (head_part F m), (mt_strm F m), (in_rep (f_ib F)), (out_rep (f_ob F) (m_ow m)),
    (tables_rep (f_gsh F) (f_gv F)), (crc_table_at (f_tsh F) (f_gv F)), (locals_rep F).
  intros. apply pred_ext; cancel.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* around the copy loop: the locals but put/from/copy (left = lft), the memory but the output and the window
   (length field = len') *)

Definition mt_lq (F: frame) (m: mst) (lft: Z) : list localdef :=
  [temp _strm (f_strmp F); temp _flush (zv (f_flush F)); temp _state (f_sp F);
   temp _next (in_ptr (f_ib F) (m_nx m));
   temp _have (zv (m_have m)); temp _left (zv lft); temp _hold (lv (m_hold m));
   temp _bits (zv (m_bits m)); temp _in (zv (m_in m)); temp _out (zv (m_out m));
   temp _ret (zv (m_ret m)); temp _leave (zv (m_leave m));
   lvar _here t_code (f_vhere F); lvar _last t_code (f_vlast F);
   lvar _hbuf (tarray tuchar 4) (f_vhbuf F); gvars (f_gv F)].

Definition mt_rs (F: frame) (m: mst) (len': Z) : list mpred :=
  [field_at Ews t_state (DOT _mode) (zv (i_mode (m_s m))) (f_sp F);
   field_at Ews t_state (DOT _wsize) (zv (i_wsize (m_s m))) (f_sp F);
   field_at Ews t_state (DOT _whave) (zv (i_whave (m_s m))) (f_sp F);
   field_at Ews t_state (DOT _wnext) (zv (i_wnext (m_s m))) (f_sp F);
   field_at Ews t_state (DOT _window) (if i_win (m_s m) then f_winp F else nullval) (f_sp F);
   field_at Ews t_state (DOT _length) (zv len') (f_sp F);
   field_at Ews t_state (DOT _offset) (zv (i_offset (m_s m))) (f_sp F);
   field_at Ews t_state (DOT _sane) (zv (i_sane (m_s m))) (f_sp F);
   mt_strm F m; mem_rep_mt F m; locals_rep F].

(* before the copy loop *)
Definition mt_loopst (F: frame) (m: mst) (from: val) (c lft len': Z) : environ -> mpred :=
  PROPx [in_ok (f_ib F) (m_inp m); out_ok (f_ob F) (m_aout m)]
  (LOCALx (temp _put (out_ptr (f_ob F) (Zlength (m_ow m))) :: temp _from from :: temp _copy (zv c) :: mt_lq F m lft)
  (SEPx (out_rep (f_ob F) (m_ow m) :: win_rep (f_winp F) (m_s m) :: mt_rs F m len'))).

(* after the copy loop: the output ow *)
Definition mt_postst (F: frame) (m: mst) (ow: list Z) (lft len': Z) : environ -> mpred :=
  PROPx [in_ok (f_ib F) (m_inp m); out_ok (f_ob F) (m_aout m)]
  (LOCALx (temp _put (out_ptr (f_ob F) (Zlength ow)) :: mt_lq F m lft)
  (SEPx (out_rep (f_ob F) ow :: win_rep (f_winp F) (m_s m) :: mt_rs F m len'))).
