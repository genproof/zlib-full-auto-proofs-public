(* Kit for inflate()'s exit inf_leave (Body5Exit.v): the pieces of the statement (RESTORE, the window
   update, the tail), a view of lstate with the nine state fields the exit touches apart (state_rep_e: the
   26 others, opaque), and the model cut along the pieces (mwin: RESTORE and the window; leave_tail). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate_api.Body5Parts.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Definition ex_restore : statement := match inflate_exit with Ssequence r _ => r | _ => Sskip end.
Definition ex_win : statement := match inflate_exit with Ssequence _ (Ssequence w _) => w | _ => Sskip end.
Definition ex_tail : statement := match inflate_exit with Ssequence _ (Ssequence _ t) => t | _ => Sskip end.

Lemma inflate_exit_eq: inflate_exit = Ssequence ex_restore (Ssequence ex_win ex_tail).
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The view                                                                                       *)

Definition state_rep_e (gv: globals) (sp strmp headp winp: val) (s: istate) : mpred :=
  field_at Ews t_state (DOT _strm) strmp sp *
  field_at Ews t_state (DOT _havedict) (zv (i_havedict s)) sp *
  field_at Ews t_state (DOT _dmax) (zv (i_dmax s)) sp *
  field_at Ews t_state (DOT _head) (if i_head s then headp else nullval) sp *
  field_at Ews t_state (DOT _wbits) (zv (i_wbits s)) sp *
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
  field_at Ews t_state (DOT _back) (zv (i_back s)) sp *
  field_at Ews t_state (DOT _was) (zv (i_was s)) sp.

(* the conjuncts 2, 3, 4, 6, 8, 9, 12, 16, 17 of 35 to the front (on variables: a cheap proof term) *)
Lemma sepcon_e_35: forall a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35: mpred,
  a1 * a2 * a3 * a4 * a5 * a6 * a7 * a8 * a9 * a10 * a11 * a12 * a13 * a14 * a15 * a16 * a17 * a18 * a19 * a20 * a21 * a22 * a23 * a24 * a25 * a26 * a27 * a28 * a29 * a30 * a31 * a32 * a33 * a34 * a35 =
  a2 * a3 * a4 * a6 * a8 * a9 * a12 * a16 * a17 * (a1 * a5 * a7 * a10 * a11 * a13 * a14 * a15 * a18 * a19 * a20 * a21 * a22 * a23 * a24 * a25 * a26 * a27 * a28 * a29 * a30 * a31 * a32 * a33 * a34 * a35).
Proof. intros. apply pred_ext; cancel. Qed.

Definition state_f9 (sp: val) (s: istate) : mpred :=
  field_at Ews t_state (DOT _mode) (zv (i_mode s)) sp *
  field_at Ews t_state (DOT _last) (zv (i_last s)) sp *
  field_at Ews t_state (DOT _wrap) (zv (i_wrap s)) sp *
  field_at Ews t_state (DOT _flags) (zv (i_flags s)) sp *
  field_at Ews t_state (DOT _check) (lv (i_check s)) sp *
  field_at Ews t_state (DOT _total) (lv (i_total s)) sp *
  field_at Ews t_state (DOT _wsize) (zv (i_wsize s)) sp *
  field_at Ews t_state (DOT _hold) (lv (i_hold s)) sp *
  field_at Ews t_state (DOT _bits) (zv (i_bits s)) sp.

Lemma state_rep_esplit: forall gv sp strmp headp winp s,
  state_rep gv sp strmp headp winp s = state_f9 sp s * state_rep_e gv sp strmp headp winp s.
Proof. intros. unfold state_rep, state_rep_e, state_f9. apply sepcon_e_35. Qed.

(* the memory but the nine fields, the stream, the output object and the crc table *)
Definition mem_rep_e (F: frame) (m: mst) : mpred :=
  state_rep_e (f_gv F) (f_sp F) (f_strmp F) (f_headp F) (f_winp F) (m_s m) *
  win_rep (f_winp F) (m_s m) *
  head_part F m *
  in_rep (f_ib F) *
  tables_rep (f_gsh F) (f_gv F).

Definition strm_e (F: frame) (m: mst) : mpred :=
  strm_rep (f_gv F) (f_shs F) (f_strmp F)
    (in_ptr (f_ib F) (m_snx m)) (zv (Zlength (m_inp m) - m_snx m)) (m_tin m)
    (out_ptr (f_ob F) (m_sow m)) (zv (m_aout m - m_sow m)) (m_tout m)
    (msg_val (f_gv F) (m_msg m)) (f_sp F) (f_dt F) (m_adler m) (f_vres F).

Lemma mem_rep_esplit: forall F m,
  mem_rep F m =
  state_f9 (f_sp F) (m_s m) * strm_e F m * out_rep (f_ob F) (m_ow m) * crc_table_at (f_tsh F) (f_gv F) *
  mem_rep_e F m.
Proof.
  intros. unfold mem_rep, mem_rep_e, strm_e. rewrite state_rep_esplit.
  apply pred_ext; cancel.
Qed.

Definition lstate_e (F: frame) (X: mpred) (m: mst) : environ -> mpred :=
  PROP (in_ok (f_ib F) (m_inp m); out_ok (f_ob F) (m_aout m))
  LOCAL (temp _strm (f_strmp F); temp _flush (zv (f_flush F)); temp _state (f_sp F);
         temp _next (in_ptr (f_ib F) (m_nx m)); temp _put (out_ptr (f_ob F) (Zlength (m_ow m)));
         temp _have (zv (m_have m)); temp _left (zv (m_left m)); temp _hold (lv (m_hold m));
         temp _bits (zv (m_bits m)); temp _in (zv (m_in m)); temp _out (zv (m_out m));
         temp _ret (zv (m_ret m)); temp _leave (zv (m_leave m));
         lvar _here t_code (f_vhere F); lvar _last t_code (f_vlast F);
         lvar _hbuf (tarray tuchar 4) (f_vhbuf F); gvars (f_gv F))
  SEP (field_at Ews t_state (DOT _mode) (zv (i_mode (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _last) (zv (i_last (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _wrap) (zv (i_wrap (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _flags) (zv (i_flags (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _check) (lv (i_check (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _total) (lv (i_total (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _wsize) (zv (i_wsize (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _hold) (lv (i_hold (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _bits) (zv (i_bits (m_s m))) (f_sp F);
       strm_e F m; out_rep (f_ob F) (m_ow m); crc_table_at (f_tsh F) (f_gv F); mem_rep_e F m;
       locals_rep F; hdr_tok F m; mem_mgr (f_gv F); zfuncs (f_gv F); X).

Lemma lstate_esplit: forall F X m, lstate F X m = lstate_e F X m.
Proof.
  intros. unfold lstate, lstate_e. rewrite mem_rep_esplit.
  f_equal. unfold SEPx. simpl. f_equal. extensionality rho. unfold state_f9. apply pred_ext; cancel.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* RESTORE                                                                                        *)

Lemma mem_rep_e_restore: forall F m, mem_rep_e F (restore m) = mem_rep_e F m.
Proof. reflexivity. Qed.

Lemma hdr_tok_restore: forall F m, hdr_tok F (restore m) = hdr_tok F m.
Proof. reflexivity. Qed.

Lemma semax_ex_restore {Espec: OracleKind} (F: frame) (X: mpred) (m: mst):
  writable_share (f_shs F) ->
  semax Delta_inflate5 (lstate F X m) ex_restore (normal_ret_assert (lstate F X (restore m))).
Proof.
  intros HWS.
  cbv beta iota zeta delta [ex_restore inflate_exit f_inflate fn_body].
  apply semax_loop with (Q' := lstate F X (restore m)).
  - rewrite !lstate_esplit. unfold lstate_e, strm_e, strm_rep.
    rewrite mem_rep_e_restore, hdr_tok_restore.
    abbreviate_semax.
    remember (f_gv F _zcalloc) as zca eqn:Hzca. remember (f_gv F _zcfree) as zcf eqn:Hzcf.
    forward. forward. forward. forward. forward. forward.
    unfold loop1_ret_assert. cbn [RA_normal].
    mnorm_goal.
    entailer!.
  - eapply semax_pre; [ | apply semax_break]. cbn [RA_break loop2_ret_assert].
    apply andp_left2. apply derives_refl.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The model cut along the pieces                                                                 *)

Definition win_data (m: mst) : list Z :=
  let copy := u32 (m_out m - m_left m) in sublist (Zlength (m_ow m) - copy) (Zlength (m_ow m)) (m_ow m).

(* RESTORE and the window update when it succeeds *)
Definition mwin (flush: Z) (m: mst) : mst :=
  let m' := restore m in
  if leave_ok flush m then upd_s m' (fun s => set_i_win (updatewindow s (win_data m')) true) else m'.

(* the rest of leave_fin *)
Definition leave_tail (flush: Z) (m: mst) : result :=
  let inn := u32 (m_in m - m_have m) in
  let out := u32 (m_out m - m_left m) in
  let m := set_m_tout (set_m_tin m (u64 (m_tin m + inn))) (u64 (m_tout m + out)) in
  let m := upd_s m (fun s => set_i_total s (u64 (i_total s + out))) in
  let m := if (negb (Z.land (i_wrap (m_s m)) 4 =? 0) && negb (out =? 0))%bool then
             let c := update_check (i_flags (m_s m)) (i_check (m_s m))
                        (sublist (Zlength (m_ow m) - out) (Zlength (m_ow m)) (m_ow m)) in
             set_m_adler (upd_s m (fun s => set_i_check s c)) c
           else m in
  let s := m_s m in
  let dt := m_bits m + (if i_last s =? 0 then 0 else 64) + (if i_mode s =? Zlib.proof.inflate.Model.TYPE then 128 else 0)
            + (if ((i_mode s =? LEN_) || (i_mode s =? COPY_))%bool then 256 else 0) in
  let r := if ((((inn =? 0) && (out =? 0)) || (flush =? Z_FINISH)) && (m_ret m =? Z_OK))%bool
           then Z_BUF_ERROR else m_ret m in
  Res r m (Some dt).

Lemma leave_fin_eq: forall flush m, leave_fin flush m = leave_tail flush (mwin flush m).
Proof. intros. unfold leave_fin, leave_tail, mwin, win_data. destruct (leave_ok flush m); reflexivity. Qed.

(* updatewindow changes only the window fields *)
Lemma updatewindow_keep: forall s d,
  let s' := updatewindow s d in
  i_mode s' = i_mode s /\ i_last s' = i_last s /\ i_wrap s' = i_wrap s /\ i_flags s' = i_flags s /\
  i_check s' = i_check s /\ i_total s' = i_total s /\ i_hold s' = i_hold s /\ i_bits s' = i_bits s /\
  i_head s' = i_head s.
Proof.
  intros. subst s'. unfold updatewindow.
  destruct (i_wsize s =? 0); cbv zeta;
  repeat match goal with |- context [if ?b then _ else _] => destruct b end;
  repeat split; reflexivity.
Qed.

(* what the tail needs of the machine after RESTORE and the window update *)
Definition tail_facts (m: mst) : Prop :=
  m_snx m = m_nx m /\ m_sow m = Zlength (m_ow m) /\ i_bits (m_s m) = m_bits m /\
  m_in m = Zlength (m_inp m) /\ 0 <= m_nx m <= Zlength (m_inp m) /\ Zlength (m_inp m) <= Int.max_signed /\
  m_left m <= m_out m <= m_aout m /\ Zlength (m_ow m) <= m_aout m <= Int.max_signed /\ bytes_ok (m_ow m) /\
  lrange (m_tin m) /\ lrange (m_tout m) /\ lrange (i_check (m_s m)) /\ lrange (i_total (m_s m)) /\
  0 <= i_wrap (m_s m) <= 15 /\ srange (i_flags (m_s m)) /\ 0 <= m_bits m <= 39 /\ 0 <= i_last (m_s m) <= 1 /\
  HEAD <= i_mode (m_s m) <= SYNC /\ -5 <= m_ret m <= 2.

(* the tail: in -= avail_in; out -= avail_out; the counters; UPDATE_CHECK; data_type; the return code *)
Definition ex_tail_stmt : Prop :=
  forall {Espec: OracleKind} (F: frame) (X: mpred) (m: mst) (R: ret_assert),
  frame_ok5 F -> tail_facts m ->
  ENTAIL Delta_inflate5,
    PROPx [] (LOCALx (ret_locals F)
      (SEPx [mem_rep (set_f_winp_dt F (f_winp F) (res_dt F (leave_tail (f_flush F) m))) (r_m (leave_tail (f_flush F) m));
             locals_rep F; hdr_tok F m; mem_mgr (f_gv F); zfuncs (f_gv F); X]))
    |-- RA_return R (Some (zv (r_ret (leave_tail (f_flush F) m)))) ->
  semax Delta_inflate5 (lstate F X m) ex_tail R.
