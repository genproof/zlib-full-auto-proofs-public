(* inflate(), case HEAD, the zlib-header branch after contract fix F7: the window size is checked
   BEFORE it is stored (`if (len > 15 || (state->wbits != 0 && len > state->wbits)) BAD; if (state->wbits == 0)
   state->wbits = len;`), model Model2.c_HEAD2 / HeadDefs5.head_zlib_out. *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate.CaseHyps5.
Require Import Zlib.proof.inflate.HeadDefs5.
Require Import Zlib.proof.crc32.Spec Zlib.proof.adler32.Spec.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.
(* ---------------------------------------------------------------------------------------------- *)
(* the fields the zlib branch reads or writes (mode, wrap, flags, dmax, check, head, wbits) apart from
   the 28 others, the head part and the stream apart, the rest of the memory one opaque item (so
   that Qed does not unfold the whole state)                                                      *)

Definition state_rep_z (gv: globals) (sp strmp winp: val) (s: istate) : mpred :=
  field_at Ews t_state (DOT _strm) strmp sp *
  field_at Ews t_state (DOT _last) (zv (i_last s)) sp *
  field_at Ews t_state (DOT _havedict) (zv (i_havedict s)) sp *
  field_at Ews t_state (DOT _total) (lv (i_total s)) sp *
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

Lemma sepcon_z_35: forall a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35: mpred,
  a1 * a2 * a3 * a4 * a5 * a6 * a7 * a8 * a9 * a10 * a11 * a12 * a13 * a14 * a15 * a16 * a17 * a18 * a19 * a20 * a21 * a22 * a23 * a24 * a25 * a26 * a27 * a28 * a29 * a30 * a31 * a32 * a33 * a34 * a35 =
  a2 * a4 * a6 * a7 * a8 * a10 * a11 * (a1 * a3 * a5 * a9 * a12 * a13 * a14 * a15 * a16 * a17 * a18 * a19 * a20 * a21 * a22 * a23 * a24 * a25 * a26 * a27 * a28 * a29 * a30 * a31 * a32 * a33 * a34 * a35).
Proof. intros. apply pred_ext; cancel. Qed.

Lemma state_rep_zsplit: forall gv sp strmp headp winp s,
  state_rep gv sp strmp headp winp s =
  field_at Ews t_state (DOT _mode) (zv (i_mode s)) sp *
  field_at Ews t_state (DOT _wrap) (zv (i_wrap s)) sp *
  field_at Ews t_state (DOT _flags) (zv (i_flags s)) sp *
  field_at Ews t_state (DOT _dmax) (zv (i_dmax s)) sp *
  field_at Ews t_state (DOT _check) (lv (i_check s)) sp *
  field_at Ews t_state (DOT _head) (if i_head s then headp else nullval) sp *
  field_at Ews t_state (DOT _wbits) (zv (i_wbits s)) sp *
  state_rep_z gv sp strmp winp s.
Proof. intros. unfold state_rep, state_rep_z. apply sepcon_z_35. Qed.

Definition mem_rep_z (F: frame) (m: mst) : mpred :=
  state_rep_z (f_gv F) (f_sp F) (f_strmp F) (f_winp F) (m_s m) *
  win_rep (f_winp F) (m_s m) *
  in_rep (f_ib F) *
  out_rep (f_ob F) (m_ow m) *
  tables_rep (f_gsh F) (f_gv F) *
  crc_table_at (f_tsh F) (f_gv F).

Definition strm_z (F: frame) (m: mst) : mpred :=
  strm_rep (f_gv F) (f_shs F) (f_strmp F)
    (in_ptr (f_ib F) (m_snx m)) (zv (Zlength (m_inp m) - m_snx m)) (m_tin m)
    (out_ptr (f_ob F) (m_sow m)) (zv (m_aout m - m_sow m)) (m_tout m)
    (msg_val (f_gv F) (m_msg m)) (f_sp F) (f_dt F) (m_adler m) (f_vres F).

Lemma mem_rep_zsplit: forall F m,
  mem_rep F m =
  field_at Ews t_state (DOT _mode) (zv (i_mode (m_s m))) (f_sp F) *
  field_at Ews t_state (DOT _wrap) (zv (i_wrap (m_s m))) (f_sp F) *
  field_at Ews t_state (DOT _flags) (zv (i_flags (m_s m))) (f_sp F) *
  field_at Ews t_state (DOT _dmax) (zv (i_dmax (m_s m))) (f_sp F) *
  field_at Ews t_state (DOT _check) (lv (i_check (m_s m))) (f_sp F) *
  field_at Ews t_state (DOT _head) (if i_head (m_s m) then f_headp F else nullval) (f_sp F) *
  field_at Ews t_state (DOT _wbits) (zv (i_wbits (m_s m))) (f_sp F) *
  head_part F m * strm_z F m * mem_rep_z F m.
Proof.
  intros. unfold mem_rep, mem_rep_z, strm_z. rewrite state_rep_zsplit.
  apply pred_ext; cancel.
Qed.

Definition loop_state_z (F: frame) (m: mst) : environ -> mpred :=
  PROP (in_ok (f_ib F) (m_inp m); out_ok (f_ob F) (m_aout m))
  LOCAL (temp _strm (f_strmp F); temp _flush (zv (f_flush F)); temp _state (f_sp F);
         temp _next (in_ptr (f_ib F) (m_nx m)); temp _put (out_ptr (f_ob F) (Zlength (m_ow m)));
         temp _have (zv (m_have m)); temp _left (zv (m_left m)); temp _hold (lv (m_hold m));
         temp _bits (zv (m_bits m)); temp _in (zv (m_in m)); temp _out (zv (m_out m));
         temp _ret (zv (m_ret m)); temp _leave (zv (m_leave m));
         lvar _here t_code (f_vhere F); lvar _last t_code (f_vlast F);
         lvar _hbuf (tarray tuchar 4) (f_vhbuf F); gvars (f_gv F))
  SEP (field_at Ews t_state (DOT _mode) (zv (i_mode (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _wrap) (zv (i_wrap (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _flags) (zv (i_flags (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _dmax) (zv (i_dmax (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _check) (lv (i_check (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _head) (if i_head (m_s m) then f_headp F else nullval) (f_sp F);
       field_at Ews t_state (DOT _wbits) (zv (i_wbits (m_s m))) (f_sp F);
       head_part F m; strm_z F m; mem_rep_z F m; locals_rep F).

Lemma loop_state_zsplit: forall F m, loop_state F m = loop_state_z F m.
Proof.
  intros. unfold loop_state, loop_state_z. rewrite mem_rep_zsplit.
  f_equal. unfold SEPx. simpl. rewrite !sepcon_assoc. reflexivity.
Qed.


(* ---------------------------------------------------------------------------------------------- *)
(* the model of the branch, cut along the code                                                    *)

Definition zl_mh (m: mst) : mst := if i_head (m_s m) then upd_h m (fun h => set_h_done h (-1)) else m.

Definition zl_c31 (m: mst) : bool :=
  orb (Z.land (i_wrap (m_s m)) 1 =? 0) (negb (((m_hold m mod 256) * 256 + Z.shiftr (m_hold m) 8) mod 31 =? 0)).

Definition zl_tail (m: mst) : iout :=
  let m := dropbits 4 m in
  let len := m_hold m mod 16 + 8 in
  if orb (15 <? len) (andb (negb (i_wbits (m_s m) =? 0)) (i_wbits (m_s m) <? len)) then IBrk (set_bad m M_wsize) else
  let m := upd_s m (fun s => set_i_wbits s (if i_wbits s =? 0 then len else i_wbits s)) in
  let mode := if Z.land (m_hold m) 512 =? 0 then Zlib.proof.inflate.Model.TYPE else DICTID in
  let m := upd_s m (fun s => set_i_check (set_i_flags (set_i_dmax s (2 ^ len)) 0) 1) in
  IBrk (set_mode (initbits (set_m_adler m 1)) mode).

Lemma head_zlib_out_eq: forall m, head_zlib_out m =
  if zl_c31 (zl_mh m) then IBrk (set_bad (zl_mh m) M_hdr_check) else
  if negb (m_hold (zl_mh m) mod 16 =? 8) then IBrk (set_bad (zl_mh m) M_method) else zl_tail (zl_mh m).
Proof. intros. unfold head_zlib_out, zl_mh, zl_c31, zl_tail. destruct (i_head (m_s m)); reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* strm->msg = (char * )<msg>; state->mode = BAD; break;                                          *)

Definition bad_block_z (id: ident) (n: Z) : statement :=
  (Ssequence (Sassign (Efield (Ederef (Etempvar _strm (tptr (Tstruct _z_stream_s noattr))) (Tstruct _z_stream_s noattr)) _msg (tptr tschar)) (Ecast (Evar id (tarray tschar n)) (tptr tschar))) (Ssequence (Sassign (Efield (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr))) (Tstruct _inflate_state noattr)) _mode tint) (Econst_int (Int.repr 16209) tint)) Sbreak)).

Definition bad_ok_z {Espec: OracleKind} (F: frame) (e: msgid) (n: Z) : Prop :=
  forall (m m0: mst) (R: ret_assert),
    RA_break R = RA_normal (case_post2 F m0) ->
    stepf2 (f_flush F) lenfix_list distfix_list m0 = IBrk (set_bad m e) ->
    semax Delta_cases5 (loop_state F m) (bad_block_z (msg_ident e) n) R.

Lemma mem_rep_z_bad: forall F m e, mem_rep_z F (set_bad m e) = mem_rep_z F m.
Proof. reflexivity. Qed.
Lemma head_part_z_bad: forall F m e, head_part F (set_bad m e) = head_part F m.
Proof. reflexivity. Qed.

Ltac bad_z_tac F e :=
  let m := fresh "m" in let m0 := fresh "m0" in let R := fresh "R" in
  let HR := fresh "HR" in let HS := fresh "HS" in
  intros m m0 R HR HS;
  unfold bad_block_z; cbn [msg_ident];
  rewrite loop_state_zsplit; unfold loop_state_z, strm_z, strm_rep;
  abbreviate_semax;
  let zca := fresh "zca" in let zcf := fresh "zcf" in let Hzca := fresh "Hzca" in let Hzcf := fresh "Hzcf" in
  remember (f_gv F _zcalloc) as zca eqn:Hzca; remember (f_gv F _zcfree) as zcf eqn:Hzcf;
  forward; forward; forward;
  rewrite HR; unfold case_post2, RA_normal; Exists (set_bad m e);
  rewrite loop_state_zsplit; unfold loop_state_z, strm_z, strm_rep;
  rewrite (mem_rep_z_bad F m e), (head_part_z_bad F m e);
  cbn [set_bad set_mode upd_s set_m_s set_m_msg m_s m_msg i_mode set_i_mode i_wrap i_flags i_check i_head
       i_dmax i_wbits m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave m_snx m_sow m_tin m_tout
       m_adler m_have m_left msg_val];
  rewrite <- Hzca, <- Hzcf; entailer!.

Lemma bad_z_hdr {Espec: OracleKind} (F: frame) : frame_ok F -> bad_ok_z F M_hdr_check 23.
Proof. intros FOK. pose proof FOK as (HWS & HWH & HRG & HRT). bad_z_tac F M_hdr_check. Qed.
Lemma bad_z_method {Espec: OracleKind} (F: frame) : frame_ok F -> bad_ok_z F M_method 27.
Proof. intros FOK. pose proof FOK as (HWS & HWH & HRG & HRT). bad_z_tac F M_method. Qed.
Lemma bad_z_wsize {Espec: OracleKind} (F: frame) : frame_ok F -> bad_ok_z F M_wsize 20.
Proof. intros FOK. pose proof FOK as (HWS & HWH & HRG & HRT). bad_z_tac F M_wsize. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* if (state->head != Z_NULL) state->head->done = -1;                                             *)

Definition zl_hd : statement := match head_ZLIB with Ssequence c _ => c | _ => Sskip end.
Definition zl_rest : statement := match head_ZLIB with Ssequence _ c => c | _ => Sskip end.
Lemma head_ZLIB_eq: head_ZLIB = Ssequence zl_hd zl_rest.
Proof. reflexivity. Qed.

(* loop_state_z with another head part *)
Definition loop_state_zh (F: frame) (m: mst) (H: mpred) : environ -> mpred :=
  PROP (in_ok (f_ib F) (m_inp m); out_ok (f_ob F) (m_aout m))
  LOCAL (temp _strm (f_strmp F); temp _flush (zv (f_flush F)); temp _state (f_sp F);
         temp _next (in_ptr (f_ib F) (m_nx m)); temp _put (out_ptr (f_ob F) (Zlength (m_ow m)));
         temp _have (zv (m_have m)); temp _left (zv (m_left m)); temp _hold (lv (m_hold m));
         temp _bits (zv (m_bits m)); temp _in (zv (m_in m)); temp _out (zv (m_out m));
         temp _ret (zv (m_ret m)); temp _leave (zv (m_leave m));
         lvar _here t_code (f_vhere F); lvar _last t_code (f_vlast F);
         lvar _hbuf (tarray tuchar 4) (f_vhbuf F); gvars (f_gv F))
  SEP (field_at Ews t_state (DOT _mode) (zv (i_mode (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _wrap) (zv (i_wrap (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _flags) (zv (i_flags (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _dmax) (zv (i_dmax (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _check) (lv (i_check (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _head) (if i_head (m_s m) then f_headp F else nullval) (f_sp F);
       field_at Ews t_state (DOT _wbits) (zv (i_wbits (m_s m))) (f_sp F);
       H; strm_z F m; mem_rep_z F m; locals_rep F).

Lemma loop_state_z_upd_h: forall F m f,
  loop_state_z F (upd_h m f) = loop_state_zh F m (head_part F (upd_h m f)).
Proof. reflexivity. Qed.

Lemma zl_hd_ok {Espec: OracleKind} (F: frame) (m: mst): frame_ok F ->
  semax Delta_cases5 (loop_state F m) zl_hd (normal_ret_assert (loop_state F (zl_mh m))).
Proof.
  intros FOK. pose proof FOK as (HWS & HWH & HRG & HRT).
  unfold zl_hd, head_ZLIB, zl_mh.
  rewrite !loop_state_zsplit.
  destruct (i_head (m_s m)) eqn:Eh.
  - rewrite loop_state_z_upd_h. unfold loop_state_z, loop_state_zh.
    unfold head_part at 1. rewrite Eh. unfold head_rep.
    abbreviate_semax. Intros. forward. forward_if.
    + forward. forward.
      unfold head_part, head_rep. cbn [upd_h set_m_h m_s m_h set_h_done h_text h_time h_xflags h_os h_xp
        h_extra_len h_extra_max h_np h_name_max h_cp h_comm_max h_hcrc h_done h_xbuf h_nbuf h_cbuf].
      rewrite Eh. entailer!.
    + assert_PROP (isptr (f_headp F)) by entailer!. rewrite H1 in H2. contradiction.
  - unfold loop_state_z. unfold head_part at 1. rewrite Eh.
    abbreviate_semax. Intros. forward. forward_if.
    + discriminate.
    + forward. unfold head_part. rewrite Eh. entailer!.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* pure facts of the int arithmetic                                                               *)

Lemma zl_and_repr: forall a b, Int.and (Int.repr a) (Int.repr b) = Int.repr (Z.land a b).
Proof.
  intros. apply Int.same_bits_eq; intros i Hi.
  rewrite Int.bits_and by auto. rewrite !Int.testbit_repr by auto. rewrite Z.land_spec. reflexivity.
Qed.

Lemma zl_and_ones: forall h k, 0 <= k ->
  Int.and (Int.repr h) (Int.repr (2 ^ k - 1)) = Int.repr (h mod 2 ^ k).
Proof.
  intros h k Hk. rewrite zl_and_repr. replace (2 ^ k - 1) with (Z.ones k) by (rewrite Z.ones_equiv; lia).
  rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma zl_and_mask: forall h k, 0 <= k < 32 ->
  Int.and (Int.repr h) (Int.sub (Int.shl (Int.repr 1) (Int.repr k)) (Int.repr 1)) = Int.repr (h mod 2 ^ k).
Proof.
  intros h k Hk.
  assert (E: Int.sub (Int.shl (Int.repr 1) (Int.repr k)) (Int.repr 1) = Int.repr (2 ^ k - 1)).
  { rewrite Int.shl_mul_two_p. rewrite Int.unsigned_repr by rep_lia. rewrite two_p_equiv.
    rewrite Int.mul_commut, Int.mul_one. unfold Int.sub. rewrite Int.unsigned_repr; [reflexivity | ].
    assert (2 ^ k <= 2 ^ 31) by (apply Z.pow_le_mono_r; lia). rep_lia. }
  rewrite E. apply zl_and_ones. lia.
Qed.

Lemma zl_mod_small_unsigned: forall h k, 0 <= k < 32 -> Int.unsigned (Int.repr (h mod 2 ^ k)) = h mod 2 ^ k.
Proof.
  intros h k Hk. pose proof (Z.mod_pos_bound h (2 ^ k) ltac:(lia)).
  assert (2 ^ k <= 2 ^ 32) by (apply Z.pow_le_mono_r; lia).
  apply Int.unsigned_repr. rep_lia.
Qed.

Lemma zl_mod31_val: forall h, lrange h ->
  Int64.modu (Int64.add (Int64.repr (Int.unsigned (Int.shl (Int.and (Int.repr h)
      (Int.sub (Int.shl (Int.repr 1) (Int.repr 8)) (Int.repr 1))) (Int.repr 8))))
      (Int64.shru (Int64.repr h) (Int64.repr (Int.unsigned (Int.repr 8))))) (Int64.repr 31) =
  Int64.repr (((h mod 256) * 256 + Z.shiftr h 8) mod 31).
Proof.
  intros h Hh. unfold lrange in Hh.
  rewrite zl_and_mask by lia. change (2 ^ 8) with 256.
  pose proof (Z.mod_pos_bound h 256 ltac:(lia)) as B.
  rewrite Int.shl_mul_two_p. change (two_p (Int.unsigned (Int.repr 8))) with 256.
  rewrite Int.mul_signed. rewrite !Int.signed_repr by rep_lia.
  rewrite Int.unsigned_repr by rep_lia.
  rewrite Int64.shru_div_two_p. change (two_p (Int64.unsigned (Int64.repr (Int.unsigned (Int.repr 8))))) with 256.
  rewrite Int64.unsigned_repr by rep_lia.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
  assert (D: 0 <= h / 256 < 2 ^ 56) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; rep_lia).
  rewrite Int64.add_unsigned. rewrite !Int64.unsigned_repr by rep_lia.
  unfold Int64.modu. rewrite !Int64.unsigned_repr by rep_lia.
  reflexivity.
Qed.

Lemma zl_eq_repr0: forall x, 0 <= x <= Int64.max_unsigned ->
  Int64.eq (Int64.repr x) (Int64.repr 0) = (x =? 0).
Proof.
  intros x Hx. unfold Int64.eq. rewrite !Int64.unsigned_repr by rep_lia.
  destruct (zeq x 0), (Z.eqb_spec x 0); auto; lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the header check: if (!(state->wrap & 1) || ((BITS(8) << 8) + (hold >> 8)) % 31) <BAD>          *)

Definition zl_c31s : statement := match zl_rest with Ssequence c _ => c | _ => Sskip end.
Definition zl_r2 : statement := match zl_rest with Ssequence _ c => c | _ => Sskip end.
Definition zl_meth : statement := match zl_r2 with Ssequence c _ => c | _ => Sskip end.
Definition zl_r3 : statement := match zl_r2 with Ssequence _ c => c | _ => Sskip end.
Lemma zl_rest_eq: zl_rest = Ssequence zl_c31s (Ssequence zl_meth zl_r3).
Proof. reflexivity. Qed.

Lemma zl_modm: forall h, lrange h -> Int64.Z_mod_modulus h = h.
Proof. intros h Hh. unfold lrange in Hh. rewrite Int64.Z_mod_modulus_eq. apply Z.mod_small. rep_lia. Qed.

Lemma zl_v31_range: forall h, 0 <= ((h mod 256) * 256 + Z.shiftr h 8) mod 31 <= Int64.max_unsigned.
Proof. intros h. pose proof (Z.mod_pos_bound ((h mod 256) * 256 + Z.shiftr h 8) 31 ltac:(lia)). rep_lia. Qed.

Lemma zl_wrap1: forall w, 0 <= w <= 15 -> Int.and (Int.repr w) (Int.repr 1) <> Int.zero -> (Z.land w 1 =? 0) = false.
Proof.
  intros w Hw H. rewrite zl_and_repr in H. apply Z.eqb_neq. intro E. rewrite E in H. apply H. reflexivity.
Qed.

Lemma zl_wrap0: forall w, 0 <= w <= 15 -> Int.and (Int.repr w) (Int.repr 1) = Int.zero -> (Z.land w 1 =? 0) = true.
Proof.
  intros w Hw H. rewrite zl_and_repr in H. apply Z.eqb_eq.
  assert (0 <= Z.land w 1 <= 1).
  { pose proof (Z.land_ones w 1 ltac:(lia)) as E. change (Z.ones 1) with 1 in E. change (2 ^ 1) with 2 in E.
    rewrite E. pose proof (Z.mod_pos_bound w 2 ltac:(lia)). lia. }
  apply (f_equal Int.unsigned) in H. rewrite Int.unsigned_repr in H by rep_lia. exact H.
Qed.

Lemma zl_c31_ok {Espec: OracleKind} (F: frame) (m m0: mst) (R: ret_assert): frame_ok F ->
  lrange (m_hold m) -> 0 <= i_wrap (m_s m) <= 15 ->
  RA_break R = RA_normal (case_post2 F m0) ->
  (zl_c31 m = true -> stepf2 (f_flush F) lenfix_list distfix_list m0 = IBrk (set_bad m M_hdr_check)) ->
  semax Delta_cases5 (loop_state F m) zl_c31s (overridePost (!! (zl_c31 m = false) && loop_state F m) R).
Proof.
  intros FOK Hh Hw HR HS. pose proof FOK as (HWS & HWH & HRG & HRT).
  pose proof (zl_v31_range (m_hold m)) as Hv.
  assert (HB: zl_c31 m = true -> forall Q, semax Delta_cases5 (loop_state F m) (bad_block_z (msg_ident M_hdr_check) 23)
                (overridePost Q R)).
  { intros C Q. apply (bad_z_hdr F FOK m m0); [destruct R; exact HR | exact (HS C)]. }
  unfold zl_c31s, zl_rest, head_ZLIB.
  rewrite loop_state_zsplit. unfold loop_state_z.
  abbreviate_semax. forward.
  unfold abbreviate in MORE_COMMANDS. subst MORE_COMMANDS. apply semax_if_seq.
  forward_if.
  - forward. forward_if; [ | discriminate].
    assert (C: zl_c31 m = true).
    { unfold zl_c31. rewrite (zl_wrap0 _ Hw H1). reflexivity. }
    unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
    eapply semax_pre; [ | apply (HB C)].
    rewrite loop_state_zsplit. unfold loop_state_z. entailer!.
  - forward. forward_if.
    + assert (C: zl_c31 m = true).
      { unfold zl_c31. rewrite (zl_wrap1 _ Hw H1). cbn [orb].
        rewrite (zl_modm _ Hh), (zl_mod31_val _ Hh), (zl_eq_repr0 _ Hv) in H2.
        destruct (_ =? 0); [contradiction | reflexivity]. }
      unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
    eapply semax_pre; [ | apply (HB C)].
      rewrite loop_state_zsplit. unfold loop_state_z. entailer!.
    + assert (C: zl_c31 m = false).
      { unfold zl_c31. rewrite (zl_wrap1 _ Hw H1). cbn [orb].
        rewrite (zl_modm _ Hh), (zl_mod31_val _ Hh), (zl_eq_repr0 _ Hv) in H2.
        destruct (_ =? 0); [reflexivity | discriminate]. }
      forward. destruct R as [r1 r2 r3 r4]. cbn [RA_normal]. entailer!.
Qed.

(* if (BITS(4) != Z_DEFLATED) <BAD> *)
Lemma zl_mod16_neq: forall h, Int.repr (h mod 16) <> Int.repr 8 -> h mod 16 <> 8.
Proof. intros h H E. rewrite E in H. apply H. reflexivity. Qed.

Lemma zl_mod16_eq: forall h, Int.repr (h mod 16) = Int.repr 8 -> h mod 16 = 8.
Proof.
  intros h H. pose proof (Z.mod_pos_bound h 16 ltac:(lia)).
  apply (f_equal Int.unsigned) in H. rewrite !Int.unsigned_repr in H by rep_lia. exact H.
Qed.

Lemma zl_meth_ok {Espec: OracleKind} (F: frame) (m m0: mst) (R: ret_assert): frame_ok F ->
  lrange (m_hold m) ->
  RA_break R = RA_normal (case_post2 F m0) ->
  (m_hold m mod 16 <> 8 -> stepf2 (f_flush F) lenfix_list distfix_list m0 = IBrk (set_bad m M_method)) ->
  semax Delta_cases5 (loop_state F m) zl_meth (overridePost (!! (m_hold m mod 16 = 8) && loop_state F m) R).
Proof.
  intros FOK Hh HR HS. pose proof FOK as (HWS & HWH & HRG & HRT).
  assert (HB: m_hold m mod 16 <> 8 -> forall Q, semax Delta_cases5 (loop_state F m)
                (bad_block_z (msg_ident M_method) 27) (overridePost Q R)).
  { intros C Q. apply (bad_z_method F FOK m m0); [destruct R; exact HR | exact (HS C)]. }
  unfold zl_meth, zl_r2, zl_rest, head_ZLIB.
  rewrite loop_state_zsplit. unfold loop_state_z.
  abbreviate_semax.
  forward_if.
  - rewrite (zl_modm _ Hh), (zl_and_mask _ 4) in H by lia. change (2 ^ 4) with 16 in H.
    apply zl_mod16_neq in H.
    unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
    eapply semax_pre; [ | apply (HB H)].
    rewrite loop_state_zsplit. unfold loop_state_z. entailer!.
  - rewrite (zl_modm _ Hh), (zl_and_mask _ 4) in H by lia. change (2 ^ 4) with 16 in H.
    apply zl_mod16_eq in H.
    forward. destruct R as [r1 r2 r3 r4]. cbn [RA_normal]. entailer!.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the rest: DROPBITS(4); len; wbits; the window size check; dmax, flags, check, adler, mode; INITBITS *)

Definition zl_m3 (m: mst) (len: Z) : mst :=
  upd_s m (fun s => set_i_wbits s (if i_wbits s =? 0 then len else i_wbits s)).

Definition zl_fin (m: mst) (len: Z) : mst :=
  set_mode (initbits (set_m_adler (upd_s m (fun s => set_i_check (set_i_flags (set_i_dmax s (2 ^ len)) 0) 1)) 1))
    (if Z.land (m_hold m) 512 =? 0 then Zlib.proof.inflate.Model.TYPE else DICTID).

Definition zl_wc (m: mst) (len: Z) : bool :=
  orb (15 <? len) (andb (negb (i_wbits (m_s m) =? 0)) (i_wbits (m_s m) <? len)).

Lemma zl_tail_eq: forall m, zl_tail m =
  let m2 := dropbits 4 m in
  let len := m_hold m2 mod 16 + 8 in
  if zl_wc m2 len then IBrk (set_bad m2 M_wsize)
  else IBrk (zl_fin (zl_m3 m2 len) len).
Proof. reflexivity. Qed.

Definition zl_drop : statement := match zl_r3 with Ssequence c _ => c | _ => Sskip end.
Definition zl_r4 : statement := match zl_r3 with Ssequence _ c => c | _ => Sskip end.
Definition zl_lenset : statement := match zl_r4 with Ssequence c _ => c | _ => Sskip end.
Definition zl_r5 : statement := match zl_r4 with Ssequence _ c => c | _ => Sskip end.
Definition zl_wsz : statement := match zl_r5 with Ssequence c _ => c | _ => Sskip end.
Definition zl_r6 : statement := match zl_r5 with Ssequence _ c => c | _ => Sskip end.
Definition zl_wbs : statement := match zl_r6 with Ssequence c _ => c | _ => Sskip end.
Definition zl_fins : statement := match zl_r6 with Ssequence _ c => c | _ => Sskip end.
Lemma zl_r3_eq: zl_r3 = Ssequence zl_drop (Ssequence zl_lenset (Ssequence zl_wsz (Ssequence zl_wbs zl_fins))).
Proof. reflexivity. Qed.

(* do { body } while (0) *)
Lemma semax_dowhile0_z {Espec: OracleKind} {cs: compspecs} (Delta: tycontext) (P Q: environ -> mpred)
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

Lemma zl_shru4: forall h, lrange h ->
  Int64.shru (Int64.repr h) (Int64.repr (Int.unsigned (Int.repr 4))) = Int64.repr (Z.shiftr h 4).
Proof.
  intros h Hh. unfold lrange in Hh. rewrite Int64.shru_div_two_p.
  change (two_p (Int64.unsigned (Int64.repr (Int.unsigned (Int.repr 4))))) with 16.
  rewrite Int64.unsigned_repr by rep_lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma zl_sub4: forall b, Int.sub (Int.repr b) (Int.repr 4) = Int.repr (u32 (b - 4)).
Proof.
  intros b. unfold u32, Int.sub. rewrite (Int.unsigned_repr 4) by rep_lia. apply Int.eqm_samerepr.
  change (2 ^ 32) with Int.modulus.
  eapply Int.eqm_trans; [ | apply Zbits.eqmod_mod; reflexivity].
  apply Int.eqm_sub; [apply Int.eqm_sym, Int.eqm_unsigned_repr | apply Int.eqm_refl].
Qed.

Lemma mem_rep_dropbits: forall F m n, mem_rep F (dropbits n m) = mem_rep F m.
Proof. reflexivity. Qed.

Lemma zl_drop_ok {Espec: OracleKind} (F: frame) (m: mst): lrange (m_hold m) ->
  semax Delta_cases5 (loop_state F m) zl_drop (normal_ret_assert (loop_state F (dropbits 4 m))).
Proof.
  intros Hh. unfold zl_drop, zl_r3, zl_r2, zl_rest, head_ZLIB.
  apply semax_dowhile0_z.
  unfold loop_state. rewrite mem_rep_dropbits.
  abbreviate_semax. forward. forward.
  rewrite (zl_shru4 _ Hh). rewrite zl_sub4.
  entailer!.
Qed.

(* loop_state_z with the local len *)
Definition loop_state_zl (F: frame) (m: mst) (len: Z) : environ -> mpred :=
  PROP (in_ok (f_ib F) (m_inp m); out_ok (f_ob F) (m_aout m))
  LOCAL (temp _len (zv len); temp _strm (f_strmp F); temp _flush (zv (f_flush F)); temp _state (f_sp F);
         temp _next (in_ptr (f_ib F) (m_nx m)); temp _put (out_ptr (f_ob F) (Zlength (m_ow m)));
         temp _have (zv (m_have m)); temp _left (zv (m_left m)); temp _hold (lv (m_hold m));
         temp _bits (zv (m_bits m)); temp _in (zv (m_in m)); temp _out (zv (m_out m));
         temp _ret (zv (m_ret m)); temp _leave (zv (m_leave m));
         lvar _here t_code (f_vhere F); lvar _last t_code (f_vlast F);
         lvar _hbuf (tarray tuchar 4) (f_vhbuf F); gvars (f_gv F))
  SEP (field_at Ews t_state (DOT _mode) (zv (i_mode (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _wrap) (zv (i_wrap (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _flags) (zv (i_flags (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _dmax) (zv (i_dmax (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _check) (lv (i_check (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _head) (if i_head (m_s m) then f_headp F else nullval) (f_sp F);
       field_at Ews t_state (DOT _wbits) (zv (i_wbits (m_s m))) (f_sp F);
       head_part F m; strm_z F m; mem_rep_z F m; locals_rep F).

(* the window object's size is 2^wbits: wbits = 0 must mean no window (Inv3.s3_head) *)
Lemma mem_rep_z_m3: forall F m len, (i_wbits (m_s m) = 0 -> i_win (m_s m) = false) ->
  mem_rep_z F (zl_m3 m len) = mem_rep_z F m.
Proof.
  intros F m len Hwin. unfold mem_rep_z, win_rep, zl_m3, upd_s.
  cbn [set_m_s m_s set_i_wbits i_win i_wbits m_ow].
  destruct (i_wbits (m_s m) =? 0) eqn:E.
  - apply Z.eqb_eq in E. rewrite (Hwin E). reflexivity.
  - reflexivity.
Qed.
Lemma head_part_m3: forall F m len, head_part F (zl_m3 m len) = head_part F m.
Proof. reflexivity. Qed.
Lemma strm_z_m3: forall F m len, strm_z F (zl_m3 m len) = strm_z F m.
Proof. reflexivity. Qed.

Lemma zl_len_val: forall h, lrange h ->
  Int.add (Int.and (Int.repr (Int64.unsigned (Int64.repr h)))
     (Int.sub (Int.shl (Int.repr 1) (Int.repr 4)) (Int.repr 1))) (Int.repr 8) = Int.repr (h mod 16 + 8).
Proof.
  intros h Hh. unfold lrange in Hh. rewrite Int64.unsigned_repr by rep_lia.
  rewrite zl_and_mask by lia. change (2 ^ 4) with 16. rewrite Int.add_unsigned.
  pose proof (Z.mod_pos_bound h 16 ltac:(lia)).
  rewrite !Int.unsigned_repr by rep_lia. reflexivity.
Qed.

(* len = BITS(4) + 8; *)
Lemma zl_lset_ok {Espec: OracleKind} (F: frame) (m: mst) (X: statement) (R: ret_assert): frame_ok F ->
  lrange (m_hold m) ->
  semax Delta_cases5 (loop_state_zl F m (m_hold m mod 16 + 8)) X R ->
  semax Delta_cases5 (loop_state F m) (Ssequence zl_lenset X) R.
Proof.
  intros FOK Hh HX. pose proof FOK as (HWS & HWH & HRG & HRT).
  unfold zl_lenset, zl_r4, zl_r3, zl_r2, zl_rest, head_ZLIB.
  rewrite loop_state_zsplit. unfold loop_state_z.
  abbreviate_semax. forward. rewrite (zl_len_val _ Hh).
  eapply semax_pre; [ | exact HX].
  unfold loop_state_zl. entailer!.
Qed.

(* if (state->wbits == 0) state->wbits = len; *)
Lemma zl_wbs_ok {Espec: OracleKind} (F: frame) (m: mst) (len: Z): frame_ok F ->
  8 <= len <= 15 -> 0 <= i_wbits (m_s m) <= 23 -> (i_wbits (m_s m) = 0 -> i_win (m_s m) = false) ->
  semax Delta_cases5 (loop_state_zl F m len) zl_wbs (normal_ret_assert (loop_state_zl F (zl_m3 m len) len)).
Proof.
  intros FOK Hl Hwb Hwin. pose proof FOK as (HWS & HWH & HRG & HRT).
  unfold zl_wbs, zl_r6, zl_r5, zl_r4, zl_r3, zl_r2, zl_rest, head_ZLIB.
  unfold loop_state_zl at 1.
  abbreviate_semax. forward. forward_if.
  - forward.
    unfold loop_state_zl. rewrite (mem_rep_z_m3 _ _ _ Hwin), head_part_m3, strm_z_m3.
    unfold zl_m3. cbn [upd_s set_m_s m_s set_i_wbits i_mode i_wrap i_flags i_dmax i_check i_head i_wbits
       m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave].
    rewrite (proj2 (Z.eqb_eq _ _) H1).
    entailer!.
  - forward.
    unfold loop_state_zl. rewrite (mem_rep_z_m3 _ _ _ Hwin), head_part_m3, strm_z_m3.
    unfold zl_m3. cbn [upd_s set_m_s m_s set_i_wbits i_mode i_wrap i_flags i_dmax i_check i_head i_wbits
       m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave].
    rewrite (proj2 (Z.eqb_neq _ _) H1).
    entailer!.
Qed.

(* if (len > 15 || (state->wbits != 0 && len > state->wbits)) <BAD> *)
Lemma zl_wsz_ok {Espec: OracleKind} (F: frame) (m m0: mst) (len: Z) (R: ret_assert): frame_ok F ->
  8 <= len <= 23 -> 0 <= i_wbits (m_s m) <= 23 ->
  RA_break R = RA_normal (case_post2 F m0) ->
  (zl_wc m len = true -> stepf2 (f_flush F) lenfix_list distfix_list m0 = IBrk (set_bad m M_wsize)) ->
  semax Delta_cases5 (loop_state_zl F m len) zl_wsz
    (overridePost (!! (zl_wc m len = false) && loop_state_zl F m len) R).
Proof.
  intros FOK Hl Hwb HR HS. pose proof FOK as (HWS & HWH & HRG & HRT).
  assert (HB: zl_wc m len = true -> forall Q, semax Delta_cases5 (loop_state F m)
                (bad_block_z (msg_ident M_wsize) 20) (overridePost Q R)).
  { intros C Q. apply (bad_z_wsize F FOK m m0); [destruct R; exact HR | exact (HS C)]. }
  unfold zl_wsz, zl_r5, zl_r4, zl_r3, zl_r2, zl_rest, head_ZLIB.
  unfold loop_state_zl.
  abbreviate_semax.
  apply semax_if_seq.
  forward_if.
  - forward. forward_if; [ | discriminate].
    assert (C: zl_wc m len = true)
      by (unfold zl_wc; apply orb_true_iff; left; apply Z.ltb_lt; lia).
    try (unfold abbreviate in MORE_COMMANDS; subst MORE_COMMANDS).
    try (unfold abbreviate in POSTCONDITION; subst POSTCONDITION).
    eapply semax_pre; [ | apply (HB C)].
    rewrite loop_state_zsplit. unfold loop_state_z. entailer!.
  - forward.
    apply semax_if_seq.
    forward_if.
    + forward. forward. forward. forward_if.
      * assert (C: zl_wc m len = true).
        { unfold zl_wc. apply orb_true_iff; right. apply andb_true_iff. split.
          - apply negb_true_iff, Z.eqb_neq. intro E. rewrite E in H2. contradiction.
          - apply Z.ltb_lt. destruct (zlt (i_wbits (m_s m)) len); [assumption | discriminate]. }
        try (unfold abbreviate in MORE_COMMANDS; subst MORE_COMMANDS).
        try (unfold abbreviate in POSTCONDITION; subst POSTCONDITION).
        eapply semax_pre; [ | apply (HB C)].
        rewrite loop_state_zsplit. unfold loop_state_z. entailer!.
      * assert (C: zl_wc m len = false).
        { unfold zl_wc. apply orb_false_iff; split; [apply Z.ltb_ge; lia | ].
          apply andb_false_iff. right. apply Z.ltb_ge.
          destruct (zlt (i_wbits (m_s m)) len); [discriminate | lia]. }
        forward. destruct R as [r1 r2 r3 r4]. cbn [RA_normal]. entailer!.
    + forward. forward_if; [ exfalso; auto | ].
      assert (C: zl_wc m len = false).
      { unfold zl_wc. apply orb_false_iff; split; [apply Z.ltb_ge; lia | ].
        apply andb_false_iff. left. apply negb_false_iff, Z.eqb_eq.
        exact H2. }
      forward. destruct R as [r1 r2 r3 r4]. cbn [RA_normal]. entailer!.
Qed.

(* state->dmax = 1U << len; state->flags = 0; strm->adler = state->check = adler32(0L, Z_NULL, 0);
   state->mode = hold & 0x200 ? DICTID : TYPE; INITBITS(); break; *)
Lemma zl_and64_repr: forall a b, Int64.and (Int64.repr a) (Int64.repr b) = Int64.repr (Z.land a b).
Proof.
  intros. apply Int64.same_bits_eq; intros i Hi.
  rewrite Int64.bits_and by auto. rewrite !Int64.testbit_repr by auto. rewrite Z.land_spec. reflexivity.
Qed.

Lemma zl_land512_range: forall h, 0 <= Z.land h 512 <= 512.
Proof.
  intros h. split.
  - apply Z.land_nonneg; lia.
  - apply Zbits.Ztestbit_le; [lia | ]. intros i _ T. rewrite Z.land_spec in T. apply andb_prop in T. tauto.
Qed.

Lemma zl_shl1: forall len, 0 <= len < 31 -> Int.shl (Int.repr 1) (Int.repr len) = Int.repr (2 ^ len).
Proof.
  intros len H. rewrite Int.shl_mul_two_p. rewrite Int.unsigned_repr by rep_lia. rewrite two_p_equiv.
  rewrite Int.mul_commut, Int.mul_one. reflexivity.
Qed.

Lemma mem_rep_z_fin: forall F m len, mem_rep_z F (zl_fin m len) = mem_rep_z F m.
Proof. reflexivity. Qed.
Lemma head_part_fin: forall F m len, head_part F (zl_fin m len) = head_part F m.
Proof. reflexivity. Qed.

Lemma m_have_fin: forall m len, m_have (zl_fin m len) = m_have m.
Proof. reflexivity. Qed.
Lemma m_left_fin: forall m len, m_left (zl_fin m len) = m_left m.
Proof. reflexivity. Qed.

Ltac zl_fin_tac F m len Em Hzca Hzcf :=
  rewrite loop_state_zsplit; unfold loop_state_z, strm_z, strm_rep;
  rewrite (mem_rep_z_fin F m len), (head_part_fin F m len), (m_have_fin m len), (m_left_fin m len);
  unfold zl_fin;
  cbn [set_mode upd_s set_m_s m_s set_i_mode i_mode initbits set_m_bits set_m_hold set_m_adler m_hold m_bits
       m_adler set_i_check set_i_flags set_i_dmax i_check i_flags i_dmax i_wrap i_head i_wbits m_inp m_aout m_nx
       m_ow m_in m_out m_ret m_leave m_snx m_sow m_tin m_tout m_msg];
  rewrite Em; rewrite (zl_shl1 len) by lia;
  rewrite <- Hzca, <- Hzcf; entailer!.

Lemma zl_fin_ok {Espec: OracleKind} (F: frame) (m m0: mst) (len: Z) (R: ret_assert): frame_ok F ->
  8 <= len <= 15 -> lrange (m_hold m) ->
  RA_break R = RA_normal (case_post2 F m0) ->
  stepf2 (f_flush F) lenfix_list distfix_list m0 = IBrk (zl_fin m len) ->
  semax Delta_cases5 (loop_state_zl F m len) zl_fins R.
Proof.
  intros FOK Hl Hh HR HS. pose proof FOK as (HWS & HWH & HRG & HRT).
  unfold zl_fins, zl_r6, zl_r5, zl_r4, zl_r3, zl_r2, zl_rest, head_ZLIB.
  unfold loop_state_zl.
  abbreviate_semax.
  forward.
  { entailer!. change (Int.unsigned Int.iwordsize) with 32. lia. }
  forward.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    apply semax_pre with (PROPx P (LOCALx Q (SEPx (emp :: emp :: R)))); [entailer! |] end.
  forward_call (0, nullval, 0, true, Ews, nullval, 0, 0, @nil val, @nil Z, false, Ews).
  unfold strm_z, strm_rep.
  remember (f_gv F _zcalloc) as zca eqn:Hzca. remember (f_gv F _zcfree) as zcf eqn:Hzcf.
  forward. forward.
  pose proof (zl_land512_range (m_hold m)) as H512.
  unfold abbreviate in MORE_COMMANDS. subst MORE_COMMANDS.
  apply -> seq_assoc. apply semax_if_seq.
  assert (FIN: forall Pre, semax Delta Pre (Sloop (Ssequence (Sset _hold (Ecast (Econst_int (Int.repr 0) tint) tulong))
                 (Sset _bits (Econst_int (Int.repr 0) tint))) Sbreak) (normal_ret_assert (loop_state F (zl_fin m len))) ->
     semax Delta Pre (Ssequence (Sloop (Ssequence (Sset _hold (Ecast (Econst_int (Int.repr 0) tint) tulong))
                 (Sset _bits (Econst_int (Int.repr 0) tint))) Sbreak) Sbreak) R).
  { intros Pre HP. eapply semax_seq'; [exact HP | ].
    eapply semax_pre; [ | apply semax_break]. rewrite HR. unfold case_post2, RA_normal.
    apply andp_left2. Exists (zl_fin m len). apply andp_right; [apply prop_right; exact HS | apply derives_refl]. }
  rewrite <- (m_have_fin m len), <- (m_left_fin m len).
  destruct (Z.land (m_hold m) 512 =? 0) eqn:Em.
  - forward_if.
    { exfalso. apply Z.eqb_eq in Em. rewrite zl_and64_repr, Em in H1. apply H1. reflexivity. }
    forward. forward. apply FIN. apply semax_dowhile0_z. forward. forward.
    zl_fin_tac F m len Em Hzca Hzcf.
  - forward_if.
    2:{ exfalso. apply Z.eqb_neq in Em. rewrite zl_and64_repr in H1. apply Em.
        apply (f_equal Int64.unsigned) in H1. rewrite Int64.unsigned_repr in H1 by rep_lia. exact H1. }
    forward. forward. apply FIN. apply semax_dowhile0_z. forward. forward.
    zl_fin_tac F m len Em Hzca Hzcf.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the whole branch, given that wbits = 0 means no window (Inv3.s3_head: mode HEAD, wrap <> 0)      *)

Lemma zl_shiftr_lrange: forall h k, lrange h -> 0 <= k -> lrange (Z.shiftr h k).
Proof.
  intros h k Hh Hk. unfold lrange in *. rewrite Z.shiftr_div_pow2 by lia.
  split; [apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia] | ].
  apply Z.div_le_upper_bound; [apply Z.pow_pos_nonneg; lia | ].
  assert (1 <= 2 ^ k) by (apply Z.pow_le_mono_r with (a := 2) in Hk; [simpl in Hk; lia | lia]). nia.
Qed.

Lemma head_zlib7_w {Espec: OracleKind} (F: frame) (m0 m1: mst) (R: ret_assert):
  frame_ok5 F -> mwf m1 -> m_leave m1 = 0 ->
  (i_wbits (m_s m1) = 0 -> i_win (m_s m1) = false) ->
  RA_break R = RA_normal (case_post2 F m0) ->
  stepf2 (f_flush F) lenfix_list distfix_list m0 = head_zlib_out m1 ->
  semax Delta_cases5 (loop_state F m1) head_ZLIB R.
Proof.
  intros [FOK _] W HL Hwin HR E.
  rewrite head_zlib_out_eq in E.
  pose proof (mw_hold _ W) as Hh. pose proof (sw_wrap_range _ (mw_s _ W)) as Hw.
  pose proof (sw_wbits _ (mw_s _ W)) as Hwb.
  assert (Hs: m_s (zl_mh m1) = m_s m1) by (unfold zl_mh; destruct (i_head (m_s m1)); reflexivity).
  assert (Hho: m_hold (zl_mh m1) = m_hold m1) by (unfold zl_mh; destruct (i_head (m_s m1)); reflexivity).
  rewrite head_ZLIB_eq.
  apply semax_seq' with (P' := loop_state F (zl_mh m1)); [apply zl_hd_ok; exact FOK | ].
  rewrite zl_rest_eq.
  eapply semax_seq.
  { apply (zl_c31_ok F (zl_mh m1) m0 R FOK); [rewrite Hho; exact Hh | rewrite Hs; exact Hw | exact HR | ].
    intro C. rewrite C in E. exact E. }
  apply semax_extract_prop; intros C31. rewrite C31 in E.
  eapply semax_seq.
  { apply (zl_meth_ok F (zl_mh m1) m0 R FOK); [rewrite Hho; exact Hh | exact HR | ].
    intro N. rewrite (proj2 (Z.eqb_neq _ _) N) in E. exact E. }
  apply semax_extract_prop; intros M8. rewrite (proj2 (Z.eqb_eq _ _) M8) in E. cbn [negb] in E.
  rewrite zl_r3_eq.
  apply semax_seq' with (P' := loop_state F (dropbits 4 (zl_mh m1))); [apply zl_drop_ok; rewrite Hho; exact Hh | ].
  rewrite zl_tail_eq in E. cbv zeta in E.
  assert (Hh2: lrange (m_hold (dropbits 4 (zl_mh m1)))).
  { unfold dropbits. cbn [set_m_bits set_m_hold m_hold]. rewrite Hho. apply zl_shiftr_lrange; [exact Hh | lia]. }
  assert (Hs2: m_s (dropbits 4 (zl_mh m1)) = m_s m1) by (rewrite <- Hs; reflexivity).
  apply (zl_lset_ok F (dropbits 4 (zl_mh m1)) _ R FOK Hh2).
  pose proof (Z.mod_pos_bound (m_hold (dropbits 4 (zl_mh m1))) 16 ltac:(lia)) as Hl.
  eapply semax_seq.
  { apply (zl_wsz_ok F _ m0 _ R FOK); [lia | rewrite Hs2; exact Hwb | exact HR | ].
    intro C. rewrite C in E. exact E. }
  apply semax_extract_prop; intros CW. rewrite CW in E.
  unfold zl_wc in CW. apply orb_false_iff in CW. destruct CW as [CW _]. apply Z.ltb_ge in CW.
  eapply semax_seq'.
  { apply zl_wbs_ok; [exact FOK | lia | rewrite Hs2; exact Hwb | rewrite Hs2; exact Hwin]. }
  apply (zl_fin_ok F _ m0 _ R FOK); [lia | exact Hh2 | exact HR | exact E].
Qed.
