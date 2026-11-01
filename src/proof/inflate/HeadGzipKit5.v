(* The kit of the gzip branch of case HEAD (HeadGzipW5.v), in Delta_cases5: a view of loop_state with the
   state fields mode, check and wbits, the crc table and the stack variables apart (the rest of the memory
   one opaque item mem_rep_g), and CRC2 (do { hbuf[0..1] = hold bytes; check = crc32(check, hbuf, 2); }
   while (0)) in a minimal context (ported from HdrCrc5.v, temps _t'439/_t'6). *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate.CaseHyps5.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.inflate.MwfLemmas.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Definition state_rep_g (gv: globals) (sp strmp headp winp: val) (s: istate) : mpred :=
  field_at Ews t_state (DOT _strm) strmp sp *
  field_at Ews t_state (DOT _last) (zv (i_last s)) sp *
  field_at Ews t_state (DOT _wrap) (zv (i_wrap s)) sp *
  field_at Ews t_state (DOT _havedict) (zv (i_havedict s)) sp *
  field_at Ews t_state (DOT _flags) (zv (i_flags s)) sp *
  field_at Ews t_state (DOT _dmax) (zv (i_dmax s)) sp *
  field_at Ews t_state (DOT _total) (lv (i_total s)) sp *
  field_at Ews t_state (DOT _head) (if i_head s then headp else nullval) sp *
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

(* the conjuncts 2, 8, 11 of 35 to the front (on variables: a cheap proof term) *)
Lemma sepcon_g_35: forall a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35: mpred,
  a1 * a2 * a3 * a4 * a5 * a6 * a7 * a8 * a9 * a10 * a11 * a12 * a13 * a14 * a15 * a16 * a17 * a18 * a19 * a20 * a21 * a22 * a23 * a24 * a25 * a26 * a27 * a28 * a29 * a30 * a31 * a32 * a33 * a34 * a35 =
  a2 * a8 * a11 * (a1 * a3 * a4 * a5 * a6 * a7 * a9 * a10 * a12 * a13 * a14 * a15 * a16 * a17 * a18 * a19 * a20 * a21 * a22 * a23 * a24 * a25 * a26 * a27 * a28 * a29 * a30 * a31 * a32 * a33 * a34 * a35).
Proof. intros. apply pred_ext; cancel. Qed.

Lemma state_rep_gsplit: forall gv sp strmp headp winp s,
  state_rep gv sp strmp headp winp s =
  field_at Ews t_state (DOT _mode) (zv (i_mode s)) sp *
  field_at Ews t_state (DOT _check) (lv (i_check s)) sp *
  field_at Ews t_state (DOT _wbits) (zv (i_wbits s)) sp *
  state_rep_g gv sp strmp headp winp s.
Proof. intros. unfold state_rep, state_rep_g. apply sepcon_g_35. Qed.

(* the memory but the three fields and the crc table *)
Definition mem_rep_g (F: frame) (m: mst) : mpred :=
  state_rep_g (f_gv F) (f_sp F) (f_strmp F) (f_headp F) (f_winp F) (m_s m) *
  win_rep (f_winp F) (m_s m) *
  head_part F m *
  strm_rep (f_gv F) (f_shs F) (f_strmp F)
    (in_ptr (f_ib F) (m_snx m)) (zv (Zlength (m_inp m) - m_snx m)) (m_tin m)
    (out_ptr (f_ob F) (m_sow m)) (zv (m_aout m - m_sow m)) (m_tout m)
    (msg_val (f_gv F) (m_msg m)) (f_sp F) (f_dt F) (m_adler m) (f_vres F) *
  in_rep (f_ib F) *
  out_rep (f_ob F) (m_ow m) *
  tables_rep (f_gsh F) (f_gv F).

Lemma mem_rep_gsplit: forall F m,
  mem_rep F m =
  field_at Ews t_state (DOT _mode) (zv (i_mode (m_s m))) (f_sp F) *
  field_at Ews t_state (DOT _check) (lv (i_check (m_s m))) (f_sp F) *
  field_at Ews t_state (DOT _wbits) (zv (i_wbits (m_s m))) (f_sp F) *
  crc_table_at (f_tsh F) (f_gv F) * mem_rep_g F m.
Proof.
  intros. unfold mem_rep, mem_rep_g. rewrite state_rep_gsplit.
  apply pred_ext; cancel.
Qed.

(* loop_state with these parts apart: the fields' values md, ck, wb given *)
Definition loop_state_g (F: frame) (m: mst) (md ck wb: val) : environ -> mpred :=
  PROP (in_ok (f_ib F) (m_inp m); out_ok (f_ob F) (m_aout m))
  LOCAL (temp _strm (f_strmp F); temp _flush (zv (f_flush F)); temp _state (f_sp F);
         temp _next (in_ptr (f_ib F) (m_nx m)); temp _put (out_ptr (f_ob F) (Zlength (m_ow m)));
         temp _have (zv (m_have m)); temp _left (zv (m_left m)); temp _hold (lv (m_hold m));
         temp _bits (zv (m_bits m)); temp _in (zv (m_in m)); temp _out (zv (m_out m));
         temp _ret (zv (m_ret m)); temp _leave (zv (m_leave m));
         lvar _here t_code (f_vhere F); lvar _last t_code (f_vlast F);
         lvar _hbuf (tarray tuchar 4) (f_vhbuf F); gvars (f_gv F))
  SEP (field_at Ews t_state (DOT _mode) md (f_sp F);
       field_at Ews t_state (DOT _check) ck (f_sp F);
       field_at Ews t_state (DOT _wbits) wb (f_sp F);
       crc_table_at (f_tsh F) (f_gv F);
       data_at_ Tsh (tarray tuchar 4) (f_vhbuf F);
       data_at_ Tsh t_code (f_vhere F); data_at_ Tsh t_code (f_vlast F); mem_rep_g F m).

Lemma loop_state_gsplit: forall F m,
  loop_state F m = loop_state_g F m (zv (i_mode (m_s m))) (lv (i_check (m_s m))) (zv (i_wbits (m_s m))).
Proof.
  intros. unfold loop_state, loop_state_g, locals_rep. rewrite mem_rep_gsplit.
  f_equal. unfold SEPx. simpl. f_equal. extensionality rho. apply pred_ext; cancel.
Qed.

(* the gzip branch's machine, in this view *)
Lemma win_rep_wbits: forall winp s w,
  (i_wbits s = 0 -> i_win s = false) ->
  w = (if i_wbits s =? 0 then 15 else i_wbits s) ->
  win_rep winp (set_i_wbits s w) = win_rep winp s.
Proof.
  intros winp s w H E. unfold win_rep. cbn [i_win set_i_wbits i_wbits i_wdata].
  destruct (i_win s) eqn:Ew; [ | reflexivity].
  destruct (Z.eqb_spec (i_wbits s) 0) as [Z0 | Z0].
  - discriminate (H Z0).
  - subst w. reflexivity.
Qed.

Lemma loop_state_head_gzip: forall F m (w c: Z),
  (i_wbits (m_s m) = 0 -> i_win (m_s m) = false) ->
  w = (if i_wbits (m_s m) =? 0 then 15 else i_wbits (m_s m)) ->
  loop_state F (set_mode (initbits (upd_s m (fun s => set_i_check (set_i_wbits s w) c)))
                  Zlib.proof.inflate.Model.FLAGS) =
  loop_state_g F (initbits m) (zv Zlib.proof.inflate.Model.FLAGS) (lv c) (zv w).
Proof.
  intros F m w c H E. rewrite loop_state_gsplit.
  assert (M: mem_rep_g F (set_mode (initbits (upd_s m (fun s => set_i_check (set_i_wbits s w) c)))
                  Zlib.proof.inflate.Model.FLAGS) = mem_rep_g F (initbits m)).
  { unfold mem_rep_g.
    cbn [set_mode initbits upd_s set_m_s set_m_hold set_m_bits m_s set_i_mode set_i_check].
    rewrite <- (win_rep_wbits (f_winp F) (m_s m) w H E). reflexivity. }
  unfold loop_state_g. rewrite M. reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* CRC2 in a minimal context                                                                      *)

Definition crc2_stmt (t1 t2: ident) : statement :=
  (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _hbuf (tarray tuchar 4)) (Econst_int (Int.repr 0) tint) (tptr tuchar)) tuchar) (Ecast (Etempvar _hold tulong) tuchar)) (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _hbuf (tarray tuchar 4)) (Econst_int (Int.repr 1) tint) (tptr tuchar)) tuchar) (Ecast (Ebinop Oshr (Etempvar _hold tulong) (Econst_int (Int.repr 8) tint) tulong) tuchar)) (Ssequence (Ssequence (Sset t1 (Efield (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr))) (Tstruct _inflate_state noattr)) _check tulong)) (Scall (Some t2) (Evar _crc32 (Tfunction (tulong :: (tptr tuchar) :: tuint :: nil) tulong cc_default)) ((Etempvar t1 tulong) :: (Evar _hbuf (tarray tuchar 4)) :: (Econst_int (Int.repr 2) tint) :: nil))) (Sassign (Efield (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr))) (Tstruct _inflate_state noattr)) _check tulong) (Etempvar t2 tulong))))).

Lemma hg_byte_mod: forall x, 0 <= x mod 256 <= Byte.max_unsigned.
Proof. intros x. pose proof (Z.mod_pos_bound x 256 ltac:(lia)). rep_lia. Qed.

Lemma hg_hbytes2_bytes: forall h, is_bytes (hbytes2 h).
Proof. intros h. unfold hbytes2. repeat constructor; apply hg_byte_mod. Qed.

Lemma hg_zext_mod: forall x, Int.zero_ext 8 (Int.zero_ext 8 (Int.repr x)) = Int.repr (x mod 256).
Proof.
  intros x. rewrite Int.zero_ext_idem by lia.
  apply Int.same_bits_eq; intros i Hi. rewrite Int.bits_zero_ext by lia. rewrite !Int.testbit_repr by auto.
  change 256 with (2 ^ 8). destruct (zlt i 8).
  - rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma hg_byte_shr: forall h n, lrange h -> 0 <= n ->
  Vint (Int.zero_ext 8 (Int.zero_ext 8 (Int.repr (Int64.Z_mod_modulus (Z.shiftr (Int64.unsigned (Int64.repr h)) n))))) =
  Vint (Int.repr (Z.shiftr h n mod 256)).
Proof.
  intros h n R Hn. unfold lrange in R. rewrite Int64.unsigned_repr by rep_lia.
  rewrite Int64.Z_mod_modulus_eq. rewrite Z.mod_small.
  - rewrite hg_zext_mod. reflexivity.
  - pose proof (Zshiftr_range h n ltac:(rep_lia) Hn). unfold Int64.modulus, Int64.wordsize, Wordsize_64.wordsize.
    change (two_power_nat 64) with (Int64.max_unsigned + 1). lia.
Qed.

Lemma hg_byte0: forall h, lrange h ->
  Vint (Int.zero_ext 8 (Int.zero_ext 8 (Int.repr (Int64.unsigned (Int64.repr h))))) = Vint (Int.repr (h mod 256)).
Proof. intros h R. unfold lrange in R. rewrite Int64.unsigned_repr by rep_lia. rewrite hg_zext_mod. reflexivity. Qed.

Lemma hg_upd2: forall v0 v1,
  upd_Znth 1 (upd_Znth 0 (default_val (tarray tuchar 4)) v0) v1 = [v0; v1; Vundef; Vundef].
Proof. intros. reflexivity. Qed.

(* the crc32 spec's buffer is stated in the crc32 unit's compspecs *)
Lemma hg_da_cs: forall sh (v: list val) p,
  @data_at Zlib.units.Inflate.CS sh (tarray tuchar 4) v p = @data_at Zlib.units.Crc32.CS sh (tarray tuchar 4) v p.
Proof.
  intros.
  assert (E: @data_at Zlib.units.Crc32.CS sh (tarray tuchar 4) v = @data_at Zlib.units.Inflate.CS sh (tarray tuchar 4) v).
  { apply (@data_at_change_composite _ _ CCE_crc32); [apply JMeq_refl | reflexivity]. }
  rewrite E. reflexivity.
Qed.

Definition crc_pre_g (sp vhbuf: val) (gv: globals) (tsh: share) (h c: Z) : environ -> mpred :=
  PROP () LOCAL (temp _state sp; temp _hold (lv h); lvar _hbuf (tarray tuchar 4) vhbuf; gvars gv)
  SEP (field_at Ews t_state (DOT _check) (lv c) sp; crc_table_at tsh gv; data_at_ Tsh (tarray tuchar 4) vhbuf).

Lemma semax_crc2_HEAD {Espec: OracleKind} sp vhbuf gv tsh h c:
  readable_share tsh -> lrange h -> lrange c ->
  semax Delta_cases5 (crc_pre_g sp vhbuf gv tsh h c) (crc2_stmt _t'439 _t'6)
    (normal_ret_assert (crc_pre_g sp vhbuf gv tsh h (ref_crc32 c (hbytes2 h)))).
Proof.
  intros HT RH RC. unfold crc_pre_g, crc2_stmt.
  remember (Int64.repr h) as H64 eqn:EH. abbreviate_semax.
  forward. forward. forward.
  subst H64. rewrite hg_upd2, hg_byte0, hg_byte_shr by (auto; lia).
  assert_PROP (isptr vhbuf) by entailer!.
  forward_call (c, vhbuf, 2, false, Tsh, vhbuf, 0, 4,
                [Vint (Int.repr (h mod 256)); Vint (Int.repr (Z.shiftr h 8 mod 256)); Vundef; Vundef],
                hbytes2 h, false, Tsh, gv, tsh).
  { rewrite <- hg_da_cs; cancel. }
  { split; [ | apply cbuf_valid_pos; lia].
    unfold cbuf_ok; rewrite isptr_offset_val_zero by auto.
    split; [reflexivity | ]; split; [auto | ]; split; [lia | ]; split; [lia | ]; split; [reflexivity | ].
    split; [apply hg_hbytes2_bytes | reflexivity]. }
  forward. entailer!.
Qed.

(* do { body } while (0) *)
Lemma semax_dowhile0_g {Espec: OracleKind} {cs: compspecs} (Delta: tycontext) (P Q: environ -> mpred)
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
