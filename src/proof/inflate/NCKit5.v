(* Kit of the cases NAME (6) and COMMENT (7) of inflate()'s switch (Cases5_NC.v), version 5 (Delta_cases5, Model2.v):
   - the memory with the six state fields these cases touch apart (mode, wrap, flags, check, head, length)
     and the rest one opaque item (mem_rep_nc);
   - the model of the two cases split by their branches (lemmas c_NAME_x, c_COMMENT_x);
   - mwf of the machines on the way. *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Export Zlib.proof.inflate.CaseKitT5.
Require Import Zlib.proof.inflate.Steps2.
Require Import Zlib.proof.inflate.MwfLemmas.
Require Import Zlib.proof.crc32.Spec.
Require Zlib.proof.crc32.Combine.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* ---------------------------------------------------------------------------------------------- *)
(* memory                                                                                         *)

Definition state_rep_nc (gv: globals) (sp strmp headp winp: val) (s: istate) : mpred :=
  field_at Ews t_state (DOT _strm) strmp sp *
  field_at Ews t_state (DOT _last) (zv (i_last s)) sp *
  field_at Ews t_state (DOT _havedict) (zv (i_havedict s)) sp *
  field_at Ews t_state (DOT _dmax) (zv (i_dmax s)) sp *
  field_at Ews t_state (DOT _total) (lv (i_total s)) sp *
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

Lemma sepcon_nc_35: forall a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35: mpred,
  a1 * a2 * a3 * a4 * a5 * a6 * a7 * a8 * a9 * a10 * a11 * a12 * a13 * a14 * a15 * a16 * a17 * a18 * a19 * a20 * a21 * a22 * a23 * a24 * a25 * a26 * a27 * a28 * a29 * a30 * a31 * a32 * a33 * a34 * a35 =
  a2 * a4 * a6 * a8 * a10 * a18 *
  (a1 * a3 * a5 * a7 * a9 * a11 * a12 * a13 * a14 * a15 * a16 * a17 * a19 * a20 * a21 * a22 * a23 * a24 * a25 * a26 * a27 * a28 * a29 * a30 * a31 * a32 * a33 * a34 * a35).
Proof. intros. apply pred_ext; cancel. Qed.

Lemma state_rep_nc_split: forall gv sp strmp headp winp s,
  state_rep gv sp strmp headp winp s =
  field_at Ews t_state (DOT _mode) (zv (i_mode s)) sp *
  field_at Ews t_state (DOT _wrap) (zv (i_wrap s)) sp *
  field_at Ews t_state (DOT _flags) (zv (i_flags s)) sp *
  field_at Ews t_state (DOT _check) (lv (i_check s)) sp *
  field_at Ews t_state (DOT _head) (if i_head s then headp else nullval) sp *
  field_at Ews t_state (DOT _length) (zv (i_length s)) sp *
  state_rep_nc gv sp strmp headp winp s.
Proof. intros. unfold state_rep, state_rep_nc. apply sepcon_nc_35. Qed.

(* the head part of a frame for i_head = hd and the header h *)
Definition hp (F: frame) (hd: bool) (h: hstate) : mpred :=
  if hd then head_rep (f_hsh F) (f_headp F) (f_xb F) (f_nb F) (f_cb F) h else emp.

Definition mem_rep_nc (F: frame) (m: mst) : mpred :=
  state_rep_nc (f_gv F) (f_sp F) (f_strmp F) (f_headp F) (f_winp F) (m_s m) *
  win_rep (f_winp F) (m_s m) *
  strm_rep (f_gv F) (f_shs F) (f_strmp F)
    (in_ptr (f_ib F) (m_snx m)) (zv (Zlength (m_inp m) - m_snx m)) (m_tin m)
    (out_ptr (f_ob F) (m_sow m)) (zv (m_aout m - m_sow m)) (m_tout m)
    (msg_val (f_gv F) (m_msg m)) (f_sp F) (f_dt F) (m_adler m) (f_vres F) *
  out_rep (f_ob F) (m_ow m) *
  tables_rep (f_gsh F) (f_gv F).

Lemma mem_rep_nc_split: forall F m,
  mem_rep F m =
  field_at Ews t_state (DOT _mode) (zv (i_mode (m_s m))) (f_sp F) *
  field_at Ews t_state (DOT _wrap) (zv (i_wrap (m_s m))) (f_sp F) *
  field_at Ews t_state (DOT _flags) (zv (i_flags (m_s m))) (f_sp F) *
  field_at Ews t_state (DOT _check) (lv (i_check (m_s m))) (f_sp F) *
  field_at Ews t_state (DOT _head) (if i_head (m_s m) then f_headp F else nullval) (f_sp F) *
  field_at Ews t_state (DOT _length) (zv (i_length (m_s m))) (f_sp F) *
  hp F (i_head (m_s m)) (m_h m) * in_rep (f_ib F) * crc_table_at (f_tsh F) (f_gv F) * mem_rep_nc F m.
Proof.
  intros. unfold mem_rep, mem_rep_nc, head_part, hp. rewrite state_rep_nc_split.
  apply pred_ext; cancel.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the model                                                                                      *)

(* one byte of the do-while: the new length and buffer *)
Definition zst_L (wr: bool) (L max: Z) : Z := if andb wr (L <? max) then L + 1 else L.
Definition zst_buf (wr: bool) (L max: Z) (buf: list Z) (b: Z) : list Z :=
  if andb wr (L <? max) then upd_Znth L buf b else buf.

Lemma zstr_f_step: forall bytes have L max wr buf j,
  0 <= j < have ->
  zstr_f (Z.to_nat (have - j)) bytes have L max wr buf j =
  let b := Znth j bytes in
  if andb (negb (b =? 0)) (j + 1 <? have)
  then zstr_f (Z.to_nat (have - (j + 1))) bytes have (zst_L wr L max) max wr (zst_buf wr L max buf b) (j + 1)
  else (j + 1, b, zst_L wr L max, zst_buf wr L max buf b).
Proof.
  intros. replace (Z.to_nat (have - j)) with (S (Z.to_nat (have - (j + 1)))) by lia.
  cbn [zstr_f]. unfold zst_L, zst_buf. destruct (andb wr (L <? max)); reflexivity.
Qed.

Lemma zstr_f_ok: forall k bytes have length max wr buf copy,
  bytes_ok bytes -> have <= Zlength bytes -> 0 <= copy < have -> 0 <= length -> max <= Zlength buf ->
  bytes_ok buf ->
  let '(c, b, ln, buf') := zstr_f k bytes have length max wr buf copy in
  0 <= c <= have /\ length <= ln <= Z.max length max /\ Zlength buf' = Zlength buf /\ bytes_ok buf'.
Proof.
  induction k; intros bytes have length max wr buf copy B HB C L M BO; simpl.
  - split; [lia |]. split; [lia |]. auto.
  - assert (BY: 0 <= Znth copy bytes <= Byte.max_unsigned).
    { apply (Forall_Znth bytes (fun b => 0 <= b <= Byte.max_unsigned)); auto. lia. }
    destruct (andb wr (length <? max)) eqn:WR.
    + apply andb_prop in WR. destruct WR as [_ WR]. apply Z.ltb_lt in WR.
      assert (ZL: Zlength (upd_Znth length buf (Znth copy bytes)) = Zlength buf)
        by (apply upd_Znth_Zlength; lia).
      assert (BO': bytes_ok (upd_Znth length buf (Znth copy bytes))) by (apply Forall_upd_Znth; auto).
      destruct (andb (negb (Znth copy bytes =? 0)) (copy + 1 <? have)) eqn:NX.
      * apply andb_prop in NX. destruct NX as [_ NX]. apply Z.ltb_lt in NX.
        specialize (IHk bytes have (length + 1) max wr (upd_Znth length buf (Znth copy bytes)) (copy + 1)
                    B HB ltac:(lia) ltac:(lia) ltac:(rewrite ZL; lia) BO').
        destruct (zstr_f k _ _ _ _ _ _ _) as [[[c b] ln] buf']. destruct IHk as (I1 & I2 & I3 & I4).
        split; [lia |]. split; [lia |]. split; [congruence | auto].
      * split; [lia |]. split; [lia |]. auto.
    + destruct (andb (negb (Znth copy bytes =? 0)) (copy + 1 <? have)) eqn:NX.
      * apply andb_prop in NX. destruct NX as [_ NX]. apply Z.ltb_lt in NX.
        specialize (IHk bytes have length max wr buf (copy + 1) B HB ltac:(lia) L M BO).
        destruct (zstr_f k _ _ _ _ _ _ _) as [[[c b] ln] buf']. destruct IHk as (I1 & I2 & I3 & I4).
        split; [lia |]. split; [lia |]. auto.
      * split; [lia |]. split; [lia |]. auto.
Qed.

(* the machine after NAME's do-while and crc (copy bytes read, length ln, buffer buf) *)
Definition nm_name (m: mst) (c ln: Z) (buf: list Z) : mst :=
  let m := crc_if m (inbytes m c) in
  let m := upd_h (upd_s m (fun s => set_i_length s ln)) (fun h => set_h_nbuf h buf) in
  set_m_nx m (m_nx m + c).
Definition nm_comment (m: mst) (c ln: Z) (buf: list Z) : mst :=
  let m := crc_if m (inbytes m c) in
  let m := upd_h (upd_s m (fun s => set_i_length s ln)) (fun h => set_h_cbuf h buf) in
  set_m_nx m (m_nx m + c).

Definition name_bytes (m: mst) : list Z := sublist (m_nx m) (Zlength (m_inp m)) (m_inp m).

Lemma c_NAME2_have0: forall m,
  Z.land (i_flags (m_s m)) 2048 <> 0 -> m_have m = 0 -> c_NAME2 m = IBrk (set_leave m).
Proof.
  intros m F H. unfold c_NAME2. rewrite (proj2 (Z.eqb_neq _ _) F), H. reflexivity.
Qed.

Lemma c_NAME2_str: forall m c b ln buf,
  Z.land (i_flags (m_s m)) 2048 <> 0 -> m_have m <> 0 ->
  zstr_f (Z.to_nat (m_have m)) (name_bytes m) (m_have m) (i_length (m_s m)) (h_name_max (m_h m))
    (andb (i_head (m_s m)) (h_np (m_h m))) (h_nbuf (m_h m)) 0 = (c, b, ln, buf) ->
  c_NAME2 m = if negb (b =? 0) then IBrk (set_leave (nm_name m c ln buf))
             else c_COMMENT2 (set_mode (upd_s (nm_name m c ln buf) (fun s => set_i_length s 0)) COMMENT).
Proof.
  intros m c b ln buf F H Z. unfold c_NAME2. rewrite (proj2 (Z.eqb_neq _ _) F), (proj2 (Z.eqb_neq _ _) H).
  cbv beta zeta. unfold name_bytes in Z. simpl negb. rewrite Z. reflexivity.
Qed.

Lemma c_NAME2_none: forall m,
  Z.land (i_flags (m_s m)) 2048 = 0 ->
  c_NAME2 m = c_COMMENT2 (set_mode (upd_s (if i_head (m_s m) then upd_h m (fun h => set_h_np h false) else m)
                                        (fun s => set_i_length s 0)) COMMENT).
Proof. intros m F. unfold c_NAME2. rewrite F. reflexivity. Qed.

Lemma c_COMMENT2_have0: forall m,
  Z.land (i_flags (m_s m)) 4096 <> 0 -> m_have m = 0 -> c_COMMENT2 m = IBrk (set_leave m).
Proof.
  intros m F H. unfold c_COMMENT2. rewrite (proj2 (Z.eqb_neq _ _) F), H. reflexivity.
Qed.

Lemma c_COMMENT2_str: forall m c b ln buf,
  Z.land (i_flags (m_s m)) 4096 <> 0 -> m_have m <> 0 ->
  zstr_f (Z.to_nat (m_have m)) (name_bytes m) (m_have m) (i_length (m_s m)) (h_comm_max (m_h m))
    (andb (i_head (m_s m)) (h_cp (m_h m))) (h_cbuf (m_h m)) 0 = (c, b, ln, buf) ->
  c_COMMENT2 m = if negb (b =? 0) then IBrk (set_leave (nm_comment m c ln buf))
             else c_HCRC (set_mode (nm_comment m c ln buf) HCRC).
Proof.
  intros m c b ln buf F H Z. unfold c_COMMENT2. rewrite (proj2 (Z.eqb_neq _ _) F), (proj2 (Z.eqb_neq _ _) H).
  cbv beta zeta. unfold name_bytes in Z. simpl negb. rewrite Z. reflexivity.
Qed.

Lemma c_COMMENT2_none: forall m,
  Z.land (i_flags (m_s m)) 4096 = 0 ->
  c_COMMENT2 m = c_HCRC (set_mode (if i_head (m_s m) then upd_h m (fun h => set_h_cp h false) else m) HCRC).
Proof. intros m F. unfold c_COMMENT2. rewrite F. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the invariant                                                                                  *)

Lemma modewf_hdr: forall s, HEAD <= i_mode s <= TYPEDO -> modewf s.
Proof.
  intros s H. unfold HEAD, TYPEDO in H.
  constructor; repeat match goal with |- _ /\ _ => split end; unfold decode_mode; intros E;
  unfold LENLENS, CODELENS, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT in E; exfalso; lia.
Qed.

Lemma swf3_hdr: forall s, FLAGS <= i_mode s <= TYPEDO -> swf3 s.
Proof.
  intros s H. unfold FLAGS, TYPEDO in H.
  constructor; unfold decode_mode; intros E;
  unfold HEAD, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT in E; exfalso; lia.
Qed.

(* a header-mode machine built from m by changing the state, the header and next *)
Lemma mwf_hdr: forall m m',
  mwf m -> m_mode m = NAME \/ m_mode m = COMMENT -> HEAD <= m_mode m' <= TYPEDO ->
  swf (m_s m') -> hwf (m_h m') -> 0 <= m_nx m' <= Zlength (m_inp m) ->
  m_inp m' = m_inp m -> m_aout m' = m_aout m -> m_ow m' = m_ow m -> m_hold m' = m_hold m ->
  m_bits m' = m_bits m -> m_in m' = m_in m -> m_out m' = m_out m -> m_ret m' = m_ret m ->
  m_leave m' = m_leave m -> m_adler m' = m_adler m -> m_tin m' = m_tin m -> m_tout m' = m_tout m ->
  m_snx m' = m_snx m -> m_sow m' = m_sow m ->
  mwf m'.
Proof.
  intros m m' W HM HM' S H NX E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12 E13 E14.
  assert (O: m_out m = m_aout m).
  { apply mwf_out_eq; auto; destruct HM as [HM | HM]; rewrite HM; unfold NAME, COMMENT, LENGTH, DONE, BAD;
    lia. }
  destruct W. constructor; rewrite ?E1, ?E2, ?E3, ?E4, ?E5, ?E6, ?E7, ?E8, ?E9, ?E10, ?E11, ?E12, ?E13, ?E14;
    auto.
  - apply modewf_hdr. exact HM'.
Qed.

Lemma swf_length: forall s v, swf s -> urange v -> swf (set_i_length s v).
Proof. intros s v [] H; constructor; simpl; auto. Qed.
Lemma swf_check: forall s v, swf s -> lrange v -> swf (set_i_check s v).
Proof. intros s v [] H; constructor; simpl; auto. Qed.
Lemma swf_mode: forall s v, swf s -> HEAD <= v <= SYNC -> swf (set_i_mode s v).
Proof. intros s v [] H; constructor; simpl; auto. Qed.
Lemma hwf_nbuf: forall h v, hwf h -> Zlength v = h_name_max h -> bytes_ok v -> hwf (set_h_nbuf h v).
Proof. intros h v [] H1 H2; constructor; simpl; auto. Qed.
Lemma hwf_cbuf: forall h v, hwf h -> Zlength v = h_comm_max h -> bytes_ok v -> hwf (set_h_cbuf h v).
Proof. intros h v [] H1 H2; constructor; simpl; auto. Qed.
Lemma hwf_np: forall h v, hwf h -> hwf (set_h_np h v).
Proof. intros h v []; constructor; simpl; auto. Qed.
Lemma hwf_cp: forall h v, hwf h -> hwf (set_h_cp h v).
Proof. intros h v []; constructor; simpl; auto. Qed.

(* crc_if only changes the check *)
Definition crc_val (s: istate) (data: list Z) : Z :=
  if andb (negb (Z.land (i_flags s) 512 =? 0)) (negb (Z.land (i_wrap s) 4 =? 0))
  then ref_crc32 (i_check s) data else i_check s.

Lemma crc_if_eq: forall m d, crc_if m d = set_m_s m (set_i_check (m_s m) (crc_val (m_s m) d)).
Proof.
  intros m d. unfold crc_if, crc_val, upd_s.
  destruct (andb _ _); [reflexivity |]. destruct m as [s]; destruct s; reflexivity.
Qed.

Lemma crc_val_range: forall s d, swf s -> is_bytes d -> lrange (crc_val s d).
Proof.
  intros s d S B. unfold crc_val. destruct (andb _ _); [| apply (sw_check _ S)].
  pose proof (Zlib.proof.crc32.Combine.ref_crc32_range (i_check s) d B). unfold Zlib.proof.crc32.GF2.is32 in *. unfold lrange.
  rep_lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* `state->length = 0; state->mode = md;`                                                          *)

Lemma mem_rep_nc_len_mode: forall F m v md,
  mem_rep_nc F (set_mode (upd_s m (fun s => set_i_length s v)) md) = mem_rep_nc F m.
Proof. reflexivity. Qed.

Lemma semax_len0_mode {Espec: OracleKind} (F: frame) (m: mst) (md: Z):
  semax Delta_cases5 (loop_state F m)
    (Ssequence
      (Sassign (Efield (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                         (Tstruct _inflate_state noattr)) _length tuint)
         (Econst_int (Int.repr 0) tint))
      (Sassign (Efield (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                         (Tstruct _inflate_state noattr)) _mode tint)
         (Econst_int (Int.repr md) tint)))
    (normal_ret_assert (loop_state F (set_mode (upd_s m (fun s => set_i_length s 0)) md))).
Proof.
  unfold loop_state. rewrite !mem_rep_nc_split, mem_rep_nc_len_mode.
  abbreviate_semax. Intros.
  forward. forward.
  entailer!. apply derives_refl.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* bit tests                                                                                      *)

Lemma land_range: forall a b, 0 <= b -> 0 <= Z.land a b <= b.
Proof.
  intros a b H. split.
  - apply Z.land_nonneg; auto.
  - apply Zbits.Ztestbit_le; auto. intros i _ T. rewrite Z.land_spec in T. apply andb_prop in T. tauto.
Qed.

Lemma int_and_repr: forall a k, 0 <= k <= Int.max_unsigned ->
  Int.and (Int.repr a) (Int.repr k) = Int.repr (Z.land a k).
Proof.
  intros a k K. unfold Int.and. rewrite (Int.unsigned_repr k) by lia. rewrite Int.unsigned_repr_eq.
  f_equal. change Int.modulus with (2 ^ 32).
  rewrite <- (Z.land_ones a 32) by lia. rewrite <- Z.land_assoc. f_equal.
  rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. rep_lia.
Qed.

Lemma int_and_zero: forall a k, 0 <= k <= Int.max_unsigned ->
  (Int.and (Int.repr a) (Int.repr k) = Int.zero <-> Z.land a k = 0).
Proof.
  intros a k K. rewrite int_and_repr by auto. pose proof (land_range a k ltac:(lia)).
  split; intros E.
  - apply (f_equal Int.unsigned) in E. rewrite Int.unsigned_repr in E by lia. exact E.
  - rewrite E. reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the input object from next on                                                                  *)

Lemma in_split: forall sh n (c: list val) p k,
  field_compatible (tarray tuchar n) [] p -> 0 <= k <= n -> Zlength c = n ->
  data_at sh (tarray tuchar n) c p =
  data_at sh (tarray tuchar k) (sublist 0 k c) p * data_at sh (tarray tuchar (n - k)) (sublist k n c) (offset_val k p).
Proof.
  intros sh n c p k FC K L. pose proof (offset_val_field_address0_tuchar n k p FC K) as E.
  unfold tarray in *. rewrite (split2_data_at_Tarray_tuchar sh n k) by auto.
  rewrite <- E. reflexivity.
Qed.

Lemma in_sfx_bytes: forall sh p lo n c inp nx k,
  in_ok (InBuf sh p lo n c) inp -> 0 <= nx -> 0 <= k -> nx + k <= Zlength inp ->
  sublist 0 k (sublist (lo + nx) n c) = byte_vals (sublist nx (nx + k) inp).
Proof.
  intros sh p lo n c inp nx k (R & P & L0 & L1 & LC & LM & S & B) N K NK.
  rewrite sublist_sublist by lia.
  assert (E: sublist (0 + (lo + nx)) (k + (lo + nx)) c = sublist nx (nx + k) (sublist lo (lo + Zlength inp) c)).
  { rewrite sublist_sublist by lia. f_equal; lia. }
  rewrite E, S. unfold byte_vals. rewrite sublist_map. reflexivity.
Qed.

Lemma in_sfx_znth: forall sh p lo n c inp nx j,
  in_ok (InBuf sh p lo n c) inp -> 0 <= nx -> 0 <= j -> nx + j < Zlength inp ->
  Znth j (sublist (lo + nx) n c) = Vint (Int.repr (Znth j (sublist nx (Zlength inp) inp))).
Proof.
  intros sh p lo n c inp nx j I N J NJ.
  pose proof (in_sfx_bytes sh p lo n c inp nx (j + 1) I N ltac:(lia) ltac:(lia)) as E.
  destruct I as (R & P & L0 & L1 & LC & LM & S & B).
  assert (E2: Znth j (sublist (lo + nx) n c) = Znth j (sublist 0 (j + 1) (sublist (lo + nx) n c)))
    by (rewrite (Znth_sublist 0 j (j + 1)) by lia; f_equal; lia).
  rewrite E2, E. unfold byte_vals. rewrite Znth_map by list_solve.
  rewrite !Znth_sublist by lia; try reflexivity.
Qed.

