(* Kit of the switch cases EXLEN and EXTRA (Cases5_EX.v; ported from the v3 kit to Model2/stepf2): the fields of struct inflate_state these
   cases touch (mode, wrap, flags, check, head, length), the gz_header, the input and the crc table apart
   from the rest of the memory (mem_x, one opaque SEP item, unchanged by the cases' updates), and the
   model facts (mwf3 of the fallthrough machines). *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Export Zlib.proof.inflate.ExHdrKit5.
Require Export Zlib.proof.inflate.ExHdrSame5.
Require Import Zlib.proof.inflate.Steps2.
Require Import Zlib.proof.inflate.MwfLemmas.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.crc32.Combine.

#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Definition state_rep_x (gv: globals) (sp strmp headp winp: val) (s: istate) : mpred :=
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

(* conjuncts 2, 4, 6, 8, 10, 18 of 35 to the front (on variables: a cheap proof term) *)
Lemma sepcon_pick6: forall a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35: mpred,
  a1 * a2 * a3 * a4 * a5 * a6 * a7 * a8 * a9 * a10 * a11 * a12 * a13 * a14 * a15 * a16 * a17 * a18 * a19 * a20 * a21 * a22 * a23 * a24 * a25 * a26 * a27 * a28 * a29 * a30 * a31 * a32 * a33 * a34 * a35 =
  a2 * a4 * a6 * a8 * a10 * a18 *
  (a1 * a3 * a5 * a7 * a9 * a11 * a12 * a13 * a14 * a15 * a16 * a17 * a19 * a20 * a21 * a22 * a23 * a24 * a25 * a26 * a27 * a28 * a29 * a30 * a31 * a32 * a33 * a34 * a35).
Proof. intros. apply pred_ext; cancel. Qed.

Lemma state_rep_split_x: forall gv sp strmp headp winp s,
  state_rep gv sp strmp headp winp s =
  field_at Ews t_state (DOT _mode) (zv (i_mode s)) sp *
  field_at Ews t_state (DOT _wrap) (zv (i_wrap s)) sp *
  field_at Ews t_state (DOT _flags) (zv (i_flags s)) sp *
  field_at Ews t_state (DOT _check) (lv (i_check s)) sp *
  field_at Ews t_state (DOT _head) (if i_head s then headp else nullval) sp *
  field_at Ews t_state (DOT _length) (zv (i_length s)) sp *
  state_rep_x gv sp strmp headp winp s.
Proof. intros. unfold state_rep, state_rep_x. apply sepcon_pick6. Qed.

(* the rest of the memory *)
Definition mem_x (F: frame) (m: mst) : mpred :=
  state_rep_x (f_gv F) (f_sp F) (f_strmp F) (f_headp F) (f_winp F) (m_s m) *
  win_rep (f_winp F) (m_s m) *
  strm_rep (f_gv F) (f_shs F) (f_strmp F)
    (in_ptr (f_ib F) (m_snx m)) (zv (Zlength (m_inp m) - m_snx m)) (m_tin m)
    (out_ptr (f_ob F) (m_sow m)) (zv (m_aout m - m_sow m)) (m_tout m)
    (msg_val (f_gv F) (m_msg m)) (f_sp F) (f_dt F) (m_adler m) (f_vres F) *
  out_rep (f_ob F) (m_ow m) *
  tables_rep (f_gsh F) (f_gv F).

Lemma sepcon_pick_mem: forall s1 s2 s3 s4 s5 s6 sx w h st i o t c: mpred,
  s1 * s2 * s3 * s4 * s5 * s6 * sx * w * h * st * i * o * t * c =
  s1 * s2 * s3 * s4 * s5 * s6 * h * i * c * (sx * w * st * o * t).
Proof. intros. apply pred_ext; cancel. Qed.

Lemma mem_rep_split_x: forall F m,
  mem_rep F m =
  field_at Ews t_state (DOT _mode) (zv (i_mode (m_s m))) (f_sp F) *
  field_at Ews t_state (DOT _wrap) (zv (i_wrap (m_s m))) (f_sp F) *
  field_at Ews t_state (DOT _flags) (zv (i_flags (m_s m))) (f_sp F) *
  field_at Ews t_state (DOT _check) (lv (i_check (m_s m))) (f_sp F) *
  field_at Ews t_state (DOT _head) (if i_head (m_s m) then f_headp F else nullval) (f_sp F) *
  field_at Ews t_state (DOT _length) (zv (i_length (m_s m))) (f_sp F) *
  head_part F m * in_rep (f_ib F) * crc_table_at (f_tsh F) (f_gv F) * mem_x F m.
Proof.
  intros. unfold mem_rep, mem_x. rewrite state_rep_split_x. apply sepcon_pick_mem.
Qed.

(* loop_state with the fields of the cases apart *)
Definition ex_state (F: frame) (m: mst) : environ -> mpred :=
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
       field_at Ews t_state (DOT _check) (lv (i_check (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _head) (if i_head (m_s m) then f_headp F else nullval) (f_sp F);
       field_at Ews t_state (DOT _length) (zv (i_length (m_s m))) (f_sp F);
       head_part F m; in_rep (f_ib F); crc_table_at (f_tsh F) (f_gv F); mem_x F m; locals_rep F).

Lemma loop_state_ex: forall F m, loop_state F m = ex_state F m.
Proof.
  intros. unfold loop_state, ex_state. rewrite mem_rep_split_x.
  f_equal. unfold SEPx. simpl. rewrite !sepcon_assoc. reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The model                                                                                      *)

(* EXLEN with FEXTRA, after NEEDBITS(16) *)
Definition exlen_fin (m1: mst) : mst :=
  let v := u32 (m_hold m1) in
  let m2 := upd_s m1 (fun s => set_i_length s v) in
  let m3 := if i_head (m_s m2) then upd_h m2 (fun h => set_h_extra_len h v) else m2 in
  initbits (crc_if m3 (hbytes2 (m_hold m3))).

(* EXLEN without FEXTRA *)
Definition exlen_skip (m: mst) : mst :=
  if i_head (m_s m) then upd_h m (fun h => set_h_xp h false) else m.

(* EXTRA with FEXTRA: the copy of min(length, have) bytes *)
Definition extra_n (len copy max: Z) : Z := if max <? u32 (len + copy) then max - len else copy.

Definition extra_upd (m: mst) : mst :=
  let s := m_s m in
  let copy := Z.min (i_length s) (m_have m) in
  if negb (copy =? 0) then
    let h := m_h m in
    let len := u32 (h_extra_len h - i_length s) in
    let m := if andb (andb (i_head s) (h_xp h)) (len <? h_extra_max h) then
               let n := if h_extra_max h <? u32 (len + copy) then h_extra_max h - len else copy in
               upd_h m (fun h => set_h_xbuf h (put_bytes (h_xbuf h) len (inbytes m n)))
             else m in
    let m := crc_if m (inbytes m copy) in
    set_m_nx (upd_s m (fun s => set_i_length s (i_length s - copy))) (m_nx m + copy)
  else m.

Definition extra_fin (m: mst) : mst := set_mode (upd_s m (fun s => set_i_length s 0)) NAME.

Lemma needbits_f_sh: forall k n m, m_s (needbits_f k n m) = m_s m /\ m_h (needbits_f k n m) = m_h m.
Proof.
  induction k; intros n m; simpl; auto.
  destruct (m_bits m <? n); auto. destruct (m_have m =? 0); auto. destruct (IHk n (pull m)) as [A B].
  rewrite A, B. auto.
Qed.

Lemma needbits_sh: forall n m, m_s (needbits n m) = m_s m /\ m_h (needbits n m) = m_h m.
Proof. intros. apply needbits_f_sh. Qed.

(* the step of EXLEN *)
Lemma step_exlen_set: forall fl m, m_mode m = EXLEN -> Z.land (i_flags (m_s m)) 1024 <> 0 ->
  let m1 := needbits 16 m in
  (m_leave m1 = 1 -> stepf2 fl lenfix_list distfix_list m = IBrk m1) /\
  (m_leave m1 = 0 -> stepf2 fl lenfix_list distfix_list m =
                     stepf2 fl lenfix_list distfix_list (set_mode (exlen_fin m1) EXTRA)).
Proof.
  intros fl m HM Hf m1.
  rewrite (stepf2_EXLEN _ _ _ m HM).
  split; intro E.
  - unfold c_EXLEN2. apply Z.eqb_neq in Hf. rewrite Hf. cbv beta zeta. fold m1. rewrite E. reflexivity.
  - etransitivity; [ | symmetry; exact (stepf2_EXTRA fl lenfix_list distfix_list (set_mode (exlen_fin m1) EXTRA) eq_refl)].
    unfold c_EXLEN2. apply Z.eqb_neq in Hf. rewrite Hf. cbv beta zeta. fold m1. rewrite E.
    reflexivity.
Qed.

Lemma step_exlen_skip: forall fl m, m_mode m = EXLEN -> Z.land (i_flags (m_s m)) 1024 = 0 ->
  stepf2 fl lenfix_list distfix_list m = stepf2 fl lenfix_list distfix_list (set_mode (exlen_skip m) EXTRA).
Proof.
  intros fl m HM Hf.
  rewrite (stepf2_EXLEN _ _ _ m HM).
  etransitivity; [ | symmetry; exact (stepf2_EXTRA fl lenfix_list distfix_list (set_mode (exlen_skip m) EXTRA) eq_refl)].
  unfold c_EXLEN2. rewrite Hf. reflexivity.
Qed.

(* the step of EXTRA *)
Lemma step_extra: forall fl m, m_mode m = EXTRA ->
  let m' := if Z.land (i_flags (m_s m)) 1024 =? 0 then m else extra_upd m in
  (i_length (m_s m') <> 0 -> Z.land (i_flags (m_s m)) 1024 <> 0 ->
     stepf2 fl lenfix_list distfix_list m = IBrk (set_leave m')) /\
  (i_length (m_s m') = 0 \/ Z.land (i_flags (m_s m)) 1024 = 0 ->
     stepf2 fl lenfix_list distfix_list m = stepf2 fl lenfix_list distfix_list (extra_fin m')).
Proof.
  intros fl m HM m'.
  rewrite (stepf2_EXTRA _ _ _ m HM).
  split.
  - intros E Hf. subst m'. apply Z.eqb_neq in Hf. rewrite Hf in *. unfold c_EXTRA2. rewrite Hf.
    cbv beta zeta. unfold extra_upd in E. apply Z.eqb_neq in E. rewrite E. reflexivity.
  - intros E.
    etransitivity; [ | symmetry; exact (stepf2_NAME fl lenfix_list distfix_list (extra_fin m') eq_refl)].
    subst m'. unfold c_EXTRA2. destruct (Z.land (i_flags (m_s m)) 1024 =? 0) eqn:Hf.
    + reflexivity.
    + destruct E as [E | E]; [ | apply Z.eqb_eq in E; congruence].
      cbv beta zeta. unfold extra_upd in E. apply Z.eqb_eq in E. rewrite E. reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* mwf3 of the fallthrough machines                                                               *)

Definition crc_val (s: istate) (data: list Z) : Z :=
  if andb (negb (Z.land (i_flags s) 512 =? 0)) (negb (Z.land (i_wrap s) 4 =? 0))
  then ref_crc32 (i_check s) data else i_check s.

Lemma crc_if_eq: forall m d, crc_if m d = set_m_s m (set_i_check (m_s m) (crc_val (m_s m) d)).
Proof.
  intros m d. unfold crc_if, crc_val, upd_s.
  destruct (andb _ _); [reflexivity |]. destruct m as [s]; destruct s; reflexivity.
Qed.

Lemma crc_val_range: forall s d, swf s -> bytes_ok d -> lrange (crc_val s d).
Proof.
  intros s d W B. unfold crc_val. destruct (andb _ _).
  - pose proof (ref_crc32_range (i_check s) d B). unfold is32 in *. unfold lrange. rep_lia.
  - apply (sw_check _ W).
Qed.

Lemma modewf_hdr: forall s, i_mode s = EXLEN \/ i_mode s = EXTRA \/ i_mode s = NAME -> modewf s.
Proof.
  intros s H.
  assert (N: forall P: Prop, i_mode s = LENLENS \/ i_mode s = CODELENS \/ decode_mode (i_mode s) \/
                             i_mode s = LENEXT \/ i_mode s = DISTEXT \/ i_mode s = MATCH \/ i_mode s = DIST -> P).
  { intros P D. exfalso. unfold decode_mode in D.
    unfold EXLEN, EXTRA, NAME, LENLENS, CODELENS, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT in *. lia. }
  constructor; try (intros; apply N; tauto); repeat split; intros; apply N; tauto.
Qed.

Lemma swf3_hdr: forall s, i_mode s = EXLEN \/ i_mode s = EXTRA \/ i_mode s = NAME -> swf3 s.
Proof.
  intros s H.
  assert (N: forall P: Prop, i_mode s = HEAD \/ decode_mode (i_mode s) \/
                             i_mode s = LENEXT \/ i_mode s = DISTEXT -> P).
  { intros P D. exfalso. unfold decode_mode in D.
    unfold EXLEN, EXTRA, NAME, HEAD, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT in *. lia. }
  constructor; intros; apply N; tauto.
Qed.

Lemma hbytes2_ok: forall h, bytes_ok (hbytes2 h).
Proof.
  intros. unfold hbytes2, bytes_ok. rep_lia || (repeat constructor; 
    try (pose proof (Z.mod_pos_bound h 256 ltac:(lia)); rep_lia);
    try (pose proof (Z.mod_pos_bound (Z.shiftr h 8) 256 ltac:(lia)); rep_lia)).
Qed.

Lemma u32_range: forall x, urange (u32 x).
Proof. intros. unfold urange, u32. pose proof (Z.mod_pos_bound x (2^32) ltac:(lia)). rep_lia. Qed.

Lemma mwf3_exlen_fin: forall m1, mwf m1 -> m_mode m1 = EXLEN ->
  mwf3 (set_mode (exlen_fin m1) EXTRA) /\ m_leave (set_mode (exlen_fin m1) EXTRA) = m_leave m1.
Proof.
  intros m1 W HM. unfold exlen_fin. cbv zeta.
  change (i_head (m_s (upd_s m1 (fun s => set_i_length s (u32 (m_hold m1)))))) with (i_head (m_s m1)).
  rewrite crc_if_eq.
  pose proof (u32_range (m_hold m1)) as U.
  assert (O: m_out m1 = m_aout m1).
  { apply mwf_out_eq; [exact W | ..]; rewrite HM; unfold EXLEN, LENGTH, DONE, BAD; lia. }
  assert (C: forall s, swf s -> lrange (crc_val s (hbytes2 (m_hold m1))))
    by (intros; apply crc_val_range; auto; apply hbytes2_ok).
  destruct W as [MD S H I A NX OW HO B IN OUT R L AD TI TO SNX SOW OE].
  destruct (i_head (m_s m1)); (split; [split | reflexivity]);
    [ | apply swf3_hdr; right; left; reflexivity | | apply swf3_hdr; right; left; reflexivity];
    (constructor; cbn -[crc_val]; auto;
     [ apply modewf_hdr; right; left; reflexivity
     | destruct S; constructor; cbn -[crc_val]; auto;
       [ unfold EXTRA, HEAD, SYNC; lia | apply C; constructor; auto ]
     | ..]).
  - destruct H; constructor; cbn; auto.
  - unfold initbits, lrange; cbn; rep_lia.
  - unfold initbits; cbn; lia.
  - unfold initbits, lrange; cbn; rep_lia.
  - unfold initbits; cbn; lia.
Qed.

Lemma mwf3_exlen_skip: forall m, mwf m -> m_mode m = EXLEN ->
  mwf3 (set_mode (exlen_skip m) EXTRA) /\ m_leave (set_mode (exlen_skip m) EXTRA) = m_leave m.
Proof.
  intros m W HM. unfold exlen_skip.
  assert (O: m_out m = m_aout m).
  { apply mwf_out_eq; [exact W | ..]; rewrite HM; unfold EXLEN, LENGTH, DONE, BAD; lia. }
  destruct W as [MD S H I A NX OW HO B IN OUT R L AD TI TO SNX SOW OE].
  destruct (i_head (m_s m)); (split; [split | reflexivity]);
    [ | apply swf3_hdr; right; left; reflexivity | | apply swf3_hdr; right; left; reflexivity];
    (constructor; cbn; auto;
     [ apply modewf_hdr; right; left; reflexivity
     | destruct S; constructor; cbn; auto; unfold EXTRA, HEAD, SYNC; lia
     | ..]).
  destruct H; constructor; cbn; auto.
Qed.

Lemma extra_n_range: forall len copy max,
  0 <= len < max -> max <= 65536 -> 0 <= copy <= Int.max_signed ->
  0 <= extra_n len copy max <= copy /\ len + extra_n len copy max <= max.
Proof.
  intros len copy max A B C. unfold extra_n, u32.
  rewrite Z.mod_small by rep_lia.
  destruct (Z.ltb_spec max (len + copy)); lia.
Qed.

Lemma put_bytes_len: forall buf pos b, 0 <= pos -> pos + Zlength b <= Zlength buf ->
  Zlength (put_bytes buf pos b) = Zlength buf.
Proof. intros. unfold put_bytes. list_solve. Qed.

Lemma put_bytes_ok: forall buf pos b, 0 <= pos -> pos + Zlength b <= Zlength buf ->
  bytes_ok buf -> bytes_ok b -> bytes_ok (put_bytes buf pos b).
Proof.
  intros buf pos b P Q Hb Hc. unfold put_bytes, bytes_ok in *.
  apply Forall_app; split; [ | apply Forall_app; split; auto];
    apply Forall_sublist; auto.
Qed.

Lemma inbytes_len: forall m n, 0 <= n -> 0 <= m_nx m -> m_nx m + n <= Zlength (m_inp m) ->
  Zlength (inbytes m n) = n.
Proof. intros. unfold inbytes. rewrite Zlength_sublist by lia. lia. Qed.

Lemma inbytes_ok: forall m n, bytes_ok (m_inp m) -> bytes_ok (inbytes m n).
Proof. intros. unfold inbytes, bytes_ok in *. apply Forall_sublist; auto. Qed.

Lemma mwf_extra_upd: forall m, mwf m -> m_mode m = EXTRA ->
  mwf (extra_upd m) /\ m_mode (extra_upd m) = EXTRA /\ m_leave (extra_upd m) = m_leave m.
Proof.
  intros m W HM. unfold extra_upd. cbv zeta.
  destruct (negb (Z.min (i_length (m_s m)) (m_have m) =? 0)); [ | auto].
  pose proof (mwf_have m W) as HV.
  pose proof (sw_length _ (mw_s _ W)) as LN.
  set (copy := Z.min (i_length (m_s m)) (m_have m)) in *.
  assert (CP: 0 <= copy <= m_have m /\ copy <= i_length (m_s m)) by (unfold urange in LN; lia).
  set (len := u32 (h_extra_len (m_h m) - i_length (m_s m))).
  pose proof (hw_extra_max _ (mw_h _ W)) as XM.
  pose proof (hw_xbuf _ (mw_h _ W)) as XB.
  pose proof (mw_nx _ W) as NX. pose proof (mw_inp _ W) as INP.
  assert (WX: mwf (if andb (andb (i_head (m_s m)) (h_xp (m_h m))) (len <? h_extra_max (m_h m)) then
                 let n := if h_extra_max (m_h m) <? u32 (len + copy) then h_extra_max (m_h m) - len else copy in
                 upd_h m (fun h => set_h_xbuf h (put_bytes (h_xbuf h) len (inbytes m n)))
               else m)).
  { destruct (andb (andb _ _) (len <? _)) eqn:E; [ | exact W].
    apply andb_prop in E. destruct E as [_ E]. apply Z.ltb_lt in E.
    assert (LP: 0 <= len) by (unfold len, u32; apply Z.mod_pos_bound; lia).
    destruct (extra_n_range len copy (h_extra_max (m_h m))) as [N1 N2]; [lia | lia | rep_lia | ].
    unfold extra_n in N1, N2. cbv zeta.
    set (n := if h_extra_max (m_h m) <? u32 (len + copy) then h_extra_max (m_h m) - len else copy) in *.
    assert (LB: Zlength (inbytes m n) = n) by (apply inbytes_len; unfold m_have in *; lia).
    destruct W as [MD S H I A NX' OW HO B IN OUT R L AD TI TO SNX SOW OE].
    constructor; cbn -[put_bytes inbytes]; auto.
    destruct H; constructor; cbn -[put_bytes inbytes]; auto.
    destruct hw_xbuf as [X1 X2].
    split; [rewrite put_bytes_len; lia | apply put_bytes_ok; auto; try lia; apply inbytes_ok; tauto]. }
  set (m0 := if andb _ _ then _ else m) in WX |- *.
  assert (E0: m_s m0 = m_s m /\ m_nx m0 = m_nx m /\ m_inp m0 = m_inp m /\ m_leave m0 = m_leave m).
  { subst m0. destruct (andb _ _); auto. }
  destruct E0 as (E1 & E2 & E3 & E4).
  rewrite crc_if_eq.
  assert (C: lrange (crc_val (m_s m0) (inbytes m0 copy))).
  { apply crc_val_range; [apply WX | apply inbytes_ok; apply WX]. }
  clearbody m0.
  destruct WX as [MD S H I A NX' OW HO B IN OUT R L AD TI TO SNX SOW OE].
  rewrite E1 in *. rewrite E2, E3 in *.
  split; [ | split; [cbn; exact HM | cbn; exact E4]].
  assert (HMs: i_mode (m_s m) = EXTRA) by exact HM.
  constructor; cbn; rewrite ?E1, ?E2, ?E3; auto;
    try (intros; exfalso; unfold decode_mode in *;
         unfold EXTRA, LENLENS, CODELENS, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT in *; lia);
    try (repeat split; intros; exfalso; unfold EXTRA, LENEXT, DIST, DISTEXT in *; lia).
  all: lazymatch goal with
       | |- modewf _ => apply modewf_hdr; right; left; exact HM
       | |- swf _ => destruct S; constructor; cbn; auto; unfold urange in *; lia
       | |- _ \/ _ => unfold m_mode in OE; rewrite E1 in OE; exact OE
       | |- _ => unfold m_have in *; lia
       end.
Qed.

Lemma mwf3_extra_fin: forall m, mwf m -> m_mode m = EXTRA ->
  mwf3 (extra_fin m) /\ m_leave (extra_fin m) = m_leave m.
Proof.
  intros m W HM. unfold extra_fin.
  assert (O: m_out m = m_aout m).
  { apply mwf_out_eq; [exact W | ..]; rewrite HM; unfold EXTRA, LENGTH, DONE, BAD; lia. }
  destruct W as [MD S H I A NX OW HO B IN OUT R L AD TI TO SNX SOW OE].
  split; [split | reflexivity]; [ | apply swf3_hdr; right; right; reflexivity].
  constructor; cbn; auto.
  - apply modewf_hdr; right; right; reflexivity.
  - destruct S; constructor; cbn; auto; unfold NAME, HEAD, SYNC, urange; rep_lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* mem_x and head_part under the updates of the cases                                             *)

Lemma land_repr: forall x c, 0 <= c < 2 ^ 32 -> Z.land (Int.unsigned (Int.repr x)) c = Z.land x c.
Proof.
  intros x c Hc. rewrite Int.unsigned_repr_eq. change Int.modulus with (2 ^ 32).
  rewrite <- Z.land_ones by lia. rewrite <- Z.land_assoc. f_equal.
  rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small; lia.
Qed.

Lemma mem_x_upd_h: forall F m f, mem_x F (upd_h m f) = mem_x F m.
Proof. reflexivity. Qed.
Lemma mem_x_length: forall F m v, mem_x F (upd_s m (fun s => set_i_length s v)) = mem_x F m.
Proof. reflexivity. Qed.
Lemma mem_x_check: forall F m v, mem_x F (set_m_s m (set_i_check (m_s m) v)) = mem_x F m.
Proof. reflexivity. Qed.
Lemma mem_x_initbits: forall F m, mem_x F (initbits m) = mem_x F m.
Proof. reflexivity. Qed.
Lemma mem_x_nx: forall F m v, mem_x F (set_m_nx m v) = mem_x F m.
Proof. reflexivity. Qed.
Lemma mem_x_leave: forall F m, mem_x F (set_leave m) = mem_x F m.
Proof. reflexivity. Qed.
Lemma mem_x_mode: forall F m md, mem_x F (set_mode m md) = mem_x F m.
Proof. reflexivity. Qed.

Lemma head_part_length: forall F m v, head_part F (upd_s m (fun s => set_i_length s v)) = head_part F m.
Proof. reflexivity. Qed.
Lemma head_part_chk: forall F m v, head_part F (set_m_s m (set_i_check (m_s m) v)) = head_part F m.
Proof. reflexivity. Qed.
Lemma head_part_initbits: forall F m, head_part F (initbits m) = head_part F m.
Proof. reflexivity. Qed.
Lemma head_part_nx: forall F m v, head_part F (set_m_nx m v) = head_part F m.
Proof. reflexivity. Qed.
Lemma head_part_leave: forall F m, head_part F (set_leave m) = head_part F m.
Proof. reflexivity. Qed.
Lemma head_part_mode: forall F m md, head_part F (set_mode m md) = head_part F m.
Proof. reflexivity. Qed.
Lemma head_part_upd_h: forall F m f, i_head (m_s m) = true ->
  head_part F (upd_h m f) = head_rep (f_hsh F) (f_headp F) (f_xb F) (f_nb F) (f_cb F) (f (m_h m)).
Proof. intros F m f E. unfold head_part. cbn. rewrite E. reflexivity. Qed.
Lemma head_part_on: forall F m, i_head (m_s m) = true ->
  head_part F m = head_rep (f_hsh F) (f_headp F) (f_xb F) (f_nb F) (f_cb F) (m_h m).
Proof. intros F m E. unfold head_part. rewrite E. reflexivity. Qed.
Lemma head_part_off: forall F m, i_head (m_s m) = false -> head_part F m = emp.
Proof. intros F m E. unfold head_part. rewrite E. reflexivity. Qed.

Ltac x_simpl :=
  rewrite ?mem_x_upd_h, ?mem_x_length, ?mem_x_check, ?mem_x_initbits, ?mem_x_nx, ?mem_x_leave, ?mem_x_mode,
          ?head_part_length, ?head_part_chk, ?head_part_initbits, ?head_part_nx, ?head_part_leave,
          ?head_part_mode.

Lemma repr_u32: forall x, Int.repr (u32 x) = Int.repr x.
Proof.
  intros. unfold u32. rewrite <- (Int.repr_unsigned (Int.repr x)), Int.unsigned_repr_eq. reflexivity.
Qed.

(* do { c } while (0) *)
Lemma semax_dowhile0R {Espec: OracleKind}: forall Delta P c R,
  semax Delta P c (normal_ret_assert (RA_normal R)) -> semax Delta P (Sloop c Sbreak) R.
Proof.
  intros Delta P c R H.
  apply semax_loop with (Q' := RA_normal R).
  - eapply semax_post; [ | | | | exact H]; destruct R; simpl; intros; apply andp_left2;
      [ apply derives_refl | apply prop_left; tauto | apply prop_left; tauto | apply prop_left; tauto ].
  - eapply semax_pre; [ | apply semax_break]. destruct R; simpl. intro rho. apply andp_left2. apply derives_refl.
Qed.

(* ex_state with the temporary _t'24 (the condition of CRC2) *)
Definition ex_state_t24 (F: frame) (m: mst) (v: val) : environ -> mpred :=
  PROP (in_ok (f_ib F) (m_inp m); out_ok (f_ob F) (m_aout m))
  LOCAL (temp _t'24 v; temp _strm (f_strmp F); temp _flush (zv (f_flush F)); temp _state (f_sp F);
         temp _next (in_ptr (f_ib F) (m_nx m)); temp _put (out_ptr (f_ob F) (Zlength (m_ow m)));
         temp _have (zv (m_have m)); temp _left (zv (m_left m)); temp _hold (lv (m_hold m));
         temp _bits (zv (m_bits m)); temp _in (zv (m_in m)); temp _out (zv (m_out m));
         temp _ret (zv (m_ret m)); temp _leave (zv (m_leave m));
         lvar _here t_code (f_vhere F); lvar _last t_code (f_vlast F);
         lvar _hbuf (tarray tuchar 4) (f_vhbuf F); gvars (f_gv F))
  SEP (field_at Ews t_state (DOT _mode) (zv (i_mode (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _wrap) (zv (i_wrap (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _flags) (zv (i_flags (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _check) (lv (i_check (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _head) (if i_head (m_s m) then f_headp F else nullval) (f_sp F);
       field_at Ews t_state (DOT _length) (zv (i_length (m_s m))) (f_sp F);
       head_part F m; in_rep (f_ib F); crc_table_at (f_tsh F) (f_gv F); mem_x F m; locals_rep F).

(* whether crc_if updates the check *)
Definition crc_on (s: istate) : bool :=
  andb (negb (Z.land (i_flags s) 512 =? 0)) (negb (Z.land (i_wrap s) 4 =? 0)).

Lemma crc_if_on: forall m d, crc_on (m_s m) = true ->
  crc_if m d = set_m_s m (set_i_check (m_s m) (ref_crc32 (i_check (m_s m)) d)).
Proof. intros m d E. rewrite crc_if_eq. unfold crc_val. unfold crc_on in E. rewrite E. reflexivity. Qed.

Lemma crc_if_off: forall m d, crc_on (m_s m) = false -> crc_if m d = m.
Proof. intros m d E. unfold crc_if. unfold crc_on in E. rewrite E. reflexivity. Qed.

(* projections of the machine under upd_s / upd_h / set_m_s *)
Lemma m_h_upd_s: forall m (f: istate -> istate), m_h (upd_s m f) = m_h m. Proof. reflexivity. Qed.
Lemma m_inp_upd_s: forall m (f: istate -> istate), m_inp (upd_s m f) = m_inp m. Proof. reflexivity. Qed.
Lemma m_aout_upd_s: forall m (f: istate -> istate), m_aout (upd_s m f) = m_aout m. Proof. reflexivity. Qed.
Lemma m_nx_upd_s: forall m (f: istate -> istate), m_nx (upd_s m f) = m_nx m. Proof. reflexivity. Qed.
Lemma m_ow_upd_s: forall m (f: istate -> istate), m_ow (upd_s m f) = m_ow m. Proof. reflexivity. Qed.
Lemma m_hold_upd_s: forall m (f: istate -> istate), m_hold (upd_s m f) = m_hold m. Proof. reflexivity. Qed.
Lemma m_bits_upd_s: forall m (f: istate -> istate), m_bits (upd_s m f) = m_bits m. Proof. reflexivity. Qed.
Lemma m_in_upd_s: forall m (f: istate -> istate), m_in (upd_s m f) = m_in m. Proof. reflexivity. Qed.
Lemma m_out_upd_s: forall m (f: istate -> istate), m_out (upd_s m f) = m_out m. Proof. reflexivity. Qed.
Lemma m_ret_upd_s: forall m (f: istate -> istate), m_ret (upd_s m f) = m_ret m. Proof. reflexivity. Qed.
Lemma m_leave_upd_s: forall m (f: istate -> istate), m_leave (upd_s m f) = m_leave m. Proof. reflexivity. Qed.
Lemma m_have_upd_s: forall m (f: istate -> istate), m_have (upd_s m f) = m_have m. Proof. reflexivity. Qed.
Lemma m_left_upd_s: forall m (f: istate -> istate), m_left (upd_s m f) = m_left m. Proof. reflexivity. Qed.
Lemma m_snx_upd_s: forall m (f: istate -> istate), m_snx (upd_s m f) = m_snx m. Proof. reflexivity. Qed.
Lemma m_sow_upd_s: forall m (f: istate -> istate), m_sow (upd_s m f) = m_sow m. Proof. reflexivity. Qed.
Lemma m_tin_upd_s: forall m (f: istate -> istate), m_tin (upd_s m f) = m_tin m. Proof. reflexivity. Qed.
Lemma m_tout_upd_s: forall m (f: istate -> istate), m_tout (upd_s m f) = m_tout m. Proof. reflexivity. Qed.
Lemma m_adler_upd_s: forall m (f: istate -> istate), m_adler (upd_s m f) = m_adler m. Proof. reflexivity. Qed.
Lemma m_msg_upd_s: forall m (f: istate -> istate), m_msg (upd_s m f) = m_msg m. Proof. reflexivity. Qed.
Lemma m_inp_upd_h: forall m (f: hstate -> hstate), m_inp (upd_h m f) = m_inp m. Proof. reflexivity. Qed.
Lemma m_aout_upd_h: forall m (f: hstate -> hstate), m_aout (upd_h m f) = m_aout m. Proof. reflexivity. Qed.
Lemma m_nx_upd_h: forall m (f: hstate -> hstate), m_nx (upd_h m f) = m_nx m. Proof. reflexivity. Qed.
Lemma m_ow_upd_h: forall m (f: hstate -> hstate), m_ow (upd_h m f) = m_ow m. Proof. reflexivity. Qed.
Lemma m_hold_upd_h: forall m (f: hstate -> hstate), m_hold (upd_h m f) = m_hold m. Proof. reflexivity. Qed.
Lemma m_bits_upd_h: forall m (f: hstate -> hstate), m_bits (upd_h m f) = m_bits m. Proof. reflexivity. Qed.
Lemma m_in_upd_h: forall m (f: hstate -> hstate), m_in (upd_h m f) = m_in m. Proof. reflexivity. Qed.
Lemma m_out_upd_h: forall m (f: hstate -> hstate), m_out (upd_h m f) = m_out m. Proof. reflexivity. Qed.
Lemma m_ret_upd_h: forall m (f: hstate -> hstate), m_ret (upd_h m f) = m_ret m. Proof. reflexivity. Qed.
Lemma m_leave_upd_h: forall m (f: hstate -> hstate), m_leave (upd_h m f) = m_leave m. Proof. reflexivity. Qed.
Lemma m_have_upd_h: forall m (f: hstate -> hstate), m_have (upd_h m f) = m_have m. Proof. reflexivity. Qed.
Lemma m_left_upd_h: forall m (f: hstate -> hstate), m_left (upd_h m f) = m_left m. Proof. reflexivity. Qed.
Lemma m_snx_upd_h: forall m (f: hstate -> hstate), m_snx (upd_h m f) = m_snx m. Proof. reflexivity. Qed.
Lemma m_sow_upd_h: forall m (f: hstate -> hstate), m_sow (upd_h m f) = m_sow m. Proof. reflexivity. Qed.
Lemma m_tin_upd_h: forall m (f: hstate -> hstate), m_tin (upd_h m f) = m_tin m. Proof. reflexivity. Qed.
Lemma m_tout_upd_h: forall m (f: hstate -> hstate), m_tout (upd_h m f) = m_tout m. Proof. reflexivity. Qed.
Lemma m_adler_upd_h: forall m (f: hstate -> hstate), m_adler (upd_h m f) = m_adler m. Proof. reflexivity. Qed.
Lemma m_msg_upd_h: forall m (f: hstate -> hstate), m_msg (upd_h m f) = m_msg m. Proof. reflexivity. Qed.
Lemma m_h_set_m_s: forall m s, m_h (set_m_s m s) = m_h m. Proof. reflexivity. Qed.
Lemma m_inp_set_m_s: forall m s, m_inp (set_m_s m s) = m_inp m. Proof. reflexivity. Qed.
Lemma m_aout_set_m_s: forall m s, m_aout (set_m_s m s) = m_aout m. Proof. reflexivity. Qed.
Lemma m_nx_set_m_s: forall m s, m_nx (set_m_s m s) = m_nx m. Proof. reflexivity. Qed.
Lemma m_ow_set_m_s: forall m s, m_ow (set_m_s m s) = m_ow m. Proof. reflexivity. Qed.
Lemma m_hold_set_m_s: forall m s, m_hold (set_m_s m s) = m_hold m. Proof. reflexivity. Qed.
Lemma m_bits_set_m_s: forall m s, m_bits (set_m_s m s) = m_bits m. Proof. reflexivity. Qed.
Lemma m_in_set_m_s: forall m s, m_in (set_m_s m s) = m_in m. Proof. reflexivity. Qed.
Lemma m_out_set_m_s: forall m s, m_out (set_m_s m s) = m_out m. Proof. reflexivity. Qed.
Lemma m_ret_set_m_s: forall m s, m_ret (set_m_s m s) = m_ret m. Proof. reflexivity. Qed.
Lemma m_leave_set_m_s: forall m s, m_leave (set_m_s m s) = m_leave m. Proof. reflexivity. Qed.
Lemma m_have_set_m_s: forall m s, m_have (set_m_s m s) = m_have m. Proof. reflexivity. Qed.
Lemma m_left_set_m_s: forall m s, m_left (set_m_s m s) = m_left m. Proof. reflexivity. Qed.
Lemma m_snx_set_m_s: forall m s, m_snx (set_m_s m s) = m_snx m. Proof. reflexivity. Qed.
Lemma m_sow_set_m_s: forall m s, m_sow (set_m_s m s) = m_sow m. Proof. reflexivity. Qed.
Lemma m_tin_set_m_s: forall m s, m_tin (set_m_s m s) = m_tin m. Proof. reflexivity. Qed.
Lemma m_tout_set_m_s: forall m s, m_tout (set_m_s m s) = m_tout m. Proof. reflexivity. Qed.
Lemma m_adler_set_m_s: forall m s, m_adler (set_m_s m s) = m_adler m. Proof. reflexivity. Qed.
Lemma m_msg_set_m_s: forall m s, m_msg (set_m_s m s) = m_msg m. Proof. reflexivity. Qed.
Lemma m_s_upd_s: forall m f, m_s (upd_s m f) = f (m_s m). Proof. reflexivity. Qed.
Lemma m_s_upd_h: forall m f, m_s (upd_h m f) = m_s m. Proof. reflexivity. Qed.
Lemma m_h_upd_h: forall m f, m_h (upd_h m f) = f (m_h m). Proof. reflexivity. Qed.
Lemma m_s_set_m_s: forall m s, m_s (set_m_s m s) = s. Proof. reflexivity. Qed.
Ltac xp_simpl := rewrite ?m_h_upd_s, ?m_inp_upd_s, ?m_aout_upd_s, ?m_nx_upd_s, ?m_ow_upd_s, ?m_hold_upd_s, ?m_bits_upd_s, ?m_in_upd_s, ?m_out_upd_s, ?m_ret_upd_s, ?m_leave_upd_s, ?m_have_upd_s, ?m_left_upd_s, ?m_snx_upd_s, ?m_sow_upd_s, ?m_tin_upd_s, ?m_tout_upd_s, ?m_adler_upd_s, ?m_msg_upd_s, ?m_inp_upd_h, ?m_aout_upd_h, ?m_nx_upd_h, ?m_ow_upd_h, ?m_hold_upd_h, ?m_bits_upd_h, ?m_in_upd_h, ?m_out_upd_h, ?m_ret_upd_h, ?m_leave_upd_h, ?m_have_upd_h, ?m_left_upd_h, ?m_snx_upd_h, ?m_sow_upd_h, ?m_tin_upd_h, ?m_tout_upd_h, ?m_adler_upd_h, ?m_msg_upd_h, ?m_h_set_m_s, ?m_inp_set_m_s, ?m_aout_set_m_s, ?m_nx_set_m_s, ?m_ow_set_m_s, ?m_hold_set_m_s, ?m_bits_set_m_s, ?m_in_set_m_s, ?m_out_set_m_s, ?m_ret_set_m_s, ?m_leave_set_m_s, ?m_have_set_m_s, ?m_left_set_m_s, ?m_snx_set_m_s, ?m_sow_set_m_s, ?m_tin_set_m_s, ?m_tout_set_m_s, ?m_adler_set_m_s, ?m_msg_set_m_s, ?m_h_set_m_s, ?m_s_upd_s, ?m_s_upd_h, ?m_h_upd_h, ?m_s_set_m_s;
  cbn [i_mode i_wrap i_flags i_check i_head i_length set_i_length set_i_check set_i_mode
    h_text h_time h_xflags h_os h_xp h_extra_len h_extra_max h_xbuf h_np h_name_max h_nbuf h_cp h_comm_max h_cbuf h_hcrc h_done
    set_h_extra_len set_h_xp set_h_xbuf] in *.

(* ---------------------------------------------------------------------------------------------- *)
(* the extra-field buffer of the gz_header (EXTRA's zmemcpy)                                      *)

Lemma hbuf_rep_null: forall max c, hbuf_rep nullval max c = emp.
Proof. intros. unfold hbuf_rep. destruct (eq_dec nullval nullval); [reflexivity | congruence]. Qed.

Lemma hbuf_rep_pos: forall b max c, b <> nullval ->
  hbuf_rep b max c = data_at Ews (tarray tuchar max) (byte_vals c) b.
Proof. intros. unfold hbuf_rep. destruct (eq_dec b nullval); [congruence | reflexivity]. Qed.

(* ex_state with the temporary _copy *)
Definition ex_state_copy (F: frame) (m: mst) (v: val) : environ -> mpred :=
  PROP (in_ok (f_ib F) (m_inp m); out_ok (f_ob F) (m_aout m))
  LOCAL (temp _copy v; temp _strm (f_strmp F); temp _flush (zv (f_flush F)); temp _state (f_sp F);
         temp _next (in_ptr (f_ib F) (m_nx m)); temp _put (out_ptr (f_ob F) (Zlength (m_ow m)));
         temp _have (zv (m_have m)); temp _left (zv (m_left m)); temp _hold (lv (m_hold m));
         temp _bits (zv (m_bits m)); temp _in (zv (m_in m)); temp _out (zv (m_out m));
         temp _ret (zv (m_ret m)); temp _leave (zv (m_leave m));
         lvar _here t_code (f_vhere F); lvar _last t_code (f_vlast F);
         lvar _hbuf (tarray tuchar 4) (f_vhbuf F); gvars (f_gv F))
  SEP (field_at Ews t_state (DOT _mode) (zv (i_mode (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _wrap) (zv (i_wrap (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _flags) (zv (i_flags (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _check) (lv (i_check (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _head) (if i_head (m_s m) then f_headp F else nullval) (f_sp F);
       field_at Ews t_state (DOT _length) (zv (i_length (m_s m))) (f_sp F);
       head_part F m; in_rep (f_ib F); crc_table_at (f_tsh F) (f_gv F); mem_x F m; locals_rep F).
