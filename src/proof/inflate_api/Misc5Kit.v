(* Helpers of Body5_misc.v (v5 specs): struct inflate_state split into the fields the small API functions
   touch (strm, mode, wrap, head, hold, bits, length, next, codes, back, was) and the rest (one opaque SEP
   item), and the invariant of the states they make. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate_api.Bodies5.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Lemma perm35_misc: forall a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35: mpred,
  a1 * a2 * a3 * a4 * a5 * a6 * a7 * a8 * a9 * a10 * a11 * a12 * a13 * a14 * a15 * a16 * a17 * a18 * a19 * a20 * a21 * a22 * a23 * a24 * a25 * a26 * a27 * a28 * a29 * a30 * a31 * a32 * a33 * a34 * a35 =
  a1 * a2 * a4 * a10 * a16 * a17 * a18 * a29 * a32 * a34 * a35 *
  (a3 * a5 * a6 * a7 * a8 * a9 * a11 * a12 * a13 * a14 * a15 * a19 * a20 * a21 * a22 * a23 * a24 * a25 * a26 * a27 * a28 * a30 * a31 * a33).
Proof. intros. apply pred_ext; cancel. Qed.

Definition U_misc (gv: globals) (sp winp: val) (s: istate) : mpred :=
  field_at Ews t_state (DOT _last) (zv (i_last s)) sp *
  field_at Ews t_state (DOT _havedict) (zv (i_havedict s)) sp *
  field_at Ews t_state (DOT _flags) (zv (i_flags s)) sp *
  field_at Ews t_state (DOT _dmax) (zv (i_dmax s)) sp *
  field_at Ews t_state (DOT _check) (lv (i_check s)) sp *
  field_at Ews t_state (DOT _total) (lv (i_total s)) sp *
  field_at Ews t_state (DOT _wbits) (zv (i_wbits s)) sp *
  field_at Ews t_state (DOT _wsize) (zv (i_wsize s)) sp *
  field_at Ews t_state (DOT _whave) (zv (i_whave s)) sp *
  field_at Ews t_state (DOT _wnext) (zv (i_wnext s)) sp *
  field_at Ews t_state (DOT _window) (if i_win s then winp else nullval) sp *
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
  field_at Ews t_state (DOT _lens) (map (fun z => Vint (Int.repr z)) (i_lens s)) sp *
  field_at_ Ews t_state (DOT _work) sp *
  field_at Ews t_state (DOT _sane) (zv (i_sane s)) sp.

Lemma state_rep_misc: forall gv sp strmp headp winp s,
  state_rep gv sp strmp headp winp s =
  field_at Ews t_state (DOT _strm) strmp sp *
  field_at Ews t_state (DOT _mode) (zv (i_mode s)) sp *
  field_at Ews t_state (DOT _wrap) (zv (i_wrap s)) sp *
  field_at Ews t_state (DOT _head) (if i_head s then headp else nullval) sp *
  field_at Ews t_state (DOT _hold) (lv (i_hold s)) sp *
  field_at Ews t_state (DOT _bits) (zv (i_bits s)) sp *
  field_at Ews t_state (DOT _length) (zv (i_length s)) sp *
  field_at Ews t_state (DOT _next) (codes_at sp (i_next s)) sp *
  field_at Ews t_state (DOT _codes) (map ent (i_codes s)) sp *
  field_at Ews t_state (DOT _back) (zv (i_back s)) sp *
  field_at Ews t_state (DOT _was) (zv (i_was s)) sp *
  U_misc gv sp winp s.
Proof. intros. unfold state_rep, U_misc. apply perm35_misc. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the invariant of the new states                                                                 *)

Ltac ms_simpl := cbn [l_s l_sp l_h l_hsh l_winp l_headp l_xb l_nb l_cb set_l_s set_l_head
  i_mode i_last i_wrap i_havedict i_flags i_dmax i_check i_total i_head i_wbits i_wsize i_whave i_wnext i_win i_wdata i_hold i_bits i_length i_offset i_extra i_lencode i_distcode i_lenbits i_distbits i_ncode i_nlen i_ndist i_have i_next i_lens i_codes i_sane i_back i_was
  set_i_mode set_i_last set_i_wrap set_i_havedict set_i_flags set_i_dmax set_i_check set_i_total set_i_head set_i_wbits set_i_wsize set_i_whave set_i_wnext set_i_win set_i_wdata set_i_hold set_i_bits set_i_length set_i_offset set_i_extra set_i_lencode set_i_distcode set_i_lenbits set_i_distbits set_i_ncode set_i_nlen set_i_ndist set_i_have set_i_next set_i_lens set_i_codes set_i_sane set_i_back set_i_was
  h_text h_time h_xflags h_os h_xp h_extra_len h_extra_max h_xbuf h_np h_name_max h_nbuf h_cp h_comm_max h_cbuf h_hcrc h_done set_h_done] in *.

Lemma tv_codes: forall kind s s' t rb, i_codes s' = i_codes s ->
  tvalid kind lenfix_list distfix_list s t rb -> tvalid kind lenfix_list distfix_list s' t rb.
Proof.
  intros kind s s' t rb E (sz & A & B). exists sz. split; auto.
  unfold tvalid_b in *. eapply tvalid_g_ext; [ | exact B]. intros. destruct t; simpl; congruence.
Qed.

Lemma tvl_codes: forall s s' t rb, i_codes s' = i_codes s ->
  tvalid_len lenfix_list distfix_list s t rb -> tvalid_len lenfix_list distfix_list s' t rb.
Proof.
  intros s s' t rb E (sz & A & B & C). exists sz. split; auto. split.
  - unfold tvalid_b in *. eapply tvalid_g_ext; [ | exact B]. intros. destruct t; simpl; congruence.
  - intros i Hi. specialize (C i Hi). unfold tab_entry in *. destruct t; try rewrite E; exact C.
Qed.

(* a new hold and bits *)
Lemma live_hb: forall L h b, live_ok L -> lrange h -> 0 <= b <= 39 ->
  live_ok (set_l_s L (set_i_bits (set_i_hold (l_s L) h) b)).
Proof.
  intros [sp winp s hh headp hsh xb nb cb] h b (P & W & M & HW & W3 & HS & W0 & HP & WW) Hh Hb.
  ms_simpl.
  split; [exact P | ]. split; [ | split; [ | split; [exact HW | split; [ | split; [exact HS | ]]]]].
  - destruct W. constructor; ms_simpl; auto.
  - destruct M. constructor; ms_simpl; auto.
    all: try (intro D; destruct (md_tables0 D); split; eapply tv_codes; eauto).
  - destruct W3. constructor; ms_simpl; auto.
    all: try (intro D; eapply tvl_codes; [ | apply s3_len0; exact D]; reflexivity).
  - auto.
Qed.

(* a new wrap: nonzero only when it was, zlib or gzip (wrap & 3) when there is no window size *)
Lemma live_wrap: forall L w, live_ok L -> (0 <= w <= 7 \/ 9 <= w <= 11 \/ 13 <= w <= 15) -> (w <> 0 -> i_wrap (l_s L) <> 0) ->
  (i_wbits (l_s L) = 0 -> Z.land w 3 <> 0) ->
  live_ok (set_l_s L (set_i_wrap (l_s L) w)).
Proof.
  intros [sp winp s hh headp hsh xb nb cb] w (P & W & M & HW & W3 & HS & W0 & HP & WW) Hw Hn Hz.
  ms_simpl.
  split; [exact P | ]. split; [ | split; [ | split; [exact HW | split; [ | split; [exact HS | ]]]]].
  - destruct W. constructor; ms_simpl; auto.
  - destruct M. constructor; ms_simpl; auto.
    all: try (intro D; destruct (md_tables0 D); split; eapply tv_codes; eauto).
  - destruct W3. constructor; ms_simpl; auto.
    all: try (intro D; eapply tvl_codes; [ | apply s3_len0; exact D]; reflexivity).
  - split; [ | split; [exact HP | ]].
    + intros Z0. split; [exact (Hz Z0) | apply (W0 Z0)].
    + intros A B. apply WW; auto.
Qed.

(* the application's gz_header given to the stream *)
Lemma live_head: forall L h headp hsh xb nb cb, live_ok L -> hwf h -> writable_share hsh ->
  (h_xp h = true -> xb <> nullval) -> (h_np h = true -> nb <> nullval) -> (h_cp h = true -> cb <> nullval) ->
  live_ok (set_l_head (set_l_s L (set_i_head (l_s L) true)) (set_h_done h 0) headp hsh xb nb cb).
Proof.
  intros [sp winp s hh headp0 hsh0 xb0 nb0 cb0] h headp hsh xb nb cb (P & W & M & HW & W3 & HS & W0 & HP & WW) Hh Hs X N C.
  ms_simpl.
  split; [exact P | ]. split; [ | split; [ | split; [ | split; [ | split; [exact Hs | ]]]]].
  - destruct W. constructor; ms_simpl; auto.
  - destruct M. constructor; ms_simpl; auto.
    all: try (intro D; destruct (md_tables0 D); split; eapply tv_codes; eauto).
  - destruct Hh. constructor; ms_simpl; auto. unfold srange; rep_lia.
  - destruct W3. constructor; ms_simpl; auto.
    all: try (intro D; eapply tvl_codes; [ | apply s3_len0; exact D]; reflexivity).
  - split; [exact W0 | split; [ | exact WW]]. intros _. auto.
Qed.
