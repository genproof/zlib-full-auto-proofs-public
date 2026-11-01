(* The facts behind the body of inflateSync (Body5_sync.v): the body of syncsearch, the states of inflateSync and
   their invariant live_ok, and the rearrangements of state_rep it uses. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate_api.Bodies5.
#[local] Existing Instance Zlib.units.Inflate.CS.

Local Open Scope logic.

(* ---------------------------------------------------------------------------------------------- *)
(* syncsearch                                                                                     *)

Definition ss_next (got b: Z) : Z :=
  if b =? (if got <? 2 then 0 else 255) then got + 1 else if negb (b =? 0) then 0 else 4 - got.

Lemma ssearch_cons: forall got b r, got < 4 ->
  ssearch got (b :: r) = (fst (ssearch (ss_next got b) r), snd (ssearch (ss_next got b) r) + 1).
Proof.
  intros. simpl. rewrite (proj2 (Z.ltb_lt _ _) H). unfold ss_next.
  destruct (ssearch _ r). reflexivity.
Qed.

Lemma ssearch_stop: forall got r, 4 <= got -> ssearch got r = (got, 0).
Proof.
  intros. destruct r; simpl; [reflexivity | ]. rewrite (proj2 (Z.ltb_ge _ _) H). reflexivity.
Qed.

Lemma ss_next_range: forall got b, 0 <= got < 4 -> 0 <= ss_next got b <= 4.
Proof.
  intros. unfold ss_next.
  destruct (b =? _); [lia | ]. destruct (negb _); lia.
Qed.

Lemma ssearch_range: forall got r, 0 <= got <= Int.max_unsigned ->
  0 <= fst (ssearch got r) <= Int.max_unsigned /\ 0 <= snd (ssearch got r) <= Zlength r.
Proof.
  intros got r. revert got. induction r as [ | b r IH]; intros got Hg.
  - simpl. rep_lia.
  - destruct (Z_lt_le_dec got 4) as [L | L].
    + rewrite ssearch_cons by lia. pose proof (ss_next_range got b).
      destruct (IH (ss_next got b)) as [A B]; [rep_lia | ]. cbn [fst snd]. rewrite Zlength_cons. lia.
    + rewrite ssearch_stop by lia. cbn [fst snd]. rewrite Zlength_cons. pose proof (Zlength_nonneg r). lia.
Qed.

Lemma Znth_d: forall {A} (d1 d2: Inhabitant A) i (l: list A), 0 <= i < Zlength l -> @Znth A d1 i l = @Znth A d2 i l.
Proof.
  intros. unfold Znth. destruct (Z_lt_dec i 0); [lia | ]. apply nth_indep.
  rewrite <- ZtoNat_Zlength. lia.
Qed.

Lemma body_syncsearch {E: OracleKind}: semax_body Vprog_inflate [] f_syncsearch syncsearch_spec.
Proof.
  start_function.
  match goal with Hs: sublist _ _ _ = byte_vals _ |- _ => rename Hs into HSUB end.
  match goal with Hs: bytes_ok _ |- _ => rename Hs into HBOK end.
  forward. forward.
  set (len := Zlength data).
  assert (HL: len <= Int.max_unsigned) by (unfold len; lia).
  forward_loop (EX k: Z, EX g: Z,
    PROP (0 <= k <= len; 0 <= g <= Int.max_unsigned;
          ssearch got data = pair (fst (ssearch g (sublist k len data))) ((k + snd (ssearch g (sublist k len data)))%Z))
    LOCAL (temp _got (Vint (Int.repr g)); temp _next (Vint (Int.repr k)); temp _have hp;
           temp _buf (offset_val lo p); temp _len (Vint (Int.repr len)))
    SEP (data_at hsh tuint (Vint (Int.repr got)) hp; data_at bsh (tarray tuchar n) c p))
  break: (EX k: Z, EX g: Z,
    PROP (0 <= k <= len; 0 <= g <= Int.max_unsigned; ssearch got data = pair g k)
    LOCAL (temp _got (Vint (Int.repr g)); temp _next (Vint (Int.repr k)); temp _have hp)
    SEP (data_at hsh tuint (Vint (Int.repr got)) hp; data_at bsh (tarray tuchar n) c p)).
  - Exists 0 got. entailer!. rewrite sublist_same by reflexivity. destruct (ssearch got data); reflexivity.
  - Intros k g.
    match goal with Hs: ssearch got data = _ |- _ => rename Hs into HSS end.
    destruct (Z_lt_le_dec k len) as [Hk | Hk]; [destruct (Z_lt_le_dec g 4) as [Hg | Hg] | ].
    3: { forward_if (temp _t'1 (Vint Int.zero)).
         { try (rewrite !Int.unsigned_repr in * by rep_lia); lia. }
         { forward. entailer!. }
         forward_if; [contradiction | ]. forward. Exists k g. entailer!.
         replace k with len in * by lia. rewrite sublist_nil in HSS. simpl in HSS. rewrite HSS. f_equal; lia. }
    2: { forward_if (temp _t'1 (Vint Int.zero)).
         { forward. entailer!. destruct (zlt g 4); [lia | reflexivity]. }
         { try (rewrite !Int.unsigned_repr in * by rep_lia); lia. }
         forward_if; [contradiction | ]. forward. Exists k g. entailer!.
         rewrite (ssearch_stop g) in HSS by lia. rewrite HSS. simpl. f_equal; lia. }
    forward_if (temp _t'1 (Vint Int.one)).
    { forward. entailer!. }
    { try (rewrite !Int.unsigned_repr in * by rep_lia); lia. }
    forward_if; [ | exfalso; apply Int.one_not_zero; assumption].
    assert (HB: forall d, @Znth val d (lo + k) c = Vint (Int.repr (Znth k data))).
    { intros d. rewrite (Znth_d d Inhabitant_val) by lia. replace (lo + k) with (k + lo) by lia. rewrite <- (Znth_sublist lo k (lo + len) c) by lia.
      unfold len. rewrite HSUB. unfold byte_vals. rewrite Znth_map by lia. reflexivity. }
    assert (Hb: 0 <= Znth k data <= 255).
    { unfold bytes_ok in HBOK. eapply Forall_forall in HBOK; [exact HBOK | ]. apply Znth_In. lia. }
    forward_if (temp _t'2 (Vint (Int.repr (if g <? 2 then 0 else 255)))).
    { forward. entailer!. rewrite (proj2 (Z.ltb_lt g 2)) by lia. reflexivity. }
    { forward. entailer!. rewrite (proj2 (Z.ltb_ge g 2)) by lia. reflexivity. }
    assert_PROP (force_val (sem_add_ptr_int tuchar Unsigned (offset_val lo p) (Vint (Int.repr k))) =
                 field_address (tarray tuchar n) (SUB (lo + k)) p).
    { entailer!. rewrite field_address_offset by auto with field_compatible. simpl.
      destruct p; try contradiction. simpl. f_equal. f_equal. f_equal. lia. }
    forward. { rewrite HB. entailer!; rep_lia. }
    rewrite HB.
    forward_if (PROP () LOCAL (temp _got (Vint (Int.repr (ss_next g (Znth k data)))); temp _next (Vint (Int.repr k));
      temp _have hp; temp _buf (offset_val lo p); temp _len (Vint (Int.repr len)))
      SEP (data_at hsh tuint (Vint (Int.repr got)) hp; data_at bsh (tarray tuchar n) c p)).
    { forward. entailer!.
      match goal with H: Int.repr (Znth k data) = Int.repr _ |- _ =>
        apply repr_inj_unsigned in H; [ | rep_lia | destruct (g <? 2); rep_lia];
        unfold ss_next; rewrite (proj2 (Z.eqb_eq _ _) H); reflexivity end. }
    { assert (HN: Znth k data <> (if g <? 2 then 0 else 255)).
      { intro X. rewrite X in *. contradiction. }
      forward. { rewrite HB. entailer!; rep_lia. } rewrite HB.
      forward_if.
      - forward. entailer!. unfold ss_next. rewrite (proj2 (Z.eqb_neq _ _) HN).
        destruct (Z.eqb_spec (Znth k data) 0) as [Z0 | Z0]; [ | reflexivity].
        rewrite Z0 in *. match goal with X: typed_true _ _ |- _ => compute in X; discriminate end.
      - forward. entailer!. unfold ss_next. rewrite (proj2 (Z.eqb_neq _ _) HN).
        destruct (Z.eqb_spec (Znth k data) 0) as [Z0 | Z0]; [reflexivity | ].
        exfalso. apply Z0. match goal with X: typed_false _ _ |- _ =>
          unfold typed_false, strict_bool_val in X; simpl in X; inversion X as [X'] end.
        apply negb_false_iff in X'. apply Int.same_if_eq in X'. apply repr_inj_unsigned; [rep_lia | rep_lia | exact X']. }
    forward. Exists (k + 1) (ss_next g (Znth k data)). entailer!.
    split; [pose proof (ss_next_range g (Znth k data)); rep_lia | ].
    rewrite HSS. rewrite (sublist_next k len data) by lia. rewrite ssearch_cons by lia. cbn [fst snd]. f_equal. lia.
  - Intros k g. forward. forward.
    match goal with Hs: ssearch got data = (g, k) |- _ => rewrite Hs end. cbn [fst snd]. entailer!.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* struct inflate_state split into the fields inflateSync touches and the rest                     *)

Lemma perm35_sync: forall a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35: mpred,
  a1 * a2 * a3 * a4 * a5 * a6 * a7 * a8 * a9 * a10 * a11 * a12 * a13 * a14 * a15 * a16 * a17 * a18 * a19 * a20 * a21 * a22 * a23 * a24 * a25 * a26 * a27 * a28 * a29 * a30 * a31 * a32 * a33 * a34 * a35 =
  a1 * a2 * a4 * a6 * a11 * a16 * a17 * a28 *
  (a3 * a5 * a7 * a8 * a9 * a10 * a12 * a13 * a14 * a15 * a18 * a19 * a20 * a21 * a22 * a23 * a24 * a25 * a26 * a27 * a29 * a30 * a31 * a32 * a33 * a34 * a35).
Proof. intros. apply pred_ext; cancel. Qed.

Definition U_sync (gv: globals) (sp headp winp: val) (s: istate) : mpred :=
  field_at Ews t_state (DOT _last) (zv (i_last s)) sp *
  field_at Ews t_state (DOT _havedict) (zv (i_havedict s)) sp *
  field_at Ews t_state (DOT _dmax) (zv (i_dmax s)) sp *
  field_at Ews t_state (DOT _check) (lv (i_check s)) sp *
  field_at Ews t_state (DOT _total) (lv (i_total s)) sp *
  field_at Ews t_state (DOT _head) (if i_head s then headp else nullval) sp *
  field_at Ews t_state (DOT _wsize) (zv (i_wsize s)) sp *
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
  field_at Ews t_state (DOT _next) (codes_at sp (i_next s)) sp *
  field_at Ews t_state (DOT _lens) (map (fun z => Vint (Int.repr z)) (i_lens s)) sp *
  field_at_ Ews t_state (DOT _work) sp *
  field_at Ews t_state (DOT _codes) (map ent (i_codes s)) sp *
  field_at Ews t_state (DOT _sane) (zv (i_sane s)) sp *
  field_at Ews t_state (DOT _back) (zv (i_back s)) sp *
  field_at Ews t_state (DOT _was) (zv (i_was s)) sp.

Lemma state_rep_sync: forall gv sp strmp headp winp s,
  state_rep gv sp strmp headp winp s =
  field_at Ews t_state (DOT _strm) strmp sp *
  field_at Ews t_state (DOT _mode) (zv (i_mode s)) sp *
  field_at Ews t_state (DOT _wrap) (zv (i_wrap s)) sp *
  field_at Ews t_state (DOT _flags) (zv (i_flags s)) sp *
  field_at Ews t_state (DOT _wbits) (zv (i_wbits s)) sp *
  field_at Ews t_state (DOT _hold) (lv (i_hold s)) sp *
  field_at Ews t_state (DOT _bits) (zv (i_bits s)) sp *
  field_at Ews t_state (DOT _have) (zv (i_have s)) sp *
  U_sync gv sp headp winp s.
Proof. intros. unfold state_rep, U_sync. apply perm35_sync. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the invariant of the states inflateSync makes                                                   *)

Ltac ss_simpl := cbn [l_s l_sp l_h l_hsh l_winp l_headp l_xb l_nb l_cb set_l_s
  i_mode i_last i_wrap i_havedict i_flags i_dmax i_check i_total i_head i_wbits i_wsize i_whave i_wnext i_win i_wdata i_hold i_bits i_length i_offset i_extra i_lencode i_distcode i_lenbits i_distbits i_ncode i_nlen i_ndist i_have i_next i_lens i_codes i_sane i_back i_was
  set_i_mode set_i_last set_i_wrap set_i_havedict set_i_flags set_i_dmax set_i_check set_i_total set_i_head set_i_wbits set_i_wsize set_i_whave set_i_wnext set_i_win set_i_wdata set_i_hold set_i_bits set_i_length set_i_offset set_i_extra set_i_lencode set_i_distcode set_i_lenbits set_i_distbits set_i_ncode set_i_nlen set_i_ndist set_i_have set_i_next set_i_lens set_i_codes set_i_sane set_i_back set_i_was] in *.

Lemma set_l_s_twice: forall L s1 s2, set_l_s (set_l_s L s1) s2 = set_l_s L s2.
Proof. intros [] s1 s2. reflexivity. Qed.

Lemma l_s_set: forall L s, l_s (set_l_s L s) = s.
Proof. intros [] s. reflexivity. Qed.

Lemma tv_codes': forall kind s s' t rb, i_codes s' = i_codes s ->
  tvalid kind lenfix_list distfix_list s t rb -> tvalid kind lenfix_list distfix_list s' t rb.
Proof.
  intros kind s s' t rb E (sz & A & B). exists sz. split; auto.
  unfold tvalid_b in *. eapply tvalid_g_ext; [ | exact B]. intros. destruct t; simpl; congruence.
Qed.

Lemma tvl_codes': forall s s' t rb, i_codes s' = i_codes s ->
  tvalid_len lenfix_list distfix_list s t rb -> tvalid_len lenfix_list distfix_list s' t rb.
Proof.
  intros s s' t rb E (sz & A & B & C). exists sz. split; auto. split.
  - unfold tvalid_b in *. eapply tvalid_g_ext; [ | exact B]. intros. destruct t; simpl; congruence.
  - intros i Hi. specialize (C i Hi). unfold tab_entry in *. destruct t; try rewrite E; exact C.
Qed.

Definition quiet_mode (md: Z) : Prop := md = SYNC \/ md = Zlib.proof.inflate.Model.TYPE.

Lemma quiet_not_decode: forall md, quiet_mode md -> ~ decode_mode md.
Proof.
  unfold quiet_mode, decode_mode, SYNC, Zlib.proof.inflate.Model.TYPE, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT. lia.
Qed.

(* the state s' of a quiet mode that differs from that of L in the mode, wrap, flags, hold, bits and have *)
Lemma live_quiet: forall L md w fl h b hv,
  live_ok L -> quiet_mode md -> (0 <= w <= 7 \/ 9 <= w <= 11 \/ 13 <= w <= 15) -> srange fl -> lrange h -> 0 <= b <= 39 -> 0 <= hv <= 320 ->
  (i_wbits (l_s L) = 0 -> Z.land w 3 <> 0 /\ fl = -1 /\ md = SYNC) ->
  live_ok (set_l_s L (set_i_have (set_i_bits (set_i_hold (set_i_flags (set_i_wrap (set_i_mode (l_s L) md) w) fl) h) b) hv)).
Proof.
  intros [sp winp s hh headp hsh xb nb cb] md w fl h b hv (P & W & M & HW & W3 & HS & WB0 & HD & WF) Q Hw Hf Hh Hb Hv HZ.
  ss_simpl. pose proof (quiet_not_decode _ Q) as ND.
  assert (QM: HEAD <= md <= SYNC) by (unfold quiet_mode, HEAD, SYNC, Zlib.proof.inflate.Model.TYPE in *; lia).
  split; [exact P | ]. split; [ | split; [ | split; [exact HW | split; [ | split; [exact HS | ]]]]].
  - destruct W. constructor; ss_simpl; auto.
  - constructor; ss_simpl.
    all: try (intros HM; exfalso; first [apply ND; exact HM | unfold quiet_mode, SYNC, Zlib.proof.inflate.Model.TYPE, LENLENS, CODELENS, LENEXT, DISTEXT, MATCH, DIST in *; lia]).
    all: repeat split; intros HM; exfalso; unfold quiet_mode, SYNC, Zlib.proof.inflate.Model.TYPE, LENEXT, DISTEXT, DIST in *; lia.
  - constructor; ss_simpl.
    all: intros HM; exfalso; first [apply ND; exact HM | unfold quiet_mode, SYNC, Zlib.proof.inflate.Model.TYPE, HEAD, LENEXT, DISTEXT in *; lia].
  - split; [ | split; [exact HD | ]].
    + intros E. destruct (WB0 E) as [_ WN]. destruct (HZ E) as (WZ & _ & _). split; [exact WZ | exact WN].
    + intros E _. destruct (HZ E) as (_ & F1 & M1). split; [exact F1 | ]. right; right; left; exact M1.
Qed.

Ltac rs_simpl' := unfold reset_s, reset_keep_s; ss_simpl.

Lemma head_not_decode': ~ decode_mode HEAD.
Proof. unfold decode_mode, HEAD, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT. lia. Qed.

(* the end of inflateSync after the pattern was found (patch F6), before inflateReset *)
Definition sync_fix (s: istate) : istate :=
  if i_flags s =? -1 then
    (let s := set_i_wrap s 0 in if i_wbits s =? 0 then set_i_wbits s 15 else s)
  else set_i_wrap s (Z.land (i_wrap s) (Z.lnot 4)).

(* after inflateReset *)
Definition sync_fin (s: istate) : istate :=
  set_i_mode (set_i_flags (reset_s (sync_fix s)) (i_flags (sync_fix s))) Zlib.proof.inflate.Model.TYPE.

Lemma sync_fix_wbits: forall L, live_ok L -> i_wbits (sync_fix (l_s L)) <> 0.
Proof.
  intros [sp winp s hh headp hsh xb nb cb] (P & W & M & HW & W3 & HS & WB0 & HD & WF). cbn [l_s] in *.
  destruct s; unfold sync_fix; ss_simpl.
  destruct (Z.eqb_spec i_flags (-1)) as [F | F]; [destruct (Z.eqb_spec i_wbits 0) as [E | E] | ]; ss_simpl; try lia.
  all: intro E; destruct (WB0 E) as [WZ _]; destruct (WF E (land3_wrap _ WZ)) as [F1 _]; contradiction.
Qed.

Lemma live_fixreset: forall L, live_ok L -> live_ok (set_l_s L (reset_s (sync_fix (l_s L)))).
Proof.
  intros L LOK. pose proof (sync_fix_wbits L LOK) as WN.
  destruct L as [sp winp s hh headp hsh xb nb cb]. destruct LOK as (P & W & M & HW & W3 & HS & WB0 & HD & WF).
  cbn [l_s l_sp l_h l_hsh set_l_s] in *.
  assert (FW: swf (sync_fix s) /\ i_win (sync_fix s) = i_win s /\ i_wsize (sync_fix s) = i_wsize s).
  { clear -W WB0. destruct s; unfold sync_fix; ss_simpl. destruct W; ss_simpl.
    destruct (Z.eqb_spec i_flags (-1)) as [F | F]; [destruct (Z.eqb_spec i_wbits 0) as [E | E] | ]; ss_simpl.
    - destruct (WB0 E) as [_ WF0]. split; [ | auto].
      constructor; ss_simpl; auto; try lia.
      destruct sw_wsize as [? | [X _]]; [left; auto | congruence].
    - split; [ | auto]. constructor; ss_simpl; auto; try lia.
    - split; [ | auto]. constructor; ss_simpl; auto; try (apply wrap_clear4; assumption). }
  destruct FW as (FW & FWW & _).
  set (s2 := sync_fix s) in *. clearbody s2.
  split; [exact P | ]. split; [ | split; [ | split; [exact HW | split; [ | split; [exact HS | ]]]]].
  - destruct FW. constructor; rs_simpl'; auto;
      try (unfold HEAD, SYNC, srange, urange, lrange, tref_ok, ENOUGH_CODES in *; rep_lia).
    split; [reflexivity | constructor].
  - constructor; rs_simpl'; repeat split; intros; exfalso;
      try (apply head_not_decode'; assumption);
      unfold HEAD, LENLENS, CODELENS, LENEXT, DISTEXT, MATCH, DIST in *; lia.
  - constructor; rs_simpl'; auto; intros HM;
      try (exfalso; apply head_not_decode'; exact HM);
      try (unfold HEAD, LENEXT, DISTEXT in *; lia).
  - rs_simpl'. split; [intro; contradiction | ]. split; [intro; discriminate | ].
    intros; contradiction.
Qed.

Lemma sync_fix_flags: forall s, i_flags (sync_fix s) = i_flags s.
Proof.
  intros s. destruct s. unfold sync_fix. ss_simpl.
  destruct (_ =? _); [destruct (_ =? _) | ]; reflexivity.
Qed.

Lemma live_fin: forall L, live_ok L -> live_ok (set_l_s L (sync_fin (l_s L))).
Proof.
  intros L LOK. pose proof (sync_fix_wbits L LOK) as WN. pose proof (live_fixreset L LOK) as R.
  set (L2 := set_l_s L (reset_s (sync_fix (l_s L)))) in *.
  assert (E: sync_fin (l_s L) = set_i_have (set_i_bits (set_i_hold (set_i_flags (set_i_wrap (set_i_mode (l_s L2)
     Zlib.proof.inflate.Model.TYPE) (i_wrap (l_s L2))) (i_flags (sync_fix (l_s L)))) (i_hold (l_s L2))) (i_bits (l_s L2))) (i_have (l_s L2))).
  { unfold L2, sync_fin. destruct (reset_s (sync_fix (l_s L))). destruct L. reflexivity. }
  replace (set_l_s L (sync_fin (l_s L))) with (set_l_s L2 (sync_fin (l_s L))) by (destruct L; reflexivity).
  rewrite E. pose proof R as (P & W & _). destruct W.
  apply live_quiet; auto.
  - right; reflexivity.
  - rewrite sync_fix_flags. destruct LOK as (_ & W0 & _). exact (Zlib.proof.inflate.Inv.sw_flags _ W0).
  - intro X. exfalso. apply WN. unfold L2 in X. rs_simpl'. destruct (sync_fix (l_s L)); ss_simpl; exact X.
Qed.

(* the states of inflateSync in the form of live_quiet *)
Definition qs (s: istate) (md w fl h b hv: Z) : istate :=
  set_i_have (set_i_bits (set_i_hold (set_i_flags (set_i_wrap (set_i_mode s md) w) fl) h) b) hv.

Lemma qs_have: forall s md w fl h b hv g, set_i_have (qs s md w fl h b hv) g = qs s md w fl h b g.
Proof. intros. destruct s. reflexivity. Qed.

Lemma qs_wrap: forall s md w fl h b hv w', set_i_wrap (qs s md w fl h b hv) w' = qs s md w' fl h b hv.
Proof. intros. destruct s. reflexivity. Qed.

Lemma qs_fields: forall s md w fl h b hv,
  i_mode (qs s md w fl h b hv) = md /\ i_wrap (qs s md w fl h b hv) = w /\ i_flags (qs s md w fl h b hv) = fl /\
  i_hold (qs s md w fl h b hv) = h /\ i_bits (qs s md w fl h b hv) = b /\ i_have (qs s md w fl h b hv) = hv.
Proof. intros. destruct s. repeat split. Qed.

Lemma qs_id: forall s md, i_mode s = md -> s = qs s md (i_wrap s) (i_flags s) (i_hold s) (i_bits s) (i_have s).
Proof. intros. destruct s. simpl in *. subst. reflexivity. Qed.

Lemma qs_mode_flags: forall r fl md,
  set_i_mode (set_i_flags r fl) md = qs r md (i_wrap r) fl (i_hold r) (i_bits r) (i_have r).
Proof. intros. destruct r. reflexivity. Qed.

Lemma ssearch_fst_bound: forall g r, 0 <= g -> 0 <= fst (ssearch g r) <= Z.max g 4.
Proof.
  intros g r. revert g. induction r as [ | b r IH]; intros g Hg; [simpl; lia | ].
  destruct (Z_lt_le_dec g 4) as [L | L].
  - rewrite ssearch_cons by lia. cbn [fst]. pose proof (ss_next_range g b ltac:(lia)).
    specialize (IH (ss_next g b) ltac:(lia)). lia.
  - rewrite ssearch_stop by lia. cbn [fst]. lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the bit buffer to bytes (inflateSync's first loop)                                              *)

Lemma hold_bytes_snoc: forall k h,
  hold_bytes (S k) h = hold_bytes k h ++ [Z.shiftr h (8 * Z.of_nat k) mod 256].
Proof.
  induction k as [ | k IH]; intros h.
  - simpl. rewrite Z.shiftr_0_r. reflexivity.
  - change (hold_bytes (S (S k)) h) with (h mod 256 :: hold_bytes (S k) (Z.shiftr h 8)).
    rewrite IH. change (hold_bytes (S k) h) with (h mod 256 :: hold_bytes k (Z.shiftr h 8)).
    rewrite <- app_comm_cons. f_equal. f_equal. f_equal. f_equal.
    rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed.

Lemma hold_bytes_len: forall k h, Zlength (hold_bytes k h) = Z.of_nat k.
Proof.
  induction k as [ | k IH]; intros h; [reflexivity | ].
  simpl hold_bytes. rewrite Zlength_cons, IH. lia.
Qed.

Lemma hold_bytes_ok: forall k h, bytes_ok (hold_bytes k h).
Proof.
  unfold bytes_ok. induction k as [ | k IH]; intros h; simpl; constructor; auto.
  pose proof (Z.mod_pos_bound h 256). rep_lia.
Qed.

Lemma zext8_byte: forall x, 0 <= x <= Int64.max_unsigned ->
  Int.zero_ext 8 (Int.zero_ext 8 (Int.repr (Int64.Z_mod_modulus x))) = Int.repr (x mod 256).
Proof.
  intros x Hx. rewrite Int64.Z_mod_modulus_eq, Z.mod_small by rep_lia.
  rewrite Int.zero_ext_idem by lia.
  assert (U: Int.unsigned (Int.zero_ext 8 (Int.repr x)) = x mod 256).
  { rewrite Int.zero_ext_mod by (cbn; lia). rewrite Int.unsigned_repr_eq.
    change (two_p 8) with 256. rewrite <- Znumtheory.Zmod_div_mod; [reflexivity | lia | reflexivity | ].
    exists (Int.modulus / 256). reflexivity. }
  rewrite <- (Int.repr_unsigned (Int.zero_ext 8 (Int.repr x))), U. reflexivity.
Qed.

Lemma shru_repr: forall x n, 0 <= x <= Int64.max_unsigned -> 0 <= n < 64 ->
  Int64.shru (Int64.repr x) (Int64.repr n) = Int64.repr (Z.shiftr x n).
Proof. intros. unfold Int64.shru. rewrite !Int64.unsigned_repr by rep_lia. reflexivity. Qed.

Lemma shiftr_range: forall x n, 0 <= x <= Int64.max_unsigned -> 0 <= n -> 0 <= Z.shiftr x n <= Int64.max_unsigned.
Proof.
  intros x n Hx Hn. split; [apply Z.shiftr_nonneg; lia | ].
  rewrite Z.shiftr_div_pow2 by lia. apply Z.le_trans with x; [ | lia].
  apply Z.div_le_upper_bound; [apply Z.pow_pos_nonneg; lia | ].
  pose proof (Z.pow_pos_nonneg 2 n ltac:(lia) Hn). nia.
Qed.

Lemma buf_upd: forall j h, 0 <= j < 4 ->
  upd_Znth j (byte_vals (hold_bytes (Z.to_nat j) h) ++ Zrepeat Vundef (4 - j))
    (Vint (Int.repr (Z.shiftr h (8 * j) mod 256))) =
  byte_vals (hold_bytes (Z.to_nat (j + 1)) h) ++ Zrepeat Vundef (4 - (j + 1)).
Proof.
  intros j h J.
  assert (LJ: Zlength (byte_vals (hold_bytes (Z.to_nat j) h)) = j)
    by (rewrite Zlength_byte_vals, hold_bytes_len; lia).
  rewrite upd_Znth_app2 by (rewrite LJ, Zlength_Zrepeat; lia).
  rewrite LJ, Z.sub_diag.
  replace (Zrepeat Vundef (4 - j)) with (Vundef :: Zrepeat Vundef (4 - (j + 1))).
  2: { unfold Zrepeat. replace (Z.to_nat (4 - j)) with (S (Z.to_nat (4 - (j + 1)))) by lia. reflexivity. }
  rewrite upd_Znth0.
  replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)) by lia.
  rewrite hold_bytes_snoc. unfold byte_vals. rewrite map_app, <- app_assoc.
  rewrite Z2Nat.id by lia. reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the states of inflateSync                                                                       *)

Lemma live_sync_have: forall L g, live_ok L -> i_mode (l_s L) = SYNC -> 0 <= g <= 320 ->
  live_ok (set_l_s L (set_i_have (l_s L) g)).
Proof.
  intros L g LOK M G.
  assert (E: set_i_have (l_s L) g = set_i_have (set_i_bits (set_i_hold (set_i_flags (set_i_wrap (set_i_mode (l_s L)
      SYNC) (i_wrap (l_s L))) (i_flags (l_s L))) (i_hold (l_s L))) (i_bits (l_s L))) g).
  { destruct L as [sp winp s hh headp hsh xb nb cb]. destruct s. cbn in M |- *. subst. reflexivity. }
  rewrite E. pose proof LOK as (P & W & _ & _ & _ & _ & WB0 & _ & WF). destruct W.
  apply live_quiet; auto.
  - left; reflexivity.
  - intros Z0. destruct (WB0 Z0) as [WZ _]. destruct (WF Z0 (land3_wrap _ WZ)) as [F _]. auto.
Qed.

Lemma live_sync_start: forall L, live_ok L -> live_ok (set_l_s L (sync_start (l_s L))).
Proof.
  intros L LOK. pose proof LOK as (P & W & _ & _ & _ & _ & WB0 & _ & WF).
  set (s := l_s L) in *.
  set (hold := Z.shiftr (i_hold s) (Z.land (i_bits s) 7)).
  set (bits := i_bits s - Z.land (i_bits s) 7).
  assert (E: sync_start s = set_i_have (set_i_bits (set_i_hold (set_i_flags (set_i_wrap (set_i_mode s
      SYNC) (i_wrap s)) (i_flags s)) (Z.shiftr hold (8 * (bits / 8)))) (bits mod 8))
      (fst (ssearch 0 (hold_bytes (Z.to_nat (bits / 8)) hold)))).
  { unfold sync_start, hold, bits. clearbody s. destruct s. reflexivity. }
  rewrite E. destruct W.
  assert (HR: 0 <= hold <= Int64.max_unsigned).
  { unfold hold. apply shiftr_range; [exact sw_hold | ]. apply Z.land_nonneg. lia. }
  apply live_quiet; auto.
  - left; reflexivity.
  - apply shiftr_range; [exact HR | ].
    assert (E7: Z.land (i_bits s) 7 = i_bits s mod 8)
      by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity).
    unfold bits. rewrite E7. pose proof (Z.mod_pos_bound (i_bits s) 8 ltac:(lia)).
    pose proof (Z.mod_le (i_bits s) 8 ltac:(lia) ltac:(lia)).
    apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia].
  - pose proof (Z.mod_pos_bound bits 8). lia.
  - pose proof (ssearch_fst_bound 0 (hold_bytes (Z.to_nat (bits / 8)) hold) ltac:(lia)). lia.
  - intros Z0. destruct (WB0 Z0) as [WZ _]. destruct (WF Z0 (land3_wrap _ WZ)) as [F _]. auto.
Qed.

Lemma reset_s_wrap (x: istate) (w: Z) : reset_s (set_i_wrap x w) = set_i_wrap (reset_s x) w.
Proof. destruct x. reflexivity. Qed.

(* a state with another wrap: the invariants of live_ok that do not mention wrap are kept *)
Lemma swf_set_wrap (r: istate) (w: Z) : swf r -> (0 <= w <= 7 \/ 9 <= w <= 11 \/ 13 <= w <= 15) ->
  swf (set_i_wrap r w).
Proof. intros W Hw. destruct r; destruct W; constructor; cbn in *; assumption. Qed.

Lemma modewf_set_wrap (r: istate) (w: Z) : modewf r -> modewf (set_i_wrap r w).
Proof. intros M. destruct r; destruct M; constructor; cbn in *; assumption. Qed.

Lemma swf3_set_wrap (r: istate) (w: Z) : swf3 r -> (w <> 0 -> i_wrap r <> 0) -> swf3 (set_i_wrap r w).
Proof.
  intros S N. destruct r; destruct S; constructor; cbn in *; try assumption;
    try (intros HM HB HR; apply s3_head; auto); try (intros D; exact (s3_len D)).
Qed.

(* a live state with another wrap is live when the new wrap is in range, has the same two low bits and is nonzero
   only if the old one is: only the tests wrap = 0 and wrap & 3 of live_ok see wrap. Stated over an abstract state r
   so that its kernel check does not unfold the state's record. *)
Lemma live_ok_set_wrap (L: live) (r: istate) (w: Z) : live_ok (set_l_s L r) ->
  (0 <= w <= 7 \/ 9 <= w <= 11 \/ 13 <= w <= 15) -> Z.land w 3 = Z.land (i_wrap r) 3 -> (w <> 0 -> i_wrap r <> 0) ->
  live_ok (set_l_s L (set_i_wrap r w)).
Proof.
  intros H Hw C4 C5.
  destruct L as [sp winp s0 hh headp hsh xb nb cb]. unfold live_ok in *.
  cbn [l_s l_sp l_h l_hsh l_xb l_nb l_cb set_l_s] in *.
  destruct H as (P & W & M & HW & W3 & HS & WB0 & HD & WF).
  split; [exact P | ].
  split; [apply swf_set_wrap; [exact W | exact Hw] | ].
  split; [apply modewf_set_wrap; exact M | ].
  split; [exact HW | ].
  split; [apply swf3_set_wrap; [exact W3 | exact C5] | ].
  split; [exact HS | ].
  cbn [i_wrap i_wbits i_win i_head i_flags i_mode set_i_wrap].
  split; [intros Z0; destruct (WB0 Z0) as [A B]; split; [rewrite C4; exact A | exact B] | ].
  split; [exact HD | ]. intros Z0 N. apply WF; [exact Z0 | exact (C5 N)].
Qed.

(* the state inflateSync gives to inflateReset (bit 3 of wrap hidden) is live after the reset when the state with
   bit 3 is *)
Lemma live_wrap8 (L: live) (x: istate) : live_ok (set_l_s L (reset_s x)) ->
  live_ok (set_l_s L (reset_s (set_i_wrap x (Z.land (i_wrap x) (Z.lnot 8))))).
Proof.
  intros H. rewrite reset_s_wrap.
  assert (Wr: i_wrap (reset_s x) = i_wrap x) by (destruct x; reflexivity).
  pose proof H as (_ & W & _). pose proof (sw_wrap _ W) as WW. rewrite l_s_set, Wr in WW.
  destruct (wrap_clear8 _ WW) as (C1 & _).
  apply live_ok_set_wrap; [exact H | left; exact C1 | | ].
  - rewrite Wr, <- Z.land_assoc. reflexivity.
  - rewrite Wr. intros N E. apply N. rewrite E. reflexivity.
Qed.

Section Reps.
Variables (gv: globals) (sp headp winp: val).

Lemma U_sync_have: forall x g, U_sync gv sp headp winp (set_i_have x g) = U_sync gv sp headp winp x.
Proof. intros. destruct x. reflexivity. Qed.
Lemma U_sync_start: forall x, U_sync gv sp headp winp (sync_start x) = U_sync gv sp headp winp x.
Proof. intros. destruct x. reflexivity. Qed.
Lemma U_sync_fix: forall x, U_sync gv sp headp winp (sync_fix x) = U_sync gv sp headp winp x.
Proof. intros. destruct x. unfold sync_fix. ss_simpl. destruct (_ =? _); [destruct (_ =? _) | ]; reflexivity. Qed.
Lemma U_sync_mf: forall x fl md, U_sync gv sp headp winp (set_i_mode (set_i_flags x fl) md) = U_sync gv sp headp winp x.
Proof. intros. destruct x. reflexivity. Qed.
Lemma win_rep_have: forall x g, win_rep winp (set_i_have x g) = win_rep winp x.
Proof. intros. destruct x. reflexivity. Qed.
Lemma win_rep_start: forall x, win_rep winp (sync_start x) = win_rep winp x.
Proof. intros. destruct x. reflexivity. Qed.
Lemma win_rep_mf: forall x fl md, win_rep winp (set_i_mode (set_i_flags x fl) md) = win_rep winp x.
Proof. intros. destruct x. reflexivity. Qed.
End Reps.

Lemma win_rep_fix: forall L winp, live_ok L -> win_rep winp (sync_fix (l_s L)) = win_rep winp (l_s L).
Proof.
  intros [sp winp0 s hh headp hsh xb nb cb] winp (P & W & M & HW & W3 & HS & WB0 & HD & WF). cbn [l_s] in *.
  destruct s. unfold sync_fix. ss_simpl.
  destruct (Z.eqb_spec i_flags (-1)) as [F | F]; [destruct (Z.eqb_spec i_wbits 0) as [E | E] | ]; try reflexivity.
  destruct (WB0 E) as [_ WN]. unfold win_rep. ss_simpl. rewrite WN. reflexivity.
Qed.

Lemma sync_start_fields: forall x, i_mode (sync_start x) = SYNC /\ i_wrap (sync_start x) = i_wrap x /\
  i_flags (sync_start x) = i_flags x /\ i_wbits (sync_start x) = i_wbits x.
Proof. intros. destruct x. repeat split. Qed.

Lemma sync_fix_fields: forall x, i_mode (sync_fix x) = i_mode x /\ i_flags (sync_fix x) = i_flags x /\
  i_hold (sync_fix x) = i_hold x /\ i_bits (sync_fix x) = i_bits x /\ i_have (sync_fix x) = i_have x.
Proof. intros. destruct x. unfold sync_fix. ss_simpl. destruct (_ =? _); [destruct (_ =? _) | ]; repeat split. Qed.

Lemma have_fields: forall x g, i_mode (set_i_have x g) = i_mode x /\ i_wrap (set_i_have x g) = i_wrap x /\
  i_flags (set_i_have x g) = i_flags x /\ i_wbits (set_i_have x g) = i_wbits x /\
  i_hold (set_i_have x g) = i_hold x /\ i_bits (set_i_have x g) = i_bits x /\ i_have (set_i_have x g) = g.
Proof. intros. destruct x. repeat split. Qed.

Lemma zf_ok_in: forall z ni ai t, zf_ok z -> 0 <= ai <= Int.max_unsigned -> zf_ok (set_zf_in z ni ai (u64 t)).
Proof.
  intros z ni ai t (A & B & C & D & E & F) G. unfold zf_ok, set_zf_in, u64. cbn [zf_ai zf_ao zf_tin zf_tout zf_dt zf_adler].
  pose proof (Z.mod_pos_bound t (2 ^ 64) ltac:(lia)). repeat split; rep_lia.
Qed.

Lemma zf_ok_counters: forall z t o, zf_ok z -> lrange t -> lrange o -> zf_ok (set_zf_counters z t o).
Proof.
  intros z t o (A & B & C & D & E & F) G K. unfold zf_ok, set_zf_counters, lrange in *. cbn [zf_ai zf_ao zf_tin zf_tout zf_dt zf_adler]. repeat split; rep_lia.
Qed.

Lemma sync_fix_ww: forall x,
  i_wrap (sync_fix x) = (if i_flags x =? -1 then 0 else Z.land (i_wrap x) (Z.lnot 4)) /\
  i_wbits (sync_fix x) = (if i_flags x =? -1 then (if i_wbits x =? 0 then 15 else i_wbits x) else i_wbits x).
Proof. intros. destruct x. unfold sync_fix. ss_simpl. destruct (_ =? -1); [destruct (_ =? 0) | ]; split; reflexivity. Qed.

Lemma mf_fields: forall x fl md, i_mode (set_i_mode (set_i_flags x fl) md) = md /\
  i_wrap (set_i_mode (set_i_flags x fl) md) = i_wrap x /\ i_flags (set_i_mode (set_i_flags x fl) md) = fl /\
  i_wbits (set_i_mode (set_i_flags x fl) md) = i_wbits x /\ i_hold (set_i_mode (set_i_flags x fl) md) = i_hold x /\
  i_bits (set_i_mode (set_i_flags x fl) md) = i_bits x /\ i_have (set_i_mode (set_i_flags x fl) md) = i_have x.
Proof. intros. destruct x. repeat split. Qed.

Lemma and_not4: forall w, 0 <= w <= 15 -> Int.and (Int.repr w) (Int.not (Int.repr 4)) = Int.repr (Z.land w (Z.lnot 4)).
Proof.
  intros w H. assert (C: w = 0 \/ w = 1 \/ w = 2 \/ w = 3 \/ w = 4 \/ w = 5 \/ w = 6 \/ w = 7 \/ w = 8 \/ w = 9 \/
            w = 10 \/ w = 11 \/ w = 12 \/ w = 13 \/ w = 14 \/ w = 15) by lia.
  destruct C as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]]]; reflexivity.
Qed.

(* inflateSync's store state->wrap = wrap & ~8 (patch F8: bit 3 hidden from its inflateReset call) *)
Lemma and_not8: forall w, 0 <= w <= 15 ->
  Int.and (Int.repr w) (Int.not (Int.repr 8)) = Int.repr (Z.land w (Z.lnot 8)).
Proof.
  intros w H. assert (C: w = 0 \/ w = 1 \/ w = 2 \/ w = 3 \/ w = 4 \/ w = 5 \/ w = 6 \/ w = 7 \/ w = 8 \/ w = 9 \/
            w = 10 \/ w = 11 \/ w = 12 \/ w = 13 \/ w = 14 \/ w = 15) by lia.
  destruct C as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]]]; reflexivity.
Qed.

Lemma land_not8_8 (w: Z) : Z.land (Z.land w (Z.lnot 8)) 8 = 0.
Proof. rewrite <- Z.land_assoc. change (Z.land (Z.lnot 8) 8) with 0. apply Z.land_0_r. Qed.

Lemma reset_full_clear8 (s: istate) : Z.land (i_wrap s) 8 = 0 -> reset_full_s s = reset_s s.
Proof. intros H. unfold reset_full_s, reset_hdr_s. rewrite H. reflexivity. Qed.

Lemma U_sync_wrap (gv: globals) (sp headp winp: val) (x: istate) (w: Z) :
  U_sync gv sp headp winp (set_i_wrap x w) = U_sync gv sp headp winp x.
Proof. destruct x. reflexivity. Qed.

Lemma win_rep_wrap (winp: val) (x: istate) (w: Z) : win_rep winp (set_i_wrap x w) = win_rep winp x.
Proof. destruct x. reflexivity. Qed.

Lemma reset_keep_z_wrap: forall z x y, i_wrap x = i_wrap y -> reset_keep_z z x = reset_keep_z z y.
Proof. intros. unfold reset_keep_z. rewrite H. reflexivity. Qed.

Lemma sync_s_go: forall s inp, ((Zlength inp =? 0) && (i_bits s <? 8))%bool = false ->
  sync_s s inp =
    (let s1 := if i_mode s =? SYNC then s else sync_start s in
     let got := fst (ssearch (i_have s1) inp) in let len := snd (ssearch (i_have s1) inp) in
     if got =? 4 then SyncOk (sync_fin (set_i_have s1 got)) len else SyncData (set_i_have s1 got) len).
Proof.
  intros s inp H. unfold sync_s. rewrite H. cbv zeta.
  destruct (ssearch _ inp) as [g l]. cbn [fst snd]. destruct (g =? 4); reflexivity.
Qed.


(* ---------------------------------------------------------------------------------------------- *)
(* inflateSync's body in segments: one lemma (and file) per segment, as the proof of the whole     *)
(* body in one lemma exceeds the time budget of a file. Body5_sync.v proves the start of the body  *)
(* and chains the others: Body5_sync0.v, Body5_sync1.v .. Body5_sync5.v (segment 3 in two files,   *)
(* Body5_sync3.v and Body5_sync3b.v).                                                              *)

(* from `if (state->mode != SYNC)` to the end *)
Definition sync_suf1 : statement :=
  match fn_body f_inflateSync with Ssequence _ (Ssequence _ (Ssequence _ x)) => x | _ => Sskip end.
(* from `len = syncsearch(&(state->have), strm->next_in, strm->avail_in)` to the end *)
Definition sync_suf2 : statement := match sync_suf1 with Ssequence _ x => x | _ => Sskip end.
(* the same after the call: from `len = (the result)` *)
Definition sync_suf3 : statement :=
  match sync_suf2 with Ssequence (Ssequence _ y) x => Ssequence y x | _ => Sskip end.
(* from `if (state->flags == -1)` to the end *)
Definition sync_suf4 : statement :=
  match sync_suf2 with Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ x)))) => x | _ => Sskip end.
(* from `flags = state->flags` to the end *)
Definition sync_suf5 : statement := match sync_suf4 with Ssequence _ x => x | _ => Sskip end.

(* the postcondition of inflateSync_spec on a live stream L and the input buffer ib holding inp *)
Definition sync_post (gv: globals) (shs: share) (strmp: val) (z: zfields) (L: live) (ib: inbuf) (inp: list Z)
    : ret_assert :=
  frame_ret_assert (function_body_ret_assert tint
    (PROP () RETURN (Vint (Int.repr (fst3 (on_live strmp z (Some L) (sync_f ib inp)))))
     SEP (istream_opt gv shs strmp (snd3 (on_live strmp z (Some L) (sync_f ib inp)))
            (thd3 (on_live strmp z (Some L) (sync_f ib inp)));
          in_rep ib; mem_mgr gv; zfuncs gv))%assert) (stackframe_of f_inflateSync).

(* the facts of the precondition that every segment uses *)
Definition sync_hyps (shs: share) (strmp: val) (z: zfields) (ish: share) (ip: val) (ilo ilen: Z) (ic: list val)
    (inp: list Z) : Prop :=
  in_ok (InBuf ish ip ilo ilen ic) inp /\ zf_ni z = offset_val ilo ip /\ zf_ai z = Zlength inp /\ zf_ok z /\
  writable_share shs /\ strmp <> nullval.

(* the z_stream with next_in, avail_in, total_in = ni, ai, ti and state = sp *)
Definition sync_strm (gv: globals) (z: zfields) (ni: val) (ai ti: Z) (sp: val) : reptype t_strm :=
  (ni, (Vint (Int.repr ai), (Vlong (Int64.repr ti), (zf_no z, (Vint (Int.repr (zf_ao z)),
   (Vlong (Int64.repr (zf_tout z)), (msg_val gv (zf_msg z), (sp, (gv _zcalloc, (gv _zcfree,
   (nullval, (Vint (Int.repr (zf_dt z)), (Vlong (Int64.repr (zf_adler z)), zf_res z))))))))))))).

(* the state at the test of the mode (with bufp = data_at_ of buf) and after the bit buffer (bufp = its bytes) *)
Definition sync_A (gv: globals) (shs: share) (strmp: val) (z: zfields) (sp headp winp v_buf: val) (bufp: mpred)
    (s: istate) (ib: inbuf) : environ -> mpred :=
  PROP () LOCAL (temp _state sp; lvar _buf (tarray tuchar 4) v_buf; gvars gv; temp _strm strmp)
  SEP (data_at shs t_strm (sync_strm gv z (zf_ni z) (zf_ai z) (zf_tin z) sp) strmp;
       field_at Ews t_state (DOT _strm) strmp sp;
       field_at Ews t_state (DOT _mode) (Vint (Int.repr (i_mode s))) sp;
       zfuncs gv; bufp; malloc_token Ews t_state sp;
       field_at Ews t_state (DOT _wrap) (Vint (Int.repr (i_wrap s))) sp;
       field_at Ews t_state (DOT _flags) (Vint (Int.repr (i_flags s))) sp;
       field_at Ews t_state (DOT _wbits) (Vint (Int.repr (i_wbits s))) sp;
       field_at Ews t_state (DOT _hold) (Vlong (Int64.repr (i_hold s))) sp;
       field_at Ews t_state (DOT _bits) (Vint (Int.repr (i_bits s))) sp;
       field_at Ews t_state (DOT _have) (Vint (Int.repr (i_have s))) sp;
       U_sync gv sp headp winp s; win_rep winp s; state_pad sp; in_rep ib; mem_mgr gv).

(* the state after the search of the input: state->have = got, the stream's next_in, avail_in, total_in = ni, ai,
   ti, state->wrap = wr and state->wbits = wb, tl the temporary that holds the length of the search *)
Definition sync_B (gv: globals) (shs: share) (strmp: val) (z: zfields) (sp headp winp v_buf: val) (bc: list val)
    (s1: istate) (wr wb got: Z) (ish: share) (ip: val) (ilen: Z) (ic: list val) (ni: val) (ai ti: Z) (tl: localdef)
    : environ -> mpred :=
  PROP () LOCAL (tl; temp _state sp; lvar _buf (tarray tuchar 4) v_buf; gvars gv; temp _strm strmp)
  SEP (field_at Ews t_state (DOT _have) (Vint (Int.repr got)) sp;
       data_at ish (tarray tuchar ilen) ic ip;
       data_at shs t_strm (sync_strm gv z ni ai ti sp) strmp;
       field_at Ews t_state (DOT _strm) strmp sp;
       field_at Ews t_state (DOT _mode) (Vint (Int.repr (i_mode s1))) sp;
       zfuncs gv; data_at Tsh (tarray tuchar 4) bc v_buf; malloc_token Ews t_state sp;
       field_at Ews t_state (DOT _wrap) (Vint (Int.repr wr)) sp;
       field_at Ews t_state (DOT _flags) (Vint (Int.repr (i_flags s1))) sp;
       field_at Ews t_state (DOT _wbits) (Vint (Int.repr wb)) sp;
       field_at Ews t_state (DOT _hold) (Vlong (Int64.repr (i_hold s1))) sp;
       field_at Ews t_state (DOT _bits) (Vint (Int.repr (i_bits s1))) sp;
       U_sync gv sp headp winp s1; win_rep winp s1; state_pad sp; mem_mgr gv).

(* the segments: sync_segK says that the statement sync_sufK runs from its assertion to the postcondition; each
   Body5_syncK.v proves it from sync_seg(K+1), Body5_sync.v chains them *)
Definition sync_seg1 : Prop :=
  forall (E: OracleKind) (gv: globals) (shs: share) (strmp: val) (z: zfields) (sp winp: val) (s: istate)
    (h: hstate) (headp: val) (hsh: share) (xb nb cb: val) (ish: share) (ip: val) (ilo ilen: Z) (ic: list val)
    (inp: list Z) (v_buf: val),
  sync_hyps shs strmp z ish ip ilo ilen ic inp ->
  live_ok (Live sp winp s h headp hsh xb nb cb) -> HEAD <= i_mode s <= SYNC ->
  ((Zlength inp =? 0) && (i_bits s <? 8))%bool = false ->
  semax (func_tycontext f_inflateSync Vprog_inflate Gp_sync nil)
    (sync_A gv shs strmp z sp headp winp v_buf (data_at_ Tsh (tarray tuchar 4) v_buf) s (InBuf ish ip ilo ilen ic))
    sync_suf1
    (sync_post gv shs strmp z (Live sp winp s h headp hsh xb nb cb) (InBuf ish ip ilo ilen ic) inp).

Definition sync_seg2 : Prop :=
  forall (E: OracleKind) (gv: globals) (shs: share) (strmp: val) (z: zfields) (sp winp: val) (s: istate)
    (h: hstate) (headp: val) (hsh: share) (xb nb cb: val) (ish: share) (ip: val) (ilo ilen: Z) (ic: list val)
    (inp: list Z) (v_buf: val) (s1: istate) (bc: list val),
  sync_hyps shs strmp z ish ip ilo ilen ic inp ->
  live_ok (set_l_s (Live sp winp s h headp hsh xb nb cb) s1) -> i_mode s1 = SYNC -> 0 <= i_have s1 <= 320 ->
  sync_s s inp = (if fst (ssearch (i_have s1) inp) =? 4
    then SyncOk (sync_fin (set_i_have s1 (fst (ssearch (i_have s1) inp)))) (snd (ssearch (i_have s1) inp))
    else SyncData (set_i_have s1 (fst (ssearch (i_have s1) inp))) (snd (ssearch (i_have s1) inp))) ->
  semax (func_tycontext f_inflateSync Vprog_inflate Gp_sync nil)
    (sync_A gv shs strmp z sp headp winp v_buf (data_at Tsh (tarray tuchar 4) bc v_buf) s1 (InBuf ish ip ilo ilen ic))
    sync_suf2
    (sync_post gv shs strmp z (Live sp winp s h headp hsh xb nb cb) (InBuf ish ip ilo ilen ic) inp).

Definition sync_seg3 : Prop :=
  forall (E: OracleKind) (gv: globals) (shs: share) (strmp: val) (z: zfields) (sp winp: val) (s: istate)
    (h: hstate) (headp: val) (hsh: share) (xb nb cb: val) (ish: share) (ip: val) (ilo ilen: Z) (ic: list val)
    (inp: list Z) (v_buf: val) (s1: istate) (bc: list val),
  sync_hyps shs strmp z ish ip ilo ilen ic inp ->
  live_ok (set_l_s (Live sp winp s h headp hsh xb nb cb) s1) -> i_mode s1 = SYNC -> 0 <= i_have s1 <= 320 ->
  sync_s s inp = (if fst (ssearch (i_have s1) inp) =? 4
    then SyncOk (sync_fin (set_i_have s1 (fst (ssearch (i_have s1) inp)))) (snd (ssearch (i_have s1) inp))
    else SyncData (set_i_have s1 (fst (ssearch (i_have s1) inp))) (snd (ssearch (i_have s1) inp))) ->
  semax (func_tycontext f_inflateSync Vprog_inflate Gp_sync nil)
    (sync_B gv shs strmp z sp headp winp v_buf bc s1 (i_wrap s1) (i_wbits s1) (fst (ssearch (i_have s1) inp))
       ish ip ilen ic (zf_ni z) (zf_ai z) (zf_tin z) (temp _t'4 (Vint (Int.repr (snd (ssearch (i_have s1) inp))))))
    sync_suf3
    (sync_post gv shs strmp z (Live sp winp s h headp hsh xb nb cb) (InBuf ish ip ilo ilen ic) inp).

Definition sync_seg4 : Prop :=
  forall (E: OracleKind) (gv: globals) (shs: share) (strmp: val) (z: zfields) (sp winp: val) (s: istate)
    (h: hstate) (headp: val) (hsh: share) (xb nb cb: val) (ish: share) (ip: val) (ilo ilen: Z) (ic: list val)
    (inp: list Z) (v_buf: val) (s1: istate) (bc: list val) (len: Z),
  sync_hyps shs strmp z ish ip ilo ilen ic inp ->
  live_ok (set_l_s (Live sp winp s h headp hsh xb nb cb) s1) -> i_mode s1 = SYNC ->
  ssearch (i_have s1) inp = (4, len) -> 0 <= len <= Zlength inp ->
  sync_s s inp = SyncOk (sync_fin (set_i_have s1 4)) len ->
  semax (func_tycontext f_inflateSync Vprog_inflate Gp_sync nil)
    (sync_B gv shs strmp z sp headp winp v_buf bc s1 (i_wrap s1) (i_wbits s1) 4 ish ip ilen ic
       (in_ptr (InBuf ish ip ilo ilen ic) len) (Zlength inp - len) (u64 (zf_tin z + len))
       (temp _len (Vint (Int.repr len))))
    sync_suf4
    (sync_post gv shs strmp z (Live sp winp s h headp hsh xb nb cb) (InBuf ish ip ilo ilen ic) inp).

Definition sync_seg5 : Prop :=
  forall (E: OracleKind) (gv: globals) (shs: share) (strmp: val) (z: zfields) (sp winp: val) (s: istate)
    (h: hstate) (headp: val) (hsh: share) (xb nb cb: val) (ish: share) (ip: val) (ilo ilen: Z) (ic: list val)
    (inp: list Z) (v_buf: val) (s1: istate) (bc: list val) (len: Z),
  sync_hyps shs strmp z ish ip ilo ilen ic inp ->
  live_ok (set_l_s (Live sp winp s h headp hsh xb nb cb) s1) -> i_mode s1 = SYNC ->
  ssearch (i_have s1) inp = (4, len) -> 0 <= len <= Zlength inp ->
  sync_s s inp = SyncOk (sync_fin (set_i_have s1 4)) len ->
  semax (func_tycontext f_inflateSync Vprog_inflate Gp_sync nil)
    (sync_B gv shs strmp z sp headp winp v_buf bc s1 (i_wrap (sync_fix (set_i_have s1 4)))
       (i_wbits (sync_fix (set_i_have s1 4))) 4 ish ip ilen ic (in_ptr (InBuf ish ip ilo ilen ic) len)
       (Zlength inp - len) (u64 (zf_tin z + len)) (temp _len (Vint (Int.repr len))))
    sync_suf5
    (sync_post gv shs strmp z (Live sp winp s h headp hsh xb nb cb) (InBuf ish ip ilo ilen ic) inp).

(* the start of a segment: the statement, the type context and the assertions in the form forward expects *)
Ltac sync_seg_start :=
  match goal with |- semax _ _ ?c _ =>
    let c' := eval cbv beta iota delta [sync_suf1 sync_suf2 sync_suf3 sync_suf4 sync_suf5 f_inflateSync fn_body] in c in
    change c with c' end;
  unfold sync_A, sync_B, sync_strm, sync_post; simplify_func_tycontext; abbreviate_semax.
