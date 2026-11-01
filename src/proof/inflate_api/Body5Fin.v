(* The machine after inf_leave is a live stream's (Body5Parts.v leave_fin5_stmt). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate_api.Body5Parts.
Require Zlib.proof.crc32.Combine.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* ---------------------------------------------------------------------------------------------- *)
(* The fields inf_leave does not change (all but the window, hold, bits, total, check)            *)

Definition wcore (s: istate) : istate :=
  IS (i_mode s) (i_last s) (i_wrap s) (i_havedict s) (i_flags s) (i_dmax s) 0 0 (i_head s) (i_wbits s)
     0 0 0 false [] 0 0 (i_length s) (i_offset s) (i_extra s) (i_lencode s) (i_distcode s) (i_lenbits s)
     (i_distbits s) (i_ncode s) (i_nlen s) (i_ndist s) (i_have s) (i_next s) (i_lens s) (i_codes s)
     (i_sane s) (i_back s) (i_was s).

Lemma tvalid_codes: forall k fx dx s s' t rb, i_codes s' = i_codes s ->
  tvalid k fx dx s t rb -> tvalid k fx dx s' t rb.
Proof.
  intros k fx dx s s' t rb E [sz [A B]]. exists sz. split; [exact A | ].
  unfold tvalid_b in *. eapply tvalid_g_ext; [ | exact B].
  intros i _. destruct t; simpl; congruence.
Qed.

Lemma tvalid_len_codes: forall fx dx s s' t rb, i_codes s' = i_codes s ->
  tvalid_len fx dx s t rb -> tvalid_len fx dx s' t rb.
Proof.
  intros fx dx s s' t rb E [sz [A [B C]]]. exists sz. split; [exact A | split].
  - unfold tvalid_b in *. eapply tvalid_g_ext; [ | exact B].
    intros i _. destruct t; simpl; congruence.
  - intros i Hi. replace (tab_entry fx dx s' t i) with (tab_entry fx dx s t i); [auto | ].
    destruct t; simpl; congruence.
Qed.

Ltac core_eqs E :=
  let f := fun p => let H := fresh "E" in assert (H := f_equal p E); simpl in H in
  f i_mode; f i_last; f i_wrap; f i_havedict; f i_flags; f i_dmax; f i_head; f i_wbits; f i_length;
  f i_offset; f i_extra; f i_lencode; f i_distcode; f i_lenbits; f i_distbits; f i_ncode; f i_nlen;
  f i_ndist; f i_have; f i_next; f i_lens; f i_codes; f i_sane; f i_back; f i_was.

Lemma modewf_core: forall s s', wcore s' = wcore s -> modewf s -> modewf s'.
Proof.
  intros s s' E H. core_eqs E. destruct H; constructor; repeat match goal with H: _ = _ |- _ => rewrite H end; auto.
  - intros A. destruct (md_codelens A) as (B & C & D & F & G & I). refine (conj B (conj C (conj D (conj F (conj _ I))))).
    eapply tvalid_codes; [ | exact G]; auto.
  - intros A. destruct (md_tables A) as [B C]. split; eapply tvalid_codes; eauto.
Qed.

(* the window facts of swf *)
Definition swin (s: istate) : Prop :=
  (i_wsize s = 0 \/ (i_win s = true /\ i_wsize s = 2 ^ i_wbits s)) /\
  0 <= i_whave s <= i_wsize s /\
  (0 <= i_wnext s <= i_wsize s /\ (0 < i_wsize s -> i_wnext s < i_wsize s)) /\
  (i_whave s < i_wsize s -> i_wnext s = i_whave s) /\
  (Zlength (i_wdata s) = i_whave s /\ bytes_ok (i_wdata s)).

Lemma swf_swin: forall s, swf s -> swin s.
Proof. intros s H. destruct H. unfold swin. auto 10. Qed.

Lemma swf_core: forall s s', wcore s' = wcore s -> swf s -> swin s' ->
  lrange (i_check s') -> lrange (i_total s') -> lrange (i_hold s') -> 0 <= i_bits s' <= 39 ->
  swf s'.
Proof.
  intros s s' E H (W1 & W2 & W3 & W4 & W5) C T Hh B. core_eqs E. rewrite E7 in W1.
  destruct H; constructor; repeat match goal with H: _ = _ |- _ => rewrite H end; auto.
Qed.

Lemma swf3_core: forall s s', wcore s' = wcore s -> swf3 s ->
  (i_mode s' = HEAD -> i_wbits s' = 0 -> i_wrap s' <> 0 -> i_wsize s' = 0 /\ i_win s' = false) ->
  swf3 s'.
Proof.
  intros s s' E H Hd. core_eqs E.
  destruct H; constructor; auto; repeat match goal with H: _ = _ |- _ => rewrite H end; auto.
  intros A. eapply tvalid_len_codes; [ | apply s3_len]; auto.
Qed.

Lemma win_inv5_core: forall s s', wcore s' = wcore s -> win_inv5 s ->
  (i_wbits s = 0 -> i_win s' = i_win s) -> win_inv5 s'.
Proof.
  intros s s' E [H1 H2] Hw. core_eqs E. unfold win_inv5.
  repeat match goal with H: _ = _ |- _ => rewrite H end. split; auto.
  intros A. rewrite Hw by exact A. auto.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* updatewindow                                                                                   *)

Definition uw0 (s: istate) : istate :=
  if i_wsize s =? 0 then set_i_whave (set_i_wnext (set_i_wsize s (2 ^ i_wbits s)) 0) 0 else s.

Definition uw2 (s: istate) (data: list Z) : istate :=
  let copy := Zlength data in
  let ws := i_wsize s in
  let w := i_wdata s in
  if ws <=? copy then
    set_i_wdata (set_i_whave (set_i_wnext s 0) ws) (sublist (copy - ws) copy data)
  else
    let dist := Z.min (ws - i_wnext s) copy in
    let src1 := sublist 0 dist data in
    let full := sublist 0 (i_wnext s) w ++ src1 ++ sublist (i_wnext s + dist) (Zlength w) w in
    let copy' := copy - dist in
    if negb (copy' =? 0) then
      let src2 := sublist dist copy data in
      set_i_wdata (set_i_whave (set_i_wnext s copy') ws) (src2 ++ sublist copy' (Zlength full) full)
    else
      let wn := i_wnext s + dist in
      let wh := if i_whave s <? ws then i_whave s + dist else i_whave s in
      set_i_wdata (set_i_whave (set_i_wnext s (if wn =? ws then 0 else wn)) wh) full.

Lemma updatewindow_eq: forall s data, updatewindow s data = uw2 (uw0 s) data.
Proof. reflexivity. Qed.

(* the window after its allocation *)
Definition wok (s: istate) : Prop :=
  0 < i_wsize s /\ 0 <= i_whave s <= i_wsize s /\ 0 <= i_wnext s < i_wsize s /\
  (i_whave s < i_wsize s -> i_wnext s = i_whave s) /\
  Zlength (i_wdata s) = i_whave s /\ bytes_ok (i_wdata s).

Lemma uw0_wok: forall s, swf s -> wok (uw0 s) /\ i_wsize (uw0 s) = 2 ^ i_wbits s /\ wcore (uw0 s) = wcore s.
Proof.
  intros s H. pose proof (sw_wbits _ H). pose proof (sw_whave _ H). pose proof (sw_wnext _ H).
  pose proof (sw_wvalid _ H). pose proof (sw_wdata _ H). pose proof (sw_wsize _ H) as Ws.
  assert (P: 0 < 2 ^ i_wbits s) by (apply Z.pow_pos_nonneg; lia).
  unfold uw0, wok. destruct (Z.eqb_spec (i_wsize s) 0) as [Z0 | Z0]; simpl.
  - rewrite Z0 in *. assert (i_whave s = 0) by lia.
    split; [ | split; [reflexivity | reflexivity]]. repeat split; try lia; tauto.
  - destruct Ws as [? | [_ W]]; [lia | ]. rewrite W in *.
    split; [ | split; [reflexivity | reflexivity]]. repeat split; try lia; tauto.
Qed.

Lemma bytes_ok_sublist: forall lo hi l, bytes_ok l -> bytes_ok (sublist lo hi l).
Proof. intros. apply Forall_sublist. exact H. Qed.

Lemma uw2_wok: forall s data, wok s -> bytes_ok data ->
  wok (uw2 s data) /\ i_wsize (uw2 s data) = i_wsize s /\ wcore (uw2 s data) = wcore s.
Proof.
  intros s data (A & B & C & D & F & G) Hd.
  pose proof (Zlength_nonneg data).
  unfold uw2. cbv zeta.
  destruct (Z.leb_spec (i_wsize s) (Zlength data)).
  - simpl. split; [ | split; reflexivity]. unfold wok; simpl.
    rewrite Zlength_sublist by lia. repeat split; try lia. apply bytes_ok_sublist; auto.
  - set (dist := Z.min (i_wsize s - i_wnext s) (Zlength data)).
    assert (Dd: 0 <= dist <= Zlength data /\ i_wnext s + dist <= i_wsize s) by (unfold dist; lia).
    set (full := sublist 0 (i_wnext s) (i_wdata s) ++ sublist 0 dist data ++
                 sublist (i_wnext s + dist) (Zlength (i_wdata s)) (i_wdata s)).
    assert (Fb: bytes_ok full).
    { unfold full, bytes_ok. rewrite !Forall_app. repeat split; apply bytes_ok_sublist; auto. }
    assert (Fl: Zlength full = if i_whave s <? i_wsize s then i_whave s + dist else i_wsize s).
    { unfold full. rewrite !Zlength_app. rewrite F.
      destruct (Z.ltb_spec (i_whave s) (i_wsize s)) as [Lt | Ge].
      - rewrite (D Lt). rewrite (sublist_nil_gen _ (i_whave s + dist)) by lia. rewrite Zlength_nil.
        rewrite !Zlength_sublist; rewrite ?F; lia.
      - assert (i_whave s = i_wsize s) by lia.
        rewrite !Zlength_sublist; rewrite ?F; lia. }
    destruct (Z.eqb_spec (Zlength data - dist) 0) as [Z0 | Z0]; simpl.
    + split; [ | split; reflexivity]. unfold wok; simpl. fold dist. fold full.
      destruct (Z.ltb_spec (i_whave s) (i_wsize s)) as [Lt | Ge].
      * rewrite (D Lt) in *.
        destruct (Z.eqb_spec (i_whave s + dist) (i_wsize s)); repeat split; try lia; auto.
      * destruct (Z.eqb_spec (i_wnext s + dist) (i_wsize s)); repeat split; try lia; auto.
    + split; [ | split; reflexivity]. unfold wok; simpl. fold dist. fold full.
      assert (Dw: dist = i_wsize s - i_wnext s) by (unfold dist in *; lia).
      assert (Fl2: Zlength full = i_wsize s).
      { rewrite Fl. destruct (Z.ltb_spec (i_whave s) (i_wsize s)) as [Lt | Ge]; [rewrite <- (D Lt); lia | lia]. }
      rewrite Zlength_app, !Zlength_sublist by lia.
      repeat split; try lia.
      unfold bytes_ok. rewrite Forall_app. split; apply bytes_ok_sublist; auto.
Qed.

Lemma updatewindow_swin: forall s data, swf s -> bytes_ok data ->
  swin (set_i_win (updatewindow s data) true) /\ wcore (set_i_win (updatewindow s data) true) = wcore s /\
  0 < i_wsize (updatewindow s data).
Proof.
  intros s data H Hd. rewrite updatewindow_eq.
  destruct (uw0_wok s H) as (W0 & S0 & C0).
  destruct (uw2_wok _ data W0 Hd) as ((A & B & C & D & F & G) & S2 & C2).
  split; [ | split].
  - unfold swin; simpl. rewrite S2, S0. assert (i_wbits (uw2 (uw0 s) data) = i_wbits s).
    { apply (f_equal i_wbits) in C2. apply (f_equal i_wbits) in C0. simpl in *. congruence. }
    rewrite H0. rewrite S2, S0 in *. repeat split; auto; lia.
  - change (wcore (uw2 (uw0 s) data) = wcore s). congruence.
  - lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* leave_fin: the window part and the counters / check part                                       *)

Local Open Scope bool_scope.
Local Open Scope Z_scope.

Definition lf_mid (flush: Z) (m: mst) : mst :=
  let upd := leave_ok flush m in
  let m := restore m in
  if upd then
    let copy := u32 (m_out m - m_left m) in
    upd_s m (fun s => set_i_win (updatewindow s (sublist (Zlength (m_ow m) - copy) (Zlength (m_ow m)) (m_ow m))) true)
  else m.

Definition lf_tail (flush: Z) (m: mst) : result :=
  let inn := u32 (m_in m - m_have m) in
  let out := u32 (m_out m - m_left m) in
  let m := set_m_tout (set_m_tin m (u64 (m_tin m + inn))) (u64 (m_tout m + out)) in
  let m := upd_s m (fun s => set_i_total s (u64 (i_total s + out))) in
  let m := if negb (Z.land (i_wrap (m_s m)) 4 =? 0) && negb (out =? 0) then
             let c := update_check (i_flags (m_s m)) (i_check (m_s m))
                        (sublist (Zlength (m_ow m) - out) (Zlength (m_ow m)) (m_ow m)) in
             set_m_adler (upd_s m (fun s => set_i_check s c)) c
           else m in
  let s := m_s m in
  let dt := m_bits m + (if i_last s =? 0 then 0 else 64) + (if i_mode s =? Zlib.proof.inflate.Model.TYPE then 128 else 0)
            + (if (i_mode s =? LEN_) || (i_mode s =? COPY_) then 256 else 0) in
  let r := if (((inn =? 0) && (out =? 0)) || (flush =? Z_FINISH)) && (m_ret m =? Z_OK)
           then Z_BUF_ERROR else m_ret m in
  Res r m (Some dt).

Lemma leave_fin_eq: forall flush m, leave_fin flush m = lf_tail flush (lf_mid flush m).
Proof. reflexivity. Qed.

Lemma u64_lrange: forall x, lrange (u64 x).
Proof.
  intros x. unfold lrange, u64. pose proof (Z.mod_pos_bound x (2 ^ 64) ltac:(lia)).
  unfold Int64.max_unsigned, Int64.modulus, Int64.wordsize, Wordsize_64.wordsize. simpl. lia.
Qed.

Lemma update_check_lrange: forall f c d, bytes_ok d -> lrange (update_check f c d).
Proof.
  intros f c d H. unfold update_check, lrange.
  assert (2 ^ 32 <= Int64.max_unsigned) by (unfold Int64.max_unsigned, Int64.modulus, Int64.wordsize,
    Wordsize_64.wordsize; simpl; lia).
  destruct (f =? 0).
  - destruct (adler32_z_val_range c d H) as [A _]. lia.
  - pose proof (Zlib.proof.crc32.Combine.ref_crc32_range c d H) as A. unfold Zlib.proof.crc32.GF2.is32 in A. lia.
Qed.

Lemma lf_tail_ok: forall flush m m2, mwf3 m -> win_inv5 (m_s m) ->
  wcore (m_s m2) = wcore (m_s m) -> swin (m_s m2) -> lrange (i_check (m_s m2)) ->
  lrange (i_total (m_s m2)) -> lrange (i_hold (m_s m2)) -> 0 <= i_bits (m_s m2) <= 39 ->
  (i_mode (m_s m2) = HEAD -> i_wbits (m_s m2) = 0 -> i_wrap (m_s m2) <> 0 ->
     i_wsize (m_s m2) = 0 /\ i_win (m_s m2) = false) ->
  (i_wbits (m_s m) = 0 -> i_win (m_s m2) = i_win (m_s m)) ->
  m_h m2 = m_h m -> m_inp m2 = m_inp m -> m_aout m2 = m_aout m -> m_ow m2 = m_ow m ->
  m_snx m2 = m_nx m -> m_sow m2 = Zlength (m_ow m) -> m_bits m2 = m_bits m ->
  lrange (m_tin m2) -> lrange (m_tout m2) -> lrange (m_adler m2) ->
  fin_ok5 (r_m (lf_tail flush m2)) /\ (forall d, r_dtype (lf_tail flush m2) = Some d -> srange d) /\
  m_h (r_m (lf_tail flush m2)) = m_h m /\ i_head (m_s (r_m (lf_tail flush m2))) = i_head (m_s m) /\
  m_inp (r_m (lf_tail flush m2)) = m_inp m.
Proof.
  intros flush m m2 [W S3] WI Ec Sw Hc Ht Hh Hb Hd Hw Eh Ei Ea Eo En Es Eb Ti To Ta.
  assert (Ehd: i_head (m_s m2) = i_head (m_s m)) by exact (f_equal i_head Ec).
  pose proof (mw_inp _ W). pose proof (mw_ow _ W). pose proof (mw_nx _ W).
  pose proof (mw_aout _ W). pose proof (mw_bits _ W). pose proof (Zlength_nonneg (m_ow m)).
  set (out := u32 (m_out m2 - m_left m2)).
  set (inn := u32 (m_in m2 - m_have m2)).
  set (s3 := set_i_total (m_s m2) (u64 (i_total (m_s m2) + out))).
  assert (C3: wcore s3 = wcore (m_s m)) by exact Ec.
  assert (K: forall s', wcore s' = wcore s3 -> i_wsize s' = i_wsize s3 -> i_whave s' = i_whave s3 ->
            i_wnext s' = i_wnext s3 -> i_win s' = i_win s3 -> i_wdata s' = i_wdata s3 ->
            i_hold s' = i_hold s3 -> i_bits s' = i_bits s3 -> lrange (i_check s') -> lrange (i_total s') ->
            swf s' /\ modewf s' /\ swf3 s' /\ win_inv5 s').
  { intros s' E1 E2 E3 E4 E5 E6 E7 E8 E9 E10. rewrite C3 in E1.
    assert (Sw': swin s').
    { destruct Sw as (A1 & A2 & A3 & A4 & A5). unfold swin.
      assert (i_wbits s' = i_wbits (m_s m2)).
      { apply (f_equal i_wbits) in E1. apply (f_equal i_wbits) in Ec. simpl in *. congruence. }
      rewrite E2, E3, E4, E5, E6, H5. exact (conj A1 (conj A2 (conj A3 (conj A4 A5)))). }
    split; [ | split; [ | split]].
    - apply (swf_core (m_s m) s' E1 (mw_s _ W) Sw' E9 E10); [rewrite E7; exact Hh | rewrite E8; exact Hb].
    - eapply modewf_core; eauto. apply (mw_md _ W).
    - apply (swf3_core (m_s m) s' E1 S3). rewrite E2, E5. unfold s3; simpl.
      assert (Q := eq_trans E1 (eq_sym Ec)).
      apply (f_equal i_mode) in Q as Hm. apply (f_equal i_wbits) in Q as Hwb. apply (f_equal i_wrap) in Q as Hwr.
      simpl in Hm, Hwb, Hwr. intros. apply Hd; congruence.
    - apply (win_inv5_core (m_s m) s' E1 WI). intros Z0. rewrite E5. exact (Hw Z0). }
  assert (Fr: forall m', m_inp m' = m_inp m -> m_aout m' = m_aout m -> m_snx m' = m_nx m ->
            m_sow m' = Zlength (m_ow m) -> m_h m' = m_h m -> lrange (m_tin m') -> lrange (m_tout m') ->
            lrange (m_adler m') -> swf (m_s m') /\ modewf (m_s m') /\ swf3 (m_s m') /\ win_inv5 (m_s m') ->
            fin_ok5 m').
  { intros m' F1 F2 F3 F4 F5 F6 F7 F8 (G1 & G2 & G3 & G4). unfold fin_ok5.
    rewrite F1, F2, F3, F4, F5. refine (conj G1 (conj G2 (conj (mw_h _ W) (conj G3 (conj G4 _))))).
    unfold lrange in *. destruct H as [? _], H0 as [? _]. repeat split; lia. }
  assert (Hdt: forall bits l md, 0 <= bits <= 39 ->
            srange (bits + (if l =? 0 then 0 else 64) + (if md =? Zlib.proof.inflate.Model.TYPE then 128 else 0)
                    + (if (md =? LEN_) || (md =? COPY_) then 256 else 0))).
  { intros. unfold srange. destruct (l =? 0), (md =? Zlib.proof.inflate.Model.TYPE), ((md =? LEN_) || (md =? COPY_)); rep_lia. }
  assert (Bd: bytes_ok (sublist (Zlength (m_ow m2) - out) (Zlength (m_ow m2)) (m_ow m2))).
  { apply Forall_sublist. rewrite Eo. apply H0. }
  unfold lf_tail. cbv zeta. fold out inn. simpl.
  destruct (negb (Z.land (i_wrap (m_s m2)) 4 =? 0) && negb (out =? 0)); simpl.
  - fold s3. split; [ | split; [ | split; [ | split]]]; auto.
    + apply Fr; simpl; auto using u64_lrange, update_check_lrange.
      apply K; simpl; auto using u64_lrange, update_check_lrange.
    + intros d E. inversion E. apply Hdt. rewrite Eb. auto.
  - fold s3. split; [ | split; [ | split; [ | split]]]; auto.
    + apply Fr; simpl; auto using u64_lrange.
      apply K; simpl; auto using u64_lrange.
    + intros d E. inversion E. apply Hdt. rewrite Eb. auto.
Qed.

Lemma updatewindow_keep: forall s d,
  i_check (updatewindow s d) = i_check s /\ i_total (updatewindow s d) = i_total s /\
  i_hold (updatewindow s d) = i_hold s /\ i_bits (updatewindow s d) = i_bits s.
Proof.
  intros s d. rewrite updatewindow_eq. unfold uw2, uw0. cbv zeta.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; simpl; auto.
Qed.

Ltac modes := unfold HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC, DICTID, DICT,
  Zlib.proof.inflate.Model.TYPE, TYPEDO, STORED, COPY_, COPY, TABLE, LENLENS, CODELENS, LEN_, LEN,
  LENEXT, DIST, DISTEXT, MATCH, LIT, CHECK, LENGTH, DONE, BAD, MEM, SYNC in *.

(* the window update is attempted only with wbits <> 0 *)
Lemma leave_ok_wbits: forall flush m, mwf m -> out_inv m -> win_inv5 (m_s m) ->
  leave_ok flush m = true -> i_wbits (m_s m) <> 0.
Proof.
  intros flush m W (O1 & O2 & O3) [WI1 WI2] U Wb.
  destruct (WI1 Wb) as [Wr Wn]. destruct (WI2 Wb (land3_wrap _ Wr)) as [_ Md].
  assert (Ws: i_wsize (m_s m) = 0).
  { destruct (sw_wsize _ (mw_s _ W)) as [ | [A _]]; [auto | congruence]. }
  unfold leave_ok in U. rewrite Ws in U. simpl in U.
  apply andb_prop in U as [U _]. apply andb_prop in U as [U1 U2].
  unfold m_mode in U2. destruct Md as [Md | [Md | [Md | Md]]]; rewrite Md in U2.
  - unfold m_mode in O3. specialize (O3 Md). unfold m_left in *. rewrite O3, Zlength_nil in *.
    assert (m_out m = m_aout m - 0) by lia. rewrite H, Z.eqb_refl in U1. discriminate.
  - modes. discriminate.
  - modes. discriminate.
  - modes. discriminate.
Qed.

Lemma leave_fin5 : leave_fin5_stmt.
Proof.
  intros flush m res MW O WI IL. pose proof MW as [W S3].
  pose proof (mw_s _ W) as HS. pose proof (mw_ow _ W) as [Ow Ob].
  inversion IL; subst.
  - (* the window allocation fails *)
    simpl. split; [ | split; [ | split; [ | split]]]; try discriminate; auto.
    pose proof (mw_inp _ W). pose proof (mw_nx _ W). pose proof (mw_aout _ W).
    pose proof (mw_tin _ W). pose proof (mw_tout _ W). pose proof (mw_adler _ W).
    pose proof (mw_hold _ W). pose proof (mw_bits _ W). pose proof (Zlength_nonneg (m_ow m)).
    unfold fin_ok5; simpl.
    split; [ | split; [ | split; [ | split; [ | split]]]].
    + destruct HS; constructor; simpl; auto. modes. lia.
    + constructor; simpl; unfold decode_mode; modes; intros; lia.
    + exact (mw_h _ W).
    + constructor; simpl; unfold decode_mode; modes; intros; lia.
    + destruct WI as [WI1 WI2]. split; simpl; auto.
      intros A B. destruct (WI2 A B) as [C _]. split; [exact C | ]. right; right; right; reflexivity.
    + destruct H as [H _]. unfold lrange in *. repeat split; lia.
  - (* the window update succeeds, or none *)
    rewrite leave_fin_eq. unfold lf_mid. cbv zeta.
    pose proof (mw_hold _ W). pose proof (mw_bits _ W).
    set (s1 := set_i_bits (set_i_hold (m_s m) (m_hold m)) (m_bits m)).
    assert (S1: swf s1).
    { apply (swf_core (m_s m) s1 eq_refl HS (swf_swin _ HS)); simpl; auto.
      apply (sw_check _ HS). apply (sw_total _ HS). }
    destruct (leave_ok flush m) eqn:U.
    + pose proof (leave_ok_wbits flush m W O WI U) as Wb.
      set (d := sublist _ _ _).
      assert (Bd: bytes_ok d) by (apply Forall_sublist; exact Ob).
      destruct (updatewindow_swin s1 d S1 Bd) as (Sw & Cw & _).
      destruct (updatewindow_keep s1 d) as (K1 & K2 & K3 & K4).
      pose proof (mw_tin _ W). pose proof (mw_tout _ W). pose proof (mw_adler _ W).
      apply (lf_tail_ok flush m _ MW WI); simpl; auto.
      * fold s1. rewrite K1. apply (sw_check _ HS).
      * fold s1. rewrite K2. apply (sw_total _ HS).
      * fold s1. rewrite K3. exact H.
      * fold s1. rewrite K4. exact H0.
      * intros _ Z0. fold s1 in Z0. apply (f_equal i_wbits) in Cw. simpl in Cw. congruence.
      * intros Z0. contradiction.
    + apply (lf_tail_ok flush m _ MW WI); simpl; auto.
      * exact (swf_swin _ HS).
      * apply (sw_check _ HS).
      * apply (sw_total _ HS).
      * apply (s3_head _ S3).
      * apply (mw_tin _ W).
      * apply (mw_tout _ W).
      * apply (mw_adler _ W).
Qed.
