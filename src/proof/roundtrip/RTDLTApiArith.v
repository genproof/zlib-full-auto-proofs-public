(** * deflate_api theory: the header, the trailer and the check values

    Pure arithmetic: the zlib header deflate() writes satisfies RFC 1950 (CM 8, CINFO <= 7, FCHECK, FDICT exactly
    with a dictionary, the dictionary id), the gzip header starts with 1f 8b 08, the trailer gives back the
    check value and the length, the check values compose. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDLTApiDefs.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

Lemma bytes_is_bytes : forall l, bytes l -> Zlib.proof.adler32.Bytes.is_bytes l.
Proof.
  intros l H. unfold bytes in H. unfold Zlib.proof.adler32.Bytes.is_bytes.
  eapply Forall_impl; [|exact H]. intros a Ha. simpl in Ha.
  change compcert.lib.Integers.Byte.max_unsigned with 255. lia.
Qed.

Lemma adler_valid_1 : Zlib.proof.adler32.Model.adler_valid 1.
Proof. unfold Zlib.proof.adler32.Model.adler_valid. vm_compute. repeat split; congruence. Qed.
(** Helpers of [zlib_hdr_good]: the header value depends on four small parameters; a finite check. *)
Definition zh_val (w lev st : Z) (b : bool) : Z :=
  let header := u32 (Z.shiftl (u32 (Z_DEFLATED + u32 (Z.shiftl (u32 (w - 8)) 4))) 8) in
  let level_flags :=
    if (st >=? Z_HUFFMAN_ONLY) || (lev <? 2) then 0
    else if lev <? 6 then 1
    else if lev =? 6 then 2
    else 3 in
  let header := Z.lor header (Z.shiftl level_flags 6) in
  let header := if b then header else Z.lor header PRESET_DICT in
  u32 (header + u32 (31 - header mod 31)).

Lemma zlib_header_zh_val : forall s,
  zlib_header s = zh_val (d_w_bits s) (d_level s) (d_strategy s) (d_strstart s =? 0).
Proof. intros. reflexivity. Qed.

Definition zh_ok (h : Z) (b : bool) : bool :=
  let b0 := u8 (Z.shiftr h 8) in let b1 := u8 (Z.land h 255) in
  (Z.land b0 15 =? 8) && (Z.shiftr b0 4 <=? 7) && ((b0 * 256 + b1) mod 31 =? 0) &&
  Bool.eqb (negb (Z.land b1 32 =? 0)) (negb b).

Definition zh_all : bool :=
  forallb (fun w => forallb (fun lev => forallb (fun st => forallb (fun b => zh_ok (zh_val w lev st b) b)
    [true; false]) (map Z.of_nat (seq 0 5))) (map Z.of_nat (seq 0 10))) (map (fun n => 9 + Z.of_nat n) (seq 0 7)).

Lemma zh_all_true : zh_all = true.
Proof. vm_compute. reflexivity. Qed.

Lemma zh_val_ok : forall w lev st b, 9 <= w <= 15 -> 0 <= lev <= 9 -> 0 <= st <= 4 ->
  zh_ok (zh_val w lev st b) b = true.
Proof.
  intros w lev st b Hw Hl Hs.
  assert (Iw : In w (map (fun n => 9 + Z.of_nat n) (seq 0 7))).
  { apply in_map_iff. exists (Z.to_nat (w - 9)). split; [lia|]. apply in_seq. lia. }
  assert (Il : In lev (map Z.of_nat (seq 0 10))).
  { apply in_map_iff. exists (Z.to_nat lev). split; [lia|]. apply in_seq. lia. }
  assert (Is : In st (map Z.of_nat (seq 0 5))).
  { apply in_map_iff. exists (Z.to_nat st). split; [lia|]. apply in_seq. lia. }
  assert (Ib : In b [true; false]) by (destruct b; simpl; auto).
  pose proof zh_all_true as H. unfold zh_all in H.
  rewrite forallb_forall in H. specialize (H w Iw).
  rewrite forallb_forall in H. specialize (H lev Il).
  rewrite forallb_forall in H. specialize (H st Is).
  rewrite forallb_forall in H. exact (H b Ib).
Qed.

Lemma u8_range : forall x, 0 <= u8 x < 256.
Proof. intros. unfold u8. apply Z.mod_pos_bound. lia. Qed.

Lemma be32_msb2_split : forall a, 0 <= a < 2 ^ 32 ->
  be32 (msb2 (u32 (Z.shiftr a 16)) ++ msb2 (u32 (Z.land a 65535))) = a.
Proof.
  intros a Ha.
  assert (Eq : Z.shiftr a 16 = a / 65536) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (Er : Z.land a 65535 = a mod 65536) by (change 65535 with (Z.ones 16); rewrite Z.land_ones by lia; reflexivity).
  assert (Hq : 0 <= a / 65536 < 65536) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  assert (Hr : 0 <= a mod 65536 < 65536) by (apply Z.mod_pos_bound; lia).
  assert (B : forall x, 0 <= x < 65536 ->
    u8 (Z.shiftr x 8) = x / 256 /\ u8 (Z.land x 255) = x mod 256).
  { intros x Hx. unfold u8. rewrite Z.shiftr_div_pow2 by lia. change 255 with (Z.ones 8).
    rewrite Z.land_ones by lia. change (2 ^ 8) with 256.
    rewrite Z.mod_mod by lia. split; [|reflexivity].
    apply Z.mod_small. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  rewrite Eq, Er. unfold u32.
  rewrite (Z.mod_small (a / 65536)) by lia. rewrite (Z.mod_small (a mod 65536)) by lia.
  destruct (B _ Hq) as [B1 B2]. destruct (B _ Hr) as [B3 B4].
  pose proof (Z.div_mod a 65536 ltac:(lia)).
  revert B1 B2 B3 B4 Hq Hr H. unfold be32, msb2.
  generalize (a / 65536) (a mod 65536). intros q r B1 B2 B3 B4 Hq Hr H.
  unfold Znth; simpl.
  rewrite B1, B2, B3, B4.
  pose proof (Z.div_mod q 256 ltac:(lia)).
  pose proof (Z.div_mod r 256 ltac:(lia)).
  lia.
Qed.

Lemma Znth01_0 : forall (x y : Z) l, Znth 0 (x :: y :: l) = x.
Proof. reflexivity. Qed.
Lemma Znth01_1 : forall (x y : Z) l, Znth 1 (x :: y :: l) = y.
Proof. reflexivity. Qed.

Lemma sub26 : forall (x0 x1 x2 x3 x4 x5 : Z),
  sublist 2 6 [x0; x1; x2; x3; x4; x5] = [x2; x3; x4; x5].
Proof. reflexivity. Qed.

Lemma zlib_hdr_good : forall s dict a,
  prm s -> (d_strstart s = 0 <-> dict = []) -> (dict <> [] -> a = radler 1 dict) -> 0 <= a < 2 ^ 32 ->
  hdr_good dict 1 (zlib_hdr_bytes s a).
Proof.
  intros s dict a Hp Hd Ha Hrange.
  destruct Hp as (Hw & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hl & Hs & _).
  pose proof (zh_val_ok _ _ _ (d_strstart s =? 0) Hw Hl Hs) as K.
  rewrite <- zlib_header_zh_val in K.
  unfold zh_ok in K. set (h := zlib_header s) in *.
  rewrite !andb_true_iff in K. destruct K as (((K1 & K2) & K3) & K4).
  apply Z.eqb_eq in K1. apply Z.leb_le in K2. apply Z.eqb_eq in K3. apply eqb_prop in K4.
  unfold zlib_hdr_bytes. fold h.
  split; [|split; [intros; lia|split; [|intros; lia]]].
  - unfold bytes, msb2. destruct (d_strstart s =? 0); simpl;
      repeat constructor; apply u8_range.
  - intros _. unfold msb2.
    simpl app. rewrite !Znth01_0, !Znth01_1.
    destruct (Z.eqb_spec (d_strstart s) 0) as [E|E].
    + assert (dict = []) by (apply Hd; exact E). subst dict.
      simpl in K4. split; [reflexivity|].
      split; [exact K1|]. split; [exact K2|]. split; [exact K3|].
      split; [|intros C; congruence].
      split; [intros C; destruct (Z.land (u8 (Z.land h 255)) 32 =? 0) eqn:Q;
                [apply Z.eqb_eq in Q; congruence | discriminate] | intros C; congruence].
    + assert (Hne : dict <> []) by (intros C; apply E, Hd, C).
      simpl in K4.
      split; [destruct dict; [congruence|reflexivity]|].
      split; [exact K1|]. split; [exact K2|]. split; [exact K3|].
      split.
      * split; [intros _; exact Hne|intros _].
        destruct (Z.land (u8 (Z.land h 255)) 32 =? 0) eqn:Q; [discriminate|].
        apply Z.eqb_neq in Q. exact Q.
      * intros _. rewrite <- (Ha Hne).
        rewrite sub26. apply be32_msb2_split; exact Hrange.
Qed.

Lemma gzh_u8_bytes : forall l, bytes (map Zlib.proof.huffman.Model.u8 l).
Proof.
  intros l. unfold bytes. apply Forall_map, Forall_forall. intros x _.
  unfold Zlib.proof.huffman.Model.u8. apply Z.mod_pos_bound. lia.
Qed.

Lemma gzh_land255 : forall c, 0 <= Z.land c 255 < 256.
Proof.
  intros c. split.
  - apply Z.land_nonneg. lia.
  - change 255 with (Z.ones 8). rewrite Z.land_ones by lia.
    pose proof (Z.mod_pos_bound c (2^8) ltac:(lia)). simpl in *; lia.
Qed.

Lemma gzh_bytes_app : forall l1 l2, bytes l1 -> bytes l2 -> bytes (l1 ++ l2).
Proof. intros. unfold bytes in *. apply Forall_app; auto. Qed.

Lemma gzh_cstr : forall o, cstr_ok o -> bytes (cstr_bytes o).
Proof.
  intros [l|] H; simpl; [|constructor].
  destruct (H l eq_refl) as (l0 & -> & _ & F).
  apply gzh_bytes_app; [|repeat constructor; lia].
  unfold bytes. eapply Forall_impl; [|exact F]. intros; simpl in *; lia.
Qed.

Lemma gzh_extra : forall h, hdr_ok h -> bytes (gz_extra_bytes h).
Proof.
  intros h Hh. destruct Hh as (_ & _ & _ & _ & _ & Hx & _).
  unfold gz_extra_bytes. destruct (gz_extra h) as [x|] eqn:E; [|constructor].
  apply gzh_bytes_app; [apply gzh_u8_bytes|].
  destruct (Hx x eq_refl) as [_ Bx]. unfold bytes in *.
  unfold sublist. apply Forall_skipn, Forall_firstn. exact Bx.
Qed.

Lemma gz_hdr_good : forall o xfl,
  (forall h, o = Some h -> hdr_ok h) -> (o = None -> 0 <= xfl < 256) ->
  hdr_good [] 2 (gz_hdr_bytes o xfl).
Proof.
  intros o xfl Ho Hx. destruct o as [h|].
  - specialize (Ho h eq_refl).
    assert (Bb : bytes (gz_body h xfl)).
    { unfold gz_body. apply gzh_bytes_app; [apply gzh_u8_bytes|].
      apply gzh_bytes_app; [apply gzh_extra; auto|].
      destruct Ho as (_ & _ & _ & _ & _ & _ & Hn & Hc).
      apply gzh_bytes_app; apply gzh_cstr; auto. }
    assert (Pre : exists r, gz_hdr_bytes (Some h) xfl = gz_pre h xfl ++ r).
    { unfold gz_hdr_bytes, gz_body. rewrite <- !app_assoc. eexists; reflexivity. }
    destruct Pre as [r Er].
    split; [|split; [|split]].
    + unfold gz_hdr_bytes. apply gzh_bytes_app; auto.
      destruct (gz_hcrc h =? 0); [constructor|].
      repeat constructor; apply gzh_land255.
    + intros; lia.
    + intros; lia.
    + intros _. rewrite Er. split.
      * pose proof (Zlength_nonneg r). unfold gz_pre.
        rewrite Zlength_app, Zlength_map, !Zlength_cons, Zlength_nil. lia.
      * unfold gz_pre. cbn [map app]. unfold sublist. reflexivity.
  - specialize (Hx eq_refl). split; [|split; [|split]].
    + simpl. unfold OS_CODE. repeat constructor; lia.
    + intros; lia.
    + intros; lia.
    + intros _. simpl. split; reflexivity.
Qed.

Lemma hdr_good_raw : forall dict, hdr_good dict 0 [].
Proof.
  intros dict. unfold hdr_good. split; [constructor|]. split; [auto|]. split; intros; lia.
Qed.

Lemma xfl_byte_range : forall s, 0 <= xfl_byte s < 256.
Proof.
  intros s. unfold xfl_byte.
  destruct (d_level s =? 9); [lia|]. destruct ((d_strategy s >=? Z_HUFFMAN_ONLY) || (d_level s <? 2)); lia.
Qed.

Lemma chk_ok_nil : forall wrap a, chk_ok wrap [] (hdr_adler wrap a).
Proof.
  intros wrap a. unfold chk_ok, hdr_adler. split; intros ->; vm_compute; reflexivity.
Qed.

Lemma chk_ok_upd : forall wrap D a X,
  chk_ok wrap D a -> bytes D -> bytes X -> chk_ok wrap (D ++ X) (adler_upd wrap a X).
Proof.
  intros wrap D a X [H1 H2] HD HX. unfold chk_ok, adler_upd. split; intros ->; cbn.
  - rewrite (H1 eq_refl). apply Zlib.proof.adler32.Model.ref_adler32_app. apply adler_valid_1.
  - rewrite (H2 eq_refl). apply Zlib.proof.crc32.Combine.ref_crc32_app. apply bytes_is_bytes; auto.
Qed.

Lemma chk_ok_pre : forall wrap D a, chk_ok wrap D a -> bytes D -> adler_pre wrap a.
Proof.
  intros wrap D a [H1 H2] HD. unfold adler_pre. split.
  - intros ->. rewrite (H1 eq_refl).
    apply Zlib.proof.adler32.Model.ref_adler32_valid. apply adler_valid_1.
  - intros ->. rewrite (H2 eq_refl).
    apply Zlib.proof.crc32.Combine.ref_crc32_range. apply bytes_is_bytes; auto.
Qed.

Lemma chk_ok_range : forall wrap D a, 1 <= wrap <= 2 -> chk_ok wrap D a -> bytes D -> 0 <= a < 2 ^ 32.
Proof.
  intros wrap D a Hw [H1 H2] HD. destruct (Z.eq_dec wrap 1) as [->|Hn].
  - rewrite (H1 eq_refl). apply (Zlib.proof.adler32.Model.ref_adler32_valid 1 D adler_valid_1).
  - assert (wrap = 2) as -> by lia. rewrite (H2 eq_refl).
    apply Zlib.proof.crc32.Combine.ref_crc32_range. apply bytes_is_bytes; auto.
Qed.

Lemma radler_range : forall d, 0 <= radler 1 d < 2 ^ 32.
Proof.
  intros d. pose proof (Zlib.proof.adler32.Model.ref_adler32_valid 1 d adler_valid_1) as [H _]. exact H.
Qed.

Lemma trailer_bytes : forall wrap a t, bytes (trailer wrap a t).
Proof.
  intros wrap a t. unfold trailer, msb2, bytes.
  assert (U : forall x, 0 <= u8 x < 256) by (intros; unfold u8; apply Z.mod_pos_bound; lia).
  destruct (wrap =? 1); [|destruct (wrap =? 2)]; cbn [map app];
    repeat constructor; apply U.
Qed.

Lemma Zlength_trailer : forall wrap a t,
  Zlength (trailer wrap a t) = (if wrap =? 1 then 4 else if wrap =? 2 then 8 else 0).
Proof.
  intros wrap a t. unfold trailer. destruct (wrap =? 1); [reflexivity|]. destruct (wrap =? 2); reflexivity.
Qed.

(** Helpers of [final_ok_of]. *)
Lemma fo_land255 : forall x, Z.land x 255 = x mod 256.
Proof. intros. apply (Z.land_ones x 8). lia. Qed.

Lemma fo_land65535 : forall x, Z.land x 65535 = x mod 65536.
Proof. intros. apply (Z.land_ones x 16). lia. Qed.

Lemma fo_be32 : forall a, 0 <= a < 2 ^ 32 ->
  be32 (msb2 (u32 (Z.shiftr a 16)) ++ msb2 (u32 (Z.land a 65535))) = a.
Proof.
  intros a Ha. unfold msb2, be32, u8, u32. rewrite fo_land65535, !fo_land255.
  rewrite !Z.shiftr_div_pow2 by lia. cbn [app]. repeat (rewrite Znth_0_cons || (rewrite Znth_pos_cons by lia; cbn [Z.sub])).
  change (2 ^ 16) with 65536. change (2 ^ 8) with 256.
  assert (Hq : 0 <= a / 65536 < 65536) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  assert (Hr : 0 <= a mod 65536 < 65536) by (apply Z.mod_pos_bound; lia).
  rewrite (Z.mod_small (a / 65536)) by lia. rewrite (Z.mod_small (a mod 65536) 4294967296) by lia.
  rewrite (Z.mod_small ((a / 65536) / 256)) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  rewrite (Z.mod_small ((a mod 65536) / 256)) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  rewrite !Z.mod_mod by lia.
  pose proof (Z.div_mod a 65536 ltac:(lia)).
  pose proof (Z.div_mod (a / 65536) 256 ltac:(lia)).
  pose proof (Z.div_mod (a mod 65536) 256 ltac:(lia)).
  lia.
Qed.

Lemma fo_le32 : forall x,
  le32 (map u8 [Z.land x 255; Z.land (Z.shiftr x 8) 255; Z.land (Z.shiftr x 16) 255;
                Z.land (Z.shiftr x 24) 255]) = x mod 4294967296.
Proof.
  intros x. unfold le32, u8. rewrite !fo_land255, !Z.shiftr_div_pow2 by lia.
  cbn [map]. repeat (rewrite Znth_0_cons || (rewrite Znth_pos_cons by lia; cbn [Z.sub])). rewrite !Z.mod_mod by lia.
  change 4294967296 with (256 * (256 * (256 * 256))).
  rewrite !Z.rem_mul_r by lia. rewrite !Z.div_div by lia.
  change (2 ^ 8) with 256. change (2 ^ 16) with (256 * 256). change (2 ^ 24) with (256 * (256 * 256)).
  change (256 * 256 * 256) with 16777216. change (256 * (256 * 256)) with 16777216. change (256 * 256) with 65536.
  lia.
Qed.

Lemma fo_trailer_bytes : forall wrap a t, bytes (trailer wrap a t).
Proof.
  intros. unfold trailer, bytes, msb2, u8.
  destruct (wrap =? 1); [| destruct (wrap =? 2)]; cbn [map app];
    repeat constructor; try apply Z.mod_pos_bound; lia.
Qed.

(** What deflate_api checks, from the header, any body, the trailer. *)
Lemma final_ok_of : forall dict wrap D H body a t,
  0 <= wrap <= 2 -> hdr_good dict wrap H -> bytes body -> bytes D -> chk_ok wrap D a ->
  (wrap = 2 -> t = Zlength D) ->
  final_ok dict wrap D (H ++ body ++ trailer wrap a t) a.
Proof.
  intros dict wrap D H body a t Hw Hg Hb HD Hc Ht.
  destruct Hg as (HgB & _ & Hg1 & Hg2). destruct Hc as (Hc1 & Hc2).
  pose proof (Zlength_nonneg H) as HnH. pose proof (Zlength_nonneg body) as HnB.
  assert (HB : bytes (H ++ body ++ trailer wrap a t))
    by (apply Forall_app; split; [auto | apply Forall_app; split; [auto | apply fo_trailer_bytes]]).
  rewrite app_assoc. rewrite app_assoc in HB.
  assert (HZ : forall T, Zlength ((H ++ body) ++ T) = Zlength H + Zlength body + Zlength T)
    by (intros; rewrite !Zlength_app; lia).
  assert (Hlast : forall T, sublist (Zlength ((H ++ body) ++ T) - Zlength T) (Zlength ((H ++ body) ++ T))
                             ((H ++ body) ++ T) = T).
  { intros. pose proof (Zlength_nonneg T).
    rewrite sublist_app2 by (rewrite !Zlength_app; lia).
    apply sublist_same; rewrite !Zlength_app; lia. }
  assert (Hlast' : forall (P T : list Z), sublist (Zlength (P ++ T) - Zlength T) (Zlength (P ++ T)) (P ++ T) = T).
  { intros. pose proof (Zlength_nonneg T). pose proof (Zlength_nonneg P).
    rewrite sublist_app2 by (rewrite !Zlength_app; lia).
    apply sublist_same; rewrite !Zlength_app; lia. }
  assert (Hpre : forall T i, 0 <= i < Zlength H -> Znth i ((H ++ body) ++ T) = Znth i H)
    by (intros; rewrite <- app_assoc, app_Znth1 by lia; reflexivity).
  assert (Hpres : forall T i j, 0 <= i <= j -> j <= Zlength H -> sublist i j ((H ++ body) ++ T) = sublist i j H)
    by (intros; rewrite <- app_assoc, sublist_app1 by lia; reflexivity).
  split; [exact HB | split].
  - intros ->. destruct (Hg1 eq_refl) as (HL & H0 & H1 & H2 & H3 & H4). specialize (Hc1 eq_refl).
    assert (Ha : 0 <= a < 2 ^ 32).
    { subst a. destruct (Zlib.proof.adler32.Model.ref_adler32_valid 1 D) as [? _]; [| lia].
      unfold Zlib.proof.adler32.Model.adler_valid, Zlib.proof.adler32.Model.adler_lo,
        Zlib.proof.adler32.Model.adler_hi, Zlib.proof.adler32.Model.ADLER_BASE. cbn. lia. }
    unfold trailer. rewrite Z.eqb_refl.
    set (T := msb2 (u32 (Z.shiftr a 16)) ++ msb2 (u32 (Z.land a 65535))).
    assert (HT : Zlength T = 4) by reflexivity.
    assert (HHL : 2 <= Zlength H) by (destruct dict; lia).
    rewrite !Hpre by lia.
    split; [exact Hc1 |]. split; [rewrite HZ; destruct dict; lia |].
    do 4 (split; [assumption |]). split.
    + intros Hd. rewrite Hpres; [apply H4; exact Hd | lia | destruct dict; [congruence | lia]].
    + rewrite <- HT at 1. rewrite Hlast. apply fo_be32. exact Ha.
  - intros ->. destruct (Hg2 eq_refl) as (HL & H0). specialize (Hc2 eq_refl). specialize (Ht eq_refl).
    assert (Ha : 0 <= a < 4294967296).
    { subst a. apply (Zlib.proof.crc32.Combine.ref_crc32_range 0 D). eapply Forall_impl; [| exact HD].
      intros b Hb'. cbv beta in Hb'. change Integers.Byte.max_unsigned with 255. lia. }
    unfold trailer. cbn [Z.eqb Pos.eqb].
    set (A4 := map u8 [Z.land a 255; Z.land (Z.shiftr a 8) 255; Z.land (Z.shiftr a 16) 255;
                       Z.land (Z.shiftr a 24) 255]).
    set (T4 := map u8 [Z.land t 255; Z.land (Z.shiftr t 8) 255; Z.land (Z.shiftr t 16) 255;
                       Z.land (Z.shiftr t 24) 255]).
    change (map u8 _) with (A4 ++ T4).
    assert (HA4 : Zlength A4 = 4) by reflexivity. assert (HT4 : Zlength T4 = 4) by reflexivity.
    split; [exact Hc2 |]. split; [rewrite HZ, Zlength_app; lia |].
    split; [rewrite Hpres by lia; exact H0 |].
    split.
    + replace (Zlength ((H ++ body) ++ A4 ++ T4) - 8) with (Zlength (H ++ body)) by (rewrite HZ, !Zlength_app; lia).
      replace (Zlength ((H ++ body) ++ A4 ++ T4) - 4) with (Zlength (H ++ body) + 4) by (rewrite HZ, !Zlength_app; lia).
      rewrite sublist_app2 by (rewrite Zlength_app; lia). rewrite Z.sub_diag, Z.add_simpl_l.
      rewrite sublist_app1 by lia. rewrite sublist_same by lia.
      subst A4. rewrite fo_le32. apply Z.mod_small. lia.
    + rewrite app_assoc. rewrite <- HT4 at 1. rewrite (Hlast' ((H ++ body) ++ A4) T4).
      subst T4. rewrite fo_le32. subst t. reflexivity.
Qed.
