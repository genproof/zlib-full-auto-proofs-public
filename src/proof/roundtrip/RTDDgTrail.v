(* RT-D part DEFLATE, stage 9 of deflate(): the trailer keeps KMid, and at Z_STREAM_END the output
   is the whole stream (RTFinal.dfinal) (design: RTDDgDefs.v). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDDgDefs.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** Bits and bytes *)
Lemma tt_bits_le_len : forall v n, 0 <= n -> Zlength (F.bits_le v n) = n.
Proof. intros. unfold F.bits_le. rewrite Zlength_map, Zlength_correct, seq_length. lia. Qed.

Lemma tt_bits_le_len' : forall v n, Zlength (F.bits_le v n) = Z.max 0 n.
Proof. intros. unfold F.bits_le. rewrite Zlength_map, Zlength_correct, seq_length. lia. Qed.

Lemma tt_bytes_bits_app : forall l1 l2, F.bytes_bits (l1 ++ l2) = F.bytes_bits l1 ++ F.bytes_bits l2.
Proof. intros. unfold F.bytes_bits. apply flat_map_app. Qed.

Lemma tt_bytes_bits_len : forall l, Zlength (F.bytes_bits l) = 8 * Zlength l.
Proof.
  induction l as [|b r IH]; [reflexivity|].
  change (F.bytes_bits (b :: r)) with (F.bits_le b 8 ++ F.bytes_bits r).
  rewrite Zlength_app, IH, tt_bits_le_len, Zlength_cons by lia. lia.
Qed.

Lemma tt_bval_bound : forall l, 0 <= F.bval l < 2 ^ Zlength l.
Proof.
  induction l as [|b r IH]; simpl.
  - rewrite ?Zlength_nil. simpl. lia.
  - rewrite Zlength_cons, Z.pow_succ_r by (pose proof (Zlength_nonneg r); lia).
    destruct b; simpl; lia.
Qed.

Lemma tt_bits_le_bval : forall l, F.bits_le (F.bval l) (Zlength l) = l.
Proof.
  intros l. unfold F.bits_le. rewrite ZtoNat_Zlength.
  induction l as [|b r IH]; [reflexivity|].
  simpl length. cbn [seq map]. rewrite <- seq_shift, map_map. cbn [F.bval]. f_equal.
  - destruct b; simpl.
    + rewrite Z.add_comm. apply Z.testbit_odd_0.
    + rewrite Z.add_0_l. apply Z.testbit_even_0.
  - rewrite <- IH at 2. apply map_ext. intros i.
    rewrite Nat2Z.inj_succ. destruct b; simpl.
    + rewrite Z.add_comm. apply Z.testbit_odd_succ. lia.
    + rewrite Z.add_0_l. apply Z.testbit_even_succ. lia.
Qed.

Lemma tt_bval_byte : forall b, 0 <= b < 256 -> F.bval (F.bits_le b 8) = b.
Proof.
  intros b Hb.
  assert (H: forallb (fun b => F.bval (F.bits_le b 8) =? b) (map Z.of_nat (seq 0 256)) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in H.
  specialize (H b). rewrite Z.eqb_eq in H. apply H.
  replace b with (Z.of_nat (Z.to_nat b)) by lia. apply in_map. apply in_seq. lia.
Qed.

Lemma tt_pack_aux : forall bs n n0 s, Zlength bs = 8 * n -> (s + n0 <= Z.to_nat n)%nat ->
  F.bytes_bits (map (fun k => F.bval (sublist (8 * Z.of_nat k) (8 * Z.of_nat k + 8) bs)) (seq s n0)) =
  sublist (8 * Z.of_nat s) (8 * Z.of_nat (s + n0)) bs.
Proof.
  intros bs n n0. induction n0 as [|n0 IH]; intros s Hl Hs.
  - rewrite Nat.add_0_r, sublist_nil. reflexivity.
  - cbn [seq map].
    match goal with |- F.bytes_bits (?x :: ?r) = _ =>
      change (F.bytes_bits (x :: r)) with (F.bits_le x 8 ++ F.bytes_bits r) end.
    rewrite IH by lia.
    set (L := sublist (8 * Z.of_nat s) (8 * Z.of_nat s + 8) bs).
    assert (HL: Zlength L = 8) by (unfold L; rewrite Zlength_sublist; lia).
    pose proof (tt_bits_le_bval L) as HB. rewrite HL in HB. rewrite HB. unfold L.
    replace (8 * Z.of_nat (S s)) with (8 * Z.of_nat s + 8) by lia.
    replace (S s + n0)%nat with (s + S n0)%nat by lia.
    apply sublist_rejoin; lia.
Qed.

Lemma tt_pack_bits : forall bs, Zlength bs mod 8 = 0 -> F.bytes_bits (F.pack bs) = bs.
Proof.
  intros bs H. unfold F.pack. pose proof (Zlength_nonneg bs).
  set (n := Zlength bs / 8).
  assert (Hn: Zlength bs = 8 * n) by (unfold n; pose proof (Z.div_mod (Zlength bs) 8 ltac:(lia)); lia).
  replace ((Zlength bs + 7) / 8) with n.
  2: { rewrite Hn. replace (8 * n + 7) with (7 + n * 8) by ring. rewrite Z.div_add by lia. reflexivity. }
  rewrite (tt_pack_aux bs n (Z.to_nat n) 0) by lia.
  apply sublist_same; lia.
Qed.

Lemma tt_pack_bytes : forall bs, Zlength bs mod 8 = 0 -> bytes (F.pack bs).
Proof.
  intros bs H. unfold F.pack, bytes. pose proof (Zlength_nonneg bs).
  set (n := Zlength bs / 8).
  assert (Hn: Zlength bs = 8 * n) by (unfold n; pose proof (Z.div_mod (Zlength bs) 8 ltac:(lia)); lia).
  replace ((Zlength bs + 7) / 8) with n.
  2: { rewrite Hn. replace (8 * n + 7) with (7 + n * 8) by ring. rewrite Z.div_add by lia. reflexivity. }
  apply Forall_forall. intros x Hx. apply in_map_iff in Hx as (k & <- & Hk). apply in_seq in Hk.
  set (L := sublist (8 * Z.of_nat k) (8 * Z.of_nat k + 8) bs).
  assert (HL: Zlength L = 8) by (unfold L; rewrite Zlength_sublist; lia).
  pose proof (tt_bval_bound L) as HB. rewrite HL in HB. change (2 ^ 8) with 256 in HB. exact HB.
Qed.

Lemma tt_bytes_bits_inj : forall l l', bytes l -> bytes l' -> F.bytes_bits l = F.bytes_bits l' -> l = l'.
Proof.
  induction l as [|a l IH]; intros l' Bl Bl' E; destruct l' as [|b l'].
  - reflexivity.
  - apply (f_equal (@Zlength bool)) in E. rewrite !tt_bytes_bits_len, Zlength_nil, Zlength_cons in E.
    pose proof (Zlength_nonneg l'). lia.
  - apply (f_equal (@Zlength bool)) in E. rewrite !tt_bytes_bits_len, Zlength_nil, Zlength_cons in E.
    pose proof (Zlength_nonneg l). lia.
  - change (F.bytes_bits (a :: l)) with (F.bits_le a 8 ++ F.bytes_bits l) in E.
    change (F.bytes_bits (b :: l')) with (F.bits_le b 8 ++ F.bytes_bits l') in E.
    apply app_eq_len_eq in E as [E1 E2];
      [|unfold F.bits_le; rewrite !map_length; reflexivity].
    unfold bytes in Bl, Bl'.
    inversion Bl as [|x y Ba Bl0]; subst. inversion Bl' as [|x y Bb Bl0']; subst.
    f_equal; [|apply IH; auto].
    apply (f_equal F.bval) in E1. rewrite !tt_bval_byte in E1 by lia. exact E1.
Qed.

Lemma tt_bytes_app : forall l1 l2, bytes l1 -> bytes l2 -> bytes (l1 ++ l2).
Proof. intros l1 l2 H1 H2. unfold bytes in *. apply Forall_app. auto. Qed.

(** ** The final encoding *)
Lemma tt_enc_from_true : forall BS p, enc_from p BS true = F.enc_blocks p BS.
Proof.
  induction BS as [|b r IH]; intros p; [reflexivity|].
  cbn [enc_from F.enc_blocks]. rewrite IH. destruct r; reflexivity.
Qed.

Lemma tt_enc_out : forall BS, enc_out 0 BS true = F.deflate_bits BS.
Proof. intros BS. unfold enc_out, F.deflate_bits. rewrite tt_enc_from_true. reflexivity. Qed.

Lemma tt_deflate_bits_len : forall BS, Zlength (F.deflate_bits BS) mod 8 = 0.
Proof.
  intros BS. unfold F.deflate_bits, F.zeros, F.pad8. rewrite Zlength_app, (Zlength_correct (repeat _ _)), repeat_length.
  set (e := Zlength (F.enc_blocks 0 BS)). pose proof (Zlength_nonneg (F.enc_blocks 0 BS)).
  assert (0 <= (8 - e mod 8) mod 8 < 8) by (apply Z.mod_pos_bound; lia).
  rewrite Z2Nat.id by lia.
  pose proof (Z.mod_pos_bound e 8 ltac:(lia)).
  destruct (Z.eq_dec (e mod 8) 0) as [E|E].
  - rewrite E. change ((8 - 0) mod 8) with 0. rewrite Z.add_0_r. exact E.
  - rewrite (Z.mod_small (8 - e mod 8)) by lia.
    replace (e + (8 - e mod 8)) with ((e / 8 + 1) * 8) by (pose proof (Z.div_mod e 8 ltac:(lia)); lia).
    apply Z.mod_mul. lia.
Qed.

Lemma tt_deflate_bytes_bits : forall BS, F.bytes_bits (F.deflate_bytes BS) = F.deflate_bits BS.
Proof. intros. unfold F.deflate_bytes. apply tt_pack_bits, tt_deflate_bits_len. Qed.

Lemma tt_deflate_bytes_ok : forall BS, bytes (F.deflate_bytes BS).
Proof. intros. unfold F.deflate_bytes. apply tt_pack_bytes, tt_deflate_bits_len. Qed.

(* the bits of a finished stream are whole bytes: the header then the deflate bytes, nothing in the bit buffer *)
Lemma tt_fin_bytes : forall O HDR BS bb, bytes O -> bytes HDR ->
  Zlength bb <= 7 ->
  F.bytes_bits O ++ bb = F.bytes_bits HDR ++ enc_out 0 BS true -> bb = [] /\ O = HDR ++ F.deflate_bytes BS.
Proof.
  intros O HDR BS bb HO HH Hl E.
  rewrite tt_enc_out, <- tt_deflate_bytes_bits, <- tt_bytes_bits_app in E.
  assert (Hb : bb = []).
  { apply (f_equal (@Zlength bool)) in E. rewrite Zlength_app, !tt_bytes_bits_len in E.
    pose proof (Zlength_nonneg bb).
    assert (Zlength bb = 0) by lia. apply Zlength_nil_inv. lia. }
  subst bb. rewrite app_nil_r in E. split; [reflexivity|].
  apply tt_bytes_bits_inj; auto. apply tt_bytes_app; auto. apply tt_deflate_bytes_ok.
Qed.

(** ** The trailer *)
Lemma tt_le4 : forall v, F.le_bytes v 4 = [v mod 256; v / 256 mod 256; v / 65536 mod 256; v / 16777216 mod 256].
Proof.
  intros v. unfold F.le_bytes. change (seq 0 (Z.to_nat 4)) with [0; 1; 2; 3]%nat. cbn [map].
  rewrite !Z.shiftr_div_pow2 by lia.
  change (2 ^ (8 * Z.of_nat 0)) with 1. change (2 ^ (8 * Z.of_nat 1)) with 256.
  change (2 ^ (8 * Z.of_nat 2)) with 65536. change (2 ^ (8 * Z.of_nat 3)) with 16777216.
  rewrite Z.div_1_r. reflexivity.
Qed.

Lemma tt_divmod : forall t k m, 0 < k -> 0 < m -> (t mod (k * m * 256)) / k mod 256 = t / k mod 256.
Proof.
  intros t k m Hk Hm.
  rewrite (Z.div_mod t (k * m * 256)) at 2 by lia.
  set (q := t / (k * m * 256)). set (r := t mod (k * m * 256)).
  replace (k * m * 256 * q + r) with (r + (m * q * 256) * k) by ring.
  rewrite Z.div_add by lia. rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma tt_mm : forall t M k, 0 < k -> 0 < M -> M mod (k * 256) = 0 -> (t mod M) / k mod 256 = t / k mod 256.
Proof.
  intros t M k Hk HM Hd.
  pose proof (Z.div_mod M (k * 256) ltac:(lia)) as E. rewrite Hd, Z.add_0_r in E.
  assert (Hp : 0 < M / (k * 256)) by nia.
  replace M with (k * (M / (k * 256)) * 256) at 1 by lia.
  apply tt_divmod; lia.
Qed.

Lemma tt_mm1 : forall t M, 0 < M -> M mod 256 = 0 -> t mod M mod 256 = t mod 256.
Proof.
  intros t M HM Hd. pose proof (tt_mm t M 1 ltac:(lia) HM ltac:(rewrite Z.mul_1_l; exact Hd)) as E.
  rewrite !Z.div_1_r in E. exact E.
Qed.

Lemma tt_land255 : forall x, Z.land x 255 = x mod 256.
Proof. intros. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. Qed.

Ltac tt_mm_solve :=
  repeat first [ rewrite tt_mm by (first [lia | reflexivity]) | rewrite tt_mm1 by (first [lia | reflexivity])
               | rewrite Z.div_div by lia ].

Lemma tt_trailer2 : forall a t,
  map u8 [Z.land a 255; Z.land (Z.shiftr a 8) 255; Z.land (Z.shiftr a 16) 255; Z.land (Z.shiftr a 24) 255;
          Z.land t 255; Z.land (Z.shiftr t 8) 255; Z.land (Z.shiftr t 16) 255; Z.land (Z.shiftr t 24) 255] =
  F.le_bytes a 4 ++ F.le_bytes (t mod 2 ^ 32) 4.
Proof.
  intros a t. rewrite !tt_le4. unfold u8. cbn [map app].
  rewrite !tt_land255, !Z.shiftr_div_pow2 by lia. rewrite !Z.mod_mod by lia.
  change (2 ^ 8) with 256. change (2 ^ 16) with 65536. change (2 ^ 24) with 16777216.
  change (2 ^ 32) with 4294967296.
  tt_mm_solve. reflexivity.
Qed.

Lemma tt_trailer1 : forall a,
  msb2 (u32 (Z.shiftr a 16)) ++ msb2 (u32 (Z.land a 65535)) = F.be_bytes a 4.
Proof.
  intros a. unfold F.be_bytes. rewrite tt_le4. unfold msb2, u8, u32. cbn [rev app].
  rewrite !tt_land255, !Z.shiftr_div_pow2 by lia.
  change 65535 with (Z.ones 16). rewrite Z.land_ones by lia.
  change (2 ^ 8) with 256. change (2 ^ 16) with 65536.
  tt_mm_solve. reflexivity.
Qed.

Lemma tt_trailer : forall wrap D a t, 1 <= wrap <= 2 -> chk_ok wrap D a -> (wrap = 2 -> t = Zlength D) ->
  trailer wrap a t = ftrailer wrap D.
Proof.
  intros wrap D a t Hw [H1 H2] Ht. unfold trailer, ftrailer.
  destruct (Z.eqb_spec wrap 1) as [E1|E1].
  - rewrite (H1 E1). apply tt_trailer1.
  - assert (E2 : wrap = 2) by lia. rewrite E2. cbn [Z.eqb Pos.eqb].
    rewrite (H2 E2), (Ht E2). apply tt_trailer2.
Qed.

(** ** The header *)
Lemma tt_le_bytes_ok : forall v n, bytes (F.le_bytes v n).
Proof.
  intros v n. unfold F.le_bytes, bytes. apply Forall_forall. intros x Hx.
  apply in_map_iff in Hx as (i & <- & _). apply Z.mod_pos_bound. lia.
Qed.

Lemma tt_be_bytes_ok : forall v n, bytes (F.be_bytes v n).
Proof. intros. unfold F.be_bytes, bytes. apply Forall_rev. apply tt_le_bytes_ok. Qed.

Lemma tt_cstr_bytes : forall o, cstr_ok o ->
  bytes (match option_map (@removelast Z) o with Some n => n ++ [0] | None => [] end).
Proof.
  intros [l|] H; cbn [option_map]; [|constructor].
  destruct (H l eq_refl) as (l0 & -> & _ & Hb). rewrite removelast_last.
  apply tt_bytes_app; [|repeat constructor; lia].
  unfold bytes. eapply Forall_impl; [|exact Hb]. cbv beta. lia.
Qed.

Lemma tt_gz_bytes_ok : forall gh xfl, (forall h, gh = Some h -> hdr_ok h) -> 0 <= xfl < 256 ->
  bytes (F.gz_bytes (fhdr_of gh xfl)).
Proof.
  intros gh xfl Hh Hx.
  assert (B0 : bytes (F.gz_bytes0 (fhdr_of gh xfl))).
  { unfold F.gz_bytes0.
    assert (Hflg : 0 <= F.gz_flg (fhdr_of gh xfl) < 256).
    { unfold F.gz_flg. destruct (F.gz_text _), (F.gz_hcrc _), (F.gz_extra _), (F.gz_name _), (F.gz_comment _); lia. }
    apply tt_bytes_app; [repeat constructor; lia|].
    apply tt_bytes_app; [apply tt_le_bytes_ok|].
    destruct gh as [h|]; cbn [fhdr_of F.gz_xfl F.gz_os F.gz_extra F.gz_name F.gz_comment].
    - destruct (Hh h eq_refl) as (_ & _ & _ & _ & _ & Hex & Hn & Hc).
      apply tt_bytes_app.
      { repeat constructor; try lia; [apply Z.land_nonneg; lia|].
        rewrite tt_land255. apply Z.mod_pos_bound; lia. }
      apply tt_bytes_app.
      { destruct (DS.gz_extra h) as [x|] eqn:Ex; cbn [option_map]; [|constructor].
        apply tt_bytes_app; [apply tt_le_bytes_ok|]. apply Forall_sublist. exact (proj2 (Hex x eq_refl)). }
      apply tt_bytes_app; apply tt_cstr_bytes; assumption.
    - repeat constructor; lia. }
  unfold F.gz_bytes. destruct (F.gz_hcrc _); [|exact B0].
  apply tt_bytes_app; [exact B0|apply tt_le_bytes_ok].
Qed.

Lemma tt_khdr_bytes : forall dict wrap s HDR, 0 <= wrap <= 2 -> 9 <= d_w_bits s <= 15 ->
  (forall h, d_gzhead s = Some h -> hdr_ok h) -> khdr dict wrap s HDR -> bytes HDR.
Proof.
  intros dict wrap s HDR Hw Hwb Hh Hk. unfold khdr in Hk.
  destruct (Z.eqb_spec wrap 0) as [E0|E0]; [subst HDR; constructor|].
  destruct (Z.eqb_spec wrap 1) as [E1|E1].
  - destruct Hk as (flg & (Hf & _) & ->).
    apply tt_bytes_app; [unfold zcmf; repeat constructor; lia|].
    destruct dict; [constructor|apply tt_be_bytes_ok].
  - destruct Hk as (xfl & Hx & ->). apply tt_gz_bytes_ok; [exact Hh|lia].
Qed.

Lemma tt_khdr_eq : forall dict wrap s s' HDR, d_w_bits s' = d_w_bits s -> d_gzhead s' = d_gzhead s ->
  khdr dict wrap s HDR -> khdr dict wrap s' HDR.
Proof. intros dict wrap s s' HDR E1 E2. unfold khdr. rewrite E1, E2. auto. Qed.

(** ** The end: the whole stream *)
Lemma tt_dfinal : forall dict wrap s D BS HDR O, 0 <= wrap <= 2 -> 9 <= d_w_bits s <= 15 ->
  (wrap = 2 -> dict = []) -> (wrap <> 2 -> d_gzhead s = None) -> bytes dict -> BS <> [] ->
  F.blocks_ok (2 ^ d_w_bits s) dict BS -> F.data dict BS = D -> khdr dict wrap s HDR ->
  O = HDR ++ F.deflate_bytes BS ++ ftrailer wrap D ->
  dfinal dict wrap (d_w_bits s) (d_gzhead s) D O.
Proof.
  intros dict wrap s D BS HDR O Hw Hwb Hd Hg Hbd HBS Hok Hdat Hk HO.
  split; [exact Hwb|]. exists BS. split; [split; [exact HBS|split; [exact Hbd|exact Hok]]|].
  split; [exact Hdat|]. unfold khdr in Hk.
  assert (Hw3 : wrap = 0 \/ wrap = 1 \/ wrap = 2) by lia.
  destruct Hw3 as [Ew|[Ew|Ew]]; subst wrap; cbn [Z.eqb Pos.eqb] in Hk.
  - subst HDR. rewrite HO. unfold ftrailer. cbn [Z.eqb Pos.eqb]. rewrite app_nil_r. reflexivity.
  - split; [apply Hg; lia|]. destruct Hk as (flg & Hf & EH). subst HDR. exists flg. split; [exact Hf|].
    rewrite HO. unfold ftrailer. cbn [Z.eqb Pos.eqb]. rewrite <- !app_assoc. reflexivity.
  - specialize (Hd eq_refl). subst dict. split; [reflexivity|].
    destruct Hk as (xfl & Hx & EH). subst HDR. exists xfl. split; [exact Hx|].
    rewrite HO. unfold F.stream_bytes. rewrite Hdat. unfold ftrailer. cbn [Z.eqb Pos.eqb]. reflexivity.
Qed.

Lemma kf_trailer_ok : writer_fspec -> fpend_fspec2 ->
  forall dict wrap D O inb aout tin tout flush s z s4 z4 c,
  Mid W3 hinv dict wrap D O inb aout tin tout flush s z ->
  KMid dict wrap D O inb s z ->
  d_pending s = 0 -> 0 <= flush <= 5 -> aout <= 2097152 ->
  (flush = Z_FINISH -> d_status s = FINISH_STATE) ->
  (d_status s = BUSY_STATE \/ (d_status s = FINISH_STATE /\ z_avail_in z = 0)) ->
  c_deflate_trailer s z flush = Some (s4, z4, c) ->
  d_w_bits s4 = d_w_bits s /\
  (c <> Z_STREAM_END -> KMid dict wrap D O inb s4 z4) /\
  (c = Z_STREAM_END ->
   dfinal dict wrap (d_w_bits s) (d_gzhead s) (D ++ sublist 0 (z_next_in z4) inb) (O ++ z_out z4)).
Proof.
  intros _ _ dict wrap D O inb aout tin tout flush s z s4 z4 c HM HK Hpd Hfl Haout Hfs Hst Hrun.
  unfold c_deflate_trailer in Hrun.
  destruct (Z.eqb_spec flush Z_FINISH) as [EF|NF].
  2: { cbn [negb] in Hrun. injection Hrun as E1 E2 E3. subst s4 z4 c.
       split; [reflexivity|]. split; [intros _; exact HK|]. intros E. discriminate E. }
  subst flush. cbn [negb] in Hrun. specialize (Hfs eq_refl).
  assert (Hai0 : z_avail_in z = 0).
  { destruct Hst as [Hst|[_ Hst]]; [|exact Hst]. rewrite Hfs in Hst. unfold FINISH_STATE, BUSY_STATE in Hst. lia. }
  clear Hst.
  destruct HM as (Hz & Hsz1 & Hsz2 & HIa).
  pose proof Hz as Hz0.
  destruct Hz as (Hzin & Hni & Hai & Hti & Hao & Hzo & Hto & Hbo).
  destruct HIa as (HWs & Hos & Hwr & Hw2 & Hbd & Hld & Hlf & Hgz & Htout & HbO & HbD & Htin & Hfin & Hdz & Hph).
  destruct Hph as [H0 | [Hlf2 [H1 | [H2 | H3]]]].
  { exfalso. destruct H0 as [[[Hs _]|[Hs _]] _]; rewrite Hfs in Hs; unfold FINISH_STATE, INIT_STATE, GZIP_STATE in Hs; lia. }
  { exfalso. destruct H1 as (_ & _ & _ & _ & _ & H & k & HIk & _).
    destruct (hf_status hinv hinv_facts _ _ _ _ HIk) as (_ & _ & Hs & _). rewrite Hfs in Hs.
    unfold FINISH_STATE, EXTRA_STATE, NAME_STATE, COMMENT_STATE, HCRC_STATE in Hs; lia. }
  { exfalso. destruct H2 as (Hs & _). rewrite Hfs in Hs. unfold FINISH_STATE, BUSY_STATE in Hs. lia. }
  destruct H3 as (_ & Hla & Hsy & Hbv & _ & Hchk & _).
  destruct HK as [[Hgn (BS & syms & Hkc & Hcase)] _].
  destruct Hcase as [(_ & Hs & _)|[[Hs _]|(_ & HBS & Hdat & HDR & Hkh & Hcase)]];
    [exact (False_ind _ (Hs Hfs))|rewrite Hfs in Hs; unfold FINISH_STATE, BUSY_STATE in Hs; lia|].
  set (D' := D ++ sublist 0 (z_next_in z) inb) in *. set (O' := O ++ z_out z) in *.
  pose proof (W3_prm s HWs) as Hprm.
  assert (Hwb : 9 <= d_w_bits s <= 15) by (destruct Hprm as (Hw & _); exact Hw).
  pose proof (tk_pend_nil s Hpd) as Hpn.
  assert (HbH : bytes HDR) by (eapply tt_khdr_bytes; eauto).
  assert (Hbl : F.blocks_ok (2 ^ d_w_bits s) dict BS) by (destruct Hkc as ((_ & _ & _ & X & _) & _); exact X).
  assert (Hbv0 : 0 <= d_bi_valid s) by (destruct Hos as (_ & (X & _) & _); exact (proj1 X)).
  assert (Hfb : d_wrap s = wrap -> allbits O' s = F.bytes_bits HDR ++ enc_out 0 BS true ->
                d_bi_valid s = 0 /\ O' = HDR ++ F.deflate_bytes BS).
  { intros _ Hab. unfold allbits in Hab. rewrite Hpn, app_nil_r in Hab.
    destruct (tt_fin_bytes O' HDR BS (bibits s) HbO HbH) as [Hb0 HO]; auto.
    { unfold bibits. rewrite tt_bits_le_len by lia. lia. }
    split; [|exact HO].
    unfold bibits in Hb0. apply (f_equal (@Zlength bool)) in Hb0. rewrite tt_bits_le_len in Hb0 by lia.
    exact Hb0. }
  destruct (Z.leb_spec (d_wrap s) 0) as [Hw0|Hw0].
  - cbv iota in Hrun. injection Hrun as E1 E2 E3. subst s4 z4 c.
    split; [reflexivity|]. split; [intros C; exfalso; apply C; reflexivity|]. intros _.
    destruct Hcase as [[Hdw Hab]|(Hwp & Hdw & Hb0 & HO)].
    + destruct (Hfb Hdw Hab) as [_ HO].
      assert (Ew : wrap = 0) by lia.
      eapply tt_dfinal; eauto; try lia. change (O ++ z_out z) with O'. rewrite HO, Ew. unfold ftrailer. cbn [Z.eqb Pos.eqb]. rewrite app_nil_r. reflexivity.
    + rewrite Hpn, app_nil_r in HO. eapply tt_dfinal; eauto.
  - cbv iota in Hrun.
    destruct Hcase as [[Hdw Hab]|(Hwp & Hdw & _)]; [|lia].
    destruct (Hfb Hdw Hab) as [Hb0 HO].
    edestruct (tk_put_trailer s (z_adler z) (z_total_in z)) as (s1 & E1 & Hp1 & Ho1 & Hc1 & Ha1 & Hb1);
      eauto; [lia|].
    rewrite E1 in Hrun. cbn [bind] in Hrun.
    assert (Hzo0 := Zlength_nonneg (z_out z)). assert (HO0 := Zlength_nonneg O).
    unfold O' in Htout. rewrite Zlength_app in Htout.
    edestruct (flush_pending_ok s1 z) as (s' & x & Ef & Hpx & Hlx & Hbx & Ho' & Hc' & Ha' & Hb' & Hpd' & Hpo');
      auto; try lia.
    rewrite Ef in Hrun. cbn [bind] in Hrun.
    assert (Hdw' : d_wrap s' = wrap).
    { destruct Ha1 as (_ & W1 & _), Ha' as (_ & W2 & _). lia. }
    rewrite Hdw' in Hrun. replace (wrap >? 0) with true in Hrun by (symmetry; apply Z.gtb_lt; lia).
    injection Hrun as E4 E5 E6. subst s4 z4.
    destruct Ha1 as (As1 & Aw1 & Ag1 & Ai1 & Al1 & Am1), Ha' as (As2 & Aw2 & Ag2 & Ai2 & Al2 & Am2).
    assert (Hc4 : core_eq s (set_d_wrap s' (- wrap))).
    { eapply core_eq_trans; [exact Hc1|]. eapply core_eq_trans; [exact Hc'|]. apply tk_core_eq_wrap. }
    pose proof (core_eq_fields _ _ Hc4) as (_ & _ & Hwb4 & _).
    split; [exact Hwb4|].
    assert (Htr : trailer wrap (z_adler z) (z_total_in z) = ftrailer wrap D').
    { apply tt_trailer; [lia|exact Hchk|].
      intros E2. specialize (Hw2 E2). subst dict. rewrite Zlength_nil in Htin. lia. }
    assert (Hx : x ++ pend s' = ftrailer wrap D') by (rewrite <- Htr, <- Hdw, <- Hp1; congruence).
    change (d_pending (set_d_wrap s' (- wrap))) with (d_pending s') in E6.
    cbn [z_next_in z_out]. fold D'.
    destruct (Z.eqb_spec (d_pending s') 0) as [P0|P0]; cbn [negb] in E6; subst c.
    + split; [intros C; exfalso; apply C; reflexivity|]. intros _.
      rewrite (tk_pend_nil s' P0), app_nil_r in Hx.
      eapply tt_dfinal; eauto. rewrite app_assoc. fold O'. rewrite HO, Hx, app_assoc. reflexivity.
    + split; [|intros C; discriminate C]. intros _.
      unfold KMid, KFd. cbn [z_next_in z_out]. fold D'.
      split.
      * split; [intros Hn; cbn [d_gzhead set_d_wrap]; rewrite Ag2, Ag1; exact (Hgn Hn)|].
        exists BS, syms. split; [exact (kcore3_frame dict D' BS syms s _ Hc4 Hkc)|].
        right; right. cbn [d_status set_d_wrap]. split; [congruence|].
        split; [exact HBS|]. split; [exact Hdat|]. exists HDR.
        split; [apply (tt_khdr_eq dict wrap s); [exact Hwb4|cbn [d_gzhead set_d_wrap]; congruence|exact Hkh]|].
        right. split; [lia|]. split; [reflexivity|].
        split; [change (d_bi_valid (set_d_wrap s' (- wrap))) with (d_bi_valid s'); lia|].
        change (pend (set_d_wrap s' (- wrap))) with (pend s').
        rewrite app_assoc. fold O'. rewrite <- app_assoc, Hx, HO, <- app_assoc. reflexivity.
      * intros _ Hn. exfalso. apply Hn. cbn [d_status set_d_wrap]. congruence.
Qed.
