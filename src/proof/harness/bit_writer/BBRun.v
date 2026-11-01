(* Law rj_bad_block: the first passes of inflate() over main's stream, computed on the model (Model2.loop2 from
   Spec5.m_init) after inflateInit2_ with a raw window: HEAD goes straight to TYPEDO, which pulls the first byte and
   reads BFINAL and BTYPE; a stored block whose NLEN is not the complement of LEN, BTYPE 11 and a dynamic block with
   HLIT 30/31 are refused (BAD), and the call then returns Z_DATA_ERROR.  Shared by the theory of the law (BBTheory.v)
   and the fact about the output fields after the Z_TREES stop (BBSow.v). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.bit_writer.FRFacts.
Require Import Zlib.proof.harness.bit_writer.BBFacts.
Require Import Zlib.proof.rfc1951.DecKit.
Import ListNotations.
Local Open Scope Z_scope.

(* the state after inflateInit2_(strm, w) for a raw stream: at the header, no wrapper, an empty bit buffer and
   no window *)
Lemma bbt_init sp w : -15 <= w <= -8 ->
  let s := l_s (init_live sp w) in
  i_mode s = HEAD /\ i_wrap s = 0 /\ i_last s = 0 /\ i_hold s = 0 /\ i_bits s = 0 /\ i_wsize s = 0.
Proof.
  intros Hw.
  assert (w = -15 \/ w = -14 \/ w = -13 \/ w = -12 \/ w = -11 \/ w = -10 \/ w = -9 \/ w = -8) as E by lia.
  repeat destruct E as [E|E]; subst w; repeat split; reflexivity.
Qed.

(* one pass of the loop that does not leave, and one that leaves *)
Lemma bbt_next (flush: Z) (fx dx: list entry) m m' o :
  stepf2 flush fx dx m = IBrk m' -> m_leave m' <> 1 -> loop2 flush fx dx m o -> loop2 flush fx dx m' o.
Proof. intros E N H. inversion H; subst; rewrite E in *; try discriminate; congruence. Qed.

Lemma bbt_last (flush: Z) (fx dx: list entry) m m' o :
  stepf2 flush fx dx m = IBrk m' -> m_leave m' = 1 -> loop2 flush fx dx m o -> o = IBrk m'.
Proof. intros E N H. inversion H; subst; rewrite E in *; try discriminate; congruence. Qed.

Lemma bbt_head (flush: Z) (fx dx: list entry) m :
  m_mode m = HEAD -> i_wrap (m_s m) = 0 -> stepf2 flush fx dx m = IBrk (set_mode m TYPEDO).
Proof.
  intros Hm Hw. unfold stepf2, step2. rewrite Hm. change (HEAD =? HEAD) with true. cbv iota beta.
  unfold c_HEAD2. rewrite Hw. reflexivity.
Qed.

(* the fields of a machine that the first passes of a call read or keep: the mode, the input, the bit buffer,
   nothing written, the return code still Z_OK and no window *)
Record mv (m: mst) (S: list Z) (md nx hold bits lv: Z) : Prop := {
  mv_mode : m_mode m = md; mv_inp : m_inp m = S; mv_nx : m_nx m = nx; mv_hold : m_hold m = hold;
  mv_bits : m_bits m = bits; mv_leave : m_leave m = lv; mv_ow : m_ow m = []; mv_out : m_out m = m_aout m;
  mv_in : m_in m = Zlength S; mv_ret : m_ret m = Z_OK; mv_wsize : i_wsize (m_s m) = 0 }.

Lemma bbt_nbS k n m :
  m_bits m < n -> m_have m <> 0 -> needbits_f (S k) n m = needbits_f k n (pull m).
Proof.
  intros Hb Hh. cbn [needbits_f]. replace (m_bits m <? n) with true by lia.
  replace (m_have m =? 0) with false by lia. reflexivity.
Qed.

Lemma bbt_nb0 k n m : n <= m_bits m -> needbits_f k n m = m.
Proof. intros Hb. destruct k; cbn [needbits_f]; [reflexivity|]. replace (m_bits m <? n) with false by lia. reflexivity. Qed.

Lemma bbt_u32 x : 0 <= x < 2 ^ 32 -> u32 x = x.
Proof. intros. unfold u32. apply Z.mod_small; lia. Qed.

Lemma bbt_u64 x : 0 <= x < 2 ^ 64 -> u64 x = x.
Proof. intros. unfold u64. apply Z.mod_small; lia. Qed.

Ltac bbt_fields :=
  cbn [m_mode m_s m_h m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave m_adler m_msg m_tin m_tout
       m_snx m_sow set_m_s set_m_h set_m_nx set_m_ow set_m_hold set_m_bits set_m_ret set_m_leave set_m_msg
       set_mode set_bad set_leave upd_s pull dropbits bytebits i_mode i_wsize i_last set_i_mode set_i_last
       set_i_lencode set_i_lenbits set_i_distcode set_i_distbits set_i_nlen set_i_ndist set_i_ncode set_i_have
       set_i_length].

Ltac bbt_fields_in H :=
  cbn [m_mode m_s m_h m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave m_adler m_msg m_tin m_tout
       m_snx m_sow set_m_s set_m_h set_m_nx set_m_ow set_m_hold set_m_bits set_m_ret set_m_leave set_m_msg
       set_mode set_bad set_leave upd_s pull dropbits bytebits i_mode i_wsize i_last set_i_mode set_i_last
       set_i_lencode set_i_lenbits set_i_distcode set_i_distbits set_i_nlen set_i_ndist set_i_ncode set_i_have
       set_i_length] in H.

Lemma bbt_byte0 S :
  is_bytes S -> 0 < Zlength S ->
  let B := bytes_bits S in
  Znth 0 S = bval (sublist 0 1 B) + 2 * bval (sublist 1 3 B) + 8 * bval (sublist 3 8 B) /\
  0 <= bval (sublist 0 1 B) <= 1 /\ 0 <= bval (sublist 3 8 B) < 32.
Proof.
  intros Hb Hl B.
  assert (E8 : sublist 0 8 B = bits_le (Znth 0 S) 8).
  { unfold B. pose proof (dkit_bytes_bits_sublist S 0 1 ltac:(lia) ltac:(lia)) as X.
    change (8 * 0) with 0 in X. change (8 * 1) with 8 in X. rewrite X. rewrite (sublist_one 0 1 S) by lia.
    unfold bytes_bits. cbn [flat_map]. apply app_nil_r. }
  assert (LB : Zlength B = 8 * Zlength S) by apply dkit_bytes_bits_len.
  assert (R : forall i j, 0 <= i <= j -> j <= 8 -> sublist i j B = sublist i j (bits_le (Znth 0 S) 8)).
  { intros i j Hi Hj. rewrite <- E8, sublist_sublist by lia. f_equal; lia. }
  assert (H0 : 0 <= Znth 0 S < 256).
  { unfold is_bytes in Hb. rewrite Forall_forall in Hb. specialize (Hb (Znth 0 S) (Znth_In 0 S ltac:(lia))).
    change Byte.max_unsigned with 255 in Hb. lia. }
  rewrite !R by lia.
  set (l := bits_le (Znth 0 S) 8).
  assert (Ll : Zlength l = 8) by (apply dkit_bits_le_len; lia).
  pose proof (dkit_bval_sub_bound l 0 1 ltac:(lia) ltac:(lia)).
  pose proof (dkit_bval_sub_bound l 3 8 ltac:(lia) ltac:(lia)).
  split; [|simpl in *; lia].
  rewrite <- (dkit_bval_byte (Znth 0 S)) at 1 by lia. fold l.
  rewrite <- (sublist_same 0 8 l) at 1 by lia.
  rewrite <- (sublist_rejoin 0 1 8), <- (sublist_rejoin 1 3 8) by lia.
  rewrite !dkit_bval_app, !Zlength_sublist by lia. simpl. lia.
Qed.

(* TYPEDO on an empty bit buffer: one byte x + 2 bt + 8 c is pulled, BFINAL x and BTYPE bt are dropped *)
Lemma bbt_typedo (flush: Z) (fx dx: list entry) m S x bt c :
  mv m S TYPEDO 0 0 0 0 -> i_last (m_s m) = 0 -> 0 < Zlength S ->
  Znth 0 S = x + 2 * bt + 8 * c -> 0 <= x <= 1 -> 0 <= bt <= 3 -> 0 <= c < 32 ->
  exists m', stepf2 flush fx dx m = IBrk m' /\
    mv m' S (if bt =? 0 then STORED else if bt =? 1 then LEN_ else if bt =? 2 then TABLE else BAD) 1 c 5
       (if andb (bt =? 1) (flush =? Z_TREES) then 1 else 0).
Proof.
  intros M Hl Hlen E Hx Hbt Hc.
  assert (E1: stepf2 flush fx dx m = c_TYPEDO flush m) by (unfold stepf2, step2; rewrite (mv_mode _ _ _ _ _ _ _ M); reflexivity).
  rewrite E1. unfold c_TYPEDO. rewrite Hl. change (0 =? 0) with true. cbv beta iota zeta.
  destruct M as [Hm Hi Hn Hh Hb Hlv Ho Hout Hin Hr Hw].
  unfold needbits. rewrite bbt_nbS, bbt_nb0;
    [| bbt_fields; rewrite Hb, bbt_u32 by lia; lia | rewrite Hb; lia | unfold m_have; rewrite Hi, Hn; lia].
  set (b := Znth (m_nx m) (m_inp m)).
  assert (Eb : b = x + 2 * bt + 8 * c) by (unfold b; rewrite Hn, Hi; exact E).
  assert (Lv : m_leave (pull m) =? 1 = false) by (bbt_fields; rewrite Hlv; reflexivity).
  rewrite Lv.
  assert (Hh1 : m_hold (pull m) = x + 2 * bt + 8 * c).
  { bbt_fields. fold b. rewrite Hh, Hb, Eb. unfold u64. rewrite Z.mod_small; lia. }
  assert (Hb1 : m_bits (pull m) = 8) by (bbt_fields; rewrite Hb; reflexivity).
  set (m1 := pull m) in *.
  set (m2 := dropbits 1 _).
  assert (Hh2 : m_hold m2 = bt + 4 * c).
  { unfold m2. bbt_fields. rewrite Hh1, Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2.
    replace (x + 2 * bt + 8 * c) with (x + (bt + 4 * c) * 2) by lia. rewrite Z.div_add by lia.
    rewrite Z.div_small by lia. lia. }
  assert (Hb2 : m_bits m2 = 7) by (unfold m2; bbt_fields; rewrite Hb1; reflexivity).
  assert (Bt : bitsn m2 2 = bt).
  { unfold bitsn. rewrite Hh2. change (2 ^ 2) with 4. replace (bt + 4 * c) with (bt + c * 4) by lia. rewrite Z.mod_add by lia.
    apply Z.mod_small; lia. }
  rewrite Bt.
  assert (Hh3 : Z.shiftr (m_hold m2) 2 = c).
  { rewrite Hh2, Z.shiftr_div_pow2 by lia. change (2 ^ 2) with 4.
    replace (bt + 4 * c) with (bt + c * 4) by lia. rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. }
  assert (Hn2 : m_nx m2 = 1) by (unfold m2, m1; bbt_fields; lia).
  assert (Hi2 : m_inp m2 = S) by (unfold m2, m1; bbt_fields; auto).
  assert (Ho2 : m_ow m2 = []) by (unfold m2, m1; bbt_fields; auto).
  assert (Hout2 : m_out m2 = m_aout m2) by (unfold m2, m1; bbt_fields; auto).
  assert (Hin2 : m_in m2 = Zlength S) by (unfold m2, m1; bbt_fields; auto).
  assert (Hr2 : m_ret m2 = Z_OK) by (unfold m2, m1; bbt_fields; auto).
  assert (Hlv2 : m_leave m2 = 0) by (unfold m2, m1; bbt_fields; auto).
  assert (Hw2 : i_wsize (m_s m2) = 0) by (unfold m2, m1; bbt_fields; auto).
  clearbody m2. clear Bt. cbn [negb].
  assert (bt = 0 \/ bt = 1 \/ bt = 2 \/ bt = 3) as [B|[B|[B|B]]] by lia; subst bt; cbv beta iota.
  - eexists; split; [reflexivity|]. constructor; bbt_fields; auto.
    rewrite Hb2; reflexivity.
  - destruct (flush =? Z_TREES); cbv beta iota.
    + eexists; split; [reflexivity|]. constructor; bbt_fields; auto. rewrite Hb2; reflexivity.
    + eexists; split; [reflexivity|]. constructor; bbt_fields; auto. rewrite Hb2; reflexivity.
  - eexists; split; [reflexivity|]. constructor; bbt_fields; auto. rewrite Hb2; reflexivity.
  - eexists; split; [reflexivity|]. constructor; bbt_fields; auto. rewrite Hb2; reflexivity.
Qed.

(* PULLBYTE keeps the view, with one more byte in the bit buffer *)
Lemma bbt_mv_pull m S md nx h k lv :
  mv m S md nx h k lv -> 0 <= h < 2 ^ k -> 0 <= k <= 48 -> 0 <= nx < Zlength S -> is_bytes S ->
  mv (pull m) S md (nx + 1) (h + Znth nx S * 2 ^ k) (k + 8) lv /\ 0 <= h + Znth nx S * 2 ^ k < 2 ^ (k + 8) /\
  m_s (pull m) = m_s m.
Proof.
  intros M Hh Hk Hn Hb.
  assert (B : 0 <= Znth nx S < 256).
  { unfold is_bytes in Hb. rewrite Forall_forall in Hb. specialize (Hb (Znth nx S) (Znth_In nx S ltac:(lia))).
    change Byte.max_unsigned with 255 in Hb. lia. }
  assert (R : 0 <= h + Znth nx S * 2 ^ k < 2 ^ (k + 8)).
  { rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256. nia. }
  assert (2 ^ (k + 8) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
  destruct M as [Hm Hi Hn' Hh' Hb' Hlv Ho Hout Hin Hr Hw].
  split; [|split; [exact R | reflexivity]].
  constructor; unfold m_mode in *; bbt_fields; auto; rewrite ?Hi, ?Hn', ?Hh', ?Hb';
    first [reflexivity | rewrite bbt_u64; lia | rewrite bbt_u32; [lia | change (2 ^ 32) with 4294967296; lia]].
Qed.

Lemma bbt_pow_lt k : 0 <= k <= 48 -> k + 8 < 2 ^ 32.
Proof. intros. lia. Qed.

(* byte-level facts of the stored-block check *)
Lemma bbt_lor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> Z.lor a (Z.shiftl b 8) = a + 256 * b.
Proof.
  intros Ha Hb.
  assert (H : forallb (fun a => forallb (fun b => Z.lor a (Z.shiftl b 8) =? a + 256 * b) (map Z.of_nat (seq 0 256)))
                (map Z.of_nat (seq 0 256)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H.
  assert (Ia : In a (map Z.of_nat (seq 0 256))).
  { replace a with (Z.of_nat (Z.to_nat a)) by lia. apply in_map, in_seq. lia. }
  specialize (H a Ia). rewrite forallb_forall in H.
  assert (Ib : In b (map Z.of_nat (seq 0 256))).
  { replace b with (Z.of_nat (Z.to_nat b)) by lia. apply in_map, in_seq. lia. }
  specialize (H b Ib). apply Z.eqb_eq in H. exact H.
Qed.

Lemma bbt_not16 y : 0 <= y < 65536 -> Z.land (Z.lnot y) 65535 = Z.lxor y 65535.
Proof.
  intros Hy. change 65535 with (Z.ones 16). apply Z.bits_inj'. intros n Hn.
  rewrite Z.land_spec, Z.lnot_spec, Z.lxor_spec by lia.
  destruct (Z.lt_ge_cases n 16).
  - rewrite Z.ones_spec_low by lia. destruct (Z.testbit y n); reflexivity.
  - rewrite Z.ones_spec_high by lia. rewrite <- (Z.mod_small y (2 ^ 16)) by (change (2 ^ 16) with 65536; lia).
    rewrite Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma bbt_byte S k : is_bytes S -> 0 <= k < Zlength S -> 0 <= Znth k S < 256.
Proof.
  intros Hb Hk. unfold is_bytes in Hb. rewrite Forall_forall in Hb.
  specialize (Hb (Znth k S) (Znth_In k S Hk)). change Byte.max_unsigned with 255 in Hb. lia.
Qed.

(* STORED after the block header (5 bits of the first byte left): the bytes 1 .. 4 are LEN and NLEN; NLEN is not
   the complement of LEN, so the block is refused *)
Lemma bbt_stored (flush: Z) (fx dx: list entry) m S c :
  mv m S STORED 1 c 5 0 -> 0 <= c < 32 -> 5 <= Zlength S -> is_bytes S ->
  Z.lor (Znth 1 S) (Z.shiftl (Znth 2 S) 8) <> Z.land (Z.lnot (Z.lor (Znth 3 S) (Z.shiftl (Znth 4 S) 8))) 65535 ->
  exists m', stepf2 flush fx dx m = IBrk m' /\ m_mode m' = BAD /\ m_leave m' = 0 /\ i_wsize (m_s m') = 0.
Proof.
  intros M Hc Hl Hbs Hne.
  assert (E1: stepf2 flush fx dx m = c_STORED flush m) by (unfold stepf2, step2; rewrite (mv_mode _ _ _ _ _ _ _ M); reflexivity).
  rewrite E1. unfold c_STORED.
  assert (M0 : mv (bytebits m) S STORED 1 0 0 0).
  { destruct M as [Hm Hi Hn Hh Hb Hlv Ho Hout Hin Hr Hw].
    constructor; unfold m_mode in *; bbt_fields; auto; rewrite ?Hh, ?Hb; change (5 mod 8) with 5; [|reflexivity].
    rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. change (2 ^ 5) with 32. lia. }
  assert (Ws : i_wsize (m_s (bytebits m)) = 0) by exact (mv_wsize _ _ _ _ _ _ _ M0).
  set (m0 := bytebits m) in *. clearbody m0.
  pose proof (bbt_byte S 1 Hbs ltac:(lia)). pose proof (bbt_byte S 2 Hbs ltac:(lia)).
  pose proof (bbt_byte S 3 Hbs ltac:(lia)). pose proof (bbt_byte S 4 Hbs ltac:(lia)).
  destruct (bbt_mv_pull _ _ _ _ _ _ _ M0) as (M1 & R1 & S1); [lia|lia|lia|auto|].
  destruct (bbt_mv_pull _ _ _ _ _ _ _ M1) as (M2 & R2 & S2); [lia|lia|lia|auto|].
  destruct (bbt_mv_pull _ _ _ _ _ _ _ M2) as (M3 & R3 & S3); [lia|lia|lia|auto|].
  destruct (bbt_mv_pull _ _ _ _ _ _ _ M3) as (M4 & R4 & S4); [lia|lia|lia|auto|].
  cbn -[Znth] in M4, R4.
  assert (NB : needbits 32 m0 = pull (pull (pull (pull m0)))).
  { unfold needbits. rewrite bbt_nbS, bbt_nbS, bbt_nbS, bbt_nbS; [reflexivity|..];
      first [rewrite (mv_bits _ _ _ _ _ _ _ M0) | rewrite (mv_bits _ _ _ _ _ _ _ M1)
            | rewrite (mv_bits _ _ _ _ _ _ _ M2) | rewrite (mv_bits _ _ _ _ _ _ _ M3)
            | unfold m_have; first [rewrite (mv_inp _ _ _ _ _ _ _ M0), (mv_nx _ _ _ _ _ _ _ M0)
                                   | rewrite (mv_inp _ _ _ _ _ _ _ M1), (mv_nx _ _ _ _ _ _ _ M1)
                                   | rewrite (mv_inp _ _ _ _ _ _ _ M2), (mv_nx _ _ _ _ _ _ _ M2)
                                   | rewrite (mv_inp _ _ _ _ _ _ _ M3), (mv_nx _ _ _ _ _ _ _ M3)]];
      lia. }
  rewrite NB. set (m4 := pull (pull (pull (pull m0)))) in *.
  rewrite (mv_leave _ _ _ _ _ _ _ M4), (mv_hold _ _ _ _ _ _ _ M4). change (0 =? 1) with false. cbv beta iota.
  set (hv := 0 + Znth 1 S * 1 + Znth 2 S * 256 + Znth 3 S * 65536 + Znth 4 S * 16777216).
  assert (L16 : Z.land hv 65535 = Znth 1 S + 256 * Znth 2 S).
  { change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. unfold hv.
    replace (0 + Znth 1 S * 1 + Znth 2 S * 256 + Znth 3 S * 65536 + Znth 4 S * 16777216)
      with ((Znth 1 S + 256 * Znth 2 S) + (Znth 3 S + 256 * Znth 4 S) * 2 ^ 16) by (simpl; lia).
    rewrite Z.mod_add by lia. apply Z.mod_small. change (2 ^ 16) with 65536. lia. }
  assert (H16 : Z.shiftr hv 16 = Znth 3 S + 256 * Znth 4 S).
  { rewrite Z.shiftr_div_pow2 by lia. unfold hv.
    replace (0 + Znth 1 S * 1 + Znth 2 S * 256 + Znth 3 S * 65536 + Znth 4 S * 16777216)
      with ((Znth 1 S + 256 * Znth 2 S) + (Znth 3 S + 256 * Znth 4 S) * 2 ^ 16) by (simpl; lia).
    rewrite Z.div_add by lia. rewrite Z.div_small; [lia|]. change (2 ^ 16) with 65536. lia. }
  rewrite L16, H16.
  rewrite !bbt_lor_byte, bbt_not16 in Hne by lia.
  replace (Znth 1 S + 256 * Znth 2 S =? Z.lxor (Znth 3 S + 256 * Znth 4 S) 65535) with false
    by (symmetry; apply Z.eqb_neq; exact Hne).
  cbn [negb]. eexists; split; [reflexivity|].
  unfold m_mode; bbt_fields. split; [reflexivity|]. split; [exact (mv_leave _ _ _ _ _ _ _ M4)|].
  exact (mv_wsize _ _ _ _ _ _ _ M4).
Qed.

(* TABLE after the block header: HLIT + 257 = c + 257 > 286 codes, refused *)
Lemma bbt_table (flush: Z) (fx dx: list entry) m S c :
  mv m S TABLE 1 c 5 0 -> 30 <= c < 32 -> 3 <= Zlength S -> is_bytes S ->
  exists m', stepf2 flush fx dx m = IBrk m' /\ m_mode m' = BAD /\ m_leave m' = 0 /\ i_wsize (m_s m') = 0.
Proof.
  intros M Hc Hl Hbs.
  assert (E1: stepf2 flush fx dx m = c_TABLE flush fx dx (fast fx dx) m)
    by (unfold stepf2, step2; rewrite (mv_mode _ _ _ _ _ _ _ M); reflexivity).
  rewrite E1. unfold c_TABLE.
  pose proof (bbt_byte S 1 Hbs ltac:(lia)). pose proof (bbt_byte S 2 Hbs ltac:(lia)).
  destruct (bbt_mv_pull _ _ _ _ _ _ _ M) as (M1 & R1 & S1); [change (2 ^ 5) with 32; lia|lia|lia|auto|].
  destruct (bbt_mv_pull _ _ _ _ _ _ _ M1) as (M2 & R2 & S2); [lia|lia|lia|auto|].
  cbn -[Znth] in M2, R2.
  assert (NB : needbits 14 m = pull (pull m)).
  { unfold needbits. rewrite bbt_nbS, bbt_nbS, bbt_nb0; [reflexivity|..];
      first [rewrite (mv_bits _ _ _ _ _ _ _ M) | rewrite (mv_bits _ _ _ _ _ _ _ M1)
            | rewrite (mv_bits _ _ _ _ _ _ _ M2)
            | unfold m_have; first [rewrite (mv_inp _ _ _ _ _ _ _ M), (mv_nx _ _ _ _ _ _ _ M)
                                   | rewrite (mv_inp _ _ _ _ _ _ _ M1), (mv_nx _ _ _ _ _ _ _ M1)]];
      lia. }
  rewrite NB. set (m2 := pull (pull m)) in *.
  rewrite (mv_leave _ _ _ _ _ _ _ M2). change (0 =? 1) with false. cbv beta iota zeta.
  assert (B5 : bitsn m2 5 = c).
  { unfold bitsn. rewrite (mv_hold _ _ _ _ _ _ _ M2).
    replace (c + Znth 1 S * 32 + Znth 2 S * 8192) with (c + (Znth 1 S + Znth 2 S * 256) * 2 ^ 5) by (simpl; lia).
    rewrite Z.mod_add by lia. apply Z.mod_small. change (2 ^ 5) with 32. lia. }
  rewrite B5. replace (286 <? c + 257) with true by lia. cbn [orb].
  eexists; split; [reflexivity|].
  unfold m_mode; bbt_fields. split; [reflexivity|]. split; [exact (mv_leave _ _ _ _ _ _ _ M2)|].
  exact (mv_wsize _ _ _ _ _ _ _ M2).
Qed.

(* inf_leave when the window is not updated: the return value, the output and the input consumed *)
Lemma bbt_lf flush m : leave_ok flush m = false ->
  r_ret (leave_fin flush m) =
    (if andb (orb (andb (u32 (m_in m - m_have m) =? 0) (u32 (m_out m - m_left m) =? 0)) (flush =? Z_FINISH))
          (m_ret m =? Z_OK)
     then Z_BUF_ERROR else m_ret m) /\
  m_ow (r_m (leave_fin flush m)) = m_ow m /\ m_snx (r_m (leave_fin flush m)) = m_nx m.
Proof.
  intros Hl. unfold leave_fin. rewrite Hl. cbv zeta.
  match goal with |- context [if ?b then set_m_adler _ _ else _] => destruct b end;
  (split; [|split]); reflexivity.
Qed.

(* BAD: the call returns Z_DATA_ERROR (no window: inf_leave cannot fail to allocate one) *)
Lemma bbt_bad (flush: Z) (fx dx: list entry) m o res :
  m_mode m = BAD -> i_wsize (m_s m) = 0 -> loop2 flush fx dx m o ->
  match o with IRet r m => res = Res r m None | IBrk m => inf_leave flush m res end ->
  r_ret res = Z_DATA_ERROR.
Proof.
  intros Hm Hw L R.
  assert (E1: stepf2 flush fx dx m = IBrk (set_leave (set_m_ret m Z_DATA_ERROR)))
    by (unfold stepf2, step2; rewrite Hm; reflexivity).
  rewrite (bbt_last _ _ _ _ _ _ E1 eq_refl L) in R.
  inversion R as [Ok Win|]; subst.
  - unfold leave_ok, m_mode in Ok. bbt_fields_in Ok. rewrite Hw in Ok. unfold m_mode in Hm. rewrite Hm in Ok.
    rewrite Z.ltb_irrefl, andb_false_r, andb_false_l, orb_false_r in Ok. discriminate.
  - assert (Ok : leave_ok flush (set_leave (set_m_ret m Z_DATA_ERROR)) = false).
    { unfold leave_ok, m_mode in *. bbt_fields. rewrite Hw, Hm.
      rewrite Z.ltb_irrefl, andb_false_r, andb_false_l, orb_false_r. reflexivity. }
    destruct (bbt_lf _ _ Ok) as (-> & _ & _). bbt_fields.
    change (Z_DATA_ERROR =? Z_OK) with false. rewrite andb_false_r. reflexivity.
Qed.

(* the call from the machine after inflateInit2_: HEAD (raw: straight to TYPEDO), then TYPEDO reads the block header
   from the first byte x + 2 bt + 8 c *)
Lemma bbt_hdr (flush: Z) (fx dx: list entry) z L S sp w o x bt c :
  -15 <= w <= -8 -> l_s L = l_s (init_live sp w) -> 0 < Zlength S ->
  Znth 0 S = x + 2 * bt + 8 * c -> 0 <= x <= 1 -> 0 <= bt <= 3 -> 0 <= c < 32 ->
  loop2 flush fx dx (m_init z L S) o ->
  exists m',
    mv m' S (if bt =? 0 then STORED else if bt =? 1 then LEN_ else if bt =? 2 then TABLE else BAD) 1 c 5
       (if andb (bt =? 1) (flush =? Z_TREES) then 1 else 0) /\
    (if andb (bt =? 1) (flush =? Z_TREES) then o = IBrk m' else loop2 flush fx dx m' o).
Proof.
  intros Hw HL Hl E Hx Hbt Hc Lp.
  destruct (bbt_init sp w Hw) as (Im & Iw & Il & Ih & Ib & Is). rewrite <- HL in Im, Iw, Il, Ih, Ib, Is.
  assert (E0 : m_init z L S = MS (l_s L) (l_h L) S (zf_ao z) 0 [] 0 0 (Zlength S) (zf_ao z) Z_OK 0
                                (zf_adler z) (zf_msg z) (zf_tin z) (zf_tout z) 0 0).
  { unfold m_init. cbv zeta. rewrite Im. change (HEAD =? Zlib.proof.inflate.Model.TYPE) with false.
    cbv iota. rewrite Ih, Ib. reflexivity. }
  rewrite E0 in Lp.
  set (m0 := MS (l_s L) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) in Lp.
  assert (H0 : stepf2 flush fx dx m0 = IBrk (set_mode m0 TYPEDO)) by (apply bbt_head; assumption).
  pose proof (bbt_next _ _ _ _ _ _ H0 ltac:(discriminate) Lp) as Lp1.
  assert (M1 : mv (set_mode m0 TYPEDO) S TYPEDO 0 0 0 0) by (constructor; reflexivity || exact Is).
  destruct (bbt_typedo flush fx dx _ S x bt c M1 Il Hl E Hx Hbt Hc) as (m2 & H2 & M2).
  exists m2. split; [exact M2|].
  destruct (andb (bt =? 1) (flush =? Z_TREES)) eqn:EB.
  - exact (bbt_last _ _ _ _ _ _ H2 (mv_leave _ _ _ _ _ _ _ M2) Lp1).
  - apply (bbt_next _ _ _ _ _ _ H2); [rewrite (mv_leave _ _ _ _ _ _ _ M2); discriminate | exact Lp1].
Qed.

(* the tails main writes for kinds 2 and 3 are the fixed codes of the run theory's tails *)
Lemma bbt_tail which : 0 <= which <= 1 ->
  tail_bits (TLL which) = bb_tail_bits 2 which /\ tail_bits (TDCode which) = bb_tail_bits 3 which.
Proof.
  intros Hw. assert (which = 0 \/ which = 1) as [E|E] by lia; subst which; split; vm_compute; reflexivity.
Qed.

(* the bits main wrote, from bit 1 *)
Lemma bbt_sub S B i j :
  sublist 1 (1 + Zlength B) (bytes_bits S) = B -> 1 + Zlength B <= 8 * Zlength S -> 0 <= i <= j -> j <= Zlength B ->
  sublist (1 + i) (1 + j) (bytes_bits S) = sublist i j B.
Proof.
  intros Hb Hl Hi Hj. rewrite <- Hb. rewrite sublist_sublist by lia. f_equal; lia.
Qed.


(* the stream after main's writes (bb_bits_stmt): BTYPE at bits 1-2, the rest of the block from bit 3, and the
   first byte split into BFINAL x, BTYPE and the five bits c that follow *)
Lemma bbt_layout S0 kind which lits : bb_bits_stmt -> bb_ok S0 kind which lits ->
  let S := bb_bytes S0 kind which lits in
  let Rest := concat (map (send_sym fixed_ll) lits) ++ bb_tail_bits kind which in
  Zlength S = Zlength S0 /\ is_bytes S /\ 3 + Zlength Rest <= 8 * Zlength S /\
  sublist 1 3 (bytes_bits S) = bits_le (bb_btype kind) 2 /\
  sublist 3 (3 + Zlength Rest) (bytes_bits S) = Rest /\
  Znth 0 S = bval (sublist 0 1 (bytes_bits S)) + 2 * bval (bits_le (bb_btype kind) 2) +
             8 * bval (sublist 3 8 (bytes_bits S)) /\
  0 <= bval (sublist 0 1 (bytes_bits S)) <= 1 /\ 0 <= bval (sublist 3 8 (bytes_bits S)) < 32.
Proof.
  intros BB Hok S Rest.
  pose proof (BB S0 kind which lits Hok) as HB. cbv zeta in HB. fold S Rest in HB.
  set (B := bits_le (bb_btype kind) 2 ++ Rest) in HB.
  destruct HB as (HlS & HbS & Hfit & Hbits).
  pose proof Hok as (Hk & Hwh & Hlits & Hbl & Hll & HbS0 & HS0 & Hk0).
  assert (LB : Zlength B = 2 + Zlength Rest) by (unfold B; rewrite Zlength_app, dkit_bits_le_len; lia).
  assert (Hfit' : 1 + Zlength B <= 8 * Zlength S) by lia.
  pose proof (Zlength_nonneg Rest) as LR.
  assert (Hhd : sublist 1 3 (bytes_bits S) = bits_le (bb_btype kind) 2).
  { pose proof (bbt_sub S B 0 2 Hbits Hfit' ltac:(lia) ltac:(lia)) as X.
    change (1 + 0) with 1 in X. change (1 + 2) with 3 in X. rewrite X. unfold B.
    rewrite sublist_app1 by (rewrite ?dkit_bits_le_len; lia).
    apply sublist_same; [lia | rewrite dkit_bits_le_len; lia]. }
  assert (Hrest : sublist 3 (3 + Zlength Rest) (bytes_bits S) = Rest).
  { pose proof (bbt_sub S B 2 (Zlength B) Hbits Hfit' ltac:(lia) ltac:(lia)) as X.
    change (1 + 2) with 3 in X. replace (1 + Zlength B) with (3 + Zlength Rest) in X by lia. rewrite X, LB. unfold B.
    rewrite sublist_app2 by (rewrite ?dkit_bits_le_len; lia). rewrite dkit_bits_le_len by lia.
    apply sublist_same; lia. }
  destruct (bbt_byte0 S HbS ltac:(lia)) as (E0 & Rx & Rc). rewrite Hhd in E0.
  repeat split; auto; lia.
Qed.

(* kinds 0 (stored, NLEN not ~LEN), 1 (BTYPE 11) and 4 (HLIT 30/31): the first call returns Z_DATA_ERROR *)
Lemma bbt_refused S0 kind which lits w sp L z flush res : bb_bits_stmt ->
  bb_ok S0 kind which lits -> kind <> 2 -> kind <> 3 -> -15 <= w <= -8 -> l_s L = l_s (init_live sp w) ->
  run2 flush lenfix_list distfix_list (m_init z L (bb_bytes S0 kind which lits)) res ->
  r_ret res = Z_DATA_ERROR.
Proof.
  intros BB Hok K2 K3 Hw HL Hrun.
  destruct (bbt_layout S0 kind which lits BB Hok) as (HlS & HbS & Hfit & Hhd & Hrest & E0 & Rx & Rc).
  set (S := bb_bytes S0 kind which lits) in *.
  set (Rest := concat (map (send_sym fixed_ll) lits) ++ bb_tail_bits kind which) in *.
  set (x := bval (sublist 0 1 (bytes_bits S))) in *.
  set (c := bval (sublist 3 8 (bytes_bits S))) in *.
  pose proof Hok as (Hk & Hwh & Hlits & Hbl & Hll & HbS0 & HS0 & Hk0).
  pose proof (Zlength_nonneg lits) as LL.
  pose proof Hrun as (o & Lp & Ro).
  assert (kind = 0 \/ kind = 1 \/ kind = 4) as [K|[K|K]] by lia; subst kind.
  - (* stored, NLEN not ~LEN *)
    change (bval (bits_le (bb_btype 0) 2)) with 0 in E0.
    destruct (bbt_hdr flush lenfix_list distfix_list z L S sp w o x 0 c Hw HL ltac:(lia) E0 Rx ltac:(lia) Rc Lp)
      as (m2 & M2 & L2).
    assert (M2' : mv m2 S STORED 1 c 5 0) by exact M2.
    assert (L2' : loop2 flush lenfix_list distfix_list m2 o) by exact L2.
    destruct (bbt_stored flush lenfix_list distfix_list m2 S c M2' Rc ltac:(lia) HbS (Hk0 eq_refl))
      as (m3 & H3 & Bm & Lv3 & Ws3).
    pose proof (bbt_next _ _ _ _ _ _ H3 ltac:(rewrite Lv3; discriminate) L2') as L3.
    exact (bbt_bad _ _ _ _ _ res Bm Ws3 L3 Ro).
  - (* BTYPE 11 *)
    change (bval (bits_le (bb_btype 1) 2)) with 3 in E0.
    destruct (bbt_hdr flush lenfix_list distfix_list z L S sp w o x 3 c Hw HL ltac:(lia) E0 Rx ltac:(lia) Rc Lp)
      as (m2 & M2 & L2).
    assert (M2' : mv m2 S BAD 1 c 5 0) by exact M2.
    assert (L2' : loop2 flush lenfix_list distfix_list m2 o) by exact L2.
    exact (bbt_bad _ _ _ _ _ res (mv_mode _ _ _ _ _ _ _ M2') (mv_wsize _ _ _ _ _ _ _ M2') L2' Ro).
  - (* dynamic block, HLIT 30 + which *)
    change (bval (bits_le (bb_btype 4) 2)) with 2 in E0.
    assert (Hl0 : lits = []) by (apply Hlits; discriminate).
    assert (ER : Rest = bits_le (30 + which) 5) by (unfold Rest; rewrite Hl0; reflexivity).
    assert (Hc4 : c = 30 + which).
    { assert (L8 : 3 + Zlength Rest = 8) by (rewrite ER, dkit_bits_le_len; lia).
      unfold c. rewrite <- L8, Hrest, ER. assert (which = 0 \/ which = 1) as [W|W] by lia; subst which; reflexivity. }
    destruct (bbt_hdr flush lenfix_list distfix_list z L S sp w o x 2 c Hw HL ltac:(lia) E0 Rx ltac:(lia) Rc Lp)
      as (m2 & M2 & L2).
    assert (M2' : mv m2 S TABLE 1 c 5 0) by exact M2.
    assert (L2' : loop2 flush lenfix_list distfix_list m2 o) by exact L2.
    destruct (bbt_table flush lenfix_list distfix_list m2 S c M2' ltac:(lia) ltac:(lia) HbS)
      as (m3 & H3 & Bm & Lv3 & Ws3).
    pose proof (bbt_next _ _ _ _ _ _ H3 ltac:(rewrite Lv3; discriminate) L2') as L3.
    exact (bbt_bad _ _ _ _ _ res Bm Ws3 L3 Ro).
Qed.
