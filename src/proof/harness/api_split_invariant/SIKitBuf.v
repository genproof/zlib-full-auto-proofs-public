(* The bit buffer operations of the concrete machine (PULLBYTE, NEEDBITS, DROPBITS, INITBITS, BYTEBITS)
   keep the buffer's hold equal to the input's bits at the bit position (`bitbuf`). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.api_split_invariant.SIDefs.
Require Import Zlib.proof.harness.api_split_invariant.SIKitBits.
Import ListNotations.
Local Open Scope Z_scope.

(* m' differs from m at most in the bit buffer (next, hold, bits) and leave *)
Definition shp (m m': mst) : Prop :=
  m' = set_m_leave (set_m_bits (set_m_hold (set_m_nx m (m_nx m')) (m_hold m')) (m_bits m')) (m_leave m').

Lemma shp_refl m : shp m m.
Proof. destruct m; reflexivity. Qed.

Lemma shp_trans m1 m2 m3 : shp m1 m2 -> shp m2 m3 -> shp m1 m3.
Proof.
  unfold shp. intros H1 H2. rewrite H2. rewrite H1 at 1. destruct m1; reflexivity.
Qed.

Lemma shp_pull m : shp m (pull m).
Proof. destruct m; reflexivity. Qed.

Lemma shp_leave m : shp m (set_leave m).
Proof. destruct m; reflexivity. Qed.

Lemma shp_s m m' : shp m m' -> m_s m' = m_s m /\ m_inp m' = m_inp m.
Proof. intros ->. split; reflexivity. Qed.

Lemma sik_pow_le a b : 0 <= a <= b -> 2 ^ a <= 2 ^ b.
Proof. intros. apply Z.pow_le_mono_r; lia. Qed.

(* PULLBYTE *)
Lemma sik_pull src P0 m : bitbuf src P0 m -> 0 < m_have m -> m_bits m <= 31 ->
  bitbuf src P0 (pull m) /\ mq P0 (pull m) = mq P0 m.
Proof.
  intros [B P I N [Bi Bq] H] Hv Hb. unfold m_have in Hv.
  assert (Ebits: m_bits (pull m) = m_bits m + 8).
  { unfold pull. cbn [m_bits set_m_bits]. unfold u32. apply Z.mod_small.
    pose proof (sik_pow_le 6 32 ltac:(lia)). change (2 ^ 6) with 64 in *. lia. }
  assert (Enx: m_nx (pull m) = m_nx m + 1) by reflexivity.
  assert (Einp: m_inp (pull m) = m_inp m) by reflexivity.
  assert (Eq: mq P0 (pull m) = mq P0 m) by (unfold mq; rewrite Ebits, Enx; lia).
  split; [|exact Eq].
  assert (Eb: Znth (m_nx m) (m_inp m) = Znth (P0 + m_nx m) src).
  { destruct I as [I1 I2]. rewrite I2 at 1. rewrite Znth_sublist by lia. f_equal; lia. }
  constructor; try rewrite Einp; try rewrite Enx; try rewrite Ebits; auto; try lia.
  - rewrite Eq.
    unfold mq in *. rewrite sik_sbits_app by (auto; lia).
    replace (8 * (P0 + m_nx m) - m_bits m + m_bits m) with (8 * (P0 + m_nx m)) by lia.
    rewrite sik_sbits_byte by (auto; try lia; rewrite Z.mul_comm, Z_mod_mult; reflexivity).
    unfold sbyte. replace (8 * (P0 + m_nx m) / 8) with (P0 + m_nx m) by (rewrite (Z.mul_comm 8), Z.div_mul; lia).
    unfold pull. cbn [m_hold set_m_bits set_m_hold]. rewrite Eb, <- H.
    rewrite (Z.mul_comm (Znth _ src)). unfold u64. apply Z.mod_small.
    pose proof (sik_sbits_range src (8 * (P0 + m_nx m) - m_bits m) (m_bits m) ltac:(lia)).
    pose proof (sik_byte_range src (P0 + m_nx m) B).
    rewrite H. pose proof (sik_pow_le (m_bits m) 31 ltac:(lia)).
    assert (2 ^ 31 * 256 < 2 ^ 64) by (vm_compute; reflexivity).
    split; [nia|]. nia.
Qed.

Lemma sik_bitbuf_leave src P0 m : bitbuf src P0 m -> bitbuf src P0 (set_leave m).
Proof. intros [B P I N Bb H]. constructor; [exact B|exact P|exact I|exact N|exact Bb|exact H]. Qed.

Lemma sik_mq_leave P0 m : mq P0 (set_leave m) = mq P0 m.
Proof. destruct m; reflexivity. Qed.

(* NEEDBITS(n) with enough fuel *)
Lemma sik_needbits_f src P0 n : forall k m, bitbuf src P0 m -> m_leave m = 0 -> 0 <= n <= 32 ->
  n <= m_bits m + 8 * Z.of_nat k ->
  let m' := needbits_f k n m in
  bitbuf src P0 m' /\ mq P0 m' = mq P0 m /\ shp m m' /\
  (m_leave m' = 0 -> n <= m_bits m' /\ m_bits m' <= Z.max (m_bits m) (n + 7)) /\
  (m_leave m' <> 0 -> m_leave m' = 1 /\ m_have m' = 0 /\ m_bits m' < n).
Proof.
  induction k as [|k IH]; intros m Hb Hl Hn Hf; cbn zeta.
  - cbn [needbits_f]. split; [auto|]. split; [auto|]. split; [apply shp_refl|].
    split; [intros; lia|]. intros; lia.
  - cbn [needbits_f]. destruct (Z.ltb_spec (m_bits m) n).
    + destruct (Z.eqb_spec (m_have m) 0).
      * split; [apply sik_bitbuf_leave; auto|]. split; [apply sik_mq_leave|]. split; [apply shp_leave|].
        split; [intros C; cbv in C; discriminate|].
        intros _. split; [reflexivity|]. destruct m; auto.
      * pose proof (bb_nx _ _ _ Hb). pose proof (bb_bits _ _ _ Hb). unfold m_have in n0.
        rewrite Nat2Z.inj_succ in Hf.
        destruct (sik_pull src P0 m Hb ltac:(unfold m_have; lia) ltac:(lia)) as [Pb Pq].
        assert (Pbits: m_bits (pull m) = m_bits m + 8).
        { unfold pull. cbn [m_bits set_m_bits]. unfold u32. apply Z.mod_small.
          pose proof (sik_pow_le 6 32 ltac:(lia)). change (2 ^ 6) with 64 in *. lia. }
        destruct (IH (pull m) Pb ltac:(destruct m; auto) Hn ltac:(rewrite Pbits; lia))
          as (R1 & R2 & R3 & R4 & R5).
        split; [auto|]. split; [congruence|]. split; [eapply shp_trans; [apply shp_pull|exact R3]|].
        split; [|exact R5]. intros L. destruct (R4 L). rewrite Pbits in *. lia.
    + split; [auto|]. split; [auto|]. split; [apply shp_refl|].
      split; [intros; lia|]. intros; lia.
Qed.

Lemma sik_needbits src P0 m n : bitbuf src P0 m -> m_leave m = 0 -> 0 <= n <= 32 ->
  let m' := needbits n m in
  bitbuf src P0 m' /\ mq P0 m' = mq P0 m /\
  m' = set_m_leave (set_m_bits (set_m_hold (set_m_nx m (m_nx m')) (m_hold m')) (m_bits m')) (m_leave m') /\
  (m_leave m' = 0 -> n <= m_bits m' /\ m_bits m' <= Z.max (m_bits m) (n + 7) /\
                     m_hold m' mod 2 ^ n = sbits src (mq P0 m) n) /\
  (m_leave m' <> 0 -> m_leave m' = 1 /\ m_have m' = 0 /\ m_bits m' < n /\
                      8 * (P0 + Zlength (m_inp m)) < mq P0 m + n).
Proof.
  intros Hb Hl Hn. cbn zeta. unfold needbits.
  pose proof (bb_bits _ _ _ Hb).
  destruct (sik_needbits_f src P0 n 4 m Hb Hl Hn ltac:(simpl; lia)) as (R1 & R2 & R3 & R4 & R5).
  set (m' := needbits_f 4 n m) in *.
  destruct (shp_s _ _ R3) as [Es Ei].
  split; [auto|]. split; [auto|]. split; [exact R3|]. split.
  - intros L. destruct (R4 L) as [A1 A2]. split; [auto|]. split; [auto|].
    rewrite (bb_hold _ _ _ R1), R2. pose proof (bb_bits _ _ _ R1).
    apply sik_sbits_mod; [apply (bb_src _ _ _ Hb)|unfold mq; lia|lia].
  - intros L. destruct (R5 L) as (A1 & A2 & A3). split; [auto|]. split; [auto|]. split; [auto|].
    rewrite <- R2. unfold mq, m_have in *. rewrite Ei in A2. lia.
Qed.

(* DROPBITS(k) and BITS(k) *)
Lemma sik_dropbits src P0 m k : bitbuf src P0 m -> 0 <= k <= m_bits m ->
  bitbuf src P0 (dropbits k m) /\ mq P0 (dropbits k m) = mq P0 m + k /\ bitsn m k = sbits src (mq P0 m) k.
Proof.
  intros [B P I N [Bi Bq] H] Hk.
  assert (Ebits: m_bits (dropbits k m) = m_bits m - k).
  { unfold dropbits. cbn [m_bits set_m_bits]. unfold u32. apply Z.mod_small.
    pose proof (sik_pow_le 6 32 ltac:(lia)). change (2 ^ 6) with 64 in *. lia. }
  assert (Eq: mq P0 (dropbits k m) = mq P0 m + k).
  { unfold mq. rewrite Ebits. change (m_nx (dropbits k m)) with (m_nx m). lia. }
  split; [|split; [exact Eq|]].
  - constructor; auto; change (m_inp (dropbits k m)) with (m_inp m);
      change (m_nx (dropbits k m)) with (m_nx m); try rewrite Ebits; auto; try lia.
    change (m_hold (dropbits k m)) with (Z.shiftr (m_hold m) k). rewrite Eq, H.
    apply sik_sbits_shiftr; auto; unfold mq; lia.
  - unfold bitsn. rewrite H. apply sik_sbits_mod; auto; unfold mq; lia.
Qed.

(* INITBITS *)
Lemma sik_initbits src P0 m : bitbuf src P0 m -> bitbuf src P0 (initbits m) /\ mq P0 (initbits m) = mq P0 m + m_bits m.
Proof.
  intros [B P I N [Bi Bq] H].
  assert (Eq: mq P0 (initbits m) = mq P0 m + m_bits m) by (unfold mq; reflexivity || (simpl; lia)).
  split; [|exact Eq].
  constructor; auto; simpl; try lia. rewrite sik_sbits_0. reflexivity.
Qed.

(* BYTEBITS *)
Lemma sik_bytebits src P0 m : bitbuf src P0 m -> bitbuf src P0 (bytebits m) /\ mq P0 (bytebits m) = align8 (mq P0 m).
Proof.
  intros [B P I N [Bi Bq] H].
  pose proof (Z.mod_pos_bound (m_bits m) 8 ltac:(lia)).
  pose proof (Z_div_mod_eq_full (m_bits m) 8).
  assert (Eq: mq P0 (bytebits m) = mq P0 m + m_bits m mod 8) by (unfold mq; simpl; lia).
  split.
  - constructor; auto; simpl; try lia.
    rewrite Eq, H. apply sik_sbits_shiftr; auto; unfold mq; lia.
  - rewrite Eq. unfold align8, mq.
    replace (8 * (P0 + m_nx m) - m_bits m + 7) with ((7 - m_bits m mod 8) + (P0 + m_nx m - m_bits m / 8) * 8) by lia.
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.

Lemma sik_kit_bits : kit_bits_stmt.
Proof.
  split; [exact sik_pull|]. split; [exact sik_needbits|]. split; [exact sik_dropbits|].
  split; [exact sik_initbits|]. split; [exact sik_bytebits|].
  split; [intros; apply sik_sbits_mod; auto; lia|].
  split; [intros; apply sik_sbits_shiftr; auto; lia|].
  split; [intros; apply sik_sbits_range; auto|].
  exact sik_sbits_byte.
Qed.
