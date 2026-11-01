(** * Bit counts of _tr_stored_block and bi_windup (for lemma (ii)) *)

From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.huffman.Model Zlib.proof.huffman.Bits.
Import ListNotations.
Local Open Scope Z_scope.

(** bi_windup rounds the bit position up to a byte boundary. *)
Lemma windup_bitpos : forall o, bits_ok o ->
  bitpos (bi_windup o) = 8 * ((bitpos o + 7) / 8) /\ bits_ok (bi_windup o).
Proof.
  intros o Hok. destruct (bi_windup_spec o Hok) as [P1 [P2 [P3 _]]].
  destruct Hok as [Hv [Hb Hp]].
  unfold bitpos. rewrite P1, P2.
  replace (8 * o_pending o + o_bi_valid o + 7) with (o_bi_valid o + 7 + o_pending o * 8) by lia.
  rewrite Z.div_add by lia. split; [lia|].
  split; [rewrite P2; lia|]. rewrite P3, P2. split; [simpl; lia|].
  assert (0 <= (o_bi_valid o + 7) / 8) by (apply Z.div_pos; lia). lia.
Qed.

(** A multiple of 8 is not moved by bi_windup's rounding. *)
Lemma round8_le : forall p A, p <= 8 * A -> 8 * ((p + 7) / 8) <= 8 * A.
Proof.
  intros p A H. assert ((p + 7) / 8 < A + 1) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.

(** _tr_stored_block: 3 header bits, padding to a byte, LEN and NLEN, the bytes. *)
Lemma stored_block_bitpos : forall o buf stored_len last,
  bits_ok o -> 0 <= last <= 1 -> 0 <= stored_len ->
  bitpos (tr_stored_block o buf stored_len last) = 8 * ((bitpos o + 3 + 7) / 8) + 32 + 8 * stored_len /\
  o_bi_valid (tr_stored_block o buf stored_len last) = 0.
Proof.
  intros o buf stored_len last Hok Hl Hs. unfold tr_stored_block.
  destruct (send_bits_spec o (Z.shiftl STORED_BLOCK 1 + last) 3 Hok ltac:(lia)) as [S1 [_ [S3 _]]].
  { unfold STORED_BLOCK. simpl. lia. }
  set (o1 := send_bits o (Z.shiftl STORED_BLOCK 1 + last) 3) in *.
  destruct (windup_bitpos o1 S3) as [W1 W2].
  destruct (bi_windup_spec o1 S3) as [_ [V2 _]].
  set (o2 := bi_windup o1) in *.
  destruct (put_short_spec o2 (u16 stored_len)) as [Q1 [_ [Q3 _]]].
  set (o3 := put_short o2 (u16 stored_len)) in *.
  destruct (put_short_spec o3 (u16 (Z.lnot stored_len))) as [R1 [_ [R3 _]]].
  set (o4 := put_short o3 (u16 (Z.lnot stored_len))) in *.
  assert (E : forall b, bitpos (mkOut b (o_pending o4 + stored_len) (o_bi_buf o4) (o_bi_valid o4) (o_bi_used o4))
                = 8 * o_pending o4 + 8 * stored_len + o_bi_valid o4) by (intros; unfold bitpos; cbn [o_pending o_bi_valid]; lia).
  rewrite E. cbn [o_bi_valid]. rewrite R1, Q1, R3, Q3. unfold bitpos in W1, S1 |- *. rewrite S1 in W1. rewrite V2 in *. split; lia.
Qed.
