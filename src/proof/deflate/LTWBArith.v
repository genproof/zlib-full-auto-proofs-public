(** * The deflateBound accounting for any sizes: the arithmetic of the three bounds

    LTBArith.v's facts without its limit [n <= 2^20], and with the margin [slk] after the last block: for
    [2^25 <= n] every accounting of the last block leaves at least one bit below the bound (the tight class
    attains its bound exactly for some n < 2^25, e.g. n = 2^18 - 1: sixteen stored blocks of 16383 bytes and a
    stored last block of 15 bytes). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTWBDefs.
Import ListNotations.
Local Open Scope Z_scope.

Record arith_w_facts : Prop := {
  aw_body_range_w : forall c n, 0 <= n -> n + 4 <= body c n <= n + n / 4 + 7;
  (** In the middle of the run: what is used so far leaves room for a last block. *)
  aw_acc_mid_w : forall c h e k n, 0 <= h -> 0 <= k -> minblk c * k <= e -> e <= n ->
    xb c h e k + 10 <= 8 * (h + body c n);
  (** The last block, tight / store: at most [B + 5] bytes, with the margin. *)
  aw_acc_byte_last_w : forall c h e k B, c <> BFixed -> 0 <= k -> minblk c * k <= e -> 0 <= B ->
    h + e + 5 * k + B + 5 + slk (e + B) <= h + body c (e + B);
  (** The last block, fixed: a Huffman block of at most [9 B + 10] bits ... *)
  aw_acc_fixed_huff_w : forall h e k B, 0 <= k -> 255 * k <= e -> 0 <= B ->
    8 * h + 9 * e + 10 * k + 9 * B + 10 + slk (e + B) <= 8 * (h + body BFixed (e + B));
  (** ... or a stored block (then [B >= 15]: it was cheaper than the static codes). *)
  aw_acc_fixed_stored_w : forall h e k B g, 0 <= k -> 255 * k <= e -> 15 <= B ->
    0 <= g <= 8 * h + 9 * e + 10 * k ->
    8 * ((g + 10) / 8) + 32 + 8 * B + slk (e + B) <= 8 * (h + body BFixed (e + B));
  (** Level 0 with Z_FINISH and all the data: room for every stored block. *)
  aw_stored_room_w : forall c n, c <> BFixed -> 0 <= n -> 6 + 5 * (n / 65535) + n <= body c n
}.

(** [body] with its shifts as divisions (as in LTBArith.v). *)
Lemma body_div_w : forall c n, body c n =
  match c with
  | BTight => n + n / 4096 + n / 16384 + n / 33554432 + 7
  | BFixed => n + n / 8 + n / 256 + n / 512 + 4
  | BStore => n + n / 32 + n / 128 + n / 2048 + 7
  end.
Proof.
  intros c n; destruct c; unfold body; rewrite !Z.shiftr_div_pow2 by lia; reflexivity.
Qed.

Lemma divb_w : forall n d, 0 < d -> d * (n / d) <= n < d * (n / d) + d.
Proof. intros n d Hd. split; [apply Z.mul_div_le; lia|]. pose proof (Z.mul_succ_div_gt n d Hd). lia. Qed.

(** Replaces every [n / d] of the goal by a fresh integer bounded by [divb_w]. *)
Ltac dvw := repeat match goal with |- context [?n / ?d] =>
  let q := fresh "q" in pose proof (divb_w n d ltac:(lia)); set (q := n / d) in *; clearbody q end.

Lemma slk_cases : forall n, (n < 33554432 /\ slk n = 0) \/ (33554432 <= n /\ slk n = 1).
Proof. intros n; unfold slk; destruct (Z.ltb_spec n 33554432); lia. Qed.

Theorem arith_w_proof : arith_w_facts.
Proof.
  constructor.
  - intros c n Hn. rewrite !body_div_w. destruct c; dvw; lia.
  - intros c h e k n Hh Hk Hke Hn. rewrite !body_div_w. destruct c; unfold xb, minblk in *; dvw.
    all: lia.
  - intros c h e k B Hc Hk Hke HB. rewrite !body_div_w.
    destruct (slk_cases (e + B)) as [[? ->]|[? ->]];
    destruct c; unfold minblk in *; try congruence; dvw.
    all: lia.
  - intros h e k B Hk Hke HB. rewrite !body_div_w.
    destruct (slk_cases (e + B)) as [[? ->]|[? ->]]; dvw; lia.
  - intros h e k B g Hk Hke HB Hg. rewrite !body_div_w.
    assert (Hq : (g + 10) / 8 <= (8 * h + 9 * e + 10 * k + 10) / 8) by (apply Z.div_le_mono; lia).
    replace (8 * h + 9 * e + 10 * k + 10) with ((9 * e + 10 * k + 10) + h * 8) in Hq by ring.
    rewrite Z.div_add in Hq by lia.
    revert Hq. generalize ((g + 10) / 8). intros q0 Hq. revert Hq.
    destruct (slk_cases (e + B)) as [[? ->]|[? ->]]; dvw; intros Hq; lia.
  - intros c n Hc Hn. rewrite !body_div_w. destruct c; try congruence; dvw; lia.
Qed.

Lemma body_range_w : forall c n, 0 <= n -> n + 4 <= body c n <= n + n / 4 + 7.
Proof. exact (aw_body_range_w arith_w_proof). Qed.

(** In the middle of the run: what is used so far leaves room for a last block. *)
Lemma acc_mid_w : forall c h e k n, 0 <= h -> 0 <= k -> minblk c * k <= e -> e <= n ->
  xb c h e k + 10 <= 8 * (h + body c n).
Proof. exact (aw_acc_mid_w arith_w_proof). Qed.

(** The last block, tight / store: at most [B + 5] bytes, with the margin. *)
Lemma acc_byte_last_w : forall c h e k B, c <> BFixed -> 0 <= k -> minblk c * k <= e -> 0 <= B ->
  h + e + 5 * k + B + 5 + slk (e + B) <= h + body c (e + B).
Proof. exact (aw_acc_byte_last_w arith_w_proof). Qed.

(** The last block, fixed: a Huffman block of at most [9 B + 10] bits ... *)
Lemma acc_fixed_huff_w : forall h e k B, 0 <= k -> 255 * k <= e -> 0 <= B ->
  8 * h + 9 * e + 10 * k + 9 * B + 10 + slk (e + B) <= 8 * (h + body BFixed (e + B)).
Proof. exact (aw_acc_fixed_huff_w arith_w_proof). Qed.

(** ... or a stored block (then [B >= 15]: it was cheaper than the static codes). *)
Lemma acc_fixed_stored_w : forall h e k B g, 0 <= k -> 255 * k <= e -> 15 <= B ->
  0 <= g <= 8 * h + 9 * e + 10 * k ->
  8 * ((g + 10) / 8) + 32 + 8 * B + slk (e + B) <= 8 * (h + body BFixed (e + B)).
Proof. exact (aw_acc_fixed_stored_w arith_w_proof). Qed.

(** Level 0 with Z_FINISH and all the data: room for every stored block. *)
Lemma stored_room_w : forall c n, c <> BFixed -> 0 <= n -> 6 + 5 * (n / 65535) + n <= body c n.
Proof. exact (aw_stored_room_w arith_w_proof). Qed.
