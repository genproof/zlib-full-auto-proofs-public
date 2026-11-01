(** Copy of LTBArith.v (its proof, under this module name), for LTBEvent.v. *)
(** * deflate_bound theory: the arithmetic of the three bounds *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTBDefs.
Import ListNotations.
Local Open Scope Z_scope.

Record arith_facts : Prop := {
  ar_body_mono : forall c n m, 0 <= n <= m -> body c n <= body c m;
  ar_body_range : forall c n, 0 <= n <= 1048576 -> n + 4 <= body c n <= 2 * n + 7;
  ar_acc_mid : forall c h e k n, 0 <= h -> 0 <= k -> minblk c * k <= e -> e <= n <= 1048576 ->
  xb c h e k + 10 <= 8 * (h + body c n);
  ar_acc_byte_last : forall c h e k B, c <> BFixed -> 0 <= k -> minblk c * k <= e -> 0 <= B ->
  e + B <= 1048576 ->
  h + e + 5 * k + B + 5 <= h + body c (e + B);
  ar_acc_fixed_huff : forall h e k B, 0 <= k -> 255 * k <= e -> 0 <= B -> e + B <= 1048576 ->
  8 * h + 9 * e + 10 * k + 9 * B + 10 <= 8 * (h + body BFixed (e + B));
  ar_acc_fixed_stored : forall h e k B g, 0 <= k -> 255 * k <= e -> 15 <= B -> e + B <= 1048576 ->
  0 <= g <= 8 * h + 9 * e + 10 * k ->
  8 * ((g + 10) / 8) + 32 + 8 * B <= 8 * (h + body BFixed (e + B));
  ar_stored_room : forall c n, c <> BFixed -> 0 <= n <= 1048576 ->
  6 + 5 * (n / 65535) + n <= body c n
}.

Lemma body_div : forall c n, body c n =
  match c with
  | BTight => n + n / 4096 + n / 16384 + n / 33554432 + 7
  | BFixed => n + n / 8 + n / 256 + n / 512 + 4
  | BStore => n + n / 32 + n / 128 + n / 2048 + 7
  end.
Proof.
  intros c n; destruct c; unfold body; rewrite !Z.shiftr_div_pow2 by lia; reflexivity.
Qed.

Lemma divb : forall n d, 0 < d -> d * (n / d) <= n < d * (n / d) + d.
Proof. intros n d Hd. split; [apply Z.mul_div_le; lia|]. pose proof (Z.mul_succ_div_gt n d Hd). lia. Qed.

Ltac dv := repeat match goal with |- context [?n / ?d] =>
  let q := fresh "q" in pose proof (divb n d ltac:(lia)); set (q := n / d) in *; clearbody q end.

Theorem arith_proof : arith_facts.
Proof.
  constructor.
  - intros c n m Hnm. rewrite !body_div. destruct c;
      match goal with |- ?x + n / ?a + n / ?b + n / ?d + _ <= _ =>
        assert (n / a <= m / a) by (apply Z.div_le_mono; lia);
        assert (n / b <= m / b) by (apply Z.div_le_mono; lia);
        assert (n / d <= m / d) by (apply Z.div_le_mono; lia) end; lia.
  - intros c n Hn. rewrite !body_div. destruct c; dv; lia.
  - intros c h e k n Hh Hk Hke Hn. rewrite !body_div. destruct c; unfold xb, minblk in *; dv.
    all: lia.
  - intros c h e k B Hc Hk Hke HB Hn. rewrite !body_div. destruct c; unfold minblk in *; try congruence; dv.
    all: lia.
  - intros h e k B Hk Hke HB Hn. rewrite !body_div. dv. lia.
  - intros h e k B g Hk Hke HB Hn Hg. rewrite !body_div.
    assert (Hq : (g + 10) / 8 <= (8 * h + 9 * e + 10 * k + 10) / 8) by (apply Z.div_le_mono; lia).
    replace (8 * h + 9 * e + 10 * k + 10) with ((9 * e + 10 * k + 10) + h * 8) in Hq by ring.
    rewrite Z.div_add in Hq by lia.
    revert Hq. generalize ((g + 10) / 8). intros q0 Hq. revert Hq. dv. intros Hq. lia.
  - intros c n Hc Hn. rewrite !body_div. destruct c; try congruence; dv; lia.
Qed.

Lemma body_mono : forall c n m, 0 <= n <= m -> body c n <= body c m.
Proof. exact (ar_body_mono arith_proof). Qed.

Lemma body_range : forall c n, 0 <= n <= 1048576 -> n + 4 <= body c n <= 2 * n + 7.
Proof. exact (ar_body_range arith_proof). Qed.

Lemma acc_mid : forall c h e k n, 0 <= h -> 0 <= k -> minblk c * k <= e -> e <= n <= 1048576 ->
  xb c h e k + 10 <= 8 * (h + body c n).
Proof. exact (ar_acc_mid arith_proof). Qed.

Lemma acc_byte_last : forall c h e k B, c <> BFixed -> 0 <= k -> minblk c * k <= e -> 0 <= B ->
  e + B <= 1048576 ->
  h + e + 5 * k + B + 5 <= h + body c (e + B).
Proof. exact (ar_acc_byte_last arith_proof). Qed.

Lemma acc_fixed_huff : forall h e k B, 0 <= k -> 255 * k <= e -> 0 <= B -> e + B <= 1048576 ->
  8 * h + 9 * e + 10 * k + 9 * B + 10 <= 8 * (h + body BFixed (e + B)).
Proof. exact (ar_acc_fixed_huff arith_proof). Qed.

Lemma acc_fixed_stored : forall h e k B g, 0 <= k -> 255 * k <= e -> 15 <= B -> e + B <= 1048576 ->
  0 <= g <= 8 * h + 9 * e + 10 * k ->
  8 * ((g + 10) / 8) + 32 + 8 * B <= 8 * (h + body BFixed (e + B)).
Proof. exact (ar_acc_fixed_stored arith_proof). Qed.

Lemma stored_room : forall c n, c <> BFixed -> 0 <= n <= 1048576 ->
  6 + 5 * (n / 65535) + n <= body c n.
Proof. exact (ar_stored_room arith_proof). Qed.



(** In the middle of the run: what is used so far leaves room for a last block. *)

(** The last block, tight / store: at most [B + 5] bytes. *)

(** The last block, fixed: a Huffman block of at most [9 B + 10] bits ... *)

(** ... or a stored block (then [B >= 15]: it was cheaper than the static codes). *)

(** Level 0 with Z_FINISH and all the data: room for every stored block (cf_stored_live), the header bits being
    at most 7. *)
