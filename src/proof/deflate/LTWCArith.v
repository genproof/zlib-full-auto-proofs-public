(** * The deflateBound accounting of the clip() loops: the room left for the bytes still to store

    With the accounting of LTBDefs ([acct]: [k] non-last blocks of [E] bytes in all, each at least [minblk c]
    bytes, cost at most [E + 5 k] bytes for the tight and the stored bound), deflateBound(n) leaves at least
    [n - E] bytes after them: the bytes of the stream not yet in a block.  At level 0 (never the fixed bound)
    this is what makes a Z_FINISH call of the clip() loop with more than 2^32 - 1 bytes to store get all 2^32 - 1
    bytes of output space. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.deflate.LTBArith.
Local Open Scope Z_scope.

Lemma clip_room : forall c n E k, c <> BFixed -> 0 <= k -> minblk c * k <= E -> E <= n ->
  n + 5 * k <= body c n.
Proof.
  intros c n E k Hc Hk HkE HEn. rewrite body_div.
  destruct c; [|contradiction|]; cbn [minblk] in HkE.
  all: repeat match goal with |- context [?m / ?d] =>
         let q := fresh "q" in pose proof (divb m d ltac:(lia)); set (q := m / d) in *; clearbody q end.
  all: lia.
Qed.

(** The bytes handed out or pending: deflateBound minus them is at least the bytes not yet in a block. *)
Lemma clip_left : forall c h n E k tout pend bv w0, c <> BFixed -> 0 <= k -> minblk c * k <= E -> E <= n ->
  0 <= bv -> 0 <= w0 <= 2 -> 8 * (tout + pend) + bv <= xb c h E k ->
  n - E <= h + body c n + tlen w0 - tout - pend.
Proof.
  intros c h n E k tout pend bv w0 Hc Hk HkE HEn Hbv Hw HG.
  pose proof (clip_room c n E k Hc Hk HkE HEn).
  assert (0 <= tlen w0) by (unfold tlen; destruct (w0 =? 1); [lia|destruct (w0 =? 2); lia]).
  destruct c; [|contradiction|]; cbn [xb] in HG; lia.
Qed.
