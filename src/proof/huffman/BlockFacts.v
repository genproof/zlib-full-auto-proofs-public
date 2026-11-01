(** * Lemma (i) for dynamic blocks: the facts about a block that the bound uses

    [block_facts] lists what the model of _tr_flush_block establishes about a block emitted with dynamic trees:
    the code lengths of the used literal/length and distance codes (Kraft, Fibonacci caps), the decision
    opt_len < static_len (A), the header size H (bits after the 3 block-type bits: HLIT/HDIST/HCLEN, the
    bit-length code lengths and the two run-length coded length tables), crudely and, for small lit_bufsize,
    against every bit-length code [tau] (optimality of the bit-length tree up to the repair overhead 100).
    [overlay_bound_statement] is the arithmetic consequence the overlay needs: after the header and k symbols the
    bit position is at most 8 * (L + 3k). *)

From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.huffman.Model Zlib.proof.huffman.HuffAbs Zlib.proof.huffman.Heap
               Zlib.proof.huffman.Bits Zlib.proof.huffman.Header Zlib.proof.huffman.Overlay.
Import ListNotations.
Local Open Scope Z_scope.

(** Sum of [g c] over [c = 0 .. n-1]. *)
Definition zsum (n : Z) (g : Z -> Z) : Z := HuffAbs.sumZ (map g (zseq 0 (Z.to_nat n))).

(** A bit-length code: lengths 1..15 for the 19 bit-length symbols, Kraft sum at most 1. *)
Definition tau_ok (tau : Z -> Z) : Prop :=
  (forall s, 0 <= s < BL_CODES -> 1 <= tau s <= 15) /\ zsum BL_CODES (fun s => 2 ^ (15 - tau s)) <= 2 ^ 15.

(** The facts about a dynamic block of symbols [syms] at lit_bufsize [L] with [b0] bits left over from the previous
    block: [ll]/[dl0] are the literal/length and distance code lengths (the Len fields of dyn_ltree/dyn_dtree, as
    lists, with the max codes [lmax]/[dmax]); [H] is the header size after the 3 block-type bits; [sl]/[sd] are
    the shifts of the Fibonacci caps (0 without the length-limit repair). *)
Record block_facts (L b0 : Z) (syms : list (Z * Z)) (ll dl0 : list Z) (lmax dmax H sl sd : Z) : Prop := {
  bf_L : exists ml, 1 <= ml <= 9 /\ L = 2 ^ (ml + 6);
  bf_b0 : 0 <= b0 <= 7;
  bf_n : 1 <= Zlength syms <= L - 1;
  bf_valid : forall x, In x syms -> valid_sym (fst x) (snd x);
  (* literal/length code: the used codes are exactly those with nonzero frequency *)
  bf_lmax : END_BLOCK <= lmax < L_CODES /\ Znth lmax ll <> 0 /\ Zlength ll >= L_CODES + 1;
  bf_lused : forall c, 0 <= c < L_CODES -> (0 < lfreq syms c <-> Znth c ll <> 0);
  bf_llen : forall c, 0 <= c < L_CODES -> 0 <= Znth c ll <= 15 /\ (lmax < c -> Znth c ll = 0);
  (* distance code: the used codes have nonzero lengths; at most two more (forced) codes have a length *)
  bf_dmax : 0 <= dmax < D_CODES /\ Znth dmax dl0 <> 0 /\ Zlength dl0 >= D_CODES + 1;
  bf_dused : forall d, 0 <= d < D_CODES -> 0 < dfreq syms d -> Znth d dl0 <> 0;
  bf_dlen : forall d, 0 <= d < D_CODES -> 0 <= Znth d dl0 <= 15 /\ (dmax < d -> Znth d dl0 = 0);
  bf_forced : let used := zsum D_CODES (fun d => if 0 <? dfreq syms d then 1 else 0) in
              let forced := zsum D_CODES (fun d => if (0 <? Znth d dl0) && (dfreq syms d =? 0) then 1 else 0) in
              forced <= 2 /\ (0 < forced -> used <= 1);
  (* Kraft *)
  bf_kraft_l : zsum L_CODES (fun c => if Znth c ll =? 0 then 0 else 2 ^ (15 - Znth c ll)) = 2 ^ 15;
  bf_kraft_d : zsum D_CODES (fun d => if Znth d dl0 =? 0 then 0 else 2 ^ (15 - Znth d dl0)) <= 2 ^ 15;
  (* Fibonacci caps *)
  bf_shift : 0 <= sl <= 2 /\ 0 <= sd <= 2 /\ (L <= 2048 -> sl = 0 /\ sd = 0);
  bf_cap_l : forall c, 0 <= c < L_CODES -> 0 < lfreq syms c -> lfreq syms c * fib (Znth c ll + 1 - sl) <= L + 1;
  bf_cap_d : forall d, 0 <= d < D_CODES -> 0 < dfreq syms d -> dfreq syms d * fib (Znth d dl0 + 1 - sd) <= L + 1;
  (* (A): the dynamic block was chosen, opt_len < static_len *)
  bf_A : H + zsum L_CODES (fun c => lfreq syms c * (Znth c ll - Znth c static_ltree_len))
           + zsum D_CODES (fun d => dfreq syms d * (Znth d dl0 - 5)) <= -1;
  (* the header *)
  bf_H : H <= 2283;
  bf_tau : L <= 256 -> forall tau, tau_ok tau ->
           H <= 71 + charge tau ll (lmax + 1) + charge tau dl0 (dmax + 1) + 100
}.

(** The bound the overlay needs. *)
Definition overlay_bound_statement : Prop :=
  forall L b0 syms ll dl0 lmax dmax H sl sd,
    block_facts L b0 syms ll dl0 lmax dmax H sl sd ->
    forall k, (k <= length syms)%nat ->
      b0 + 3 + H + cost_sum ll dl0 (firstn k syms) <= 8 * (L + 3 * Z.of_nat k).
