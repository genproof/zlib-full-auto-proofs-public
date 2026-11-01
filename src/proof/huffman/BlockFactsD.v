(** * Lemma (i) for lit_bufsize >= 4096: block facts on the unlimited Huffman depths

    For L >= 4096 the literal/length and distance trees may need gen_bitlen's length-limit repair, and the
    repaired lengths satisfy no shifted Fibonacci cap (Repair.cex_no_shifted_cap).  The bound is then carried by
    the unlimited Huffman depths [dd]/[dd0] (Kraft equality, Fibonacci caps, (A) because the repaired code costs at
    least the Huffman code), and the actual lengths differ from them by a repair overhead [X] (the frequency-weighted
    positive part of actual length minus depth, both trees), which must stay below [slack L]. *)

From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.huffman.Model Zlib.proof.huffman.HuffAbs Zlib.proof.huffman.Heap
               Zlib.proof.huffman.Bits Zlib.proof.huffman.Header Zlib.proof.huffman.Overlay
               Zlib.proof.huffman.BlockFacts.
Import ListNotations.
Local Open Scope Z_scope.

Record block_facts_d (L b0 : Z) (syms : list (Z * Z)) (dd dd0 : list Z) (H : Z) : Prop := {
  bd_L : exists ml, 6 <= ml <= 9 /\ L = 2 ^ (ml + 6);
  bd_b0 : 0 <= b0 <= 7;
  bd_n : 1 <= Zlength syms <= L - 1;
  bd_valid : forall x, In x syms -> valid_sym (fst x) (snd x);
  bd_size : Zlength dd >= L_CODES /\ Zlength dd0 >= D_CODES;
  (* depths: positive exactly on the used codes (literal/length); positive on the used distance codes and on at
     most two forced codes *)
  bd_lused : forall c, 0 <= c < L_CODES -> (0 < lfreq syms c <-> Znth c dd <> 0);
  bd_llen : forall c, 0 <= c < L_CODES -> 0 <= Znth c dd <= 30;
  bd_dused : forall d, 0 <= d < D_CODES -> 0 < dfreq syms d -> Znth d dd0 <> 0;
  bd_dlen : forall d, 0 <= d < D_CODES -> 0 <= Znth d dd0 <= 30;
  bd_kraft_l : zsum L_CODES (fun c => if Znth c dd =? 0 then 0 else 2 ^ (30 - Znth c dd)) = 2 ^ 30;
  bd_kraft_d : zsum D_CODES (fun d => if Znth d dd0 =? 0 then 0 else 2 ^ (30 - Znth d dd0)) <= 2 ^ 30;
  bd_cap_l : forall c, 0 <= c < L_CODES -> 0 < lfreq syms c -> lfreq syms c * fib (Znth c dd + 1) <= L + 1;
  bd_cap_d : forall d, 0 <= d < D_CODES -> 0 < dfreq syms d -> dfreq syms d * fib (Znth d dd0 + 1) <= L + 1;
  bd_A : H + zsum L_CODES (fun c => lfreq syms c * (Znth c dd - Znth c static_ltree_len))
           + zsum D_CODES (fun d => dfreq syms d * (Znth d dd0 - 5)) <= -1;
  bd_H : H <= 2283
}.
