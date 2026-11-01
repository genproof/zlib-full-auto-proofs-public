(** * Lemma (ii): the size of one block, for the tight deflateBound / compressBound

    Per-block accounting (Bound.v): if the bits written before a block are at most 8 * A (A = sum of (B_j + 5)
    over the earlier blocks, T bytes already handed out), the bits after it are at most 8 * (A + B + 5), B the
    block's stored_len.  With every block but the last holding at least 16383 bytes (deflate_fast with memLevel 8),
    Bound.acct_blocks turns this into the tight bound n + n>>12 + n>>14 + n>>25 + 7.

    [block_bound_statement] is that per-block step for the model's _tr_flush_block at memLevel 8: stored blocks,
    Huffman blocks with [buf <> NULL] (from the decision alone) and with [buf = NULL] (at least 32507 bytes in at
    most 16383 symbols, not Z_FIXED: Huffman optimality against Bound.r1 plus the repair overhead). *)

From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.huffman.Model Zlib.proof.huffman.HuffAbs Zlib.proof.huffman.Bits
               Zlib.proof.huffman.Overlay.
Import ListNotations.
Local Open Scope Z_scope.

(** The input bytes a symbol stands for: 1 for a literal, the match length lc + 3 for a match. *)
Definition sym_len (x : Z * Z) : Z := if fst x =? 0 then 1 else snd x + 3.
Definition blk_len (syms : list (Z * Z)) : Z := sumZ (map sym_len syms).

Definition block_bound_statement : Prop :=
  forall s syms buf stored_len last T A,
    flush_pre s syms -> 0 <= last <= 1 ->
    tr_lit_bufsize s = 16384 ->
    stored_len = blk_len syms ->
    match buf with
    | Some b => stored_len <= 65535 /\ stored_len <= Zlength b
    | None => 32507 <= stored_len /\ 0 < tr_level s /\ tr_strategy s <> Z_FIXED
    end ->
    0 <= T -> 8 * T + bitpos (tr_out s) <= 8 * A ->
    8 * T + bitpos (tr_out (fst (tr_flush_block s buf stored_len last))) <= 8 * (A + stored_len + 5).
