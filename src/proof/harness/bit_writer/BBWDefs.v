(* Law rj_bad_block (harness/rj_bad_block.c): the interface between main (BBWMain.v, VST) and the theory of
   inflate() fed the broken stream in clip() pieces (BBWTheory.v).  Pure Coq over the model of inflate
   (Model2.run2 from Spec5.m_init).

   main chooses kind (0 stored, 1 reserved, 2 bad literal/length code, 3 bad distance code, 4 HLIT too large),
   which (0/1), the literals lits (kinds 2 and 3 only, any number) and the arbitrary bytes S0 of the stream (any
   length up to PTRDIFF_MAX), writes the block (BBFacts.bb_bytes: the bytes after the writes), and room >= |lits|
   bytes of output space.  Then it calls inflate() in pieces: each call is offered the next
   min(rest, 2^32 - 1) input bytes and min(room left, 2^32 - 1) bytes of output space; the loop goes on while the
   call returns Z_OK or Z_BUF_ERROR and one of the two was clipped; Z_MEM_ERROR ends the run.  After the loop, if
   the code is Z_OK and flush is Z_TREES, one more call is offered what the last one left.  The code must then be
   Z_DATA_ERROR.

   The theory chooses an invariant `J S0 kind which lits pos ob s` between calls (pos: input bytes consumed, ob:
   the output so far, s: the state of the stream) and proves `bbw_facts J`: it holds after inflateInit2_, and a
   call of the loop returns Z_DATA_ERROR or Z_MEM_ERROR, or returns Z_OK / Z_BUF_ERROR and keeps it; when that
   call was not clipped, it returned Z_OK with flush = Z_TREES and the next call, offered the rest, returns
   Z_DATA_ERROR (`bbw_extra`). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Export Zlib.proof.harness.bit_writer.BBFacts.
Import ListNotations.
Local Open Scope Z_scope.

(* the inputs main reaches inflate() with: as BBFacts.bb_ok, with any number of literals and a stream of any
   length up to PTRDIFF_MAX *)
Definition bbw_ok (S0: list Z) (kind which: Z) (lits: list Z) : Prop :=
  0 <= kind <= 4 /\ 0 <= which <= 1 /\ (kind <> 2 -> kind <> 3 -> lits = []) /\
  is_bytes lits /\ is_bytes S0 /\ 5 + 2 * Zlength lits <= Zlength S0 <= Int64.max_signed /\
  (kind = 0 ->
   let S := bb_bytes S0 kind which lits in
   Z.lor (Znth 1 S) (Z.shiftl (Znth 2 S) 8) <> Z.land (Z.lnot (Z.lor (Znth 3 S) (Z.shiftl (Znth 4 S) 8))) 65535).

(* the invariant between calls: S0 kind which lits, then pos ob s *)
Definition bbw_J : Type := list Z -> Z -> Z -> list Z -> Z -> list Z -> istate -> Prop.

(* after a call that was offered everything (Z_OK with Z_TREES, at the end of the block header): the next call,
   offered the rest of the stream from pos and output space for the literals not yet written, returns
   Z_DATA_ERROR *)
Definition bbw_extra (S0: list Z) (kind which: Z) (lits: list Z) (pos: Z) (ob: list Z) (s: istate) (flush: Z)
    : Prop :=
  let S := bb_bytes S0 kind which lits in
  forall L' z' res',
    l_s L' = s -> live_ok L' -> zf_ok z' -> Zlength lits <= Zlength ob + zf_ao z' ->
    run2 flush lenfix_list distfix_list (m_init z' L' (sublist pos (Zlength S) S)) res' ->
    r_ret res' = Z_DATA_ERROR.

(* the outcome of one call of the loop, offered inp (from pos) and zf_ao z bytes of output space, out of the
   rest Zlength S - pos and the room left room - |ob| *)
Definition bbw_post (J: bbw_J) (S0: list Z) (kind which: Z) (lits: list Z) (room pos: Z) (ob: list Z)
    (z: zfields) (inp: list Z) (flush: Z) (res: result) : Prop :=
  let S := bb_bytes S0 kind which lits in
  let m := r_m res in
  let ow := m_ow m in
  r_ret res = Z_DATA_ERROR \/ r_ret res = Z_MEM_ERROR \/
  ((r_ret res = Z_OK \/ r_ret res = Z_BUF_ERROR) /\
   0 <= m_snx m <= Zlength inp /\ m_sow m = Zlength ow /\ Zlength ow <= zf_ao z /\
   J S0 kind which lits (pos + m_snx m) (ob ++ ow) (m_s m) /\
   (Zlength S - pos <= Int.max_unsigned -> room - Zlength ob <= Int.max_unsigned ->
    r_ret res = Z_OK /\ flush = Z_TREES /\ ow = [] /\
    bbw_extra S0 kind which lits (pos + m_snx m) (ob ++ ow) (m_s m) flush)).

Record bbw_facts (J: bbw_J) : Prop := {
  (* after inflateInit2_(strm, w), raw *)
  bbw_init : forall S0 kind which lits sp w,
    bbw_ok S0 kind which lits -> -15 <= w <= -8 -> J S0 kind which lits 0 [] (l_s (init_live sp w));
  (* inflate(strm, flush) offered the next min(rest, 2^32 - 1) bytes and min(room left, 2^32 - 1) bytes of
     output space *)
  bbw_call : forall S0 kind which lits room pos ob L z inp flush res,
    bbw_ok S0 kind which lits ->
    let S := bb_bytes S0 kind which lits in
    J S0 kind which lits pos ob (l_s L) -> live_ok L -> zf_ok z ->
    0 <= pos <= Zlength S -> Zlength lits <= room -> Zlength ob <= room ->
    inp = sublist pos (pos + Z.min (Zlength S - pos) Int.max_unsigned) S ->
    zf_ao z = Z.min (room - Zlength ob) Int.max_unsigned ->
    Int.min_signed <= flush <= Int.max_signed ->
    run2 flush lenfix_list distfix_list (m_init z L inp) res ->
    bbw_post J S0 kind which lits room pos ob z inp flush res
}.

Definition bbw_theory_stmt : Prop := exists J, bbw_facts J.
