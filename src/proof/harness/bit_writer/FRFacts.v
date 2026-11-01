(* inflate() on a raw deflate stream whose first block is a fixed-Huffman block (RFC 1951 3.2.6) of literals
   followed by an invalid element: the interface between the two laws rj_bad_block (BBTheory.v) and rj_far_back
   (FBTheory.v) and the theory of these runs (FRTheory.v).  Pure Coq over the model of inflate (Model2.run2 from
   Spec5.m_init).

   The context C: the input bytes src; its bit 0 is BFINAL (any), bits 1-2 are BTYPE 01 (fixed codes), then the
   fixed codes of the literals, then the tail:
   - TLL w:      the literal/length code 286 + w (never valid, 3.2.6);
   - TDCode w:   the length code 257 (length 3), then the distance code 30 + w (never valid);
   - TFar lc lx dc dx: the length code lc (257..285) and its extra bits lx, the distance code dc (0..29) and its
                 extra bits dx: a distance dist_base[dc] + dx larger than the number of literals (3.2.3: "a
                 distance cannot refer past the beginning of the output stream");
   then anything.  fr_end C is the bit position after the tail.

   The theory chooses an invariant `I C pos ob s` between calls (pos: input bytes consumed so far, ob: the
   output so far, s: the state of the stream) and proves `fr_facts I`: it holds after inflateInit2_, the output
   is never more than the literals, and one inflate() call keeps it and either reaches the error (Z_DATA_ERROR),
   or fails to allocate the window (Z_MEM_ERROR), or returns Z_OK / Z_BUF_ERROR for one of the reasons
   `fr_stop`: Z_TREES at the end of the block header, the output space full before the error, or the input
   ending before fr_end C. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Export Zlib.proof.rfc1951.Format.
Require Export Zlib.proof.inflate_api.Spec5.
Require Export Zlib.proof.inflate.Model2.
Import ListNotations.
Local Open Scope Z_scope.

Inductive frtail :=
| TLL (w: Z)
| TDCode (w: Z)
| TFar (lc lx dc dx: Z).

Record frc := FRC { fr_src : list Z; fr_lits : list Z; fr_tail : frtail }.

(* the bits of the tail *)
Definition tail_bits (t: frtail) : list bool :=
  match t with
  | TLL w => send_sym fixed_ll (286 + w)
  | TDCode w => send_sym fixed_ll 257 ++ send_sym fixed_dl (30 + w)
  | TFar lc lx dc dx =>
      send_sym fixed_ll lc ++ bits_le lx (Znth (lc - 257) len_extra) ++
      send_sym fixed_dl dc ++ bits_le dx (Znth dc dist_extra)
  end.

Definition tail_ok (n: Z) (t: frtail) : Prop :=
  match t with
  | TLL w => 0 <= w <= 1
  | TDCode w => 0 <= w <= 1
  | TFar lc lx dc dx =>
      257 <= lc <= 285 /\ 0 <= lx < 2 ^ Znth (lc - 257) len_extra /\
      0 <= dc <= 29 /\ 0 <= dx < 2 ^ Znth dc dist_extra /\ n < Znth dc dist_base + dx
  end.

Definition is_far (t: frtail) : Prop := match t with TFar _ _ _ _ => True | _ => False end.

(* the block's bits after BFINAL and BTYPE *)
Definition fr_body (C: frc) : list bool := concat (map (send_sym fixed_ll) (fr_lits C)) ++ tail_bits (fr_tail C).
Definition fr_end (C: frc) : Z := 3 + Zlength (fr_body C).

Definition fr_ok (C: frc) : Prop :=
  bytes_ok (fr_src C) /\
  Forall (fun l => 0 <= l < 256) (fr_lits C) /\ Zlength (fr_lits C) <= Int64.max_unsigned /\
  tail_ok (Zlength (fr_lits C)) (fr_tail C) /\
  fr_end C <= 8 * Zlength (fr_src C) /\
  sublist 1 3 (bytes_bits (fr_src C)) = [true; false] /\
  sublist 3 (fr_end C) (bytes_bits (fr_src C)) = fr_body C.

(* why a call that did not reach the error returned (pos: consumed before the call, used: consumed by it, ninp:
   offered, nob: output before the call, now: output of the call, aout: output space offered) *)
Definition fr_stop (C: frc) (pos used ninp nob now aout flush: Z) : Prop :=
  (* Z_TREES: "when the end of each deflate block header is reached" (the call started before it) *)
  (flush = Z_TREES /\ pos = 0 /\ 0 < used /\ now = 0) \/
  (* the output space is full with a literal still to write, or with the match to copy *)
  (now = aout /\ (nob + now < Zlength (fr_lits C) \/ (is_far (fr_tail C) /\ nob + now = Zlength (fr_lits C)))) \/
  (* the input ends before the error *)
  8 * (pos + ninp) < fr_end C.

(* the outcome of one call, offered inp (the next bytes of src) and zf_ao z bytes of output space *)
Definition fr_post (I: frc -> Z -> list Z -> istate -> Prop) (C: frc) (pos: Z) (ob: list Z) (L: live)
    (z: zfields) (inp: list Z) (flush: Z) (res: result) : Prop :=
  let m := r_m res in
  let ow := m_ow m in
  let stop := fr_stop C pos (m_snx m) (Zlength inp) (Zlength ob) (Zlength ow) (zf_ao z) flush in
  0 <= m_snx m <= Zlength inp /\ m_sow m = Zlength ow /\ Zlength ow <= zf_ao z /\
  (ow = [] -> i_wsize (l_s L) = 0 -> i_wsize (m_s m) = 0) /\
  ((r_ret res = Z_DATA_ERROR /\ I C (pos + m_snx m) (ob ++ ow) (m_s m)) \/
   (r_ret res = Z_MEM_ERROR /\ (stop \/ i_wsize (l_s L) <> 0)) \/
   ((r_ret res = Z_OK \/ r_ret res = Z_BUF_ERROR) /\ stop /\ I C (pos + m_snx m) (ob ++ ow) (m_s m))).

Record fr_facts (I: frc -> Z -> list Z -> istate -> Prop) : Prop := {
  (* after inflateInit2_(strm, w), raw *)
  fr_init : forall C sp w, fr_ok C -> -15 <= w <= -8 -> I C 0 [] (l_s (init_live sp w));
  fr_out : forall C pos ob s, I C pos ob s -> Zlength ob <= Zlength (fr_lits C);
  (* inflate(strm, flush) offered src[pos .. pos + |inp|) *)
  fr_call : forall C pos ob L z inp flush res,
    fr_ok C -> I C pos ob (l_s L) -> live_ok L -> zf_ok z ->
    0 <= pos -> pos + Zlength inp <= Zlength (fr_src C) -> inp = sublist pos (pos + Zlength inp) (fr_src C) ->
    Zlength inp <= Int.max_unsigned -> Int.min_signed <= flush <= Int.max_signed ->
    run2 flush lenfix_list distfix_list (m_init z L inp) res ->
    fr_post I C pos ob L z inp flush res
}.

Definition fr_theory_stmt : Prop := exists I, fr_facts I.
