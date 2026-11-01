(* LEN's fast path (inflate_fast, Model.v Section Fast) against the abstract decoder: the statements of the
   parts of si_fast and the facts they share.

   One pass of inflate_fast's loop decodes one symbol; the abstract decoder takes the steps of that symbol:
   LEN then LIT (a literal), LEN then LENEXT, DIST, DISTEXT and one MATCH step per byte (a match), LEN alone
   (the end of the block: TYPE, or an invalid code: BAD).  The concrete loop only changes the locals next,
   put, hold and bits (`fset`), and at its end the mode; the abstract steps only change the mode, length,
   offset and extra of the state (`fsx`).
   - fwalk_stmt: the table walk with at least 15 bits in the buffer reads the entry adecode finds at the
     bit position and drops its code's bits;
   - fcopy_stmt: the copy of a match (from the window, then from the output) appends lz_copy, or the
     distance is refused (F_far) exactly when it goes back past the whole output;
   - fmatch_stmt: the abstract MATCH steps of a match write lz_copy;
   - fiter_stmt: one pass of the loop moves the abstract state along the steps of its symbol.
   SISimFast.v: the loop, the unused bytes given back, and fast_sim_stmt.

   inflate_fast's own theory over the RFC 1951 decoder (rfc1951/DecFastKit.v) defines `fset` and the copy
   `fcopy`; they are used here by their qualified names (that development's `sbits` is another one). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.api_split_invariant.SIDefs.
Require Zlib.proof.rfc1951.DecFastKit.
Import ListNotations.
Local Open Scope Z_scope.

(* the copy of a match, one byte at a time: out ++ [out[|out| - dist]] ... *)
Notation lz_copy := Zlib.proof.rfc1951.Format.lz_copy.
(* the machine m0 with the locals next (nx), put (ow), hold and bits changed *)
Notation fset := Zlib.proof.rfc1951.DecFastKit.fset.
(* the copy of a match of inflate_fast: `op = out - beg; if (dist > op) { the window } else { the output }` *)
Notation fcopy := Zlib.proof.rfc1951.DecFastKit.fcopy.

(* the abstract state s after the steps of some symbols: the mode, length, offset and extra changed *)
Definition fsx (s: istate) (md l o e: Z) : istate :=
  set_i_mode (set_i_length (set_i_offset (set_i_extra s e) o) l) md.

(* ---------------------------------------------------------------------------------------------- *)
(* Traces                                                                                         *)

Lemma areach_trans src I R a b c : areach src I R a b -> areach src I R b c -> areach src I R a c.
Proof.
  intros H. revert c. induction H as [a|a n w a1 a' S NB H IH]; intros c H2; [exact H2|].
  eapply ar_step; eauto.
Qed.

(* one step within the limits *)
Lemma areach_one src I R a n w a1 :
  astep lenfix_list distfix_list src a = AGo n w a1 -> n <= 8 * I -> (w = true -> Zlength (a_O a) < R) ->
  areach src I R a a1.
Proof.
  intros S Hn Hw. eapply ar_step; [exact S| |apply ar_refl].
  simpl. intros [X|[X Y]]; [lia|]. specialize (Hw X). lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The parts                                                                                      *)

(* the walk of inflate_fast (fwalk_f, here = tab + (hold & mask), then one link at most) with at least 15
   bits in the buffer: the entry adecode finds at the bit position (the walk's link tests agree with
   adecode's on valid tables), its code's bits dropped; a final entry of the table *)
Definition fwalk_stmt : Prop :=
  forall src P0 m kind t nb sz il lk,
    bitbuf src P0 m -> tvalid_g kind (tab_entry lenfix_list distfix_list (m_s m) t) nb sz ->
    (kind = LENS /\ il = len_link /\ lk = len_islink) \/ (kind = DISTS /\ il = dist_link /\ lk = dist_islink) ->
    15 <= m_bits m ->
    let '(here, l) := adecode lenfix_list distfix_list src (m_s m) t nb lk (mq P0 m) in
    fwalk_f lenfix_list distfix_list 2 il t (tab_entry lenfix_list distfix_list (m_s m) t (m_hold m mod 2 ^ nb)) m =
      (here, dropbits l m) /\
    0 <= l <= 15 /\ entry_ok here /\ final_ok kind here /\
    exists i, 0 <= i < sz /\ here = tab_entry lenfix_list distfix_list (m_s m) t i.

(* the copy of a match of length len and distance dist with the window of the output O0 before the call
   (swin_ok) and the output m_ow of the call: refused when it goes back past O0 ++ m_ow, else lz_copy *)
Definition fcopy_stmt : Prop :=
  forall s O0 m len dist,
    swin_ok s O0 -> i_sane s = 1 -> 1 <= dist <= 32768 -> 3 <= len <= 258 ->
    (Zlength O0 + Zlength (m_ow m) < dist /\ fcopy s len dist m = (false, set_bad m F_far)) \/
    (dist <= Zlength O0 + Zlength (m_ow m) /\
     exists ow', fcopy s len dist m = (true, set_m_ow m ow') /\
                 O0 ++ ow' = lz_copy (Z.to_nat len) dist (O0 ++ m_ow m)).

(* the abstract MATCH steps of a match within the output so far: length steps, each writing one byte *)
Definition fmatch_stmt : Prop :=
  forall src I R a,
    a_mode a = MATCH -> 1 <= i_length (a_s a) -> 1 <= i_offset (a_s a) <= Zlength (a_O a) ->
    a_q a <= 8 * I -> Zlength (a_O a) + i_length (a_s a) <= R ->
    areach src I R a (AS (set_i_mode (set_i_length (a_s a) 0) LEN) (a_q a)
                         (lz_copy (Z.to_nat (i_length (a_s a))) (i_offset (a_s a)) (a_O a))).

(* one pass of inflate_fast's loop from a symbol boundary (at least 6 input bytes and 258 bytes of output
   space left, as the loop's test ensures): the abstract state moves along the steps of the symbol; the
   machine only changes its locals (mt) and, when the loop breaks, its mode: TYPE after the end-of-block
   code (the abstract state is in TYPE at the same bit position), BAD after an invalid code or a distance
   too far back (the abstract state is in BAD).  The bits pulled stay in the input of the call and the
   buffer keeps at most 30 bits. *)
Definition fiter_stmt : Prop :=
  forall src P0 O0 m a,
    bitbuf src P0 m -> m_mode m = LEN -> a_mode a = LEN -> a_q a = mq P0 m -> a_O a = O0 ++ m_ow m ->
    seq (m_s m) (a_s a) -> swin_ok (m_s m) O0 -> awf src a -> m_bits m <= 30 ->
    m_nx m + 6 <= Zlength (m_inp m) -> Zlength (m_ow m) + 258 <= m_aout m ->
    let '(go, m') := fast_iter lenfix_list distfix_list m in
    exists a' mt, areach src (P0 + Zlength (m_inp m)) (Zlength O0 + m_aout m) a a' /\
      mt = fset m (m_nx mt) (m_ow mt) (m_hold mt) (m_bits mt) /\
      bitbuf src P0 mt /\ m_bits mt <= 30 /\ m_bits mt - 8 * m_nx mt <= m_bits m - 8 * m_nx m /\
      a_O a' = O0 ++ m_ow mt /\ Zlength (m_ow mt) <= Zlength (m_ow m) + 258 /\
      ((go = true /\ m' = mt /\ Zlength (m_ow m) < Zlength (m_ow mt) /\ a_q a' = mq P0 mt /\
        exists l o e, a_s a' = fsx (a_s a) LEN l o e) \/
       (go = false /\ m' = set_mode mt Zlib.proof.inflate.Model.TYPE /\ a_q a' = mq P0 mt /\
        exists l o e, a_s a' = fsx (a_s a) Zlib.proof.inflate.Model.TYPE l o e) \/
       (go = false /\ a_mode a' = BAD /\ exists e, m' = set_bad mt e)).
