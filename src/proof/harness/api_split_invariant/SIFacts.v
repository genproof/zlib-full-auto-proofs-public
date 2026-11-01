(* The interface between main() of harness/api_split_invariant.c and the theory of the law: what the
   proof of main needs to know about inflate()'s calls, over Spec5's relation inflate_rel (the exact
   model of a call).

   `Inv w src room P O L`: the stream after inflateInit2(windowBits w) and calls that read the first P
   bytes of the input src and wrote O, in at most `room` bytes of output space.
   `Max w src room O t`: O is what a stream of this input writes before it stops for good within this
   output space, and t is how it stops (Some r: inflate() returns r, one of Z_STREAM_END, Z_NEED_DICT,
   Z_DATA_ERROR; None: it waits for input or output space).  There is one such O and t (sf_max): that is
   the law.
   A call offered the rest of the input and of the space with a flush other than Z_BLOCK and Z_TREES
   reaches it (sf_call), as does a call that returns one of the three codes.  The one call of the
   harness is such a call from the initial state. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import VST.floyd.proofauto.
Require Export Zlib.proof.harness.api_split_invariant.SIDefs.
Import ListNotations.
Local Open Scope Z_scope.

Record si_facts (Inv: Z -> list Z -> Z -> Z -> list Z -> live -> Prop)
                (Max: Z -> list Z -> Z -> list Z -> option Z -> Prop) : Prop := {
  sf_init : forall w src room sp,
    si_window w -> bytes_ok src -> Zlength src <= Int.max_unsigned -> 0 <= room <= Int.max_unsigned ->
    Inv w src room 0 [] (init_live sp w);
  sf_call : forall w src room P O L flush strmp z ib inp o r z' st' ow,
    Inv w src room P O L -> live_ok L -> zf_ok z -> zf_tout z = Zlength O ->
    strmp <> nullval -> ib <> InNull ->
    zf_ai z = Zlength inp -> inp = sublist P (P + Zlength inp) src -> P + Zlength inp <= Zlength src ->
    Zlength O + zf_ao z <= room ->
    inflate_rel flush strmp z (Some L) ib inp (Some o) r z' st' ow ->
    r <> Z_MEM_ERROR ->
    exists L', st' = Some L' /\
      0 <= zf_ai z' <= zf_ai z /\ Zlength ow <= zf_ao z /\
      Inv w src room (P + (zf_ai z - zf_ai z')) (O ++ ow) L' /\
      zf_ni z' = in_ptr ib (zf_ai z - zf_ai z') /\ zf_no z' = out_ptr o (Zlength ow) /\
      zf_ao z' = zf_ao z - Zlength ow /\ zf_tout z' = Zlength (O ++ ow) /\
      (final_code r = true -> Max w src room (O ++ ow) (Some r)) /\
      (final_code r = false -> flush <> Z_BLOCK -> flush <> Z_TREES -> P + Zlength inp = Zlength src ->
         Zlength O + zf_ao z = room -> Max w src room (O ++ ow) None);
  sf_max : forall w src room O t O' t',
    Max w src room O t -> Max w src room O' t' -> O = O' /\ t = t' }.

Definition si_theory_stmt : Prop := exists Inv Max, si_facts Inv Max.

(* the theory from the call (a part) *)
Definition facts_part_stmt : Prop := awf_stmt -> call_stmt -> si_theory_stmt.
