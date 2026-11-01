(* The pure facts about the model (model.v) that the laws need, stated against the reference model
   of harness/common.h (ref.v).  Each is a Prop here; its proof is in its own files
   (fact_result: fact_result.v and part_result.v; fact_decode: part_decode.v; fact_enough: part_enough.v).  The harness proofs take them as hypotheses, and
   the final theorem (src/contracts/suite.v) supplies the proofs. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.inftrees.model.
Require Export Zlib.proof.inftrees.ref.
Import ListNotations.
Local Open Scope Z_scope.

(* Laws inflate_table_safe / callers: the model's result, root and size are the references of
   common.h (expected_call), the entries from `used` on are unchanged, the entries stay in range. *)
Definition fact_result : Prop :=
  forall type lens req old,
  inputs_ok type lens req -> cap_ok type lens req (Zlength old) -> Forall entry_ok old ->
  match expected_call type lens req with
  | (want, root, size) =>
    match inflate_table_model type lens req old with
    | RErr => want = -1
    | REnough t => want = 1 /\ Zlength t = Zlength old /\ Forall entry_ok t
    | ROk r u t =>
        want = 0 /\ r = root /\ u = size /\ 1 <= u <= Zlength old /\
        (type = CODES -> u = Z.shiftl 1 r) /\
        Zlength t = Zlength old /\ Forall entry_ok t /\
        (forall i, u <= i < Zlength old -> Znth i t = Znth i old)
    end
  end.

(* Law inflate_table_decode: the table of a successful call is the canonical decoder (RFC 1951),
   as harness/inflate_table_decode.c checks it. *)
Definition fact_decode : Prop :=
  forall type lens req old root used t,
  inputs_ok type lens req -> cap_ok type lens req (Zlength old) -> Forall entry_ok old ->
  (type = CODES -> Zlength lens <= 19) ->
  inflate_table_model type lens req old = ROk root used t ->
  (forall s, 0 <= s < Zlength lens -> Znth s lens <> 0 ->
     forall x, 0 <= x < Z.shiftl 1 (longest lens - Znth s lens) ->
     exists op val,
       walk t used root
            (Z.lor (reverse_bits (rfc_code lens s) (Znth s lens)) (Z.shiftl x (Znth s lens)))
         = Some (op, val, Znth s lens) /\
       means_symbol type s op val = true) /\
  (kraft lens < GP_KRAFT_ONE ->
     forall pat, (if longest lens =? 0 then 0 else 1) <= pat < 2 ->
     walk t used root pat = Some (64, 0, 1)).

(* Law inflate_table_enough: ENOUGH_LENS / ENOUGH_DISTS suffice for inflate.c's dynamic blocks
   (LENS: at most 286 symbols, root 9; DISTS: at most 30 symbols, root 6). *)
Definition fact_enough : Prop :=
  forall type lens,
  (type = LENS /\ Zlength lens <= 286 \/ type = DISTS /\ Zlength lens <= 30) ->
  Forall (fun l => 0 <= l <= MAXBITS) lens ->
  expected_valid type lens = 0 ->
  two_level_size lens (expected_root (if type =? LENS then 9 else 6) lens)
    <= (if type =? LENS then ENOUGH_LENS else ENOUGH_DISTS).
