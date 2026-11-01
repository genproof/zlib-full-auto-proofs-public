(* The corrected covering fact (copied from Cover2.v: only the Definition).  Tables.v's cover_stmt is
   false for a CODES table built from 20 code lengths; inflate always builds the code length code from
   19 lengths. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.inflate.Inv.
Local Open Scope Z_scope.

Definition cover2_stmt : Prop :=
  forall type lens req old root used t,
    inputs_ok type lens req -> (type = CODES -> Zlength lens <= 19) ->
    cap_ok type lens req (Zlength old) -> Forall entry_ok old ->
    inflate_table_model type lens req old = ROk root used t ->
    tab_ok type t root used /\ used <= Zlength old.
