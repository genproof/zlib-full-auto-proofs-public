(* THE covering fact with the length bound (Inv2.v (B)): a table inflate_table builds from valid inputs
   (19 lengths at most for CODES) is valid within the entries it uses, and a LENS table's length
   entries satisfy len_ok (they come from inftrees.c's lbase/lext). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.inflate.Inv2.
Local Open Scope Z_scope.

Definition cover3_stmt : Prop :=
  forall type lens req old root used t,
    inputs_ok type lens req -> (type = CODES -> Zlength lens <= 19) ->
    cap_ok type lens req (Zlength old) -> Forall entry_ok old ->
    inflate_table_model type lens req old = ROk root used t ->
    tab_ok type t root used /\ used <= Zlength old /\
    (type = LENS -> forall i, 0 <= i < used -> len_ok (Znth i t)).

(* The statement only: it is proved (Qed) from Cover2.cover2_proof and Cover3Len.cover3_len_inv2 as
   InvQ5.cover3_proof, DecMwf.dm_cover3 and IBRun.ib_cover3. *)
