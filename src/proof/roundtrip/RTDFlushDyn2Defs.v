(* RT-D FLUSH part DYN2: the facts about flush_prep's trees the dynamic block uses (statement). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDFlushDefs2.
Import ListNotations.
Local Open Scope Z_scope.

(* For level > 0, with LT / DT / BL the code lengths (Len fields) of the three trees of flush_prep's state s':
   the max codes, the guards, the length ranges, the codes the symbols / END_BLOCK / the header symbols use,
   Kraft equality (the codes are complete), and max_blindex. *)
Definition dyn2_facts_stmt : Prop :=
  forall t syms sl s' olb slb mbi,
    flush_pre t syms -> 0 < tr_level t -> flush_prep t sl = (s', olb, slb, mbi) ->
    (256 <= tr_lmax s' < 286 /\ 0 <= tr_dmax s' < 30) /\
    (Zlength (dl (tr_ltree s')) = HEAP_SIZE /\ Zlength (dl (tr_dtree s')) = 2 * D_CODES + 1 /\
     19 <= Zlength (dl (tr_bltree s')) /\ 19 <= Zlength (fc (tr_bltree s'))) /\
    (Znth (tr_lmax s' + 1) (dl (tr_ltree s')) = 65535 /\ Znth (tr_dmax s' + 1) (dl (tr_dtree s')) = 65535) /\
    (forall i, 0 <= i <= tr_lmax s' -> 0 <= Znth i (dl (tr_ltree s')) <= 15) /\
    (forall i, 0 <= i <= tr_dmax s' -> 0 <= Znth i (dl (tr_dtree s')) <= 15) /\
    (forall x, In x syms ->
       lcode_of x <= tr_lmax s' /\ code_ok (fc (tr_ltree s')) (dl (tr_ltree s')) (lcode_of x)) /\
    (forall x, In x syms -> fst x <> 0 ->
       d_code (fst x - 1) <= tr_dmax s' /\ code_ok (fc (tr_dtree s')) (dl (tr_dtree s')) (d_code (fst x - 1))) /\
    code_ok (fc (tr_ltree s')) (dl (tr_ltree s')) END_BLOCK /\
    F.kraft_sum (sublist 0 (tr_lmax s' + 1) (dl (tr_ltree s'))) = 2 ^ 15 /\
    F.kraft_sum (sublist 0 (tr_dmax s' + 1) (dl (tr_dtree s'))) = 2 ^ 15 /\
    (forall i, 0 <= i < 19 -> 0 <= Znth i (dl (tr_bltree s')) <= 7) /\
    F.kraft_sum (sublist 0 19 (dl (tr_bltree s'))) = 2 ^ 15 /\
    (forall q, In q (Header.tree_syms (dl (tr_ltree s')) (tr_lmax s') ++
                     Header.tree_syms (dl (tr_dtree s')) (tr_dmax s')) ->
       0 <= fst q < 19 /\ code_ok (fc (tr_bltree s')) (dl (tr_bltree s')) (fst q)) /\
    3 <= mbi <= 18 /\
    (forall r, mbi + 1 <= r < 19 -> Znth (Znth r bl_order) (dl (tr_bltree s')) = 0).
