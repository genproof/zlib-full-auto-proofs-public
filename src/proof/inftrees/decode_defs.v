(* Definitions and part statements for fact_decode (facts.v).
   The table contents of the model (model.v) during and after the main loop, on fact_result.v's
   abstract view: ls = the sorted lengths (sl lens), W = the sorted symbols (sorted_syms lens),
   C_j = kpre ls j / 2^(15 - l_j) the canonical code of position j (MSB first),
   huff_j = reverse_bits C_j l_j (the code as the table indexes it). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.inftrees.facts.
Require Import Zlib.proof.inftrees.fact_result.
Require Import Zlib.proof.inftrees.model_inv.
Import ListNotations.
Local Open Scope Z_scope.

(* The hypotheses of fact_result.v's Section Loop, bundled, plus the acceptance test of
   inflate_table: an incomplete code has longest length 1. *)
Definition dhyps (type: Z) (lens W ls: list Z) (root: Z) (old: list entry) : Prop :=
  Forall (fun l => 1 <= l <= MAXBITS) ls /\
  (forall a b, 0 <= a -> a <= b < Zlength ls -> Znth a ls <= Znth b ls) /\
  0 < Zlength ls /\
  (forall i, 0 <= i < Zlength ls -> Znth (Znth i W) lens = Znth i ls) /\
  Forall (fun s => 0 <= s <= 65535) W /\
  Znth 0 ls <= root <= Znth (Zlength ls - 1) ls /\
  ksum ls <= 2 ^ MAXBITS /\
  (ksum ls < 2 ^ MAXBITS -> Znth (Zlength ls - 1) ls <= root) /\
  0 <= type <= 2 /\
  (type = CODES -> Znth (Zlength ls - 1) ls <= root) /\
  ((type = LENS -> ENOUGH_LENS <= Zlength old) /\ (type = DISTS -> ENOUGH_DISTS <= Zlength old)) /\
  2 ^ root <= Zlength old /\
  Forall entry_ok old /\
  (ksum ls < 2 ^ MAXBITS -> Znth (Zlength ls - 1) ls = 1).

(* Canonical code of sorted position j, and its bit-reversed form (the table index). *)
Definition dcode (ls: list Z) (j: Z) : Z := kpre ls j / 2 ^ (MAXBITS - Znth j ls).
Definition dhuff (ls: list Z) (j: Z) : Z := reverse_bits (dcode ls j) (Znth j ls).

(* Offset of the sub-table of root prefix q, and the root-table link entry of position j. *)
Definition dnxt (ls: list Z) (root q: Z) : Z := 2 ^ root + sumq ls root q.
Definition dlink (ls: list Z) (root j: Z) : entry :=
  mkE (gmax ls root (pfx ls root j) - root) root (dnxt ls root (pfx ls root j)).

(* The entries the do/while fill of position j wrote (rep_fill of model.step):
   short code (l <= root): huff_j + k*2^l, k < 2^(root-l), entry with l bits;
   long code: dnxt p + (huff_j >> root) + k*2^(l-root), k < 2^(g-l), entry with l-root bits. *)
Definition fills_done (type: Z) (W ls: list Z) (root j: Z) (tab: list entry) : Prop :=
  (Znth j ls <= root -> forall k, 0 <= k < 2 ^ (root - Znth j ls) ->
     Znth (dhuff ls j + k * 2 ^ Znth j ls) tab = sym_entry type (Znth j W) (Znth j ls)) /\
  (root < Znth j ls -> forall k, 0 <= k < 2 ^ (gmax ls root (pfx ls root j) - Znth j ls) ->
     Znth (dnxt ls root (pfx ls root j) + Z.shiftr (dhuff ls j) root + k * 2 ^ (Znth j ls - root)) tab
       = sym_entry type (Znth j W) (Znth j ls - root)).

(* The root-table link of the group of a long position j. *)
Definition link_done (ls: list Z) (root j: Z) (tab: list entry) : Prop :=
  root < Znth j ls -> Znth (reverse_bits (pfx ls root j) root) tab = dlink ls root j.

(* Table contents at the top of iteration i: the fills of positions < i, the links of the groups
   of positions <= i (the link of i's group is written by the iteration before the group). *)
Definition dcontent (type: Z) (W ls: list Z) (root i: Z) (tab: list entry) : Prop :=
  (forall j, 0 <= j < i -> fills_done type W ls root j tab) /\
  (forall j, 0 <= j <= i -> j < Zlength ls -> link_done ls root j tab).

(* The final table (after the loop and `finish`): every fill and link, `used` covers the root
   table and every sub-table; an incomplete code is one code of length 1, root 1, and entry 1 is
   the invalid entry. *)
Definition dfinal (type: Z) (W ls: list Z) (root used: Z) (t: list entry) : Prop :=
  (forall j, 0 <= j < Zlength ls -> fills_done type W ls root j t /\ link_done ls root j t) /\
  2 ^ root <= used /\
  (forall j, 0 <= j < Zlength ls -> root < Znth j ls ->
     dnxt ls root (pfx ls root j) + 2 ^ (gmax ls root (pfx ls root j) - root) <= used) /\
  (ksum ls < 2 ^ MAXBITS ->
     Zlength ls = 1 /\ Znth 0 ls = 1 /\ root = 1 /\ used = 2 /\ Znth 1 t = invalid_entry 1).

(* ---------------------------------------------------------------------------------------------- *)
(* Part statements.                                                                              *)

(* One iteration that continues keeps the contents (the new writes hit no earlier entry). *)
Definition dstep_stmt : Prop :=
  forall type lens W ls root old i s s',
  dhyps type lens W ls root old -> bits_stmt -> subbits_stmt ->
  inv ls root old i s -> dcontent type W ls root i (s_tab s) -> i + 1 < Zlength ls ->
  step type lens W root (Znth (Zlength ls - 1) ls) s = Continue s' ->
  dcontent type W ls root (i + 1) (s_tab s').

(* The last iteration (i = N-1) breaks with every fill done. *)
Definition dlast_stmt : Prop :=
  forall type lens W ls root old s,
  dhyps type lens W ls root old -> bits_stmt -> subbits_stmt ->
  inv ls root old (Zlength ls - 1) s -> dcontent type W ls root (Zlength ls - 1) (s_tab s) ->
  exists s', step type lens W root (Znth (Zlength ls - 1) ls) s = Break s' /\
    s_used s' = s_used s /\ s_next s' = s_next s /\ s_len s' = s_len s /\ s_drop s' = s_drop s /\
    s_huff s' = next_huff (s_huff s) (s_len s) /\
    (forall j, 0 <= j < Zlength ls -> fills_done type W ls root j (s_tab s') /\ link_done ls root j (s_tab s')).

(* The model's loop from the initial state, run to the end, gives the final table. *)
Definition drun_stmt : Prop :=
  forall type lens req old s,
  sorted_stmt -> bits_stmt -> subbits_stmt -> dstep_stmt -> dlast_stmt ->
  Forall (fun l => 0 <= l <= MAXBITS) lens -> maxlen lens <> 0 ->
  dhyps type lens (sorted_syms lens) (sl lens) (root_of req lens) old ->
  (run type lens (sorted_syms lens) (root_of req lens) (maxlen lens) (length (sorted_syms lens))
       (init_state lens (root_of req lens) old) = Break s \/
   run type lens (sorted_syms lens) (root_of req lens) (maxlen lens) (length (sorted_syms lens))
       (init_state lens (root_of req lens) old) = Continue s) ->
  dfinal type (sorted_syms lens) (sl lens) (root_of req lens) (s_used s) (finish s).

(* The decoding step on the final table: code j, extended by any bits up to the longest length,
   walks to the entry of its symbol with l_j bits. *)
Definition dwalk_stmt : Prop :=
  forall type lens W ls root old used t,
  dhyps type lens W ls root old -> bits_stmt ->
  (forall j b, 0 <= j < Zlength ls -> is_link (e_op (sym_entry type (Znth j W) b)) = false) ->
  dfinal type W ls root used t ->
  forall j x, 0 <= j < Zlength ls -> 0 <= x < 2 ^ (Znth (Zlength ls - 1) ls - Znth j ls) ->
  walk t used root (Z.lor (dhuff ls j) (Z.shiftl x (Znth j ls)))
    = Some (e_op (sym_entry type (Znth j W) 0), e_val (sym_entry type (Znth j W) 0), Znth j ls).

(* The Section Loop hypotheses hold for an accepted code with at least one symbol. *)
Definition dsetup_stmt : Prop :=
  forall type lens req old lft,
  sorted_stmt ->
  inputs_ok type lens req -> cap_ok type lens req (Zlength old) -> Forall entry_ok old ->
  maxlen lens <> 0 ->
  left_final (counts lens) = Some lft ->
  ((0 <? lft) && ((type =? CODES) || negb (maxlen lens =? 1))) = false ->
  over type (Z.shiftl 1 (root_of req lens)) = false ->
  dhyps type lens (sorted_syms lens) (sl lens) (root_of req lens) old.
