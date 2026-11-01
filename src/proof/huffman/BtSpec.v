(** * What build_tree computes: the specification used by the _tr_flush_block composition

    [bt_facts sd t w S F order R t' mc w'] describes [(t', mc, w') = build_tree sd t w]:
    - [S]: the symbols in the tree (the used ones, frequency > 0, then the forced ones [F], frequency 0 in [t],
      counted with frequency 1); [mc] = max_code = the largest symbol of [S];
    - [R]: a greedy Huffman tree over the leaves (x, fq x, 0) of [S] (HuffAbs.huff);
    - the lengths [dl t'] (Len fields): 0 outside [S]; the Huffman depths when no leaf of [R] is deeper than
      max_length; otherwise the lengths [Repair.repl] hands out along [order], the heap scan order (removal order,
      frequencies nondecreasing), from the depths along [order];
    - Kraft equality of the lengths, proper codes, opt_len/static_len accumulated as gen_bitlen does, sizes. *)

From Coq Require Import ZArith List Lia Bool Permutation.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.huffman.Model Zlib.proof.huffman.HuffAbs Zlib.proof.huffman.Heap
               Zlib.proof.huffman.Bits Zlib.proof.huffman.BuildPre Zlib.proof.huffman.Repair.
Import ListNotations.
Local Open Scope Z_scope.

(** The frequency of a symbol in the tree: 1 for a forced node, else its Freq. *)
Definition fq (t : tree) (F : list Z) (x : Z) : Z := if in_dec Z.eq_dec x F then 1 else Znth x (fc t).

(** The depth of the leaf of [R] with id [x] (0 when there is none). *)
Definition depth_of (R : item) (x : Z) : Z :=
  match find (fun l => lid l =? x) R with Some l => ld l | None => 0 end.

(** The extra bits of a symbol. *)
Definition xbits (sd : stat_desc) (n : Z) : Z := if n >=? sd_base sd then Znth (n - sd_base sd) (sd_extra sd) else 0.

Record bt_facts (sd : stat_desc) (t : tree) (w : work) (S F order : list Z) (R : item)
    (t' : tree) (mc : Z) (w' : work) : Prop := {
  bt_S : S = nzl (fc t) (sd_elems sd) ++ F /\ NoDup S /\ (forall x, In x S -> 0 <= x < sd_elems sd) /\
         (forall x, In x F -> Znth x (fc t) = 0) /\ Zlength F <= 2 /\
         (2 <= Zlength (nzl (fc t) (sd_elems sd)) -> F = []) /\ 2 <= Zlength S;
  bt_mc : In mc S /\ forall x, In x S -> x <= mc;
  bt_huff : huff (map (fun x => [(x, fq t F x, 0)]) S) R;
  bt_order : Permutation order S /\
             (forall i j, 0 <= i <= j -> j < Zlength order -> fq t F (Znth i order) <= fq t F (Znth j order));
  bt_len_out : forall c, 0 <= c < sd_elems sd -> ~ In c S -> Znth c (dl t') = 0;
  bt_len_in : forall c, In c S -> 1 <= Znth c (dl t') <= sd_maxlen sd;
  bt_noovf : (forall l, In l R -> ld l <= sd_maxlen sd) -> forall x, In x S -> Znth x (dl t') = depth_of R x;
  bt_ovf : ~ (forall l, In l R -> ld l <= sd_maxlen sd) ->
           forall k, 0 <= k < Zlength order ->
             Znth (Znth k order) (dl t') = Znth k (repl (sd_maxlen sd) (map (depth_of R) order));
  bt_kraft : HuffAbs.sumZ (map (fun x => 2 ^ (sd_maxlen sd - Znth x (dl t'))) S) = 2 ^ sd_maxlen sd;
  bt_codes : forall x, In x S -> code_ok (fc t') (dl t') x;
  bt_opt : w_opt_len w' = u64 (w_opt_len w - Zlength F +
             HuffAbs.sumZ (map (fun x => fq t F x * (Znth x (dl t') + xbits sd x)) S));
  bt_static : w_static_len w' =
             match sd_stree sd with
             | Some st => u64 (w_static_len w - HuffAbs.sumZ (map (fun x => Znth x st) F) +
                               HuffAbs.sumZ (map (fun x => fq t F x * (Znth x st + xbits sd x)) S))
             | None => w_static_len w
             end;
  bt_sizes : Zlength (fc t') = Zlength (fc t) /\ Zlength (dl t') = Zlength (dl t) /\
             Zlength (w_heap w') = HEAP_SIZE /\ Zlength (w_depth w') = HEAP_SIZE /\ Zlength (w_bl_count w') = 16
}.

(** The preconditions of build_tree (as _tr_flush_block calls it). *)
Record bt_req (sd : stat_desc) (t : tree) (w : work) : Prop := {
  bp_elems : 3 <= sd_elems sd <= 286 /\ 1 <= sd_maxlen sd <= 15 /\ sd_elems sd <= 2 ^ sd_maxlen sd;
  bp_size : Zlength (fc t) = Zlength (dl t) /\ 2 * sd_elems sd + 1 <= Zlength (fc t) <= HEAP_SIZE;
  bp_work : Zlength (w_heap w) = HEAP_SIZE /\ Zlength (w_depth w) = HEAP_SIZE /\
            0 <= w_opt_len w < 18446744073709551616 /\ 0 <= w_static_len w < 18446744073709551616;
  bp_frange : forall n, 0 <= n < Zlength (fc t) -> 0 <= Znth n (fc t) < 65536;
  bp_freq : (forall x, 0 <= x < sd_elems sd -> 0 <= Znth x (fc t)) /\
            HuffAbs.sumZ (map (fun x => Znth x (fc t)) (zseq 0 (Z.to_nat (sd_elems sd)))) + 2 < 65536;
  bp_tabs : (forall n, 0 <= n < Zlength (dl t) -> 0 <= xbits sd n <= 16) /\
            (forall st, sd_stree sd = Some st -> forall n, 0 <= n < Zlength (dl t) -> 0 <= Znth n st <= 16)
}.

Definition build_tree_statement : Prop :=
  forall sd t w, bt_req sd t w ->
    let '(t', mc, w') := build_tree sd t w in exists S F order R, bt_facts sd t w S F order R t' mc w'.
