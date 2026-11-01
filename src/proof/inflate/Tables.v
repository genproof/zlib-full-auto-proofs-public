(* Valid decoding tables: what the lookups of inflate() (LEN, DIST, CODELENS) and inflate_fast need of
   the table a pointer lencode/distcode designates, with root size lenbits/distbits.

   For every root index i < 2^rb: the entry is in the table; it is a link (op = sub-table bits,
   bits = rb, val = sub-table offset) whose sub-table entries are all in the table and final, or it is
   final.  A final entry has at most 15 bits in all (root and sub-table) and one of the meanings of its
   kind:
   - CODES (code length code): op 0 and val 0..18 (a code length symbol), or op 64 (invalid);
   - LENS: op 0, val 0..255 (literal); op 16..21, val 3..258 (length base, op & 15 extra bits);
     op 96 (end of block); op & 64 <> 0 with op & 48 = 0 (invalid);
   - DISTS: op 16..29, val 1..32768 (distance base, op & 15 extra bits); op & 64 <> 0 with op & 48 = 0
     (invalid).
   A link is "op <> 0 and op & 0xf0 = 0" for LENS/CODES (inflate's test: `here.op && (here.op & 0xf0) == 0`)
   and "op & 0xf0 = 0" for DISTS (`(here.op & 0xf0) == 0`). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.inflate.Model.
Import ListNotations.
Local Open Scope Z_scope.

Definition tab_size (t: tref) : Z :=
  match t with TLenfix => 512 | TDistfix => 32 | TCodes k => ENOUGH_CODES - k end.

Definition islink (kind op: Z) : bool :=
  (if kind =? DISTS then true else negb (op =? 0)) && (Z.land op 240 =? 0).

Definition final_ok (kind: Z) (e: entry) : Prop :=
  if kind =? CODES then (e_op e = 0 /\ 0 <= e_val e <= 18) \/ e_op e = 64
  else if kind =? LENS then
    (e_op e = 0 /\ 0 <= e_val e <= 255) \/ (16 <= e_op e <= 21 /\ 3 <= e_val e <= 258) \/ e_op e = 96 \/
    (Z.land (e_op e) 64 <> 0 /\ Z.land (e_op e) 48 = 0)
  else
    (16 <= e_op e <= 29 /\ 1 <= e_val e <= 32768) \/ (Z.land (e_op e) 64 <> 0 /\ Z.land (e_op e) 48 = 0).

(* A table given by its entry accessor `get` (index relative to the table's start): all entries read
   lie in [0, sz). *)
Definition sub_ok (kind: Z) (get: Z -> entry) (rb sz: Z) (e: entry) : Prop :=
  e_bits e = rb /\ 1 <= e_op e /\ rb + e_op e <= 15 /\
  forall j, 0 <= j < 2 ^ e_op e ->
    let e2 := get (e_val e + j) in
    0 <= e_val e + j < sz /\ entry_ok e2 /\ islink kind (e_op e2) = false /\
    rb + e_bits e2 <= 15 /\ final_ok kind e2.

Record tvalid_g (kind: Z) (get: Z -> entry) (rb sz: Z) : Prop := {
  tv_rb : 1 <= rb <= 15;
  tv_size : 2 ^ rb <= sz;
  tv_root : forall i, 0 <= i < 2 ^ rb ->
    let e := get i in
    entry_ok e /\
    (if islink kind (e_op e) then sub_ok kind get rb sz e else e_bits e <= rb /\ final_ok kind e) }.

(* the table t of the state, valid within sz entries *)
Definition tvalid_b (kind: Z) (fx dx: list entry) (s: istate) (t: tref) (rb sz: Z) : Prop :=
  tvalid_g kind (tab_entry fx dx s t) rb sz.

(* a valid table: all its reads within the table's region *)
Definition tvalid (kind: Z) (fx dx: list entry) (s: istate) (t: tref) (rb: Z) : Prop :=
  exists sz, sz <= tab_size t /\ tvalid_b kind fx dx s t rb sz.

(* a table as a list (inflate_table's output) *)
Definition tab_ok (kind: Z) (t: list entry) (rb sz: Z) : Prop := tvalid_g kind (fun i => Znth i t) rb sz.

Lemma tvalid_g_ext: forall kind g1 g2 rb sz,
  (forall i, 0 <= i < sz -> g1 i = g2 i) -> tvalid_g kind g1 rb sz -> tvalid_g kind g2 rb sz.
Proof.
  intros kind g1 g2 rb sz E [R S T]. constructor; auto.
  intros i Hi. specialize (T i Hi). cbv zeta in T |- *.
  assert (Ei: 0 <= i < sz) by (pose proof (Z.pow_pos_nonneg 2 rb); lia).
  rewrite <- (E i Ei). destruct T as [T1 T2]. split; auto.
  destruct (islink kind (e_op (g1 i))); auto.
  unfold sub_ok in *. destruct T2 as (A1 & A2 & A3 & A4).
  split; [exact A1|]. split; [exact A2|]. split; [exact A3|].
  intros j Hj. destruct (A4 j Hj) as (B1 & B2 & B3 & B4 & B5). cbv zeta in *.
  rewrite <- (E _ B1). auto.
Qed.

(* The covering fact as first stated: a table inflate_table builds is valid within the entries it
   uses.  It is false for a CODES table built from 20 code lengths; the case lemmas that build tables
   (LENLENS, CODELENS) use the corrected fact of Cover2.v (cover2_stmt) instead. *)
Definition cover_stmt : Prop :=
  forall type lens req old root used t,
    inputs_ok type lens req -> cap_ok type lens req (Zlength old) -> Forall entry_ok old ->
    inflate_table_model type lens req old = ROk root used t ->
    tab_ok type t root used /\ used <= Zlength old.
