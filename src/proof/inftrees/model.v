(* A functional model of zlib 1.3.2 inflate_table (inftrees.c), in plain Coq over the list of code
   lengths.  It follows the C code step by step (same variables, same order of writes), so that the
   VST proof of the body is a simulation, and the laws are theorems about this model.

   Conventions: all numbers are Z; `type` is 0 (CODES), 1 (LENS) or 2 (DISTS); `lens` is the list of
   code lengths lens[0..codes-1] (each 0..15); `req` is the requested root *bits (0..2^32-1); the table
   is the list of entries from *table on (index 0 = *table), `old` its contents before the call.
   Results: RErr (return -1, nothing written), REnough t (return 1, t = the table as left by the
   partial construction), ROk root used t (return 0, *bits := root, *table += used, t = the table). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* Table entries (inftrees.h `code`): op (uchar), bits (uchar), val (ushort).                      *)

Record entry := mkE { e_op : Z; e_bits : Z; e_val : Z }.

#[export] Instance entry_inhabitant : Inhabitant entry := mkE 0 0 0.

Definition entry_ok (e: entry) : Prop :=
  0 <= e_op e <= 255 /\ 0 <= e_bits e <= 255 /\ 0 <= e_val e <= 65535.

Definition CODES : Z := 0.
Definition LENS : Z := 1.
Definition DISTS : Z := 2.
Definition MAXBITS : Z := 15.
Definition ENOUGH_LENS : Z := 852.
Definition ENOUGH_DISTS : Z := 592.
Definition ENOUGH : Z := 1444.

(* The largest `codes` for which the call is defined (harness/common.h max_codes). *)
Definition max_codes (type: Z) : Z :=
  if type =? CODES then 20 else if type =? LENS then 288 else 32.

(* inftrees.c's static tables. *)
Definition lbase : list Z :=
  [3; 4; 5; 6; 7; 8; 9; 10; 11; 13; 15; 17; 19; 23; 27; 31;
   35; 43; 51; 59; 67; 83; 99; 115; 131; 163; 195; 227; 258; 0; 0].
Definition lext : list Z :=
  [16; 16; 16; 16; 16; 16; 16; 16; 17; 17; 17; 17; 18; 18; 18; 18;
   19; 19; 19; 19; 20; 20; 20; 20; 21; 21; 21; 21; 16; 199; 75].
Definition dbase : list Z :=
  [1; 2; 3; 4; 5; 7; 9; 13; 17; 25; 33; 49; 65; 97; 129; 193;
   257; 385; 513; 769; 1025; 1537; 2049; 3073; 4097; 6145;
   8193; 12289; 16385; 24577; 0; 0].
Definition dext : list Z :=
  [16; 16; 16; 16; 17; 17; 18; 18; 19; 19; 20; 20; 21; 21; 22; 22;
   23; 23; 24; 24; 25; 25; 26; 26; 27; 27;
   28; 28; 29; 29; 64; 64].

(* switch (type): match, base, extra (CODES: base = extra = NULL, never read for codes <= 19). *)
Definition match_of (type: Z) : Z :=
  if type =? CODES then 20 else if type =? LENS then 257 else 0.
Definition base_of (type: Z) : list Z :=
  if type =? CODES then [] else if type =? LENS then lbase else dbase.
Definition extra_of (type: Z) : list Z :=
  if type =? CODES then [] else if type =? LENS then lext else dext.

(* The entry of symbol s with `bits` bits (the first statements of the main loop). *)
Definition sym_entry (type s bits: Z) : entry :=
  let m := match_of type in
  if s + 1 <? m then mkE 0 bits s
  else if m <=? s then mkE (Znth (s - m) (extra_of type)) bits (Znth (s - m) (base_of type))
  else mkE 96 bits 0.

Definition invalid_entry (bits: Z) : entry := mkE 64 bits 0.

(* ---------------------------------------------------------------------------------------------- *)
(* Counts, min, max, root, the Kraft test, the sorted symbols.                                     *)

Fixpoint zseq (start: Z) (n: nat) : list Z :=
  match n with O => [] | S n' => start :: zseq (start + 1) n' end.

(* count[len] after the counting loop. *)
Definition count_len (lens: list Z) (l: Z) : Z := Zlength (filter (Z.eqb l) lens).
Definition counts (lens: list Z) : list Z := map (count_len lens) (zseq 0 16).

(* max: the longest length (0 when no symbol); min: the shortest nonzero length (when max >= 1). *)
Definition maxlen (lens: list Z) : Z := fold_right Z.max 0 lens.
Definition minlen (lens: list Z) : Z :=
  fold_right (fun l m => if l =? 0 then m else Z.min l m) 16 lens.

(* root: *bits lowered to max, raised to min (max >= 1). *)
Definition root_of (req: Z) (lens: list Z) : Z := Z.max (Z.min req (maxlen lens)) (minlen lens).

(* The `left` loop: for len = 1..15, left = 2*left - count[len], -1 as soon as it is negative. *)
Fixpoint left_loop (k: nat) (len left: Z) (cnt: list Z) : option Z :=
  match k with
  | O => Some left
  | S k' => let left' := 2 * left - Znth len cnt in
            if left' <? 0 then None else left_loop k' (len + 1) left' cnt
  end.
Definition left_final (cnt: list Z) : option Z := left_loop 15 1 1 cnt.

(* work[0..n): the used symbols sorted by length, by symbol within a length. *)
Definition syms_of_len (lens: list Z) (l: Z) : list Z :=
  map fst (filter (fun p => snd p =? l) (combine (zseq 0 (length lens)) lens)).
Definition sorted_syms (lens: list Z) : list Z := flat_map (syms_of_len lens) (zseq 1 15).

(* ---------------------------------------------------------------------------------------------- *)
(* The main loop.                                                                                 *)

(* The state at the top of the for(;;) loop.  `sym` indexes the sorted symbols; `next` is the
   offset of the current table from *table; `cnt` is count[] (decremented as codes are entered);
   `tab` the whole table region. *)
Record state := mkSt {
  s_huff : Z; s_sym : Z; s_len : Z; s_curr : Z; s_drop : Z; s_low : Z;
  s_used : Z; s_next : Z; s_cnt : list Z; s_tab : list entry }.

(* do { fill -= incr; next[base + fill] = here; } while (fill != 0), from fill = n * incr:
   writes at base + (n-1)*incr, ..., base + incr, base. *)
Fixpoint rep_fill (t: list entry) (base incr: Z) (n: nat) (e: entry) : list entry :=
  match n with
  | O => t
  | S n' => rep_fill (upd_Znth (base + Z.of_nat n' * incr) t e) base incr n' e
  end.

(* incr = 1 << (len - 1); while (huff & incr) incr >>= 1; *)
Fixpoint bincr_loop (k: nat) (huff incr: Z) : Z :=
  match k with
  | O => incr
  | S k' => if Z.land huff incr =? 0 then incr else bincr_loop k' huff (Z.shiftr incr 1)
  end.

(* The backwards increment of the len-bit code huff. *)
Definition next_huff (huff len: Z) : Z :=
  let incr := bincr_loop 16 huff (Z.shiftl 1 (len - 1)) in
  if incr =? 0 then 0 else Z.land huff (incr - 1) + incr.

(* curr = len - drop; left = 1 << curr;
   while (curr + drop < max) { left -= count[curr + drop]; if (left <= 0) break; curr++; left <<= 1; } *)
Fixpoint sub_loop (k: nat) (curr drop mx left: Z) (cnt: list Z) : Z :=
  match k with
  | O => curr
  | S k' =>
      if curr + drop <? mx then
        let left' := left - Znth (curr + drop) cnt in
        if left' <=? 0 then curr else sub_loop k' (curr + 1) drop mx (2 * left') cnt
      else curr
  end.
Definition sub_bits (len drop mx: Z) (cnt: list Z) : Z :=
  sub_loop 16 (len - drop) drop mx (Z.shiftl 1 (len - drop)) cnt.

(* (type == LENS && used > ENOUGH_LENS) || (type == DISTS && used > ENOUGH_DISTS) *)
Definition over (type used: Z) : bool :=
  ((type =? LENS) && (ENOUGH_LENS <? used)) || ((type =? DISTS) && (ENOUGH_DISTS <? used)).

Inductive outcome := Continue (s: state) | Break (s: state) | Full (s: state).

(* One iteration of the for(;;) loop.  W = work[] (sorted symbols), root, mx = max,
   mask = (1 << root) - 1. *)
Definition step (type: Z) (lens W: list Z) (root mx: Z) (s: state) : outcome :=
  let huff := s_huff s in let len := s_len s in let drop := s_drop s in let curr := s_curr s in
  let here := sym_entry type (Znth (s_sym s) W) (len - drop) in
  let t1 := rep_fill (s_tab s) (s_next s + Z.shiftr huff drop) (Z.shiftl 1 (len - drop))
                     (Z.to_nat (Z.shiftl 1 curr / Z.shiftl 1 (len - drop))) here in
  let min := Z.shiftl 1 curr in
  let huff' := next_huff huff len in
  let sym' := s_sym s + 1 in
  let c := Znth len (s_cnt s) - 1 in
  let cnt' := upd_Znth len (s_cnt s) c in
  let mask := Z.shiftl 1 root - 1 in
  if (c =? 0) && (len =? mx) then
    Break (mkSt huff' sym' len curr drop (s_low s) (s_used s) (s_next s) cnt' t1)
  else
    let len' := if c =? 0 then Znth (Znth sym' W) lens else len in
    if (root <? len') && negb (Z.land huff' mask =? s_low s) then
      let drop' := if drop =? 0 then root else drop in
      let next' := s_next s + min in
      let curr' := sub_bits len' drop' mx cnt' in
      let used' := s_used s + Z.shiftl 1 curr' in
      if over type used' then
        Full (mkSt huff' sym' len' curr' drop' (s_low s) used' next' cnt' t1)
      else
        let low' := Z.land huff' mask in
        let t2 := upd_Znth low' t1 (mkE curr' root next') in
        Continue (mkSt huff' sym' len' curr' drop' low' used' next' cnt' t2)
    else Continue (mkSt huff' sym' len' curr drop (s_low s) (s_used s) (s_next s) cnt' t1).

(* Iterate the loop at most k times. *)
Fixpoint run (type: Z) (lens W: list Z) (root mx: Z) (k: nat) (s: state) : outcome :=
  match k with
  | O => Continue s
  | S k' =>
      match step type lens W root mx s with
      | Continue s' => run type lens W root mx k' s'
      | o => o
      end
  end.

(* The initial state of the loop. *)
Definition init_state (lens: list Z) (root: Z) (old: list entry) : state :=
  mkSt 0 0 (minlen lens) root 0 (Z.ones 32) (Z.shiftl 1 root) 0 (counts lens) old.

(* After the loop: if (huff != 0) next[huff] = invalid entry of len - drop bits. *)
Definition finish (s: state) : list entry :=
  if s_huff s =? 0 then s_tab s
  else upd_Znth (s_next s + s_huff s) (s_tab s) (invalid_entry (s_len s - s_drop s)).

Inductive result := RErr | REnough (t: list entry) | ROk (root used: Z) (t: list entry).

(* The whole function.  (The loop runs once per used symbol: fuel = number of used symbols.) *)
Definition inflate_table_model (type: Z) (lens: list Z) (req: Z) (old: list entry) : result :=
  let mx := maxlen lens in
  if mx =? 0 then
    ROk 1 2 (upd_Znth 1 (upd_Znth 0 old (invalid_entry 1)) (invalid_entry 1))
  else
    let root := root_of req lens in
    match left_final (counts lens) with
    | None => RErr
    | Some lft =>
        if (0 <? lft) && ((type =? CODES) || negb (mx =? 1)) then RErr
        else
          let W := sorted_syms lens in
          if over type (Z.shiftl 1 root) then REnough old
          else
            match run type lens W root mx (length W) (init_state lens root old) with
            | Break s => ROk root (s_used s) (finish s)
            | Full s => REnough (s_tab s)
            | Continue s => ROk root (s_used s) (finish s)   (* unreachable: the loop breaks *)
            end
    end.

(* What the call returns, the table afterwards, how far *table advances, and *bits afterwards. *)
Definition it_ret (r: result) : Z :=
  match r with RErr => -1 | REnough _ => 1 | ROk _ _ _ => 0 end.
Definition it_tab (old: list entry) (r: result) : list entry :=
  match r with RErr => old | REnough t => t | ROk _ _ t => t end.
Definition it_adv (r: result) : Z :=
  match r with ROk _ u _ => u | _ => 0 end.
Definition it_bits (req: Z) (r: result) : Z :=
  match r with ROk root _ _ => root | _ => req end.

(* The capacity the call needs (the precondition of the spec): LENS/DISTS at least ENOUGH_LENS /
   ENOUGH_DISTS entries; CODES: A5 (the requested root is at least every length) and at least
   2^max entries, at least 2. *)
Definition cap_ok (type: Z) (lens: list Z) (req: Z) (cap: Z) : Prop :=
  (type = CODES -> maxlen lens <= req /\ 2 <= cap /\ Z.shiftl 1 (maxlen lens) <= cap) /\
  (type = LENS -> ENOUGH_LENS <= cap) /\
  (type = DISTS -> ENOUGH_DISTS <= cap).

(* The preconditions on the inputs. *)
Definition inputs_ok (type: Z) (lens: list Z) (req: Z) : Prop :=
  0 <= type <= 2 /\ Zlength lens <= max_codes type /\ Forall (fun l => 0 <= l <= MAXBITS) lens /\
  0 <= req <= 4294967295.
