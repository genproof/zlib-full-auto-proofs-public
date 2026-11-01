(* The reference model of harness/common.h, in plain Coq: the functions the harnesses use to state
   their checks (Kraft sum, longest/shortest length, expected result and root, two-level table size,
   RFC 1951 canonical codes, bit reversal, inflate's decoding step `walk`, the meaning of a symbol).
   Each definition computes what the C function of common.h computes, for in-range inputs (lengths
   0..15, at most 320 symbols, tables of entries with uchar/uchar/ushort fields): the harness proofs
   show that the C function returns this value; the facts (facts.v) relate them to the model of
   inflate_table (model.v).  Loops over an array are fold_left over the list, in the C order. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.inftrees.model.
Import ListNotations.
Local Open Scope Z_scope.

Definition GP_KRAFT_ONE : Z := 32768.

(* longest(lens, n) *)
Definition longest (lens: list Z) : Z := fold_left (fun m l => if m <? l then l else m) lens 0.

(* shortest(lens, n): the shortest nonzero length, 0 when none *)
Definition shortest (lens: list Z) : Z :=
  fold_left (fun m l => if negb (l =? 0) && ((m =? 0) || (l <? m)) then l else m) lens 0.

(* kraft(lens, n) = sum over used symbols of 2^(15 - len) *)
Definition kraft (lens: list Z) : Z :=
  fold_left (fun k l => if l =? 0 then k else k + Z.shiftl 1 (MAXBITS - l)) lens 0.

(* expected_valid(type, lens, n): 0 or -1 *)
Definition expected_valid (type: Z) (lens: list Z) : Z :=
  let mx := longest lens in
  let k := kraft lens in
  if mx =? 0 then 0
  else if GP_KRAFT_ONE <? k then -1
  else if (k <? GP_KRAFT_ONE) && ((type =? CODES) || negb (mx =? 1)) then -1
  else 0.

(* expected_root(req, lens, n) *)
Definition expected_root (req: Z) (lens: list Z) : Z :=
  let mx := longest lens in
  let mn := shortest lens in
  if mx =? 0 then 1
  else let r := if mx <? req then mx else req in
       if r <? mn then mn else r.

(* rfc_codes: bc[l] = number of codes of length l (bc[0] = 0); nc[1] = 0,
   nc[l] = (nc[l-1] + bc[l-1]) << 1; the symbols in increasing order get consecutive codes. *)
Definition bl_count (lens: list Z) (l: Z) : Z := if l =? 0 then 0 else count_len lens l.

Fixpoint next_code_loop (k: nat) (l c: Z) (lens: list Z) : Z :=
  match k with
  | O => c
  | S k' => next_code_loop k' (l + 1) (Z.shiftl (c + bl_count lens (l - 1)) 1) lens
  end.
(* nc[l] before the symbol loop, for 1 <= l <= 15: the loop c = (c + bc[l'-1]) << 1 for l' = 1..l *)
Definition next_code (lens: list Z) (l: Z) : Z := next_code_loop (Z.to_nat l) 1 0 lens.

(* cv[s]: the canonical code of symbol s (0 when unused) *)
Definition rfc_code (lens: list Z) (s: Z) : Z :=
  let l := Znth s lens in
  if l =? 0 then 0 else next_code lens l + count_len (sublist 0 s lens) l.

(* reverse_bits(c, len): r = (r << 1) | ((c >> i) & 1) for i = 0..len-1 *)
Fixpoint reverse_loop (k: nat) (i r c: Z) : Z :=
  match k with
  | O => r
  | S k' => reverse_loop k' (i + 1) (Z.lor (Z.shiftl r 1) (Z.land (Z.shiftr c i) 1)) c
  end.
Definition reverse_bits (c len: Z) : Z := reverse_loop (Z.to_nat len) 0 0 c.

(* two_level_size(lens, n, root): grp[p] = the longest code longer than root whose reversed code has
   low root bits p (0 when none); size = 2^root + sum over p with grp[p] != 0 of 2^(grp[p] - root). *)
Definition grp (lens: list Z) (root p: Z) : Z :=
  fold_left (fun g s =>
               let len := Znth s lens in
               if (root <? len) && (Z.land (reverse_bits (rfc_code lens s) len) (Z.shiftl 1 root - 1) =? p)
               then (if g <? len then len else g) else g)
            (zseq 0 (length lens)) 0.

Definition two_level_size (lens: list Z) (root: Z) : Z :=
  fold_left (fun total p => let g := grp lens root p in
                            if g =? 0 then total else total + Z.shiftl 1 (g - root))
            (zseq 0 (Z.to_nat (Z.shiftl 1 root))) (Z.shiftl 1 root).

(* expected_call(type, lens, n, req, &root, &size): (result, root, size) *)
Definition expected_call (type: Z) (lens: list Z) (req: Z) : Z * Z * Z :=
  let valid := expected_valid type lens in
  let root := expected_root req lens in
  let size := two_level_size lens root in
  let want := if negb (valid =? 0) then -1
              else if (type =? LENS) && (ENOUGH_LENS <? size) then 1
              else if (type =? DISTS) && (ENOUGH_DISTS <? size) then 1
              else 0 in
  (want, root, size).

(* walk(t, used, root, pat, &op, &val, &nbits): None for return 0, Some (op, val, nbits) for 1. *)
Definition is_link (op: Z) : bool := negb (op =? 0) && (Z.land op 240 =? 0).

Definition walk (t: list entry) (used root pat: Z) : option (Z * Z * Z) :=
  let i := Z.land pat (Z.shiftl 1 root - 1) in
  if used <=? i then None else
  let e := Znth i t in
  let o := e_op e in let b := e_bits e in let v := e_val e in
  if is_link o then
    if MAXBITS <? b + o then None else
    let j := v + Z.shiftr (Z.land pat (Z.shiftl 1 (b + o) - 1)) b in
    if used <=? j then None else
    let e2 := Znth j t in
    if is_link (e_op e2) then None else Some (e_op e2, e_val e2, b + e_bits e2)
  else Some (o, v, b).

(* RFC 1951 3.2.5 tables *)
Definition rfc_len_base : list Z :=
  [3; 4; 5; 6; 7; 8; 9; 10; 11; 13; 15; 17; 19; 23; 27; 31;
   35; 43; 51; 59; 67; 83; 99; 115; 131; 163; 195; 227; 258].
Definition rfc_len_extra : list Z :=
  [0; 0; 0; 0; 0; 0; 0; 0; 1; 1; 1; 1; 2; 2; 2; 2;
   3; 3; 3; 3; 4; 4; 4; 4; 5; 5; 5; 5; 0].
Definition rfc_dist_base : list Z :=
  [1; 2; 3; 4; 5; 7; 9; 13; 17; 25; 33; 49; 65; 97; 129; 193;
   257; 385; 513; 769; 1025; 1537; 2049; 3073; 4097; 6145; 8193; 12289; 16385; 24577].
Definition rfc_dist_extra : list Z :=
  [0; 0; 0; 0; 1; 1; 2; 2; 3; 3; 4; 4; 5; 5; 6; 6;
   7; 7; 8; 8; 9; 9; 10; 10; 11; 11; 12; 12; 13; 13].

Definition K_LIT : Z := 0.
Definition K_LENDIST : Z := 1.
Definition K_EOB : Z := 3.
Definition K_INVALID : Z := 4.

Definition sym_kind (type s: Z) : Z :=
  if type =? CODES then K_LIT
  else if type =? LENS then
    (if s <? 256 then K_LIT else if s =? 256 then K_EOB else if s <=? 285 then K_LENDIST else K_INVALID)
  else if s <=? 29 then K_LENDIST else K_INVALID.

Definition sym_value (type s: Z) : Z :=
  if type =? CODES then s
  else if type =? LENS then (if s <? 256 then s else Znth (s - 257) rfc_len_base)
  else Znth s rfc_dist_base.

Definition sym_extra (type s: Z) : Z :=
  if type =? LENS then Znth (s - 257) rfc_len_extra else Znth s rfc_dist_extra.

Definition means_symbol (type s op val: Z) : bool :=
  let k := sym_kind type s in
  if k =? K_LIT then (op =? 0) && (val =? sym_value type s)
  else if k =? K_LENDIST then (op =? 16 + sym_extra type s) && (val =? sym_value type s)
  else if k =? K_EOB then op =? 96
  else Z.land op 112 =? 64.
