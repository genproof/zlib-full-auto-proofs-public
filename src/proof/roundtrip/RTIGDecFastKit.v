(* RT-I: copy of rfc1951/DecFastKit.v over the generalized definitions RTIGDefs.v. *)
(* Part of the decode theory: inflate_fast.  The model's pass (Model.v fast_iter) cut
   along the C code, the invariant of inflate_fast's loop at a symbol
   boundary (`fi`) and at the end of the block (`fe`), and the statements of the parts:
   - walk_stmt (DecFastWalk.v): the table walk of inflate_fast decodes the symbol whose code is in the hold;
   - hblk_stmt (DecFastBlk.v): the facts of a Huffman block at symbol j (codes, bits, data, next symbol);
   - copy_stmt (DecFastCopy.v): the copy of a reference (window and output) is lz_copy;
   - iter_stmt (DecFastIter.v): one pass of the loop from `fi` at symbol j gives `fi` at j + 1 or `fe`.
   DecFast.v: the loop, the unused bytes given back, and Kd (dfast). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTIGDefs.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* the model's pass, along the C code (fast_iter_eq)                                              *)

(* if (bits < 15) { two bytes } *)
Definition refill2 (m: mst) : mst := if m_bits m <? 15 then fpull (fpull m) else m.

(* here = lcode + (hold & lmask); for (;;) { ... } *)
Definition lwalk (s: istate) (m: mst) : entry * mst :=
  fwalk_f lenfix_list distfix_list 2 len_link (i_lencode s)
    (tab_entry lenfix_list distfix_list s (i_lencode s) (m_hold m mod 2 ^ i_lenbits s)) m.
Definition dwalk (s: istate) (m: mst) : entry * mst :=
  fwalk_f lenfix_list distfix_list 2 dist_link (i_distcode s)
    (tab_entry lenfix_list distfix_list s (i_distcode s) (m_hold m mod 2 ^ i_distbits s)) m.

(* len = here->val; op &= 15; if (op) { ... } *)
Definition lenx (here: entry) (m: mst) : Z * mst :=
  let len := e_val here in
  let opx := Z.land (e_op here) 15 in
  if negb (opx =? 0) then
    let m := if m_bits m <? opx then fpull m else m in
    (u32 (len + m_hold m mod 2 ^ opx), set_m_bits (set_m_hold m (Z.shiftr (m_hold m) opx)) (u32 (m_bits m - opx)))
  else (len, m).

(* dist = here->val; op &= 15; pulls; dist += ...; hold >>= op; bits -= op; *)
Definition distx (here: entry) (m: mst) : Z * mst :=
  let dist := e_val here in
  let opx := Z.land (e_op here) 15 in
  let m := if m_bits m <? opx then (let m := fpull m in if m_bits m <? opx then fpull m else m) else m in
  let dist := u32 (dist + m_hold m mod 2 ^ opx) in
  let m := set_m_bits (set_m_hold m (Z.shiftr (m_hold m) opx)) (u32 (m_bits m - opx)) in
  (dist, m).

(* op = out - beg; the window or the direct copy *)
Definition fcopy (s: istate) (len dist: Z) (m: mst) : bool * mst :=
  let op := Zlength (m_ow m) in
  if op <? dist then
    let op := dist - op in
    if andb (i_whave s <? op) (negb (i_sane s =? 0)) then (false, set_bad m F_far) else
    let w := i_wdata s in
    let wsz := i_wsize s in let wnx := i_wnext s in
    let '(ow, sr, len) :=
      if wnx =? 0 then
        if op <? len then
          let '(ow, _) := copy_bytes w (SWin (wsz - op)) op (m_ow m) in
          (ow, SOut (Zlength ow - dist), len - op)
        else (m_ow m, SWin (wsz - op), len)
      else if wnx <? op then
        let op2 := op - wnx in
        if op2 <? len then
          let '(ow, _) := copy_bytes w (SWin (wsz + wnx - op)) op2 (m_ow m) in
          let len := len - op2 in
          if wnx <? len then
            let '(ow, _) := copy_bytes w (SWin 0) wnx ow in
            (ow, SOut (Zlength ow - dist), len - wnx)
          else (ow, SWin 0, len)
        else (m_ow m, SWin (wsz + wnx - op), len)
      else
        if op <? len then
          let '(ow, _) := copy_bytes w (SWin (wnx - op)) op (m_ow m) in
          (ow, SOut (Zlength ow - dist), len - op)
        else (m_ow m, SWin (wnx - op), len) in
    let '(ow, _) := copy_bytes w sr len ow in
    (true, set_m_ow m ow)
  else
    let '(ow, _) := copy_bytes (i_wdata s) (SOut (Zlength (m_ow m) - dist)) len (m_ow m) in
    (true, set_m_ow m ow).

(* the length branch *)
Definition flen (s: istate) (here: entry) (m: mst) : bool * mst :=
  let '(len, m) := lenx here m in
  let m := refill2 m in
  let '(here, m) := dwalk s m in
  if negb (Z.land (e_op here) 16 =? 0) then
    let '(dist, m) := distx here m in fcopy s len dist m
  else (false, set_bad m F_d_code).

(* the if-else chain after the length/literal walk *)
Definition fdisp (s: istate) (here: entry) (m: mst) : bool * mst :=
  let op := e_op here in
  if op =? 0 then (true, set_m_ow m (m_ow m ++ (e_val here mod 256)%Z :: nil))
  else if negb (Z.land op 16 =? 0) then flen s here m
  else if negb (Z.land op 32 =? 0) then (false, set_mode m Zlib.proof.inflate.Model.TYPE)
  else (false, set_bad m F_ll_code).

Lemma fast_iter_eq: forall m,
  fast_iter lenfix_list distfix_list m =
  (let '(here, m1) := lwalk (m_s m) (refill2 m) in fdisp (m_s m) here m1).
Proof. intros m. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the loop's invariant                                                                           *)

(* the machine m0 (inflate_fast's entry) with the locals next (nx), put (ow), hold and bits changed *)
Definition fset (m0: mst) (nx: Z) (ow: list Z) (hold bits: Z) : mst :=
  set_m_bits (set_m_hold (set_m_ow (set_m_nx m0 nx) ow) hold) bits.

(* at a symbol boundary: before symbol j of Huffman block k (j = |syms|: the end-of-block code); pos bytes
   consumed before the inflate() call, ob the output before it (history included) *)
Record fi (G: dctx) (pos: Z) (ob: list Z) (m0 m: mst) (k j: Z) (ll dl: list Z) (syms: list sym) : Prop := {
  fi_m : m = fset m0 (m_nx m) (m_ow m) (m_hold m) (m_bits m);
  fi_huff : in_huff G (m_s m0) k j ll dl syms (8 * (pos + m_nx m) - m_bits m);
  fi_out : ob ++ m_ow m = outj G k syms j;
  fi_hold : hold_ok G (pos + m_nx m) (m_hold m) (m_bits m);
  fi_bits : 0 <= m_bits m <= 32;
  fi_nx : m_nx m0 <= m_nx m <= Zlength (m_inp m0) /\ m_bits m - 8 * m_nx m <= m_bits m0 - 8 * m_nx m0;
  fi_ow : exists d, m_ow m = m_ow m0 ++ d }.

(* after the end-of-block code of block k (before `state->mode = TYPE`) *)
Record fe (G: dctx) (pos: Z) (ob: list Z) (m0 m: mst) (k: Z) : Prop := {
  fe_m : m = fset m0 (m_nx m) (m_ow m) (m_hold m) (m_bits m);
  fe_blk : in_blk G (m_s m0) k;
  fe_pos : 8 * (pos + m_nx m) - m_bits m = bpos G (k + 1);
  fe_out : ob ++ m_ow m = outk G (k + 1);
  fe_hold : hold_ok G (pos + m_nx m) (m_hold m) (m_bits m);
  fe_bits : 0 <= m_bits m <= 32;
  fe_nx : m_nx m0 <= m_nx m <= Zlength (m_inp m0) /\ m_bits m - 8 * m_nx m <= m_bits m0 - 8 * m_nx m0;
  fe_ow : exists d, m_ow m = m_ow m0 ++ d }.

(* ---------------------------------------------------------------------------------------------- *)
(* the parts                                                                                      *)

(* the walk (lwalk / dwalk) on a hold whose low bits are the code of sy (code bits available) gives the
   entry of sy and drops exactly its code length *)
Definition walk_stmt : Prop :=
  forall G c m type il t root lens sy,
    hold_ok G c (m_hold m) (m_bits m) -> bytes_ok (dc_src G) -> m_bits m <= 64 ->
    tdec (m_s m) t root type lens -> tvalid type lenfix_list distfix_list (m_s m) t root ->
    ((type = LENS /\ il = len_link) \/ (type = DISTS /\ il = dist_link)) ->
    0 <= sy < Zlength lens -> Znth sy lens <> 0 -> Znth sy lens <= m_bits m ->
    sublist (8 * c - m_bits m) (8 * c - m_bits m + Znth sy lens) (sbits G) = send_sym lens sy ->
    let l := Znth sy lens in
    let '(here, m') := fwalk_f lenfix_list distfix_list 2 il t
                         (tab_entry lenfix_list distfix_list (m_s m) t (m_hold m mod 2 ^ root)) m in
    ref.means_symbol type sy (e_op here) (e_val here) = true /\
    m' = set_m_bits (set_m_hold m (Z.shiftr (m_hold m) l)) (m_bits m - l).

(* a Huffman block at symbol j: its codes, its bits from p0 to the next block, the symbol j (well-formed, its
   data, the position after it), the end of its data *)
Definition hblk_stmt : Prop :=
  forall G s k j ll dl syms p0,
    dctx_ok G -> in_huff G s k j ll dl syms p0 ->
    Forall (fun l => 0 <= l <= 15) ll /\ Forall (fun l => 0 <= l <= 15) dl /\
    Znth 256 ll <> 0 /\ 256 < Zlength ll /\
    bpos G (k + 1) <= Zlength (sbits G) /\
    p0 + Zlength (flat_map (send_one ll dl) (skipn (Z.to_nat j) syms) ++ send_sym ll 256) = bpos G (k + 1) /\
    sublist p0 (bpos G (k + 1)) (sbits G) = flat_map (send_one ll dl) (skipn (Z.to_nat j) syms) ++ send_sym ll 256 /\
    (j < Zlength syms ->
       sym_ok (2 ^ dc_wb G) ll dl (outj G k syms j) (sym_at syms j) /\
       outj G k syms (j + 1) = sym_data (outj G k syms j) (sym_at syms j) /\
       in_huff G s k (j + 1) ll dl syms (p0 + Zlength (send_one ll dl (sym_at syms j)))) /\
    (j = Zlength syms -> outj G k syms j = outk G (k + 1)).

(* the copy of a reference (length len, distance dist within the output so far and the window) *)
Definition copy_stmt : Prop :=
  forall G s ob m len dist,
    swf s -> win_ok G s ob -> dc_wb G <= i_wbits s ->
    1 <= dist <= Zlength (ob ++ m_ow m) -> dist <= 2 ^ dc_wb G -> 3 <= len <= 258 ->
    exists ow', fcopy s len dist m = (true, set_m_ow m ow') /\
                ob ++ ow' = lz_copy (Z.to_nat len) dist (ob ++ m_ow m).

(* one pass of inflate_fast's loop (in < last, out < end: 6 input bytes, 258 output bytes) *)
Definition iter_stmt : Prop :=
  forall G pos ob m0 m k j ll dl syms,
    dctx_ok G -> 0 <= pos -> pos + Zlength (m_inp m0) <= Zlength (dc_src G) ->
    m_inp m0 = sublist pos (pos + Zlength (m_inp m0)) (dc_src G) ->
    mwf3 m0 -> m_mode m0 = LEN -> win_ok G (m_s m0) ob -> glob_ok G (m_s m0) ->
    fi G pos ob m0 m k j ll dl syms ->
    m_nx m + 6 <= Zlength (m_inp m0) -> Zlength (m_ow m) + 258 <= m_aout m0 ->
    let '(go, m') := fast_iter lenfix_list distfix_list m in
    (j < Zlength syms /\ go = true /\ fi G pos ob m0 m' k (j + 1) ll dl syms /\
     Zlength (m_ow m) < Zlength (m_ow m')) \/
    (j = Zlength syms /\ go = false /\
     exists mt, m' = set_mode mt Zlib.proof.inflate.Model.TYPE /\ fe G pos ob m0 mt k).
