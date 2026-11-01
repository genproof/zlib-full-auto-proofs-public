(* RT-D part FLUSH: interface v2 of the parts.  [RTDFlushDefs.tabs_stmt] is false: zlib's
   base_length[28] is 0 (length 258 has no extra bits), not len_base[28] - 3.  [tabs2_stmt] guards that conjunct
   with a nonzero number of extra bits (the only case in which compress_block sends lc - base_length). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDFlushDefs.
Import ListNotations.
Local Open Scope Z_scope.

Definition tabs2_stmt : Prop :=
  (forall c, 0 <= c < 288 -> cimpl static_ltree_code static_ltree_len F.fixed_ll c) /\
  (forall d, 0 <= d < 30 -> cimpl static_dtree_code static_dtree_len F.fixed_dl d) /\
  (forall lc, 0 <= lc <= 255 ->
     let code := Znth lc length_code_tab in
     code = F.len_code (lc + 3) /\ 0 <= code < 29 /\
     Znth code extra_lbits = Znth code F.len_extra /\
     (Znth code F.len_extra <> 0 -> Znth code base_length_tab = Znth code F.len_base - 3) /\
     0 <= Znth code F.len_extra <= 5 /\ 0 <= lc + 3 - Znth code F.len_base < 2 ^ Znth code F.len_extra) /\
  (forall dist, 1 <= dist <= 32768 ->
     let code := d_code (dist - 1) in
     code = F.dist_code dist /\ 0 <= code < 30 /\
     Znth code extra_dbits = Znth code F.dist_extra /\ Znth code base_dist_tab = Znth code F.dist_base - 1 /\
     0 <= Znth code F.dist_extra <= 13 /\ 0 <= dist - Znth code F.dist_base < 2 ^ Znth code F.dist_extra).
