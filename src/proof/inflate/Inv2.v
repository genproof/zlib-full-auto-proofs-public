(* The invariant of the inflate machine, strengthened (Inv.v's mwf is not preserved by one pass of the
   switch, and is too weak for inflate_fast):
   (A) the window size is 0 while wbits is 0 (HEAD changes wbits from 0, never wsize);
   (B) the length/literal table of a decoding mode is valid with every length entry's maximum length
       base + 2^extra - 1 <= 258 (Tables.final_ok LENS allows up to 289: inflate_fast would overflow
       its 258 bytes of guaranteed output space);
   (C) in LENEXT the length (a length base) is <= 258 (no 32-bit wrap to 0 when adding the extra bits);
   (D) in DISTEXT the offset (a distance base) is <= 32768 (no wrap to 0). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.inflate.Inv.
Import ListNotations.
Local Open Scope Z_scope.

(* a length entry's longest length *)
Definition len_ok (e: entry) : Prop := 16 <= e_op e <= 21 -> e_val e + 2 ^ (e_op e - 16) - 1 <= 258.

(* a valid length/literal table (Tables.v tvalid LENS) whose entries all satisfy len_ok *)
Definition tvalid_len (fx dx: list entry) (s: istate) (t: tref) (rb: Z) : Prop :=
  exists sz, sz <= tab_size t /\ tvalid_b LENS fx dx s t rb sz /\
    forall i, 0 <= i < sz -> len_ok (tab_entry fx dx s t i).

Record swf2 (s: istate) : Prop := {
  s2_wbits : i_wbits s = 0 -> i_wsize s = 0;
  s2_len : decode_mode (i_mode s) -> tvalid_len lenfix_list distfix_list s (i_lencode s) (i_lenbits s);
  s2_lenext : i_mode s = LENEXT -> i_length s <= 258;
  s2_distext : i_mode s = DISTEXT -> i_offset s <= 32768 }.

Definition mwf2 (m: mst) : Prop := mwf m /\ swf2 (m_s m).

Lemma mwf2_mwf: forall m, mwf2 m -> mwf m.
Proof. intros m [W _]. exact W. Qed.

Lemma tvalid_len_tvalid: forall fx dx s t rb, tvalid_len fx dx s t rb -> tvalid LENS fx dx s t rb.
Proof. intros fx dx s t rb (sz & A & B & _). exists sz. auto. Qed.
