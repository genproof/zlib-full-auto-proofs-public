(* The invariant of the inflate machine, third version.  Inv2.v's (A) (wbits = 0 -> wsize = 0) does not
   hold after inflateSync made a stream raw with wbits 0; what HEAD needs (it changes wbits
   only when wbits = 0 and wrap <> 0, without reallocating the window) is (A3): in HEAD with wbits 0 and a
   wrapper, the window is neither allocated nor in use (otherwise HEAD's change of wbits would change
   the size of a window in use, which then overflows).  (B)-(D) as in Inv2.v. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.inflate.Inv2.
Import ListNotations.
Local Open Scope Z_scope.

Record swf3 (s: istate) : Prop := {
  s3_head : i_mode s = HEAD -> i_wbits s = 0 -> i_wrap s <> 0 -> i_wsize s = 0 /\ i_win s = false;
  s3_len : decode_mode (i_mode s) -> tvalid_len lenfix_list distfix_list s (i_lencode s) (i_lenbits s);
  s3_lenext : i_mode s = LENEXT -> i_length s <= 258;
  s3_distext : i_mode s = DISTEXT -> i_offset s <= 32768 }.

Definition mwf3 (m: mst) : Prop := mwf m /\ swf3 (m_s m).

Lemma mwf3_mwf: forall m, mwf3 m -> mwf m.
Proof. intros m [W _]. exact W. Qed.
