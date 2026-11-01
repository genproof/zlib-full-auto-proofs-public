(* Law rt_session: the inflate side's facts for the sessions with a dictionary and the zlib wrapper: the zlib header
   and DICTID (6 bytes) read in any pieces, Z_NEED_DICT once DICTID is complete, inflateSetDictionary at mode DICT,
   then the decode theory for calls of any size (Decode7) on the context whose history is the dictionary. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.harness.rt_session.SIFacts.
Require Zlib.proof.harness.rt_session.SZdTheory.
Import ListNotations.
Local Open Scope Z_scope.

Theorem ses_itheory_zdict : ses_itheory_zdict_stmt.
Proof.
  (* SZdTheory.v: the invariants and their proof, on the decode theory Decode7 *)
  exact Zlib.proof.harness.rt_session.SZdTheory.szd_itheory_closed.
Qed.
