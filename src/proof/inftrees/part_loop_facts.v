(* Part: the loop invariants of the model (model_inv.v). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.inftrees.model_inv.
Require Zlib.proof.inftrees.slf_lib.
Require Zlib.proof.inftrees.slf_sorted_syms.
Require Zlib.proof.inftrees.slf_c_sorted.
Require Zlib.proof.inftrees.slf_c_bits.
Require Zlib.proof.inftrees.slf_c_subbits.
Import ListNotations.
Local Open Scope Z_scope.

Lemma loop_facts_ok : loop_facts.
Proof.
  exact (Zlib.proof.inftrees.slf_lib.slf_loop_facts
           Zlib.proof.inftrees.slf_c_sorted.sorted_ok2
           Zlib.proof.inftrees.slf_c_bits.bits_ok2
           Zlib.proof.inftrees.slf_c_subbits.subbits_ok2
           Zlib.proof.inftrees.slf_sorted_syms.slf_sorted_syms_ok).
Qed.
