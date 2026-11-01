(* RT-D part FLUSH: the codes of _tr_flush_block's trees are the canonical codes of their lengths (interface: RTDFlushDefs.v). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDFlushDefs.
Require Zlib.proof.roundtrip.RTDFlushCanonApp.
Import ListNotations.
Local Open Scope Z_scope.

Theorem rtd_canon_ok : canon_stmt.
Proof.
  intros t syms sl s' olb slb mbi Hfp Hlev Hprep.
  assert (H := Zlib.proof.roundtrip.RTDFlushCanonApp.canon_prep t syms sl Hfp Hlev).
  rewrite Hprep in H. exact H.
Qed.
