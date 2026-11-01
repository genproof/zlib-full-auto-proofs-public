(** * Core part of the deflate law theory: INSERT_STRING and longest_match
    Statement: LTCSpecs.v; invariant: LTCW.v; shared lemmas: LTCLib.v. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTCLib.
Require Import Zlib.proof.deflate.LTCLmKit.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

Theorem lm_ok : ins_spec /\ lm_spec.
Proof.
  split; [exact ins_ok | exact lm_ok'].
Qed.
