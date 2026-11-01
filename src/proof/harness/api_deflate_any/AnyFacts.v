(* Law api_deflate_any: the model facts main needs, and the return codes of deflate() and deflateParams().

   main of harness/api_deflate_any.c drives one stream by the calls of law api_deterministic's main (deflateInit2
   with any parameters, then deflate() calls on pieces of the data, maybe deflateParams() before each, Z_FINISH
   repeated with the rest once given), with two differences: the flush is any int, and deflateParams() is called
   only before the first Z_FINISH.  So main's loop invariant is a [J] with the facts [det_facts2 J] of that law
   (DetFacts2.v), and three more facts of the states [J] describes ([ay_live]): deflateStateCheck passes, no gzip
   header was given (deflate's spec then holds no header memory), and before Z_FINISH the stream is not in
   FINISH_STATE.  From these, and from the model alone (AnyCodes.v): deflate() with a flush out of
   Z_NO_FLUSH..Z_BLOCK returns Z_STREAM_ERROR and changes nothing, with a valid flush it returns Z_OK, Z_BUF_ERROR
   or Z_STREAM_END (only for Z_FINISH); deflateParams() with an invalid level or strategy returns Z_STREAM_ERROR
   and changes nothing, with valid ones Z_OK or Z_BUF_ERROR.  [any_theory_stmt] is proved in AnyTheory.v. *)
From Coq Require Import ZArith.
From Coq Require Import List.
From Coq Require Import Lia.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.DetFacts2.
Import ListNotations.
Local Open Scope Z_scope.

Record any_facts (J : det_inv) : Prop := {
  ay_det : det_facts2 J;
  ay_live : forall fin s tin adler, J fin s tin adler ->
    bad_state s = false /\ d_gzhead s = None /\ (fin = None -> d_status s <> FINISH_STATE)
}.

Definition any_theory_stmt : Prop := exists J, any_facts J.
