(** * Core part of the deflate law theory: the _tr_tally macros and _tr_flush_block, against the corrected specs of LTCSpecs2.v.
    With LTCSpecs2.tally_spec_2 / fpend_spec_2 it also holds under the original specifications of
    LTCSpecs.v. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTCSpecs2.
Require Import Zlib.proof.deflate.LTCTrKit Zlib.proof.deflate.LTCTrTally Zlib.proof.deflate.LTCTrees.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

Lemma trflush_room_ok : overlay_statement -> trflush_room.
Proof.
  intros Hov t m syms buf sl last t' m' kind Hfp Htr Hlev Hlast Hmb Hsl Hbuf Hrun'.
  destruct (flush_run Hov t m syms buf sl last Hfp Htr Hlev Hlast Hmb Hsl Hbuf)
    as (s' & o4 & M' & kind' & Hrun & Hsz & Hcfg & Ok4 & V4 & P4 & L4 & B4).
  rewrite Hrun in Hrun'. inversion Hrun'; subst t' m' kind.
  rewrite tr_out_set_out, L4. exact B4.
Qed.

Theorem trees_ok2 : overlay_statement -> tally_spec2 /\ trflush_spec /\ trflush_room.
Proof.
  intros Hov. split; [exact tally_some|]. split; [exact (trflush_ok Hov)|exact (trflush_room_ok Hov)].
Qed.
