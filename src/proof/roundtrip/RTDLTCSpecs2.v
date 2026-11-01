(** * Core part of the deflate law theory: corrected part specifications

    Three specifications of RTDLTCSpecs.v are defective:
    - [tally_spec]: nothing bounds lit_bufsize, so the u16 frequencies can wrap.  Fixed:
      [tally_spec2] adds [tr_lit_bufsize t <= 32768] (every caller has prm).
    - [fpend_spec] is false: bi_flush writes at pending_buf[pending] without
      guaranteed room.  Fixed: [fpend_spec2] adds [prm s] and RTDLTCFlushKit.fp_room (bi_valid < 8, or pending_out
      at the start and the bits fit in pending_buf).  Proved: [fpend2_ok].
    - [fbo_spec] needs room for the bits after _tr_flush_block: RTDLTCFlushKit.trflush_room, proved
      from lemma (i) (RTDLTCTrees2.trflush_room_ok).  [fbo_ok] (LTCFlushKit): trflush_spec -> trflush_room -> fbo_spec.
    The compressor parts are proved against [tally_spec2] and [fpend_spec2]: since [tally_spec -> tally_spec2]
    and [fpend_spec -> fpend_spec2], their original targets follow from the corrected ones. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDLTCFlushKit.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

Definition tally_spec2 : Prop :=
  (forall t m syms c,
     tree_ok t m syms -> Zlength syms <= tr_lit_bufsize t - 2 -> tr_lit_bufsize t <= 32768 -> 0 <= c < 256 ->
     exists t' m',
       c_tr_tally_lit (t, m) c = Some ((t', m'), 3 * Zlength syms + 3 =? tr_sym_end t) /\
       tree_ok t' m' (syms ++ [(0, c)]) /\ tally_frame t m t' m') /\
  (forall t m syms dist len,
     tree_ok t m syms -> Zlength syms <= tr_lit_bufsize t - 2 -> tr_lit_bufsize t <= 32768 ->
     1 <= dist <= 32768 -> 0 <= len <= 255 ->
     exists t' m',
       c_tr_tally_dist (t, m) dist len = Some ((t', m'), 3 * Zlength syms + 3 =? tr_sym_end t) /\
       tree_ok t' m' (syms ++ [(dist, len)]) /\ tally_frame t m t' m').

Definition fpend_spec2 : Prop :=
  forall s z, prm s -> outok s -> zout_ok z -> fp_room s -> fpend_concl s z.

Lemma tally_spec_2 : tally_spec -> tally_spec2.
Proof.
  intros [H1 H2]. split.
  - intros t m syms c T L _ C. exact (H1 t m syms c T L C).
  - intros t m syms d l T L _ D E. exact (H2 t m syms d l T L D E).
Qed.

Lemma fpend_spec_2 : fpend_spec -> fpend_spec2.
Proof. intros H s z _ Ho Hz _. exact (H s z Ho Hz). Qed.

Lemma fpend2_ok : fpend_spec2.
Proof. intros s z Hp Ho Hz Hr. exact (fpend_fixed_ok s z Hp Ho Hz Hr). Qed.

(** ** The invariant of the theory: [W] and deflate_slow's lazy-match fact (after the pending
    literal at the end of deflate_slow, prev_length must already be below MIN_MATCH).  Only deflate_slow
    produces match_available = 1, so the other parts keep their specifications over [W]. *)
Definition slow_extra (s : dstate) : Prop :=
  d_match_available s = 1 -> MIN_MATCH <= d_prev_length s -> d_prev_length s < d_match_length s.

Definition W2 (s : dstate) : Prop := W s /\ slow_extra s.

Definition compress_pre2 (s : dstate) (z : strm) (flush : Z) : Prop :=
  W2 s /\ outok s /\ quiet s /\ 0 <= flush <= 5 /\ zin_ok z /\ 0 <= d_wrap s <= 2 /\
  adler_ok (d_wrap s) (z_adler z).

Definition slow_spec2 : Prop :=
  forall s z flush, compress_pre2 s z flush -> fn_of s = 2 ->
    exists s' z' bs evs, c_deflate_slow s z flush = Some (s', z', bs) /\ cpost W2 s z flush s' z' bs evs.
