(** * Core part of the deflate law theory: a compression call that consumes no input from a state
    with everything in blocks at strstart 0 leaves strstart at 0 (interface v3, cf_still).

    Definitions shared by the parts LTCStillFill / Stored / Fast / Slow / Huff / Rle.
 *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDLTCHuffKit.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** The start state: everything read is in blocks and strstart = 0. *)
Definition still_at (s : dstate) : Prop := d_strstart s = 0 /\ d_block_start s = 0 /\ d_lookahead s = 0.

(** The conclusion for a compressor [c]: a run that consumes no input ends at strstart 0. *)
Definition still_concl (c : dstate -> strm -> Z -> option (dstate * strm * bstate)) (s : dstate) (z : strm)
    (flush : Z) : Prop :=
  forall s' z' bs, c s z flush = Some (s', z', bs) -> z_next_in z' = z_next_in z -> d_strstart s' = 0.

(** fill_window without input, after a fill_window (fill_spec's last two facts): nothing to do. *)
Definition fill_idem_spec : Prop :=
  forall s z, fill_pre s -> zall z -> adler_ok (d_wrap s) (z_adler z) -> z_avail_in z = 0 ->
    d_strstart s < d_w_size s + MAX_DIST s ->
    Z.min (d_window_size s) (d_strstart s + d_lookahead s + WIN_INIT) <= d_high_water s ->
    c_fill_window s z = Some (s, z).

(** A loop's run depends on its start only through the first iteration. *)
Lemma loop2_body_eq {A B : Type} (body : A -> option (A + B)) d a b :
  body a = body b -> loop2 d body a = loop2 d body b.
Proof.
  revert a b. induction d as [|d IH]; intros a b H; cbn [loop2]; [exact H|].
  rewrite (IH a b H). reflexivity.
Qed.

Lemma loop_body_eq {A B : Type} (body : A -> option (A + B)) d a b :
  body a = body b -> loop d body a = loop d body b.
Proof. intros H. unfold loop. rewrite (loop2_body_eq body d a b H). reflexivity. Qed.
