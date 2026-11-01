(** * The compressors with up to 2^32 - 1 bytes of output space: the wide preconditions and specifications

    The core theory (LTCore.v) proves the compression functions for streams with [zin_ok] (LTDefs.v), whose
    output space is at most 2^30 bytes.  [zwide] (DetWide.v) allows up to 2^32 - 1 bytes.  The compressors'
    proofs use [zin_ok] almost only through [zall] (LTCSpecs.v), which [zwide] implies too; the files DetCore*.v
    re-assemble them for [zwide] streams.  Here: [compress_prew] / [compress_pre2w] (LTCSpecs.compress_pre /
    LTCSpecs2.compress_pre2 with [zwide]) and the specifications over them. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.DetWide Zlib.proof.deflate.LTCStill.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** A wide stream is sane: no counter can wrap during a call. *)
Lemma zwide_zall z : zwide z -> zall z.
Proof.
  unfold zwide, zall, zin_in, zout_ok. intros (? & ? & ? & ? & ? & ? & ?). repeat split; auto; lia.
Qed.

Lemma zin_ok_zwide z : zin_ok z -> zwide z.
Proof. unfold zin_ok, zwide. intros (? & ? & ? & ? & ? & ? & ?). repeat split; auto; lia. Qed.

(** LTCSpecs.compress_pre for a wide stream. *)
Definition compress_prew (s : dstate) (z : strm) (flush : Z) : Prop :=
  W s /\ outok s /\ quiet s /\ 0 <= flush <= 5 /\ zwide z /\ 0 <= d_wrap s <= 2 /\
  adler_ok (d_wrap s) (z_adler z).

(** LTCSpecs2.compress_pre2 for a wide stream. *)
Definition compress_pre2w (s : dstate) (z : strm) (flush : Z) : Prop :=
  W2 s /\ outok s /\ quiet s /\ 0 <= flush <= 5 /\ zwide z /\ 0 <= d_wrap s <= 2 /\
  adler_ok (d_wrap s) (z_adler z).

(** LTCSpecs.comp_spec for wide streams. *)
Definition comp_specw (f : Z) (c : dstate -> strm -> Z -> option (dstate * strm * bstate)) : Prop :=
  forall s z flush, compress_prew s z flush -> fn_of s = f ->
    exists s' z' bs evs, c s z flush = Some (s', z', bs) /\ cpost W s z flush s' z' bs evs.

Definition stored_specw : Prop := comp_specw 0 c_deflate_stored.
Definition fast_specw : Prop := comp_specw 1 c_deflate_fast.
Definition rle_specw : Prop := comp_specw 4 c_deflate_rle.

(** LTCSpecs2.slow_spec2 for wide streams. *)
Definition slow_spec2w : Prop :=
  forall s z flush, compress_pre2w s z flush -> fn_of s = 2 ->
    exists s' z' bs evs, c_deflate_slow s z flush = Some (s', z', bs) /\ cpost W2 s z flush s' z' bs evs.

(** LTCHuffKit.huff_specX for wide streams. *)
Definition huff_specXw : Prop :=
  forall s z flush, compress_prew s z flush -> huff_extra s -> fn_of s = 3 ->
    exists s' z' bs evs, c_deflate_huff s z flush = Some (s', z', bs) /\
      cpost W s z flush s' z' bs evs /\ huff_extra s'.
