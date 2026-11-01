(** * deflate() and deflateParams() without the size limits of the deflate_api theory: the statements of the parts

    The deflate_api theory (LTApi*.v over [core_facts] / [hdr_facts], LTIface.v) proves that every call of
    deflate() / deflateParams() is defined for calls offering at most 2^20 bytes of output space, at most 2^22
    bytes of output in all, and deflateParams only before Z_FINISH.  Law api_deterministic (harness/
    api_deterministic.c) offers up to 2^32 - 1 bytes of output space per call, makes any number of calls (so
    total_out grows without bound: repeated flush markers) and may call deflateParams after Z_FINISH.  The parts
    stated here lift the limits; DetFacts.v / DetTheory.v assemble them into the facts the law's main uses.

    - [tout_shift_stmt]: the model only adds to total_out (modulo 2^64) and never reads it, so a call on a
      stream whose total_out is shifted by [d] is the same call with total_out shifted by [d].  The other parts
      then run every call from total_out = the (short) output kept in the invariant.
    - [core_wide_stmt]: the compression functions with up to 2^32 - 1 bytes of output space ([zwide]: zin_ok of
      LTDefs.v with avail_out < 2^32 instead of avail_out <= 2^30), for the state invariant of a [core_facts].
    - [hdr_wide_stmt]: the header stages likewise ([hdr_pre_wide]).
    - [api_wide_stmt]: deflate() and deflateParams() on the deflate_api invariant [Iapi] (LTApiDefs.v) with up to
      2^32 - 1 bytes of output space, the output kept below 2^33 bytes, and next_in anywhere in the input object
      (deflate after a deflateParams that consumed part of it). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTApiDefs.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** total_out is only counted *)

(** The stream with total_out shifted by [d] (modulo 2^64). *)
Definition zsh (d : Z) (z : strm) : strm := set_z_total_out z (u64 (z_total_out z + d)).
Definition rsh (d : Z) (r : dstate * strm * Z) : dstate * strm * Z := (fst (fst r), zsh d (snd (fst r)), snd r).

Definition tout_shift_stmt : Prop :=
  (forall s z flush d, c_deflate s (zsh d z) flush = option_map (rsh d) (c_deflate s z flush)) /\
  (forall s z level strategy d,
     c_deflateParams s (zsh d z) level strategy = option_map (rsh d) (c_deflateParams s z level strategy)).

(** ** The compression functions with up to 2^32 - 1 bytes of output space *)

(** zin_ok (LTDefs.v) with avail_out below 2^32. *)
Definition zwide (z : strm) : Prop :=
  bytes (z_in z) /\ 0 <= z_next_in z /\ 0 <= z_avail_in z <= 1073741824 /\
  z_next_in z + z_avail_in z <= Zlength (z_in z) /\ 0 <= z_avail_out z <= 4294967295 /\
  0 <= z_total_in z <= 1099511627776 /\ 0 <= z_total_out z <= 1099511627776.

(** cf_compress and cf_still of [core_facts] for such streams. *)
Definition cf_compress_wide (W : dstate -> Prop) : Prop :=
  forall s z flush,
    W s -> outok s -> quiet s -> 0 <= flush <= 5 -> zwide z ->
    0 <= d_wrap s <= 2 -> adler_pre (d_wrap s) (z_adler z) ->
    exists s' z' bs evs, c_compress_func s z flush = Some (s', z', bs) /\ cpost W s z flush s' z' bs evs.

Definition cf_still_wide (W : dstate -> Prop) : Prop :=
  forall s z flush s' z' bs,
    W s -> outok s -> quiet s -> 0 <= flush <= 5 -> zwide z ->
    0 <= d_wrap s <= 2 -> adler_pre (d_wrap s) (z_adler z) ->
    c_compress_func s z flush = Some (s', z', bs) ->
    ub s = 0 -> d_strstart s = 0 -> z_next_in z' = z_next_in z -> d_strstart s' = 0.

Definition core_wide_stmt : Prop :=
  Zlib.proof.huffman.Overlay.overlay_statement ->
  exists W, core_facts W /\ cf_compress_wide W /\ cf_still_wide W.

(** ** The header stages with up to 2^32 - 1 bytes of output space *)

(** hdr_pre (LTIface.v) with avail_out below 2^32. *)
Definition hdr_pre_wide (HI : hdr_inv) (s : dstate) (z : strm) (H : list Z) (k : Z) : Prop :=
  prm s /\ outok s /\ d_pending s = 0 /\ d_sym_next s = 0 /\ d_bi_valid s = 0 /\
  0 <= z_avail_out z <= 4294967295 /\ 0 <= z_total_out z <= 1099511627776 /\
  (forall h, d_gzhead s = Some h -> hdr_ok h) /\
  ((d_status s = INIT_STATE /\ 0 <= d_wrap s <= 1 /\ H = hdr_bytes s (z_adler z) /\ k = 0) \/
   (d_status s = GZIP_STATE /\ d_wrap s = 2 /\ H = hdr_bytes s (z_adler z) /\ k = 0) \/
   HI s (z_adler z) H k).

Definition hf_run_wide (HI : hdr_inv) : Prop :=
  forall s z H k, hdr_pre_wide HI s z H k ->
    exists s' z' r, hdr_stages s z = Some (s', z', r) /\ hdr_post HI s z H k s' z' r.

Definition hdr_wide_stmt : Prop := exists HI, hdr_facts HI /\ hf_run_wide HI.

(** ** deflate() and deflateParams() on [Iapi] *)

(** The stream after a call given the input object [inb] with next_in at [nin] (avail_in the rest of it),
    [aout] bytes of output space, total_in [tin], total_out [tout]: next_in advanced by the bytes consumed,
    the counters, the bytes written. *)
Definition call_okw (inb : list Z) (nin aout tin tout : Z) (z' : strm) : Prop :=
  z_in z' = inb /\ nin <= z_next_in z' <= Zlength inb /\ z_avail_in z' = Zlength inb - z_next_in z' /\
  z_total_in z' = tin + (z_next_in z' - nin) /\
  0 <= z_avail_out z' <= aout /\ Zlength (z_out z') = aout - z_avail_out z' /\
  z_total_out z' = u64 (tout + (aout - z_avail_out z')) /\ bytes (z_out z').

(** af_deflate of LawFacts.v on [Iapi] without its size limits (data still at most 2^20 bytes), with next_in at
    any [nin]: the data consumed are [D ++ sublist nin next_in' inb]. *)
Definition api_deflate_wide (W : dstate -> Prop) (HI : hdr_inv) : Prop :=
  forall dict wrap D O fin s tin tout adler inb nin aout flush msg,
    Iapi W HI dict wrap D O fin s tin tout adler ->
    0 <= flush <= 5 -> bytes inb -> 0 <= nin <= Zlength inb -> Zlength D + (Zlength inb - nin) <= 1048576 ->
    0 <= aout <= 4294967295 -> Zlength O + aout <= 8589934592 ->
    (forall R, fin = Some R -> flush = Z_FINISH /\ R = sublist nin (Zlength inb) inb) ->
    exists s' z' code,
      c_deflate s (zcall inb nin (Zlength inb - nin) tin aout tout adler msg) flush = Some (s', z', code) /\
      d_gzhead s' = d_gzhead s /\ call_okw inb nin aout tin tout z' /\
      (0 <= adler < 4294967296 -> 0 <= z_adler z' < 4294967296) /\
      (code <> Z_STREAM_END ->
       Iapi W HI dict wrap (D ++ sublist nin (z_next_in z') inb) (O ++ z_out z')
         (if flush =? Z_FINISH then Some (sublist (z_next_in z') (Zlength inb) inb) else None)
         s' (z_total_in z') (z_total_out z') (z_adler z')).

(** af_params of LawFacts.v likewise (before Z_FINISH). *)
Definition api_params_wide (W : dstate -> Prop) (HI : hdr_inv) : Prop :=
  forall dict wrap D O s tin tout adler inb nin aout level strategy msg,
    Iapi W HI dict wrap D O None s tin tout adler -> s32 level -> s32 strategy ->
    bytes inb -> 0 <= nin <= Zlength inb -> Zlength D + (Zlength inb - nin) <= 1048576 ->
    0 <= aout <= 4294967295 -> Zlength O + aout <= 8589934592 ->
    exists s' z' code,
      c_deflateParams s (zcall inb nin (Zlength inb - nin) tin aout tout adler msg) level strategy =
        Some (s', z', code) /\
      d_gzhead s' = d_gzhead s /\ call_okw inb nin aout tin tout z' /\
      (0 <= adler < 4294967296 -> 0 <= z_adler z' < 4294967296) /\
      Iapi W HI dict wrap (D ++ sublist nin (z_next_in z') inb) (O ++ z_out z') None
        s' (z_total_in z') (z_total_out z') (z_adler z').

Definition api_wide_stmt : Prop :=
  forall W HI, core_facts W -> cf_compress_wide W -> cf_still_wide W -> hdr_facts HI -> hf_run_wide HI ->
    api_deflate_wide W HI /\ api_params_wide W HI.
