(** * The output of deflate at level 0: the statements of the three stages of the call

    [Level0.level0_shape] follows one deflate(Z_FINISH) call on a fresh level-0 stream through the stages of
    the model's deflate() ([LTDefs.c_deflate_stages]):
    - [l0_head_stmt]: the entry stage and the header stages write the wrapper header (none, 2 or 10 bytes) and
      flush it: the state is BUSY with nothing pending, and only the output part of the state changed;
    - [l0_stored_stmt]: deflate_stored, with all the input offered and room for every block, writes
      [Level0Defs.stored_blocks] of the input and ends with [finish_done], nothing pending;
    - [l0_trail_stmt]: the trailer (none, 4 or 8 bytes) is put and flushed and the call returns Z_STREAM_END.
    The byte values of the header and the trailer do not matter here, only their lengths. *)
From Coq Require Import ZArith List Lia.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTCW Zlib.proof.deflate.Level0Defs.
Import ListNotations.
Local Open Scope Z_scope.

(** The lengths of the wrapper's header and trailer by [s->wrap] (0: raw, 1: zlib, 2: gzip without a user
    header). *)
Definition hdr_len (wrap : Z) : Z := if wrap =? 0 then 0 else if wrap =? 1 then 2 else 10.
Definition tlr_len (wrap : Z) : Z := if wrap =? 0 then 0 else if wrap =? 1 then 4 else 8.

(** The entry stage and the header stages on the state deflateInit2_ leaves (no dictionary, no user gzip
    header), with room for the whole header. *)
Definition l0_head_stmt : Prop :=
  forall s z,
    prm s -> outok s -> d_pending s = 0 -> d_po s = 0 -> d_bi_valid s = 0 -> d_sym_next s = 0 ->
    d_strstart s = 0 -> d_gzhead s = None -> d_last_flush s = -2 -> 0 <= d_wrap s <= 2 ->
    d_status s = (if d_wrap s =? 2 then GZIP_STATE else INIT_STATE) ->
    hdr_len (d_wrap s) < z_avail_out z <= 4294967295 -> 0 <= z_total_out z <= 1099511627776 ->
    exists s2 z2 H,
      then_stage (c_deflate_entry s z Z_FINISH) hdr_stages = Some (s2, z2, None) /\
      core_eq s s2 /\ outok s2 /\ d_pending s2 = 0 /\ d_po s2 = 0 /\ d_bi_valid s2 = 0 /\
      d_status s2 = BUSY_STATE /\ d_wrap s2 = d_wrap s /\
      Zlength H = hdr_len (d_wrap s) /\ z_out z2 = z_out z ++ H /\
      z_in z2 = z_in z /\ z_next_in z2 = z_next_in z /\ z_avail_in z2 = z_avail_in z /\
      z_total_in z2 = z_total_in z /\ z_msg z2 = z_msg z /\
      z_avail_out z2 = z_avail_out z - hdr_len (d_wrap s) /\
      z_total_out z2 = z_total_out z + hdr_len (d_wrap s).

(** deflate_stored(s, Z_FINISH) on a stream whose window holds nothing (strstart = block_start = 0), nothing
    pending, offered all of [inb] and at least the room of its stored blocks: every block but the last has
    65535 bytes (the loop's first phase copies straight from next_in), and the call finishes. *)
Definition l0_stored_stmt : Prop :=
  forall s inb O tin aout tout adler msg,
    W s -> outok s -> d_pending s = 0 -> d_po s = 0 -> d_bi_valid s = 0 ->
    d_level s = 0 -> d_strstart s = 0 -> d_block_start s = 0 ->
    bytes inb -> Zlength inb <= 1048576 ->
    5 * l0_blocks (Zlength inb) + Zlength inb <= aout -> 0 <= tout -> tout + aout <= 4294967295 ->
    exists s' z',
      c_deflate_stored s (mkST inb 0 (Zlength inb) tin O aout tout adler msg) Z_FINISH =
        Some (s', z', finish_done) /\
      z_out z' = O ++ stored_blocks inb /\
      z_avail_out z' = aout - (5 * l0_blocks (Zlength inb) + Zlength inb) /\
      z_total_out z' = tout + (5 * l0_blocks (Zlength inb) + Zlength inb) /\
      z_avail_in z' = 0 /\ z_msg z' = msg /\
      outok s' /\ d_pending s' = 0 /\ d_po s' = 0 /\ d_bi_valid s' = 0 /\
      d_wrap s' = d_wrap s /\ Zlength (o_buf (tr_out (d_tr s'))) = Zlength (o_buf (tr_out (d_tr s))).

(** The trailer with nothing pending and room for it. *)
Definition l0_trail_stmt : Prop :=
  forall s z,
    outok s -> d_pending s = 0 -> d_po s = 0 -> d_bi_valid s = 0 ->
    8 <= Zlength (o_buf (tr_out (d_tr s))) -> 0 <= d_wrap s <= 2 ->
    tlr_len (d_wrap s) <= z_avail_out z -> 0 <= z_total_out z -> z_total_out z + z_avail_out z <= 4294967295 ->
    exists s' z' T,
      c_deflate_trailer s z Z_FINISH = Some (s', z', Z_STREAM_END) /\
      z_out z' = z_out z ++ T /\ Zlength T = tlr_len (d_wrap s) /\
      z_total_out z' = z_total_out z + tlr_len (d_wrap s).
