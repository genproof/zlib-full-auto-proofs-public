(** * deflate_stored when [left + avail_in] may reach 2^32: the statements of the parts of LTWClipCore.v

    deflate_stored compares a block length with [left + strm->avail_in] in 32 bits (the clamp of len uses 64
    bits, the tests [len != left + avail_in] and [last = ... len == left + avail_in] do not).  The wide theory
    (src/proof/wide/deflate/LTCStored*.v) runs the loop of direct stored blocks under
    [flush <> Z_NO_FLUSH -> ub s + avail_in <= UINT_MAX].  Here the loop is run with no such hypothesis:

    - [clip_ok]: the 32-bit tests agree with the exact ones at the first iteration, either because the sum does
      not wrap or because [ub s <= 65535] and avail_out has room for a header and 65535 bytes, so the first block
      has len = 65535 while the wrapped sum is at most 65534.  [clip_ok] holds again at every later iteration
      (the sum is then below 2^32);
    - [dsloop_clip_stmt]: the loop's result for any call; what it says about the blocks written (the events)
      only under [clip_ok];
    - [blk2_ub_stmt]: the second-phase stored block leaves at most 65535 bytes of the window not yet written,
      whatever the input;
    - [stored_clip_spec], [stored_ub_spec]: deflate_stored's contract under [clip_ok], and [ub s' <= 65535]
      after any call from [ub s <= 65535]. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.wide.deflate.LTCSpecs2 Zlib.proof.wide.deflate.LTCStoredKit.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** The 32-bit [left + avail_in] of deflate_stored's first iteration does not mislead it. *)
Definition clip_ok (s : dstate) (z : strm) (flush : Z) : Prop :=
  flush = Z_NO_FLUSH \/ ub s + z_avail_in z <= 4294967295 \/ (ub s <= 65535 /\ 65541 <= z_avail_out z).

(** The first-phase loop for any call: the facts of the output side (LTCStoredKit.dsloop_stmt_w without its
    hypothesis on [ub s + avail_in]), and its blocks under [clip_ok]. *)
Definition dsloop_clip_stmt : Prop :=
  forall s z flush,
    W s -> outok s -> quiet s -> d_level s = 0 -> zall_w z -> adler_ok (d_wrap s) (z_adler z) ->
    0 <= flush <= 5 -> z_avail_out z <= 4294967295 ->
    exists s1 z1 last k x,
      loop FUEL (ds_body flush (ds_min_block s)) (s, z) = Some (s1, z1, last) /\
      ob_keep s1 = ob_keep s /\
      d_block_start s <= d_block_start s1 <= d_strstart s /\
      outok s1 /\ quiet s1 /\
      pb_grow (tr_out (d_tr s)) (d_pbm s) (tr_out (d_tr s1)) (d_pbm s1) /\
      zstep (d_wrap s) z z1 k x /\ bytes x /\ 0 <= z_avail_out z1 /\
      (0 < k -> d_block_start s1 = d_strstart s) /\
      (last = 0 \/ last = 1) /\
      (last = 0 -> flush = Z_FINISH ->
       z_avail_out z1 < stored_hdr s1 + (d_strstart s - d_block_start s1) + z_avail_in z1) /\
      (clip_ok s z flush ->
       exists evs,
         k + ub s = sum_len evs + ub s1 /\
         ev_chain (Gb s (z_total_out z)) evs (Gb s1 (z_total_out z1)) /\
         Forall (ev_ok s flush) evs /\
         ((last = 0 /\ Forall (fun e => ev_last e = 0) evs) \/
          (last = 1 /\ last_ev evs /\ flush = Z_FINISH /\ z_avail_in z1 = 0 /\
           d_block_start s1 = d_strstart s /\ d_bi_valid s1 = 0))).

(** The second-phase stored block: it writes min(left, have) bytes when left >= min_block, with
    have >= pending_buf_size - 6 >= 506, so at most 65535 bytes of a window of 65536 remain. *)
Definition blk2_ub_stmt : Prop :=
  forall A s z flush (K : dstate -> strm -> Z -> option A) r,
    ds_blk2 s z flush K = Some r ->
    0 <= d_bi_valid s <= 7 -> 512 <= d_pending_buf_size s <= 131072 ->
    0 <= d_strstart s - d_block_start s <= 65536 ->
    exists s' z' last,
      K s' z' last = Some r /\ d_strstart s' = d_strstart s /\ d_lookahead s' = d_lookahead s /\
      d_strstart s' - d_block_start s' <= 65535.

(** deflate_stored's contract (LTCSpecs.stored_spec_w) under [clip_ok]. *)
Definition stored_clip_spec : Prop :=
  forall s z flush, compress_pre_w s z flush -> clip_ok s z flush -> fn_of s = 0 ->
    exists s' z' bs evs, c_deflate_stored s z flush = Some (s', z', bs) /\ cpost W s z flush s' z' bs evs.

(** At every return of deflate_stored, at most 65535 bytes of the window are not yet written. *)
Definition stored_ub_spec : Prop :=
  forall s z flush s' z' bs,
    compress_pre_w s z flush -> fn_of s = 0 -> ub s <= 65535 ->
    c_deflate_stored s z flush = Some (s', z', bs) -> ub s' <= 65535.
