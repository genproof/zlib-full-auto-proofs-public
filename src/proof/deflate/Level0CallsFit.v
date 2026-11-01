(** * Level 0 over several deflate() calls when the trailer always fits: the interface of rfc_level0_size

    The loop of harness/rfc_level0_size.c and harness/rfc_level0_blocks.c is described in Level0Calls.v; its facts
    [l0_facts] allow what happens with gzip when the first call is also the last and carries all the data in
    65532 blocks: the trailer does not fit in the call's 2^32 - 1 bytes of output, and with [room = size] the
    loop ends with Z_BUF_ERROR (a size check would fail there).  This file states the stronger facts that hold
    when that cannot happen, as a function of two parameters of a harness: [kmax], the most blocks a call is given
    (the harness draws k = 1 + upto(kmax - 1)), and [slack], the least room beyond the size ([room >= size +
    slack]).  With [kmax <= 65531] the first call needs at most 18 + 65531 * 65540 < 2^32 - 1 bytes; with
    [slack >= 1] the call after a cut trailer gets more space than the bytes pending.  Then the output object
    always has room left, and the loop ends with Z_STREAM_END and the whole output ([l0_fit_stmt]).

    The fields are those of Level0Calls.l0_facts with [|O| < room] and, at any code other than Z_OK,
    Z_STREAM_END. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.Level0Calls.
Import ListNotations.
Local Open Scope Z_scope.

Record l0_fit_facts (kmax slack : Z) (J : Z -> list Z -> Z -> Z -> list Z -> dstate -> Z -> Z -> Z -> Prop)
    : Prop := {
  (** deflateInit2 with level 0 and method Z_DEFLATED returned Z_OK, room at least size + slack *)
  ff_init : forall vok sok snull wbits mem strategy a1 a2 a3 a4 a5 z0 os z1 data room,
    c_deflateInit2_ vok sok snull 0 Z_DEFLATED wbits mem strategy a1 a2 a3 a4 a5 z0 = Some (os, z1, Z_OK) ->
    bytes data -> Zlength data <= l0_max_size ->
    l0_size wbits (Zlength data) + slack <= room <= l0_max_u64 ->
    exists s, os = Some s /\ J wbits data room 0 [] s (z_total_in z1) (z_total_out z1) (z_adler z1);
  (** what J says of the quantities at the head of the loop: in particular room is left *)
  ff_range : forall wbits data room pos O s tin tout adler,
    J wbits data room pos O s tin tout adler ->
    0 <= pos <= Zlength data /\ Zlength data <= l0_max_size /\ 0 <= Zlength O < room /\ room <= l0_max_u64 /\
    bytes data /\ bytes O /\ d_gzhead s = None /\
    0 <= tin <= l0_max_u64 /\ 0 <= tout <= l0_max_u64 /\ 0 <= adler <= l0_max_u64;
  (** one iteration of the loop with k <= kmax blocks drawn (as Level0Calls.lf_call); any code other than
      Z_OK is Z_STREAM_END with the whole output *)
  ff_call : forall wbits data room pos O s tin tout adler msg k,
    J wbits data room pos O s tin tout adler -> 1 <= k <= kmax ->
    let inb := l0_inb data pos k in
    let aout := l0_clip (room - Zlength O) in
    exists s' z' code,
      c_deflate s (zcall inb 0 (Zlength inb) tin aout tout adler msg) (l0_flush (Zlength data) pos k) =
        Some (s', z', code) /\
      z_in z' = inb /\
      0 <= z_avail_in z' <= Zlength inb /\ z_next_in z' = Zlength inb - z_avail_in z' /\
      z_total_in z' = tin + (Zlength inb - z_avail_in z') /\
      0 <= z_avail_out z' <= aout /\ Zlength (z_out z') = aout - z_avail_out z' /\
      z_total_out z' = tout + (aout - z_avail_out z') /\ bytes (z_out z') /\
      d_gzhead s' = None /\
      (code = Z_OK ->
         J wbits data room (pos + (Zlength inb - z_avail_in z')) (O ++ z_out z') s'
           (z_total_in z') (z_total_out z') (z_adler z')) /\
      (code <> Z_OK ->
         code = Z_STREAM_END /\
         exists H T, O ++ z_out z' = H ++ stored_blocks data ++ T /\
           Zlength H = l0_hlen wbits /\ Zlength T = l0_tlen wbits /\
           z_total_out z' = l0_size wbits (Zlength data))
}.

(** The facts hold for every harness that gives at most 65531 blocks per call, or leaves at least one byte of
    room beyond the size. *)
Definition l0_fit_stmt : Prop :=
  forall kmax slack, 1 <= kmax <= 65532 -> 0 <= slack -> (kmax <= 65531 \/ 1 <= slack) ->
    exists J, l0_fit_facts kmax slack J.
