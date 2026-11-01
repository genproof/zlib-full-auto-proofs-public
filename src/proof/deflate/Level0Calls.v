(** * Level 0 over several deflate() calls: the interface between the mains of rfc_level0_size and
    rfc_level0_blocks and the model theory of deflate

    Both harnesses (harness/rfc_level0_size.c, harness/rfc_level0_blocks.c) run, after deflateInit2 with level 0:
      do { rest = n - consumed; piece = 65535 * k  (k = 1 + upto(65530), any 1 .. 65531);
           flush = Z_NO_FLUSH; if (piece >= rest) { piece = rest; flush = Z_FINISH; }
           avail_in = piece; avail_out = clip(room - produced); code = deflate(&strm, flush); }
      while (code == Z_OK);
    with [room >= l0_size wbits n] bytes of output space in all.  Each deflate() call is given the next piece of
    the data as its own input object (the slice [consumed, consumed + piece) of the data: DSpec.deflate_spec
    bounds the object to 2^32 - 1 bytes) and the next clip(room - produced) bytes of the output object.

    Why it works: a call given k whole blocks of 65535 bytes and room for them writes k full stored blocks
    straight from next_in (deflate_stored's first loop: each block is min(65535, left + avail_in, avail_out - 5)
    bytes, and nothing is left in the window, [left = 0]); 65532 blocks of 65540 bytes fit in one call's
    2^32 - 1 bytes of output, so clip() never cuts a block short.  The last call (Z_FINISH) writes the rest as
    [ceil(rest / 65535)] blocks (one empty block when there is no data at all), the last one final, then the
    trailer.

    The facts are stated for calls of up to 65532 blocks, one more than the harnesses draw, where the trailer may
    NOT fit: with gzip (10 + 8 wrapper bytes) and all the data (65532 blocks) in the first call, that call needs up
    to 2^32 + 2 bytes.  Then it returns Z_OK with 1 to 3 trailer bytes pending; the next call (no input, Z_FINISH)
    flushes them and returns Z_STREAM_END, or, when it gets exactly that much space (room = size), Z_OK with all
    of room written, and the call after it gets no output space and returns Z_BUF_ERROR.  So these facts allow the
    loop to reach [|O| = room], and promise the output only at Z_STREAM_END; the blocks harness, which returns
    before its check unless the code is Z_STREAM_END, needs no more.  For at most 65531 blocks per call the
    stronger facts of Level0CallsFit.v hold.

    The invariant [J wbits data room pos O s tin tout adler] at the head of the loop is abstract ([data]: the n
    bytes; [room]: the size of the output object; [pos]: the bytes consumed; [O]: the bytes produced; [s] and
    [tin], [tout], [adler]: the state and the z_stream's fields): the theory chooses it
    ([l0_facts_stmt := exists J, l0_facts J]), the mains use only the facts. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.Level0Defs.
Import ListNotations.
Local Open Scope Z_scope.

(* laws_common.h's clip(n): the most one call can take *)
Definition l0_clip (n : Z) : Z := Z.min n 4294967295.

(* the call made after [pos] of the [n] bytes were consumed, with k blocks drawn: its input length and its flush *)
Definition l0_piece (n pos k : Z) : Z := if n - pos <=? 65535 * k then n - pos else 65535 * k.
Definition l0_flush (n pos k : Z) : Z := if n - pos <=? 65535 * k then Z_FINISH else Z_NO_FLUSH.

(* the input object of that call *)
Definition l0_inb (data : list Z) (pos k : Z) : list Z :=
  sublist pos (pos + l0_piece (Zlength data) pos k) data.

Definition l0_max_size : Z := 9223372036854775807.   (* PTRDIFF_MAX *)
Definition l0_max_u64 : Z := 18446744073709551615.    (* SIZE_MAX *)

Record l0_facts (J : Z -> list Z -> Z -> Z -> list Z -> dstate -> Z -> Z -> Z -> Prop) : Prop := {
  (** deflateInit2 with level 0 and method Z_DEFLATED returned Z_OK: the stream is live and the loop starts
      from J for the data and the room the harness chose before *)
  lf_init : forall vok sok snull wbits mem strategy a1 a2 a3 a4 a5 z0 os z1 data room,
    c_deflateInit2_ vok sok snull 0 Z_DEFLATED wbits mem strategy a1 a2 a3 a4 a5 z0 = Some (os, z1, Z_OK) ->
    bytes data -> Zlength data <= l0_max_size ->
    l0_size wbits (Zlength data) <= room <= l0_max_u64 ->
    exists s, os = Some s /\ J wbits data room 0 [] s (z_total_in z1) (z_total_out z1) (z_adler z1);
  (** what J says of the quantities at the head of the loop *)
  lf_range : forall wbits data room pos O s tin tout adler,
    J wbits data room pos O s tin tout adler ->
    0 <= pos <= Zlength data /\ Zlength data <= l0_max_size /\ 0 <= Zlength O <= room /\ room <= l0_max_u64 /\
    bytes data /\ bytes O /\ d_gzhead s = None /\
    0 <= tin <= l0_max_u64 /\ 0 <= tout <= l0_max_u64 /\ 0 <= adler <= l0_max_u64;
  (** one iteration of the loop with k blocks drawn: deflate(strm, l0_flush ..) offered the object
      [l0_inb data pos k] and clip(room - |O|) bytes of output space, any msg; the run is defined; the stream
      moves on as RTDIface.rcall_ok says; Z_OK keeps J; Z_STREAM_END comes with the whole output: the wrapper
      header, the stored blocks of the data, the trailer, and total_out = l0_size *)
  lf_call : forall wbits data room pos O s tin tout adler msg k,
    J wbits data room pos O s tin tout adler -> 1 <= k <= 65532 ->
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
      (code = Z_STREAM_END ->
         exists H T, O ++ z_out z' = H ++ stored_blocks data ++ T /\
           Zlength H = l0_hlen wbits /\ Zlength T = l0_tlen wbits /\
           z_total_out z' = l0_size wbits (Zlength data))
}.

Definition l0_facts_stmt : Prop := exists J, l0_facts J.
