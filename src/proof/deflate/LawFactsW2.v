(* The deflateBound accounting of LawFactsW.v for the clip() loops of four short laws.

   harness/rt_partial.c, rj_truncated.c, rj_bad_checksum.c and rfc_trailing_bytes.c take any accepted
   parameters, n = data_len up to PTRDIFF_MAX = 2^63 - 1 and b = deflateBound_z(strm, n), then loop
     do { rest = n - consumed; flush = rest <= UINT_MAX ? Z_FINISH : Z_NO_FLUSH;
          avail_in = clip(rest); avail_out = clip(b - produced); deflate(strm, flush); } while (Z_OK)
   each call given the next piece of the data as its own object.  LawFactsW.bound_facts_w starts the accounting
   [Brun] after deflateBound for n < 2^32 only (bw_bound), and has no fact for a loop of calls: a general one is
   false at level 0 (deflate_stored compares len with left + avail_in in 32 bits: with left + avail_in >= 2^32
   and len equal to its value modulo 2^32 it writes a last block with input left).
   In the clip loop that cannot happen: with ample output space every Z_NO_FLUSH call leaves fewer than
   min_block bytes in the window, and the accounting keeps b - total_out at least the bytes still to store.

   - [bw_bound_big]: bw_bound for n <= 2^63 - 1;
   - [bw_range_w]: what Brun says of the position and of the output so far;
   - [bw_clip]: one call of the clip loop from Brun: the model run is defined, the stream moves on by the bytes
     consumed and produced, the codes, Brun kept unless Z_STREAM_END. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LawFactsW.
Import ListNotations.
Local Open Scope Z_scope.

Definition bw_bound_big (Bpre : bpre_inv) (Brun : brun_inv) : Prop :=
  forall level wbits mem strategy ds s tin tout adler n,
    Bpre level wbits mem strategy ds s tin tout adler -> 0 <= n <= 9223372036854775807 ->
    exists b, c_deflateBound (Some s) n = Some b /\ 0 <= b <= 18446744073709551615 /\
      Brun n b 0 false s tin tout adler.

Definition bw_range_w (Brun : brun_inv) : Prop :=
  forall n b pos fin s tin tout adler,
    Brun n b pos fin s tin tout adler -> 0 <= pos <= n /\ 0 <= tout <= b.

(* the call of the clip loop at position pos: the object inb of min(n - pos, UINT_MAX) bytes (all of it
   offered), min(b - total_out, UINT_MAX) bytes of output space, Z_FINISH exactly with the rest of the data *)
Definition bw_clip (Brun : brun_inv) : Prop :=
  forall n b pos fin s tin tout adler inb msg,
    Brun n b pos fin s tin tout adler -> bytes inb ->
    Zlength inb = Z.min (n - pos) 4294967295 -> (fin = true -> n - pos <= 4294967295) ->
    let flush := if n - pos <=? 4294967295 then Z_FINISH else Z_NO_FLUSH in
    let aout := Z.min (b - tout) 4294967295 in
    exists s' z' code,
      c_deflate s (mkST inb 0 (Zlength inb) tin [] aout tout adler msg) flush = Some (s', z', code) /\
      d_gzhead s' = d_gzhead s /\
      z_in z' = inb /\ 0 <= z_avail_in z' <= Zlength inb /\ z_next_in z' = Zlength inb - z_avail_in z' /\
      0 <= z_avail_out z' <= aout /\ Zlength (z_out z') = aout - z_avail_out z' /\ bytes (z_out z') /\
      z_total_in z' = tin + (Zlength inb - z_avail_in z') /\ z_total_out z' = tout + (aout - z_avail_out z') /\
      z_total_out z' <= b /\
      (code = Z_OK \/ code = Z_BUF_ERROR \/ code = Z_STREAM_END) /\
      (code = Z_STREAM_END -> flush = Z_FINISH /\ z_avail_in z' = 0) /\
      (code <> Z_STREAM_END ->
       Brun n b (pos + (Zlength inb - z_avail_in z')) (flush =? Z_FINISH) s' (z_total_in z') (z_total_out z')
         (z_adler z')).

Definition bound_w_big_stmt : Prop :=
  exists Bpre Brun, bound_facts_w Bpre Brun /\ bw_bound_big Bpre Brun /\ bw_range_w Brun /\ bw_clip Brun.
