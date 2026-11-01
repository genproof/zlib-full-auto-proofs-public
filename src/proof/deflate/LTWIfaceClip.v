(* The wide core (LTWIface.core_facts_w) for the level-0 calls of the clip() loops.

   core_facts_w's compression facts at level 0 with a flush other than Z_NO_FLUSH ask ub s + avail_in < 2^32:
   deflate_stored compares len with left + avail_in in 32 bits, and with the sum >= 2^32 and len equal to its
   value modulo 2^32 it writes a last stored block with input left.  The clip() loops of harness/rt_partial.c,
   rj_truncated.c, rj_bad_checksum.c and rfc_trailing_bytes.c give a Z_FINISH call up to UINT_MAX bytes while
   the window may still hold bytes, so the sum may reach 2^32 + 65534.  The wrap then still cannot happen:
   - at every return of deflate_stored, left = strstart - block_start <= 65535 (the last step writes
     min(left, have) bytes to pending, have = min(pending_buf_size - header, 65535) >= 507, and left was at most
     window_size <= 65536) [cw_stored_ub];
   - so at a call ub + avail_in <= 2^32 + 65534, and with avail_out >= 131072 (the stored header takes at most
     7 bytes: (bi_valid + 42) / 8; with avail_out = 65540 and a 6-byte header len could be 65534 = the wrapped
     sum) the first block has len = 65535, which is not the sum modulo 2^32; after it the sum is below 2^32
     [cw_compress_clip, cw_still_clip].  In the clip loops the compression stage then has avail_out >= UINT_MAX
     minus the pending bytes and header written before it. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTWIface.
Require Zlib.proof.deflate.LTCore.
Local Open Scope Z_scope.

Definition cw_compress_clip (W : dstate -> Prop) : Prop :=
  forall s z flush,
    W s -> outok s -> quiet s -> 0 <= flush <= 5 -> zin_okw z ->
    0 <= d_wrap s <= 2 -> adler_pre (d_wrap s) (z_adler z) ->
    d_level s = 0 -> ub s <= 65535 -> 131072 <= z_avail_out z ->
    exists s' z' bs evs, c_compress_func s z flush = Some (s', z', bs) /\ cpost W s z flush s' z' bs evs.

Definition cw_still_clip (W : dstate -> Prop) : Prop :=
  forall s z flush s' z' bs,
    W s -> outok s -> quiet s -> 0 <= flush <= 5 -> zin_okw z ->
    0 <= d_wrap s <= 2 -> adler_pre (d_wrap s) (z_adler z) ->
    d_level s = 0 -> ub s <= 65535 -> 131072 <= z_avail_out z ->
    c_compress_func s z flush = Some (s', z', bs) ->
    ub s = 0 -> d_strstart s = 0 -> z_next_in z' = z_next_in z -> d_strstart s' = 0.

Definition cw_stored_ub (W : dstate -> Prop) : Prop :=
  forall s z flush s' z' bs,
    W s -> outok s -> quiet s -> 0 <= flush <= 5 -> zin_okw z ->
    0 <= d_wrap s <= 2 -> adler_pre (d_wrap s) (z_adler z) ->
    d_level s = 0 -> ub s <= 65535 ->
    c_compress_func s z flush = Some (s', z', bs) -> ub s' <= 65535.

(* the facts for the core's concrete invariant LTCore.W3 (the one the wide core LTWCore.core_facts_w3 is proved for);
   core_facts_w W3 from LTWCore.core_facts_w3, the three clip facts from LTWClipCore.v *)
Definition core_clip3_stmt : Prop :=
  cw_compress_clip Zlib.proof.deflate.LTCore.W3 /\ cw_still_clip Zlib.proof.deflate.LTCore.W3 /\
  cw_stored_ub Zlib.proof.deflate.LTCore.W3.

Definition core_w_clip_stmt : Prop :=
  core_facts_w Zlib.proof.deflate.LTCore.W3 /\ core_clip3_stmt.
