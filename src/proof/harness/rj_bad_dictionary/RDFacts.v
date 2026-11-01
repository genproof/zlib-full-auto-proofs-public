(* Law rj_bad_dictionary: THE interface between the main of harness/rj_bad_dictionary.c (VST) and the pure
   theory of the one inflate() call (over Spec5's inflate_rel = Model2.run2 of m_init, and ApiModel's
   setdict_check).

   The harness writes a zlib header into the first two bytes of any stream: CMF = CINFO << 4 | 8 with
   CINFO <= windowBits - 8, FLG = the top two bits (FLEVEL) of the byte that was there, FDICT, and the FCHECK
   that makes CMF * 256 + FLG a multiple of 31; the next four bytes, whatever they are, are the dictionary id
   (RFC 1950 2.2, most significant byte first).  One inflate() call on the bytes offered (the first
   clip(stream_len) bytes of the stream: from 6 to 2^32 - 1 of them; any output space, any flush) right after
   inflateInit2_(windowBits) stops in DICT and returns Z_NEED_DICT; afterwards a dictionary whose Adler-32 is
   not the id is refused (setdict_check = SDData, so inflateSetDictionary returns Z_DATA_ERROR). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Export Zlib.proof.inflate_api.Spec5.
Require Zlib.proof.adler32.Model.
Import ListNotations.
Local Open Scope Z_scope.

(* the header bytes the harness computes: stream[0] = (unsigned char) (cinfo << 4 | 8) and, from the byte x
   that was in stream[1], f0 = (x & 0xc0) | 0x20, then stream[1] = f0 + (31 - (stream[0] * 256 + f0) % 31) % 31
   (at most 0xe0 + 30: no carry into FDICT, no wrap of the unsigned char) *)
Definition rbd_b0 (cinfo: Z) : Z := cinfo * 16 + 8.
Definition rbd_f0 (x: Z) : Z := Z.land x 192 + 32.
Definition rbd_b1 (cinfo x: Z) : Z :=
  rbd_f0 x + (31 - (rbd_b0 cinfo * 256 + rbd_f0 x) mod 31) mod 31.

(* the dictionary id the harness reads: stream[2] << 24 | stream[3] << 16 | stream[4] << 8 | stream[5] *)
Definition rbd_dictid (src: list Z) : Z :=
  Znth 2 src * 16777216 + Znth 3 src * 65536 + Znth 4 src * 256 + Znth 5 src.

(* The theory: after inflateInit2_(w) (the live part init_live sp w), with the stream fields z offering the
   bytes src (an input object, any output object), inflate() returns Z_NEED_DICT and leaves a live stream
   that refuses every dictionary whose Adler-32 is not the id. *)
Definition rbd_theory_stmt : Prop :=
  forall (w cinfo x: Z) (src: list Z) (flush: Z) (strmp sp: val) (z: zfields) (ib: inbuf) (o: outbuf)
         (r: Z) (z': zfields) (st': option live) (ow: list Z),
  8 <= w <= 15 -> 0 <= cinfo <= w - 8 -> 0 <= x <= 255 ->
  bytes_ok src -> 6 <= Zlength src <= Int.max_unsigned ->
  Znth 0 src = rbd_b0 cinfo -> Znth 1 src = rbd_b1 cinfo x ->
  strmp <> nullval -> ib <> InNull -> zf_ok z -> zf_ai z = Zlength src ->
  inflate_rel flush strmp z (Some (init_live sp w)) ib src (Some o) r z' st' ow ->
  r = Z_NEED_DICT /\
  exists L', st' = Some L' /\
    forall dict, Zlib.proof.adler32.Model.adler32_z_val 1 dict <> rbd_dictid src ->
      setdict_check (l_s L') dict = SDData.
