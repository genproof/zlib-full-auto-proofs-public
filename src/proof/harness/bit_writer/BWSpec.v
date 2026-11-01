(* THE specifications of the bit writer put_bits / put_literal of harness/rj_bad_block.c and harness/rj_far_back.c
   (the same Clight terms in both programs: identifiers are name-based; the terms are taken from rj_bad_block's
   unit).  At the compspecs of the adler32 unit (no struct), like the byte helpers of laws_common.h; each law moves
   the bodies (bit_writer_ok, proved in BWBodies.v) into its program with QuickProof.Assembly's entry_shared.

   The stream is an object of n bytes [data_at sh (tarray tuchar n) (bytes_rep bytes)], the bit position a size_t
   object; the new bytes are given by the model BWModel.v. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.adler32.Bytes.
Require Export Zlib.proof.harness.bit_writer.BWModel.
Require Zlib.units.Adler32.
Require Zlib.harness.rj_bad_block.code.
Module BWC := Zlib.harness.rj_bad_block.code.

Section Specs.
#[local] Existing Instance Zlib.units.Adler32.CS.

(* put_bits(stream, &bit, value, count, huffman): bits [bit, bit + count) of the stream := the count low bits of
   value (least significant first, or most significant first when huffman <> 0); bit += count *)
Definition put_bits_spec :=
  DECLARE BWC._put_bits
  WITH sh : share, stream : val, shb : share, bitp : val, bytes : list Z, bit : Z, value : Z, count : Z,
       huffman : Z
  PRE [ tptr tuchar, tptr tulong, tuint, tuint, tint ]
    PROP (writable_share sh; writable_share shb; is_bytes bytes; Zlength bytes <= Ptrofs.max_unsigned;
          0 <= bit; 0 <= count <= 32; bit + count <= 8 * Zlength bytes; bit + count <= Int64.max_unsigned;
          0 <= value <= Int.max_unsigned; Int.min_signed <= huffman <= Int.max_signed)
    PARAMS (stream; bitp; Vint (Int.repr value); Vint (Int.repr count); Vint (Int.repr huffman))
    SEP (data_at sh (tarray tuchar (Zlength bytes)) (bytes_rep bytes) stream;
         data_at shb tulong (Vlong (Int64.repr bit)) bitp)
  POST [ tvoid ]
    PROP ()
    RETURN ()
    SEP (data_at sh (tarray tuchar (Zlength bytes)) (bytes_rep (put_bits_m bytes bit value count huffman)) stream;
         data_at shb tulong (Vlong (Int64.repr (bit + count))) bitp).

(* put_literal(stream, &bit, literal): the fixed code of the literal (RFC 1951 3.2.6) at bit; bit += its length *)
Definition put_literal_spec :=
  DECLARE BWC._put_literal
  WITH sh : share, stream : val, shb : share, bitp : val, bytes : list Z, bit : Z, lit : Z
  PRE [ tptr tuchar, tptr tulong, tuint ]
    PROP (writable_share sh; writable_share shb; is_bytes bytes; Zlength bytes <= Ptrofs.max_unsigned;
          0 <= bit; 0 <= lit < 256; bit + lit_len lit <= 8 * Zlength bytes;
          bit + lit_len lit <= Int64.max_unsigned)
    PARAMS (stream; bitp; Vint (Int.repr lit))
    SEP (data_at sh (tarray tuchar (Zlength bytes)) (bytes_rep bytes) stream;
         data_at shb tulong (Vlong (Int64.repr bit)) bitp)
  POST [ tvoid ]
    PROP ()
    RETURN ()
    SEP (data_at sh (tarray tuchar (Zlength bytes)) (bytes_rep (put_literal_m bytes bit lit)) stream;
         data_at shb tulong (Vlong (Int64.repr (bit + lit_len lit))) bitp).

End Specs.

(* The contexts of the bodies: the callees. *)
Definition Vprog_bw : varspecs := [].
Definition Gprog_put_bits : funspecs := [].
Definition Gprog_put_literal : funspecs := [put_bits_spec].

(* The two bodies against their specifications (BWBodies.bit_writer_bodies proves it). *)
Definition bit_writer_ok : Prop :=
  @semax_body Vprog_bw Gprog_put_bits Zlib.units.Adler32.CS BWC.f_put_bits put_bits_spec /\
  @semax_body Vprog_bw Gprog_put_literal Zlib.units.Adler32.CS BWC.f_put_literal put_literal_spec.
