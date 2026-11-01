(* THE specifications of crc32.c (zlib 1.3.2, configuration -DZ_TESTW=: no braided CRC, constant tables),
   shared by every law.

   Stated in the compspecs of the crc32 unit (Zlib.units.Crc32.CS; crc32.c has no composites).

   crc32_z(crc, buf, len) and crc32(crc, buf, len): the constant table crc_table must be readable
   (crc_table_at tsh gv, any readable share tsh: callers carry it from main's globals, where it is
   data_at Ers (tarray tuint 256) .. (gv _crc_table) with the code's constants, equal to crc_table_rep by
   computation);
   - buf = Z_NULL (isnull = true): returns 0, for ANY crc and len (the documented initial value);
   - otherwise buf points at the slice [lo, lo + len) of an object p of n bytes (adler32/Bytes.v cbuf_ok)
     holding the bytes data (and, for an empty object, its malloc token: cbuf_valid): returns ref_crc32 crc data (Model.v: the bit-by-bit reference of
     harness/zlib_common.h), for ANY 64-bit crc.  The object and the table are not changed.
   get_crc_table(): returns the address of crc_table, whose contents are crc_table_rep (the CRC of every
   byte value, ref_crc_byte 0 i). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Crc32.
Require Import Zlib.crc32.code.
Require Export Zlib.proof.crc32.Model.

#[local] Existing Instance Zlib.units.Crc32.CS.

Definition crc_table_at (sh: share) (gv: globals) : mpred :=
  data_at sh (tarray tuint 256) crc_table_rep (gv _crc_table).

Definition crc32_z_spec :=
  DECLARE _crc32_z
  WITH crc: Z, buf: val, len: Z, isnull: bool, sh: share, p: val, lo: Z, n: Z, contents: list val,
       data: list Z, tok: bool, vsh: share, gv: globals, tsh: share
  PRE [ tulong, tptr tuchar, tulong ]
    PROP (0 <= crc <= Int64.max_unsigned; 0 <= len <= Int64.max_unsigned; readable_share tsh;
          cbuf_ok isnull buf sh p lo n len contents data; cbuf_valid isnull tok n)
    PARAMS (Vlong (Int64.repr crc); buf; Vlong (Int64.repr len))
    GLOBALS (gv)
    SEP (crc_table_at tsh gv; if tok then malloc_token vsh (tarray tuchar n) p else emp;
         if isnull then emp else data_at sh (tarray tuchar n) contents p)
  POST [ tulong ]
    PROP ()
    RETURN (Vlong (Int64.repr (if isnull then 0 else ref_crc32 crc data)))
    SEP (crc_table_at tsh gv; if tok then malloc_token vsh (tarray tuchar n) p else emp;
         if isnull then emp else data_at sh (tarray tuchar n) contents p).

Definition crc32_spec :=
  DECLARE _crc32
  WITH crc: Z, buf: val, len: Z, isnull: bool, sh: share, p: val, lo: Z, n: Z, contents: list val,
       data: list Z, tok: bool, vsh: share, gv: globals, tsh: share
  PRE [ tulong, tptr tuchar, tuint ]
    PROP (0 <= crc <= Int64.max_unsigned; 0 <= len <= Int.max_unsigned; readable_share tsh;
          cbuf_ok isnull buf sh p lo n len contents data; cbuf_valid isnull tok n)
    PARAMS (Vlong (Int64.repr crc); buf; Vint (Int.repr len))
    GLOBALS (gv)
    SEP (crc_table_at tsh gv; if tok then malloc_token vsh (tarray tuchar n) p else emp;
         if isnull then emp else data_at sh (tarray tuchar n) contents p)
  POST [ tulong ]
    PROP ()
    RETURN (Vlong (Int64.repr (if isnull then 0 else ref_crc32 crc data)))
    SEP (crc_table_at tsh gv; if tok then malloc_token vsh (tarray tuchar n) p else emp;
         if isnull then emp else data_at sh (tarray tuchar n) contents p).

Definition get_crc_table_spec :=
  DECLARE _get_crc_table
  WITH gv: globals, tsh: share
  PRE [ ]
    PROP (readable_share tsh) PARAMS () GLOBALS (gv) SEP (crc_table_at tsh gv)
  POST [ tptr tuint ]
    PROP () RETURN (gv _crc_table) SEP (crc_table_at tsh gv).

Definition Vprog : varspecs. mk_varspecs Zlib.crc32.code.prog. Defined.

(* The context of each body proof: its callees only (QuickProof.Assembly, entry_shared). *)
Definition Gprog_crc32_z : funspecs := [].
Definition Gprog_crc32 : funspecs := [crc32_z_spec].
Definition Gprog_get_crc_table : funspecs := [].
