(* THE specifications of adler32.c (zlib 1.3.2), shared by every law.

   Stated in the compspecs of the adler32 unit (Zlib.units.Adler32.CS; adler32.c has no composites, and
   byte arrays are the same at every compspecs: Assembly.data_at_tuchar_cs).

   adler32_z(adler, buf, len) and adler32(adler, buf, len):
   - buf = Z_NULL (isnull = true): returns 1, for ANY adler and len (the documented initial value);
   - otherwise buf points at the slice [lo, lo + len) of an object p of n bytes (Bytes.v cbuf_ok) holding
     the bytes data (and, for an empty object, its malloc token: Bytes.v cbuf_valid): returns adler32_z_val adler data (Model.v), for ANY 64-bit adler.  For a valid adler
     (both halves below 65521, at most 32 bits: adler_valid) that is ref_adler32 adler data, the reference
     of harness/zlib_common.h (Model.adler32_z_val_ref).  The object is not changed.
   adler32_combine(adler1, adler2, len2): adler32_combine_impl (Model.v: the exact result of the code for
   any arguments); for valid checksums and len2 >= 0 it is the RFC 1950 algebra adler32_combine_val
   (Facts.v).  adler32_combine_ (static) is the function that adler32_combine and adler32_combine64 call. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Adler32.
Require Import Zlib.adler32.code.
Require Export Zlib.proof.adler32.Model.

#[local] Existing Instance Zlib.units.Adler32.CS.

Definition adler32_z_spec :=
  DECLARE _adler32_z
  WITH adler: Z, buf: val, len: Z, isnull: bool, sh: share, p: val, lo: Z, n: Z, contents: list val,
       data: list Z, tok: bool, vsh: share
  PRE [ tulong, tptr tuchar, tulong ]
    PROP (0 <= adler <= Int64.max_unsigned; 0 <= len <= Int64.max_unsigned;
          cbuf_ok isnull buf sh p lo n len contents data; cbuf_valid isnull tok n)
    PARAMS (Vlong (Int64.repr adler); buf; Vlong (Int64.repr len))
    SEP (if tok then malloc_token vsh (tarray tuchar n) p else emp;
         if isnull then emp else data_at sh (tarray tuchar n) contents p)
  POST [ tulong ]
    PROP ()
    RETURN (Vlong (Int64.repr (if isnull then 1 else adler32_z_val adler data)))
    SEP (if tok then malloc_token vsh (tarray tuchar n) p else emp;
         if isnull then emp else data_at sh (tarray tuchar n) contents p).

Definition adler32_spec :=
  DECLARE _adler32
  WITH adler: Z, buf: val, len: Z, isnull: bool, sh: share, p: val, lo: Z, n: Z, contents: list val,
       data: list Z, tok: bool, vsh: share
  PRE [ tulong, tptr tuchar, tuint ]
    PROP (0 <= adler <= Int64.max_unsigned; 0 <= len <= Int.max_unsigned;
          cbuf_ok isnull buf sh p lo n len contents data; cbuf_valid isnull tok n)
    PARAMS (Vlong (Int64.repr adler); buf; Vint (Int.repr len))
    SEP (if tok then malloc_token vsh (tarray tuchar n) p else emp;
         if isnull then emp else data_at sh (tarray tuchar n) contents p)
  POST [ tulong ]
    PROP ()
    RETURN (Vlong (Int64.repr (if isnull then 1 else adler32_z_val adler data)))
    SEP (if tok then malloc_token vsh (tarray tuchar n) p else emp;
         if isnull then emp else data_at sh (tarray tuchar n) contents p).

(* The exact result of adler32_combine_(adler1, adler2, len2) for len2 >= 0 and any 64-bit adler1, adler2. *)
Definition adler32_combine_impl (x y len2: Z) : Z :=
  let rem := len2 mod ADLER_BASE in
  let x1 := adler_lo x in let x2 := adler_hi x in
  let y1 := adler_lo y in let y2 := adler_hi y in
  let sum1 := x1 + y1 + ADLER_BASE - 1 in
  let sum2 := (rem * x1) mod ADLER_BASE + x2 + y2 + ADLER_BASE - rem in
  let sum1 := if sum1 <? ADLER_BASE then sum1 else sum1 - ADLER_BASE in
  let sum1 := if sum1 <? ADLER_BASE then sum1 else sum1 - ADLER_BASE in
  let sum2 := if sum2 <? 2 * ADLER_BASE then sum2 else sum2 - 2 * ADLER_BASE in
  let sum2 := if sum2 <? ADLER_BASE then sum2 else sum2 - ADLER_BASE in
  Z.lor sum1 (sum2 * 65536).

Definition adler32_combine_result (x y len2: Z) : Z :=
  if len2 <? 0 then 4294967295 else adler32_combine_impl x y len2.

Definition adler32_combine__spec :=
  DECLARE _adler32_combine_
  WITH x: Z, y: Z, len2: Z
  PRE [ tulong, tulong, tlong ]
    PROP (0 <= x <= Int64.max_unsigned; 0 <= y <= Int64.max_unsigned;
          Int64.min_signed <= len2 <= Int64.max_signed)
    PARAMS (Vlong (Int64.repr x); Vlong (Int64.repr y); Vlong (Int64.repr len2))
    SEP ()
  POST [ tulong ]
    PROP ()
    RETURN (Vlong (Int64.repr (adler32_combine_result x y len2)))
    SEP ().

Definition adler32_combine_spec :=
  DECLARE _adler32_combine
  WITH x: Z, y: Z, len2: Z
  PRE [ tulong, tulong, tlong ]
    PROP (0 <= x <= Int64.max_unsigned; 0 <= y <= Int64.max_unsigned;
          Int64.min_signed <= len2 <= Int64.max_signed)
    PARAMS (Vlong (Int64.repr x); Vlong (Int64.repr y); Vlong (Int64.repr len2))
    SEP ()
  POST [ tulong ]
    PROP ()
    RETURN (Vlong (Int64.repr (adler32_combine_result x y len2)))
    SEP ().

Definition Vprog : varspecs. mk_varspecs Zlib.adler32.code.prog. Defined.

(* The context of each body proof: its callees only (QuickProof.Assembly, entry_shared). *)
Definition Gprog_adler32_z : funspecs := [].
Definition Gprog_adler32 : funspecs := [adler32_z_spec].
Definition Gprog_adler32_combine_ : funspecs := [].
Definition Gprog_adler32_combine : funspecs := [adler32_combine__spec].
