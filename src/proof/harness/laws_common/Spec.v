(* The helpers of harness/laws_common.h (upto, clip, any_bytes, copy_of, bytes_eq, offer, new_stream):
   THE specifications, one per function, shared by every short law (prefixes rt_, ck_, rj_, rfc_, api_, res_).

   Each helper is the same Clight term in every harness unit that keeps it (identifiers are name-based; a
   unit drops the helpers its main does not call); the terms are taken here from harness/api_untouched_output.c's
   unit, which keeps all seven.  The byte helpers are specified at the compspecs of the adler32 unit (no
   struct), offer and new_stream at those of the compress unit (struct z_stream_s only); QuickProof.Assembly's
   entry_shared moves a body proved at these compspecs into each law's program.

   Byte slices are given as in src/proof/adler32/HarnessBytes.v: [cbuf_ok false buf sh p lo n len contents
   data] (adler32/Bytes.v): buf = p + lo, the object at p has n bytes [contents], and the slice [lo, lo + len)
   holds the bytes [data].  A new object of n arbitrary bytes is [data_at Ews (tarray tuchar n) (bytes_rep bs)]
   with its malloc token. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require Import Zlib.proof.adler32.Bytes.
Require Zlib.units.Adler32 Zlib.units.Compress.
Require Zlib.harness.api_untouched_output.code.
Module HL := Zlib.harness.api_untouched_output.code.

Section ByteHelpers.
#[local] Existing Instance Zlib.units.Adler32.CS.

(* upto(max): any value from 0 to max *)
Definition upto_spec :=
  DECLARE HL._upto
  WITH max : Z
  PRE [ tulong ]
    PROP (0 <= max <= Int64.max_unsigned)
    PARAMS (Vlong (Int64.repr max))
    SEP ()
  POST [ tulong ]
    EX v : Z,
    PROP (0 <= v <= max)
    RETURN (Vlong (Int64.repr v))
    SEP ().

(* clip(n): the most one call can take, min(n, UINT_MAX) *)
Definition clip_spec :=
  DECLARE HL._clip
  WITH n : Z
  PRE [ tulong ]
    PROP (0 <= n <= Int64.max_unsigned)
    PARAMS (Vlong (Int64.repr n))
    SEP ()
  POST [ tuint ]
    PROP ()
    RETURN (Vint (Int.repr (Z.min n Int.max_unsigned)))
    SEP ().

(* any_bytes(n): a new object of n arbitrary bytes, or NULL when malloc fails *)
Definition any_bytes_spec :=
  DECLARE HL._alloc_any_bytes
  WITH n : Z, gv : globals
  PRE [ tulong ]
    PROP (0 <= n <= Ptrofs.max_unsigned)
    PARAMS (Vlong (Int64.repr n)) GLOBALS (gv)
    SEP (mem_mgr gv)
  POST [ tptr tuchar ]
    EX q : val, EX bs : list Z,
    PROP (Zlength bs = n; is_bytes bs)
    RETURN (q)
    SEP (mem_mgr gv;
         if eq_dec q nullval then emp
         else (malloc_token Ews (tarray tuchar n) q * data_at Ews (tarray tuchar n) (bytes_rep bs) q)).

(* copy_of(source, len): a new object holding the slice source[0..len), or NULL when malloc fails *)
Definition copy_of_spec :=
  DECLARE HL._copy_of
  WITH buf : val, sh : share, p : val, lo : Z, n : Z, contents : list val, len : Z, data : list Z,
       gv : globals
  PRE [ tptr tuchar, tulong ]
    PROP (0 <= len <= Ptrofs.max_unsigned; cbuf_ok false buf sh p lo n len contents data)
    PARAMS (buf; Vlong (Int64.repr len)) GLOBALS (gv)
    SEP (mem_mgr gv; data_at sh (tarray tuchar n) contents p)
  POST [ tptr tuchar ]
    EX q : val,
    PROP ()
    RETURN (q)
    SEP (mem_mgr gv; data_at sh (tarray tuchar n) contents p;
         if eq_dec q nullval then emp
         else (malloc_token Ews (tarray tuchar len) q * data_at Ews (tarray tuchar len) (bytes_rep data) q)).

(* bytes_eq(a, b, len): 1 when the two slices hold the same bytes, 0 otherwise *)
Definition bytes_eq_spec :=
  DECLARE HL._bytes_eq
  WITH a : val, sha : share, pa : val, loa : Z, na : Z, ca : list val, da : list Z,
       b : val, shb : share, pb : val, lob : Z, nb : Z, cb : list val, db : list Z, len : Z
  PRE [ tptr tuchar, tptr tuchar, tulong ]
    PROP (0 <= len <= Int64.max_unsigned; cbuf_ok false a sha pa loa na len ca da;
          cbuf_ok false b shb pb lob nb len cb db)
    PARAMS (a; b; Vlong (Int64.repr len))
    SEP (data_at sha (tarray tuchar na) ca pa; data_at shb (tarray tuchar nb) cb pb)
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr (if list_eq_dec Z.eq_dec da db then 1 else 0)))
    SEP (data_at sha (tarray tuchar na) ca pa; data_at shb (tarray tuchar nb) cb pb).

End ByteHelpers.

Section StreamHelpers.
#[local] Existing Instance Zlib.units.Compress.CS.

Definition t_zs : type := Tstruct HL._z_stream_s noattr.

(* A z_stream's 14 members in declaration order: next_in, avail_in, total_in, next_out, avail_out,
   total_out, msg, state, zalloc, zfree, opaque, data_type, adler, reserved. *)
Definition zs_val (next_in avail_in total_in next_out avail_out total_out msg state zalloc zfree opaque
                   data_type adler reserved : val) : reptype t_zs :=
  (next_in, (avail_in, (total_in, (next_out, (avail_out, (total_out, (msg, (state,
   (zalloc, (zfree, (opaque, (data_type, (adler, reserved))))))))))))).

(* offer(strm, in, in_len, out, out_len): next_in = in, avail_in = (uInt) in_len, next_out = out,
   avail_out = (uInt) out_len; every other member unchanged (any values, Vundef included) *)
Definition offer_spec :=
  DECLARE HL._set_buffer
  WITH sp : val, sh : share, inp : val, in_len : Z, outp : val, out_len : Z,
       ni : val, ai : val, ti : val, no : val, ao : val, to : val, msg : val, st : val,
       za : val, zf : val, op : val, dt : val, ad : val, rs : val
  PRE [ tptr t_zs, tptr tuchar, tulong, tptr tuchar, tulong ]
    PROP (writable_share sh; 0 <= in_len <= Int64.max_unsigned; 0 <= out_len <= Int64.max_unsigned)
    PARAMS (sp; inp; Vlong (Int64.repr in_len); outp; Vlong (Int64.repr out_len))
    SEP (data_at sh t_zs (zs_val ni ai ti no ao to msg st za zf op dt ad rs) sp)
  POST [ tvoid ]
    PROP ()
    RETURN ()
    SEP (data_at sh t_zs (zs_val inp (Vint (Int.repr in_len)) ti outp (Vint (Int.repr out_len)) to msg st
                            za zf op dt ad rs) sp).

(* new_stream(strm): zalloc, zfree, opaque Z_NULL (zlib's own allocator), next_in and next_out Z_NULL,
   avail_in and avail_out 0; every other member unchanged *)
Definition new_stream_spec :=
  DECLARE HL._new_stream
  WITH sp : val, sh : share,
       ni : val, ai : val, ti : val, no : val, ao : val, to : val, msg : val, st : val,
       za : val, zf : val, op : val, dt : val, ad : val, rs : val
  PRE [ tptr t_zs ]
    PROP (writable_share sh)
    PARAMS (sp)
    SEP (data_at sh t_zs (zs_val ni ai ti no ao to msg st za zf op dt ad rs) sp)
  POST [ tvoid ]
    PROP ()
    RETURN ()
    SEP (data_at sh t_zs (zs_val nullval (Vint (Int.repr 0)) ti nullval (Vint (Int.repr 0)) to msg st
                            nullval nullval nullval dt ad rs) sp).

End StreamHelpers.

(* The contexts of the bodies: the callees of each helper. *)
Definition Vprog_lc : varspecs := [].
Definition Gprog_upto : funspecs := [nondet_size_spec].
Definition Gprog_clip : funspecs := [].
Definition Gprog_any_bytes : funspecs :=
  [(_quickproof_malloc, @malloc_spec' Zlib.units.Adler32.CS); @nondet_bytes_spec Zlib.units.Adler32.CS].
Definition Gprog_copy_of : funspecs := [(_quickproof_malloc, @malloc_spec' Zlib.units.Adler32.CS)].
Definition Gprog_bytes_eq : funspecs := [].
Definition Gprog_offer : funspecs := [].
Definition Gprog_new_stream : funspecs := [offer_spec].

(* The bodies of the seven helpers against their specifications: every short law's assembly takes this
   as its hypothesis (src/proof/harness/laws_common/Bodies.v proves it). *)
Definition laws_common_ok : Prop :=
  @semax_body Vprog_lc Gprog_upto Zlib.units.Adler32.CS HL.f_upto upto_spec /\
  @semax_body Vprog_lc Gprog_clip Zlib.units.Adler32.CS HL.f_clip clip_spec /\
  @semax_body Vprog_lc Gprog_any_bytes Zlib.units.Adler32.CS HL.f_alloc_any_bytes any_bytes_spec /\
  @semax_body Vprog_lc Gprog_copy_of Zlib.units.Adler32.CS HL.f_copy_of copy_of_spec /\
  @semax_body Vprog_lc Gprog_bytes_eq Zlib.units.Adler32.CS HL.f_bytes_eq bytes_eq_spec /\
  @semax_body Vprog_lc Gprog_offer Zlib.units.Compress.CS HL.f_set_buffer offer_spec /\
  @semax_body Vprog_lc Gprog_new_stream Zlib.units.Compress.CS HL.f_new_stream new_stream_spec.
