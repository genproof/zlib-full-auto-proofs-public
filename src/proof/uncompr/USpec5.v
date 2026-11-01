(* Version 5 (inflate_api/Spec5.v; Version 4: the source's malloc token stok too (inflate() compares next_in with NULL); the destination's malloc token when it may be empty: uncompress2_z
   compares dest with NULL when its length is 0). THE external specifications of uncompr.c (uncompress2_z, uncompress2, uncompress), at the
   compspecs of the uncompr unit: the result is the model's uncompress_rel (Model.v).  The source is
   the first |src| bytes of an object, the destination the first cap bytes of an object; sizes below
   2^31 (uncompress2_z then offers everything in one chunk per call). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Uncompr.
Require Import Zlib.uncompr.code.
Require Export Zlib.proof.uncompr.UModel.
Require Import Zlib.proof.inflate_api.Spec5.
Require Import Zlib.proof.crc32.Spec.

#[local] Existing Instance Zlib.units.Uncompr.CS.
Local Open Scope logic.

(* uncompr.c's ZLIB_VERSION literal "1.3.2" *)
Definition uversion_lit (gv: globals) : mpred :=
  data_at Ers (tarray tschar 6) (map (fun c => Vint (Int.repr c)) [49; 46; 51; 46; 50; 0])
    (gv ___stringlit_uncompr_1).

(* what inflate() needs of the program's globals (at the inflate unit's compspecs) *)
Definition inflate_globals (gsh tsh: share) (gv: globals) : mpred :=
  @tables_rep gsh gv * crc_table_at tsh gv * @version_lit gv * @zfuncs gv.

Definition dest_after (dc: list val) (dn: Z) (out: list Z) : list val :=
  byte_vals out ++ sublist (Zlength out) dn dc.

Definition uncompress2_spec :=
  DECLARE _uncompress2
  WITH gv: globals, dsh: share, dp: val, dn: Z, dc: list val, cap: Z, dlp: val, dtok: bool, stok: bool,
       ssh: share, sp: val, sn: Z, sc: list val, src: list Z, slp: val, gsh: share, tsh: share
  PRE [ tptr tuchar, tptr tulong, tptr tuchar, tptr tulong ]
    PROP (writable_share dsh; isptr dp; 0 <= cap <= dn; dtok = false -> 0 < dn; Zlength dc = dn; dn <= Int.max_signed;
          readable_share ssh; isptr sp; stok = false -> 0 < sn; Zlength src <= sn; Zlength sc = sn; sn <= Int.max_signed;
          sublist 0 (Zlength src) sc = byte_vals src; bytes_ok src;
          readable_share gsh; readable_share tsh)
    PARAMS (dp; dlp; sp; slp) GLOBALS (gv)
    SEP (data_at dsh (tarray tuchar dn) dc dp; if dtok then malloc_token Ews (tarray tuchar dn) dp else emp; data_at Tsh tulong (Vlong (Int64.repr cap)) dlp;
         data_at ssh (tarray tuchar sn) sc sp; if stok then malloc_token Ews (tarray tuchar sn) sp else emp; data_at Tsh tulong (Vlong (Int64.repr (Zlength src))) slp;
         uversion_lit gv; inflate_globals gsh tsh gv; mem_mgr gv)
  POST [ tint ]
    EX r: Z, EX slen: Z, EX dlen: Z, EX out: list Z,
    PROP (uncompress_rel src cap r slen dlen out)
    RETURN (Vint (Int.repr r))
    SEP (data_at dsh (tarray tuchar dn) (dest_after dc dn out) dp; if dtok then malloc_token Ews (tarray tuchar dn) dp else emp;
         data_at Tsh tulong (Vlong (Int64.repr dlen)) dlp;
         data_at ssh (tarray tuchar sn) sc sp; if stok then malloc_token Ews (tarray tuchar sn) sp else emp; data_at Tsh tulong (Vlong (Int64.repr slen)) slp;
         uversion_lit gv; inflate_globals gsh tsh gv; mem_mgr gv).

Definition uncompress_spec :=
  DECLARE _uncompress
  WITH gv: globals, dsh: share, dp: val, dn: Z, dc: list val, cap: Z, dlp: val, dtok: bool, stok: bool,
       ssh: share, sp: val, sn: Z, sc: list val, src: list Z, gsh: share, tsh: share
  PRE [ tptr tuchar, tptr tulong, tptr tuchar, tulong ]
    PROP (writable_share dsh; isptr dp; 0 <= cap <= dn; dtok = false -> 0 < dn; Zlength dc = dn; dn <= Int.max_signed;
          readable_share ssh; isptr sp; stok = false -> 0 < sn; Zlength src <= sn; Zlength sc = sn; sn <= Int.max_signed;
          sublist 0 (Zlength src) sc = byte_vals src; bytes_ok src;
          readable_share gsh; readable_share tsh)
    PARAMS (dp; dlp; sp; Vlong (Int64.repr (Zlength src))) GLOBALS (gv)
    SEP (data_at dsh (tarray tuchar dn) dc dp; if dtok then malloc_token Ews (tarray tuchar dn) dp else emp; data_at Tsh tulong (Vlong (Int64.repr cap)) dlp;
         data_at ssh (tarray tuchar sn) sc sp; if stok then malloc_token Ews (tarray tuchar sn) sp else emp;
         uversion_lit gv; inflate_globals gsh tsh gv; mem_mgr gv)
  POST [ tint ]
    EX r: Z, EX slen: Z, EX dlen: Z, EX out: list Z,
    PROP (uncompress_rel src cap r slen dlen out)
    RETURN (Vint (Int.repr r))
    SEP (data_at dsh (tarray tuchar dn) (dest_after dc dn out) dp; if dtok then malloc_token Ews (tarray tuchar dn) dp else emp;
         data_at Tsh tulong (Vlong (Int64.repr dlen)) dlp;
         data_at ssh (tarray tuchar sn) sc sp; if stok then malloc_token Ews (tarray tuchar sn) sp else emp;
         uversion_lit gv; inflate_globals gsh tsh gv; mem_mgr gv).

(* uncompress2_z: the same with z_size_t (unsigned long) lengths *)
Definition uncompress2_z_spec :=
  DECLARE _uncompress2_z
  WITH gv: globals, dsh: share, dp: val, dn: Z, dc: list val, cap: Z, dlp: val, dtok: bool, stok: bool,
       ssh: share, sp: val, sn: Z, sc: list val, src: list Z, slp: val, gsh: share, tsh: share
  PRE [ tptr tuchar, tptr tulong, tptr tuchar, tptr tulong ]
    PROP (writable_share dsh; isptr dp; 0 <= cap <= dn; dtok = false -> 0 < dn; Zlength dc = dn; dn <= Int.max_signed;
          readable_share ssh; isptr sp; stok = false -> 0 < sn; Zlength src <= sn; Zlength sc = sn; sn <= Int.max_signed;
          sublist 0 (Zlength src) sc = byte_vals src; bytes_ok src;
          readable_share gsh; readable_share tsh)
    PARAMS (dp; dlp; sp; slp) GLOBALS (gv)
    SEP (data_at dsh (tarray tuchar dn) dc dp; if dtok then malloc_token Ews (tarray tuchar dn) dp else emp; data_at Tsh tulong (Vlong (Int64.repr cap)) dlp;
         data_at ssh (tarray tuchar sn) sc sp; if stok then malloc_token Ews (tarray tuchar sn) sp else emp; data_at Tsh tulong (Vlong (Int64.repr (Zlength src))) slp;
         uversion_lit gv; inflate_globals gsh tsh gv; mem_mgr gv)
  POST [ tint ]
    EX r: Z, EX slen: Z, EX dlen: Z, EX out: list Z,
    PROP (uncompress_rel src cap r slen dlen out)
    RETURN (Vint (Int.repr r))
    SEP (data_at dsh (tarray tuchar dn) (dest_after dc dn out) dp; if dtok then malloc_token Ews (tarray tuchar dn) dp else emp;
         data_at Tsh tulong (Vlong (Int64.repr dlen)) dlp;
         data_at ssh (tarray tuchar sn) sc sp; if stok then malloc_token Ews (tarray tuchar sn) sp else emp; data_at Tsh tulong (Vlong (Int64.repr slen)) slp;
         uversion_lit gv; inflate_globals gsh tsh gv; mem_mgr gv).
