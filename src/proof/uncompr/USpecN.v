(* uncompress2_z / uncompress2 with a destination that may be Z_NULL.

   zlib.h allows dest = Z_NULL when *destLen = 0; uncompress2_z then points next_out at its stream's member
   `reserved` (inflate_api/SpecSelf.v).  USpec5's specifications require a pointer destination.  The
   specifications below take a flag dnull: dnull = false is USpec5's case exactly (the destination is the first
   cap bytes of an object of dn bytes); dnull = true is the Z_NULL destination with cap = 0 and no object.  The
   result is USpec5's (UModel.uncompress_rel), so callers of USpec5 lose nothing.

   The bodies (round 1's UBodiesN.v; the laws here use USpecW.v, whose bodies UBodiesW.v
   proves): uncompress2_z against [uncompress2_z_spec_n] in the context of inflateInit_,
   inflate (SpecSelf.inflate_spec_s, which allows the stream's own member as the output) and inflateEnd;
   uncompress2 against [uncompress2_spec_n] in the context of [uncompress2_z_spec_n]. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Uncompr.
Require Import Zlib.uncompr.code.
Require Export Zlib.proof.uncompr.USpec5.
Require Import Zlib.proof.inflate_api.Spec5.
Require Zlib.proof.inflate_api.SpecSelf.
Require Zlib.proof.uncompr.UBodies5.
Require Import Zlib.proof.crc32.Spec.

#[local] Existing Instance Zlib.units.Uncompr.CS.
Local Open Scope logic.

(* the destination: Z_NULL with no space, or the first cap bytes of an object of dn bytes (USpec5) *)
Definition dest_ok (dnull: bool) (dsh: share) (dp: val) (dn: Z) (dc: list val) (cap: Z) (dtok: bool) : Prop :=
  if dnull then dp = nullval /\ cap = 0 /\ dn = 0 /\ dc = [] /\ dtok = false
  else writable_share dsh /\ isptr dp /\ 0 <= cap <= dn /\ (dtok = false -> 0 < dn) /\ Zlength dc = dn /\
       dn <= Int.max_signed.

Definition dest_rep (dnull: bool) (dsh: share) (dp: val) (dn: Z) (dc: list val) (dtok: bool) : mpred :=
  if dnull then emp
  else data_at dsh (tarray tuchar dn) dc dp * (if dtok then malloc_token Ews (tarray tuchar dn) dp else emp).

Definition uncompress2_z_spec_n :=
  DECLARE _uncompress2_z
  WITH gv: globals, dnull: bool, dsh: share, dp: val, dn: Z, dc: list val, cap: Z, dlp: val, dtok: bool,
       stok: bool, ssh: share, sp: val, sn: Z, sc: list val, src: list Z, slp: val, gsh: share, tsh: share
  PRE [ tptr tuchar, tptr tulong, tptr tuchar, tptr tulong ]
    PROP (dest_ok dnull dsh dp dn dc cap dtok;
          readable_share ssh; isptr sp; stok = false -> 0 < sn; Zlength src <= sn; Zlength sc = sn; sn <= Int.max_signed;
          sublist 0 (Zlength src) sc = byte_vals src; bytes_ok src;
          readable_share gsh; readable_share tsh)
    PARAMS (dp; dlp; sp; slp) GLOBALS (gv)
    SEP (dest_rep dnull dsh dp dn dc dtok; data_at Tsh tulong (Vlong (Int64.repr cap)) dlp;
         data_at ssh (tarray tuchar sn) sc sp; if stok then malloc_token Ews (tarray tuchar sn) sp else emp; data_at Tsh tulong (Vlong (Int64.repr (Zlength src))) slp;
         uversion_lit gv; inflate_globals gsh tsh gv; mem_mgr gv)
  POST [ tint ]
    EX r: Z, EX slen: Z, EX dlen: Z, EX out: list Z,
    PROP (uncompress_rel src cap r slen dlen out)
    RETURN (Vint (Int.repr r))
    SEP (dest_rep dnull dsh dp dn (dest_after dc dn out) dtok;
         data_at Tsh tulong (Vlong (Int64.repr dlen)) dlp;
         data_at ssh (tarray tuchar sn) sc sp; if stok then malloc_token Ews (tarray tuchar sn) sp else emp; data_at Tsh tulong (Vlong (Int64.repr slen)) slp;
         uversion_lit gv; inflate_globals gsh tsh gv; mem_mgr gv).

Definition uncompress2_spec_n :=
  DECLARE _uncompress2
  WITH gv: globals, dnull: bool, dsh: share, dp: val, dn: Z, dc: list val, cap: Z, dlp: val, dtok: bool,
       stok: bool, ssh: share, sp: val, sn: Z, sc: list val, src: list Z, slp: val, gsh: share, tsh: share
  PRE [ tptr tuchar, tptr tulong, tptr tuchar, tptr tulong ]
    PROP (dest_ok dnull dsh dp dn dc cap dtok;
          readable_share ssh; isptr sp; stok = false -> 0 < sn; Zlength src <= sn; Zlength sc = sn; sn <= Int.max_signed;
          sublist 0 (Zlength src) sc = byte_vals src; bytes_ok src;
          readable_share gsh; readable_share tsh)
    PARAMS (dp; dlp; sp; slp) GLOBALS (gv)
    SEP (dest_rep dnull dsh dp dn dc dtok; data_at Tsh tulong (Vlong (Int64.repr cap)) dlp;
         data_at ssh (tarray tuchar sn) sc sp; if stok then malloc_token Ews (tarray tuchar sn) sp else emp; data_at Tsh tulong (Vlong (Int64.repr (Zlength src))) slp;
         uversion_lit gv; inflate_globals gsh tsh gv; mem_mgr gv)
  POST [ tint ]
    EX r: Z, EX slen: Z, EX dlen: Z, EX out: list Z,
    PROP (uncompress_rel src cap r slen dlen out)
    RETURN (Vint (Int.repr r))
    SEP (dest_rep dnull dsh dp dn (dest_after dc dn out) dtok;
         data_at Tsh tulong (Vlong (Int64.repr dlen)) dlp;
         data_at ssh (tarray tuchar sn) sc sp; if stok then malloc_token Ews (tarray tuchar sn) sp else emp; data_at Tsh tulong (Vlong (Int64.repr slen)) slp;
         uversion_lit gv; inflate_globals gsh tsh gv; mem_mgr gv).

(* uncompress2_z's callees, with inflate's specification that allows the stream's own member as the output *)
Definition Gp_uncompress2_z_n : funspecs :=
  [Zlib.proof.inflate_api.Spec5.inflateInit__spec; Zlib.proof.inflate_api.SpecSelf.inflate_spec_s;
   Zlib.proof.inflate_api.Spec5.inflateEnd_spec].

Definition uncompr_bodies_n_stmt : Prop :=
  forall {Espec: OracleKind},
  semax_body UBodies5.Vprog_uncompr5 Gp_uncompress2_z_n f_uncompress2_z uncompress2_z_spec_n /\
  semax_body UBodies5.Vprog_uncompr5 [uncompress2_z_spec_n] f_uncompress2 uncompress2_spec_n.
