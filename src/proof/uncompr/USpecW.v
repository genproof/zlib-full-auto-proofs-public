(* uncompress2_z / uncompress2 for any sizes, with a destination and a source that may be Z_NULL.

   USpec5's and USpecN's specifications take a source and a destination of at most 2^31-1 bytes (uncompress2_z
   then offers each in one piece).  The laws api_short_output and rt_roundtrip give uncompress2 data of any
   length the allocator provides: uncompress2_z then feeds inflate() pieces of at most 2^32-1 bytes
   (UModelW.uncompressw_rel).  These are USpecN's specifications for any object sizes (up to
   Ptrofs.max_unsigned), with the result of UModelW.  The flag dnull is USpecN's: dnull = false, the destination
   is the first cap bytes of an object of dn bytes; dnull = true, the destination is Z_NULL with cap = 0 (zlib.h
   allows it; uncompress2_z then points next_out at its stream's member `reserved`).  The flag snull does the same
   for the source: snull = false, the source is the first |src| bytes of an object of sn bytes; snull = true, the
   source is Z_NULL with no bytes (sn = 0, src = []): zlib.h allows it when *sourceLen is 0 (uncompress2_z rejects
   only `*sourceLen > 0 && source == NULL`), and rj_uncompress_any passes one, as alloc_any_bytes(0) may return
   NULL.  inflate() is then offered next_in = Z_NULL with avail_in = 0 (SpecWSelf.inflate_specW_s's InNull).

   The bodies (statement [uncompr_bodies_w_stmt]): uncompress2_z against [uncompress2_z_spec_w] in the context
   of Spec5's inflateInit_ and inflateEnd and SpecWSelf.inflate_specW_s (inflate() for any uInt sizes, the
   stream's own member allowed as the output); uncompress2 against [uncompress2_spec_w] in the context of
   [uncompress2_z_spec_w]. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Uncompr.
Require Import Zlib.uncompr.code.
Require Export Zlib.proof.uncompr.UModelW.
Require Export Zlib.proof.uncompr.USpecN.
Require Import Zlib.proof.inflate_api.Spec5.
Require Zlib.proof.inflate_api.SpecWSelf.
Require Zlib.proof.uncompr.UBodies5.
Require Import Zlib.proof.crc32.Spec.

#[local] Existing Instance Zlib.units.Uncompr.CS.
Local Open Scope logic.

(* the destination: Z_NULL with no space, or the first cap bytes of an object of dn bytes (any size) *)
Definition dest_ok_w (dnull: bool) (dsh: share) (dp: val) (dn: Z) (dc: list val) (cap: Z) (dtok: bool) : Prop :=
  if dnull then dp = nullval /\ cap = 0 /\ dn = 0 /\ dc = [] /\ dtok = false
  else writable_share dsh /\ isptr dp /\ 0 <= cap <= dn /\ (dtok = false -> 0 < dn) /\ Zlength dc = dn /\
       dn <= Ptrofs.max_unsigned.

(* the source: Z_NULL with no bytes, or the first |src| bytes of an object of sn bytes (any size) *)
Definition src_ok_w (snull: bool) (sp: val) (sn: Z) (sc: list val) (src: list Z) (stok: bool) : Prop :=
  if snull then sp = nullval /\ sn = 0 /\ sc = [] /\ src = [] /\ stok = false
  else isptr sp /\ (stok = false -> 0 < sn) /\ Zlength src <= sn /\ Zlength sc = sn /\ sn <= Ptrofs.max_unsigned /\
       sublist 0 (Zlength src) sc = byte_vals src.

Definition src_rep (snull: bool) (ssh: share) (sp: val) (sn: Z) (sc: list val) (stok: bool) : mpred :=
  if snull then emp
  else data_at ssh (tarray tuchar sn) sc sp * (if stok then malloc_token Ews (tarray tuchar sn) sp else emp).

(* a source object's resource, as the clients that pass one hold it *)
Lemma src_rep_obj ssh sp sn sc stok :
  src_rep false ssh sp sn sc stok =
  data_at ssh (tarray tuchar sn) sc sp * (if stok then malloc_token Ews (tarray tuchar sn) sp else emp).
Proof. reflexivity. Qed.

Definition uncompress2_z_spec_w :=
  DECLARE _uncompress2_z
  WITH gv: globals, dnull: bool, dsh: share, dp: val, dn: Z, dc: list val, cap: Z, dlp: val, dtok: bool,
       snull: bool, stok: bool, ssh: share, sp: val, sn: Z, sc: list val, src: list Z, slp: val,
       gsh: share, tsh: share
  PRE [ tptr tuchar, tptr tulong, tptr tuchar, tptr tulong ]
    PROP (dest_ok_w dnull dsh dp dn dc cap dtok;
          readable_share ssh; src_ok_w snull sp sn sc src stok; bytes_ok src;
          readable_share gsh; readable_share tsh)
    PARAMS (dp; dlp; sp; slp) GLOBALS (gv)
    SEP (dest_rep dnull dsh dp dn dc dtok; data_at Tsh tulong (Vlong (Int64.repr cap)) dlp;
         src_rep snull ssh sp sn sc stok;
         data_at Tsh tulong (Vlong (Int64.repr (Zlength src))) slp;
         uversion_lit gv; inflate_globals gsh tsh gv; mem_mgr gv)
  POST [ tint ]
    EX r: Z, EX slen: Z, EX dlen: Z, EX out: list Z,
    PROP (uncompressw_rel src cap r slen dlen out)
    RETURN (Vint (Int.repr r))
    SEP (dest_rep dnull dsh dp dn (dest_after dc dn out) dtok;
         data_at Tsh tulong (Vlong (Int64.repr dlen)) dlp;
         src_rep snull ssh sp sn sc stok;
         data_at Tsh tulong (Vlong (Int64.repr slen)) slp;
         uversion_lit gv; inflate_globals gsh tsh gv; mem_mgr gv).

Definition uncompress2_spec_w :=
  DECLARE _uncompress2
  WITH gv: globals, dnull: bool, dsh: share, dp: val, dn: Z, dc: list val, cap: Z, dlp: val, dtok: bool,
       snull: bool, stok: bool, ssh: share, sp: val, sn: Z, sc: list val, src: list Z, slp: val,
       gsh: share, tsh: share
  PRE [ tptr tuchar, tptr tulong, tptr tuchar, tptr tulong ]
    PROP (dest_ok_w dnull dsh dp dn dc cap dtok;
          readable_share ssh; src_ok_w snull sp sn sc src stok; bytes_ok src;
          readable_share gsh; readable_share tsh)
    PARAMS (dp; dlp; sp; slp) GLOBALS (gv)
    SEP (dest_rep dnull dsh dp dn dc dtok; data_at Tsh tulong (Vlong (Int64.repr cap)) dlp;
         src_rep snull ssh sp sn sc stok;
         data_at Tsh tulong (Vlong (Int64.repr (Zlength src))) slp;
         uversion_lit gv; inflate_globals gsh tsh gv; mem_mgr gv)
  POST [ tint ]
    EX r: Z, EX slen: Z, EX dlen: Z, EX out: list Z,
    PROP (uncompressw_rel src cap r slen dlen out)
    RETURN (Vint (Int.repr r))
    SEP (dest_rep dnull dsh dp dn (dest_after dc dn out) dtok;
         data_at Tsh tulong (Vlong (Int64.repr dlen)) dlp;
         src_rep snull ssh sp sn sc stok;
         data_at Tsh tulong (Vlong (Int64.repr slen)) slp;
         uversion_lit gv; inflate_globals gsh tsh gv; mem_mgr gv).

(* uncompress2_z's callees: Spec5's inflateInit_ and inflateEnd, and inflate() for any uInt sizes with the
   stream's own member allowed as the output *)
Definition Gp_uncompress2_z_w : funspecs :=
  [Zlib.proof.inflate_api.Spec5.inflateInit__spec; Zlib.proof.inflate_api.SpecWSelf.inflate_specW_s;
   Zlib.proof.inflate_api.Spec5.inflateEnd_spec].

Definition uncompr_bodies_w_stmt : Prop :=
  forall {Espec: OracleKind},
  semax_body UBodies5.Vprog_uncompr5 Gp_uncompress2_z_w f_uncompress2_z uncompress2_z_spec_w /\
  semax_body UBodies5.Vprog_uncompr5 [uncompress2_z_spec_w] f_uncompress2 uncompress2_spec_w.
