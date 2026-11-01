(* Law rfc_stored: the stream harness/rfc_stored.c builds, as a pure function of its choices.

   The harness takes n = |d| data bytes d, a list of block lengths lens (each <= 65535, summing to n, at least
   one block), a wrapper wr (0 raw, 1 zlib, 2 gzip), inflate's window (8..15), the zlib CINFO c (<= window - 8)
   and the initial bytes s0 of the stream buffer (any_bytes).  It overwrites in s0:
   - the header (zlib: CMF, FLG with s0's FLEVEL bits and FCHECK; gzip: ID1 ID2 CM, FLG = s0's FTEXT bit,
     MTIME XFL OS left as s0 has them);
   - per block: the first byte keeps s0's five high bits (the padding before the byte boundary) with BTYPE 00
     and BFINAL on the last block, then LEN NLEN and the data bytes;
   - the trailer (zlib: ADLER32 big-endian; gzip: CRC32, ISIZE little-endian);
   the bytes after the trailer stay s0's.

   `rs_src wr c s0 pads lens d` is that stream, with the padding bytes `pads` (one per block: the high bits of
   the block's first byte) given explicitly: the harness's are s0's bytes at the blocks' first positions
   (`rs_pads`), the canonical stream of RFC 1951 (Format.enc_block: zero padding) has pads = 0. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.rfc1951.Format.
Require Zlib.proof.adler32.Model Zlib.proof.crc32.Model.
Import ListNotations.
Local Open Scope Z_scope.

(* header and trailer lengths of the wrapper *)
Definition rs_hl (wr: Z) : Z := if wr =? 1 then 2 else if wr =? 2 then 10 else 0.
Definition rs_tl (wr: Z) : Z := if wr =? 1 then 4 else if wr =? 2 then 8 else 0.

(* the header the harness writes over s0 *)
Definition rs_hdr (wr c: Z) (s0: list Z) : list Z :=
  if wr =? 1 then zlib_hdr (c + 8) (Z.shiftr (Znth 1 s0) 6) false
  else if wr =? 2 then [31; 139; 8; Z.land (Znth 3 s0) 1] ++ sublist 4 10 s0
  else [].

(* one stored block: the first byte (padding bits of pad, BTYPE 00, BFINAL), LEN, NLEN, the bytes *)
Definition rs_block (pad: Z) (last: bool) (chunk: list Z) : list Z :=
  let len := Zlength chunk in
  [Z.lor (Z.land pad 248) (if last then 1 else 0); len mod 256; len / 256;
   (65535 - len) mod 256; (65535 - len) / 256] ++ chunk.

(* the blocks: block k has length Znth k lens, padding byte Znth k pads, and the next bytes of d *)
Fixpoint rs_blocks (pads lens: list Z) (d: list Z) : list Z :=
  match lens, pads with
  | [], _ => []
  | l :: r, _ =>
      rs_block (hd 0 pads) (match r with [] => true | _ => false end) (sublist 0 l d) ++
      rs_blocks (tl pads) r (sublist l (Zlength d) d)
  end.

(* the data cut into the blocks *)
Fixpoint rs_chunks (lens: list Z) (d: list Z) : list (list Z) :=
  match lens with
  | [] => []
  | l :: r => sublist 0 l d :: rs_chunks r (sublist l (Zlength d) d)
  end.

(* the positions of the blocks' first bytes in the stream, from position p *)
Fixpoint rs_bpos (p: Z) (lens: list Z) : list Z :=
  match lens with [] => [] | l :: r => p :: rs_bpos (p + 5 + l) r end.

(* the harness's padding bytes: s0 at the blocks' first bytes *)
Definition rs_pads (wr: Z) (s0 lens: list Z) : list Z := map (fun p => Znth p s0) (rs_bpos (rs_hl wr) lens).

(* the trailer *)
Definition rs_trl (wr: Z) (d: list Z) : list Z :=
  if wr =? 1 then be_bytes (Zlib.proof.adler32.Model.ref_adler32 1 d) 4
  else if wr =? 2 then le_bytes (Zlib.proof.crc32.Model.ref_crc32 0 d) 4 ++ le_bytes (Zlength d mod 2 ^ 32) 4
  else [].

(* the length of the stream proper (header, blocks, trailer) *)
Definition rs_slen (wr: Z) (lens d: list Z) : Z := rs_hl wr + 5 * Zlength lens + Zlength d + rs_tl wr.

(* the whole buffer after the harness's writes *)
Definition rs_src (wr c: Z) (s0 pads lens d: list Z) : list Z :=
  rs_hdr wr c s0 ++ rs_blocks pads lens d ++ rs_trl wr d ++ sublist (rs_slen wr lens d) (Zlength s0) s0.

Definition rs_bytes (l: list Z) : Prop := Forall byte_ok l.

(* the harness's choices, as its code constrains them *)
Definition rs_ok (wr window c: Z) (s0 lens d: list Z) : Prop :=
  0 <= wr <= 2 /\ 8 <= window <= 15 /\ (wr = 1 -> 0 <= c <= window - 8) /\
  lens <> [] /\ Forall (fun l => 0 <= l <= 65535) lens /\ fold_right Z.add 0 lens = Zlength d /\
  rs_slen wr lens d <= Zlength s0 /\ rs_bytes s0 /\ rs_bytes d.

(* inflateInit2's windowBits: window_bits[wrapper] = {-window, window, 16 + window} *)
Definition rs_iw (wr window: Z) : Z := if wr =? 1 then window else if wr =? 2 then 16 + window else - window.

(* the stream in Format's terms *)
Definition rs_wrapper (wr c: Z) (s0: list Z) : wrapper :=
  if wr =? 1 then WZlib (c + 8) (Z.shiftr (Znth 1 s0) 6) None
  else if wr =? 2 then
    WGzip (GzHdr (Z.land (Znth 3 s0) 1 =? 1)
                 (Znth 4 s0 + 256 * Znth 5 s0 + 65536 * Znth 6 s0 + 16777216 * Znth 7 s0)
                 (Znth 8 s0) (Znth 9 s0) None None None false)
  else WRaw.
Definition rs_wb (wr window c: Z) : Z := if wr =? 1 then c + 8 else window.
Definition rs_bs (lens d: list Z) : list block := map Stored (rs_chunks lens d).
