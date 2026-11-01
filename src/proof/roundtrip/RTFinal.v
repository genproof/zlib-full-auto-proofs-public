(* The round-trip laws: THE contract between the deflate side and the inflate side.

   [dfinal dict wrap wb gh D O]: the bytes O that deflate produced, from deflateInit2 to Z_STREAM_END, are a
   well-formed stream (Format.v) of the data D, with the history [dict] (the preset dictionary, [] if none),
   window bits [wb] (deflate's w_bits, 9..15), and
   - wrap 0 (raw): the deflate bytes;
   - wrap 1 (zlib): the 2-byte header CMF FLG (CINFO = wb - 8, CM = 8, a multiple of 31, FDICT exactly when
     there is a dictionary; NB zlib's `header += 31 - header % 31` gives FCHECK = 31 when the header is already a
     multiple of 31, e.g. 78 3f, which Format.zlib_hdr does not produce), the dictionary's Adler-32 when there
     is one, the deflate bytes, the Adler-32 of D;
   - wrap 2 (gzip): Format's gzip member with the header of deflateSetHeader's fields [gh] (or zlib's default
     header 1f 8b 08 00 00000000 xfl 03 when none was set), XFL 0, 2 or 4.
   The deflate side proves that a run ends in [dfinal] (RTDIface.v), the inflate side that inflate / uncompress
   give D back from such O (RTIIface.v). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Zlib.proof.deflate.DState.
Require Zlib.proof.rfc1951.Format.
Require Zlib.proof.adler32.Model Zlib.proof.crc32.Model.
Import ListNotations.
Local Open Scope Z_scope.

Module F := Zlib.proof.rfc1951.Format.
Module DS := Zlib.proof.deflate.DState.

(* the gzip headers the harness gives to deflateSetHeader (= LawFacts.hdr_ok of the deflate laws): text and
   hcrc 0/1, os a byte, time 32 bits, the extra field the whole object of extra_len <= 2^12 bytes, the name and
   the comment whole objects of at most 2^12 non-zero bytes followed by their zero byte *)
Definition rcstr_ok (o : option (list Z)) : Prop :=
  forall l, o = Some l -> exists l0, l = l0 ++ [0] /\ Zlength l0 <= 4096 /\ Forall (fun b => 0 < b < 256) l0.
Definition rhdr_ok (h : DS.gzh) : Prop :=
  (DS.gz_text h = 0 \/ DS.gz_text h = 1) /\ (DS.gz_hcrc h = 0 \/ DS.gz_hcrc h = 1) /\
  0 <= DS.gz_os h < 256 /\ 0 <= DS.gz_time h <= 4294967295 /\ 0 <= DS.gz_extra_len h <= 4096 /\
  (forall x, DS.gz_extra h = Some x -> Zlength x = DS.gz_extra_len h /\ Forall (fun b => 0 <= b < 256) x) /\
  rcstr_ok (DS.gz_name h) /\ rcstr_ok (DS.gz_comment h).

(* Format's gzip header of deflate's: the fields of deflateSetHeader's header (the name and the comment without
   their zero byte), or zlib's default header; [xfl] the XFL byte deflate wrote *)
Definition fhdr_of (gh : option DS.gzh) (xfl : Z) : F.gzhdr :=
  match gh with
  | None => F.GzHdr false 0 xfl 3 None None None false
  | Some h =>
      F.GzHdr (negb (DS.gz_text h =? 0)) (DS.gz_time h) xfl (Z.land (DS.gz_os h) 255)
        (option_map (fun x => sublist 0 (DS.gz_extra_len h) x) (DS.gz_extra h))
        (option_map (@removelast Z) (DS.gz_name h)) (option_map (@removelast Z) (DS.gz_comment h))
        (negb (DS.gz_hcrc h =? 0))
  end.

(* the zlib header's CMF for window bits wb, and the FLG bytes deflate may write *)
Definition zcmf (wb : Z) : Z := (wb - 8) * 16 + 8.
Definition zflg_ok (wb : Z) (fdict : bool) (flg : Z) : Prop :=
  0 <= flg < 256 /\ (zcmf wb * 256 + flg) mod 31 = 0 /\ Z.testbit flg 5 = fdict.

Definition dfinal (dict : list Z) (wrap wb : Z) (gh : option DS.gzh) (D O : list Z) : Prop :=
  9 <= wb <= 15 /\
  exists bs, F.wf (2 ^ wb) dict bs /\ F.data dict bs = D /\
  match wrap with
  | 0 => O = F.deflate_bytes bs
  | 1 => gh = None /\
         exists flg, zflg_ok wb (negb (match dict with [] => true | _ => false end)) flg /\
         O = [zcmf wb; flg] ++
             match dict with [] => [] | _ => F.be_bytes (Zlib.proof.adler32.Model.ref_adler32 1 dict) 4 end ++
             F.deflate_bytes bs ++ F.be_bytes (Zlib.proof.adler32.Model.ref_adler32 1 D) 4
  | _ => dict = [] /\
         exists xfl, (xfl = 0 \/ xfl = 2 \/ xfl = 4) /\ O = F.stream_bytes (F.WGzip (fhdr_of gh xfl)) [] bs
  end.
