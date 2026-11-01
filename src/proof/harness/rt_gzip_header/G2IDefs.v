(* Law rt_gzip_header on the round-2 harness, inflate side: the definitions of the gzip header's passes when the
   header is split over calls of any size.

   The stream O starts with the gzip header deflate wrote for deflateSetHeader's gh (RTFinal.fhdr_of (Some gh) xfl).
   As in law inflate_header's theory (harness/inflate_header/IHTDefs.v), the header is described by a ghost
   `ihg` (FLG, MTIME, XFL, OS, the extra field, the name and the comment without their zero bytes; here the header
   CRC is always right: g_delta = 0), and the state of inflate() at a loop head or between calls by its position P
   (bytes of O consumed) alone: [J2], one constructor per header mode, then TYPE once the header is complete.  The
   differences from IHTDefs: the input is any list [src] whose first bytes are the header ([lay2]; what follows is
   deflate's data, not read here); names and comments of up to 2^32 - 2 bytes and gz_header buffers of any uInt
   size ([g2h_ok], RTH8Spec.hwf8); no BAD state (no reserved FLG bit, the header CRC matches); the machine also
   keeps the ranges of the state (Inv.swf) and the call's fixed fields ([Km2]'s km2_swf, km2_fr), which the
   decode theory needs once the header is passed in the middle of a call.  IHTDefs' positions (ih_xs .. ih_nh),
   gz_header predicates (hx0, hT, hxk, ...), ih_done_ok and kit statements (ih_nb_stmt, ...) are reused. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Export Zlib.proof.harness.rt_gzip_header.G2IFacts.
Require Export Zlib.proof.harness.inflate_header.IHTDefs.
Require Zlib.proof.rfc1951.Format.
Require Zlib.proof.roundtrip.RTIGW.
Module F := Zlib.proof.rfc1951.Format.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* The header deflate writes                                                                       *)

(* Format's header of deflateSetHeader's gh, with deflate's XFL *)
Definition g2_H (gh: DS.gzh) (xfl: Z) : F.gzhdr := RF.fhdr_of (Some gh) xfl.

(* its ghost (IHFacts.ihg): the header bytes are ih_hdr, then the 2 header CRC bytes with FHCRC *)
Definition g2_g (gh: DS.gzh) (xfl: Z) : ihg :=
  let H := g2_H gh xfl in
  IHG (F.gz_flg H) (F.gz_mtime H) (F.gz_xfl H) (F.gz_os H)
      (match F.gz_extra H with Some x => x | None => [] end)
      (match F.gz_name H with Some n => n | None => [] end)
      (match F.gz_comment H with Some c => c | None => [] end) 0.

(* the ranges of a ghost: IHFacts.ih_ok with names and comments of up to 2^32 - 2 bytes, no reserved FLG bit,
   the right header CRC *)
Definition g2h_ok (g: ihg) : Prop :=
  0 <= g_flg g <= 255 /\ ih_reserved g = false /\ 0 <= g_mtime g < 2 ^ 32 /\ 0 <= g_xfl g <= 255 /\
  0 <= g_os g <= 255 /\ Zlength (g_xf g) <= 65535 /\ is_bytes (g_xf g) /\
  Zlength (g_nf g) <= 4294967294 /\ Forall (fun b => 0 < b <= 255) (g_nf g) /\
  Zlength (g_cf g) <= 4294967294 /\ Forall (fun b => 0 < b <= 255) (g_cf g) /\
  g_delta g = 0.

(* the layout of the input: the header (IHTDefs.ih_lay, for any src that starts with it) *)
Record lay2 (g: ihg) (src: list Z) : Prop := {
  l2_bytes : is_bytes src;
  l2_len : ih_nh g <= Zlength src;
  l2_ord : ih_xs g <= ih_ne g /\ ih_ne g <= ih_nn g /\ ih_nn g <= ih_nc g /\ ih_nc g <= ih_nh g;
  l2_hdr : sublist 0 (ih_nc g) src = ih_hdr g;
  l2_id : ih_le (sublist 0 2 src) = 35615 /\ hbytes2 35615 = sublist 0 2 src;
  l2_fl : ih_le (sublist 2 4 src) = 8 + 256 * g_flg g /\ hbytes2 (8 + 256 * g_flg g) = sublist 2 4 src;
  l2_mt : ih_le (sublist 4 8 src) = g_mtime g /\ hbytes4 (g_mtime g) = sublist 4 8 src;
  l2_os : ih_le (sublist 8 10 src) = g_xfl g + 256 * g_os g /\
          hbytes2 (g_xfl g + 256 * g_os g) = sublist 8 10 src;
  l2_xl : fl g 4 = true -> ih_le (sublist 10 12 src) = Zlength (g_xf g) /\
          hbytes2 (Zlength (g_xf g)) = sublist 10 12 src;
  l2_xf : fl g 4 = true -> sublist 12 (ih_ne g) src = g_xf g;
  l2_nf : fl g 8 = true -> sublist (ih_ne g) (ih_nn g) src = g_nf g ++ [0];
  l2_cf : fl g 16 = true -> sublist (ih_nn g) (ih_nc g) src = g_cf g ++ [0];
  l2_hc : fl g 2 = true ->
          (ih_le (sublist (ih_nc g) (ih_nc g + 2) src) =?
           Z.land (ref_crc32 0 (sublist 0 (ih_nc g) src)) 65535) = negb (ih_badcrc g) }.

(* the bytes offered are src[pos .. pos + |inp|) *)
Definition ctx2 (src: list Z) (pos: Z) (inp: list Z) : Prop :=
  0 <= pos /\ pos + Zlength inp <= Zlength src /\ inp = sublist pos (pos + Zlength inp) src.

(* ---------------------------------------------------------------------------------------------- *)
(* The state                                                                                       *)

(* the bit buffer holds src[a .. P) *)
Definition bb2 (src: list Z) (a P hold bits: Z) : Prop :=
  bits = 8 * (P - a) /\ hold = ih_le (sublist a P src).

(* the header CRC so far (only computed with FHCRC) *)
Definition ck2 (g: ihg) (src: list Z) (s: istate) (k: Z) : Prop :=
  fl g 2 = true -> i_check s = ref_crc32 0 (sublist 0 k src).

(* in every mode: wrap 6 (inflateInit2(16 + wb)), the gz_header attached, no window, nothing produced, the
   window bits of inflateInit2 (9 .. 15: HEAD's gzip branch keeps them), the header's maxima *)
Record Jc2 (wb: Z) (h0: hstate) (s: istate) (h: hstate) : Prop := {
  jc2_wrap : i_wrap s = 6;
  jc2_head : i_head s = true;
  jc2_wsize : i_wsize s = 0;
  jc2_total : i_total s = 0;
  jc2_wbits : i_wbits s = wb;
  jc2_xmax : h_extra_max h = h_extra_max h0;
  jc2_nmax : h_name_max h = h_name_max h0;
  jc2_cmax : h_comm_max h = h_comm_max h0;
  jc2_wb : 9 <= wb <= 15 }.

(* the state at absolute position P (IHTDefs.J's header constructors over src; TYPE once the header is
   complete) *)
Inductive J2 (g: ihg) (src: list Z) (h0: hstate) (P: Z) (s: istate) (h: hstate) (hold bits: Z) : Prop :=
| J2_HEAD : i_mode s = HEAD -> 0 <= P <= 1 -> bb2 src 0 P hold bits ->
    h_done h = 0 -> hx0 h0 h -> hn0 h0 h -> hc0 h0 h -> i_last s = 0 -> J2 g src h0 P s h hold bits
| J2_FLAGS : i_mode s = FLAGS -> 2 <= P <= 3 -> bb2 src 2 P hold bits ->
    i_check s = ref_crc32 0 (sublist 0 2 src) ->
    h_done h = 0 -> hx0 h0 h -> hn0 h0 h -> hc0 h0 h -> i_last s = 0 -> J2 g src h0 P s h hold bits
| J2_TIME : i_mode s = TIME -> 4 <= P <= 7 -> bb2 src 4 P hold bits ->
    fg g s -> ih_reserved g = false -> ck2 g src s 4 ->
    h_done h = 0 -> hT g h -> hx0 h0 h -> hn0 h0 h -> hc0 h0 h -> i_last s = 0 -> J2 g src h0 P s h hold bits
| J2_OS : i_mode s = OS -> 8 <= P <= 9 -> bb2 src 8 P hold bits ->
    fg g s -> ih_reserved g = false -> ck2 g src s 8 ->
    h_done h = 0 -> hT g h -> hM g h -> hx0 h0 h -> hn0 h0 h -> hc0 h0 h -> i_last s = 0 ->
    J2 g src h0 P s h hold bits
| J2_EXLEN : i_mode s = EXLEN -> 10 <= P <= 10 + (if fl g 4 then 1 else 0) -> bb2 src 10 P hold bits ->
    fg g s -> ih_reserved g = false -> ck2 g src s 10 ->
    h_done h = 0 -> hT g h -> hM g h -> hO g h -> hx0 h0 h -> hn0 h0 h -> hc0 h0 h -> i_last s = 0 ->
    J2 g src h0 P s h hold bits
| J2_EXTRA : i_mode s = EXTRA -> ih_xs g <= P <= ih_ne g -> hold = 0 -> bits = 0 ->
    (fl g 4 = true -> i_length s = ih_ne g - P) ->
    fg g s -> ih_reserved g = false -> ck2 g src s P ->
    h_done h = 0 -> hT g h -> hM g h -> hO g h -> hxk g h0 (P - ih_xs g) h -> hn0 h0 h -> hc0 h0 h ->
    i_last s = 0 -> J2 g src h0 P s h hold bits
| J2_NAME : i_mode s = NAME -> ih_ne g <= P -> (P < ih_nn g \/ P = ih_ne g) -> hold = 0 -> bits = 0 ->
    i_length s = (if h_np h0 then Z.min (P - ih_ne g) (h_name_max h0) else 0) ->
    fg g s -> ih_reserved g = false -> ck2 g src s P ->
    h_done h = 0 -> hT g h -> hM g h -> hO g h -> hxf g h0 h -> hnk g h0 (P - ih_ne g) h -> hc0 h0 h ->
    i_last s = 0 -> J2 g src h0 P s h hold bits
| J2_COMMENT : i_mode s = COMMENT -> ih_nn g <= P -> (P < ih_nc g \/ P = ih_nn g) -> hold = 0 -> bits = 0 ->
    i_length s = (if h_cp h0 then Z.min (P - ih_nn g) (h_comm_max h0) else 0) ->
    fg g s -> ih_reserved g = false -> ck2 g src s P ->
    h_done h = 0 -> hT g h -> hM g h -> hO g h -> hxf g h0 h -> hnf g h0 h -> hck g h0 (P - ih_nn g) h ->
    i_last s = 0 -> J2 g src h0 P s h hold bits
| J2_HCRC : i_mode s = HCRC -> ih_nc g <= P <= ih_nc g + (if fl g 2 then 1 else 0) ->
    bb2 src (ih_nc g) P hold bits -> fg g s -> ih_reserved g = false -> ck2 g src s (ih_nc g) ->
    h_done h = 0 -> hT g h -> hM g h -> hO g h -> hxf g h0 h -> hnf g h0 h -> hcf g h0 h ->
    i_last s = 0 -> J2 g src h0 P s h hold bits
| J2_TYPE : i_mode s = Zlib.proof.inflate.Model.TYPE -> P = ih_nh g -> hold = 0 -> bits = 0 ->
    i_check s = 0 -> fg g s -> i_last s = 0 -> ih_done_ok g h0 h ->
    J2 g src h0 P s h hold bits.

(* the machine at a loop head (or the exit) of a call offered inp at pos, in a header mode or at TYPE; aout
   and tin: the call's avail_out and total_in *)
Record Km2 (g: ihg) (src: list Z) (h0: hstate) (wb pos: Z) (inp: list Z) (aout tin: Z) (m: mst) : Prop := {
  km2_inp : m_inp m = inp;
  km2_nx : 0 <= m_nx m <= Zlength inp;
  km2_ow : m_ow m = [];
  km2_out : m_out m = m_aout m;
  km2_tout : m_tout m = 0;
  km2_ret : m_ret m = Z_OK;
  (* a pass leaves the loop only out of input, inside the header *)
  km2_lv : m_leave m = 0 \/
           (m_leave m = 1 /\ m_nx m = Zlength inp /\ pos + m_nx m < ih_nh g /\
            m_mode m <> Zlib.proof.inflate.Model.TYPE);
  km2_jc : Jc2 wb h0 (m_s m) (m_h m);
  km2_j : J2 g src h0 (pos + m_nx m) (m_s m) (m_h m) (m_hold m) (m_bits m);
  km2_swf : swf (m_s m);
  km2_fr : m_aout m = aout /\ m_in m = Zlength inp /\ m_tin m = tin /\ m_snx m = 0 /\ m_sow m = 0 /\
           lrange (m_adler m) }.

Definition ok_out2 (g: ihg) (src: list Z) (h0: hstate) (wb pos: Z) (inp: list Z) (aout tin: Z) (o: iout)
    : Prop :=
  match o with IBrk m' => Km2 g src h0 wb pos inp aout tin m' | IRet _ _ => False end.

(* from a loop head in mode X, the case c keeps Km2 *)
Definition case_ok2 (X: Z) (c: mst -> iout) : Prop :=
  forall g src h0 wb pos inp aout tin m,
    g2h_ok g -> hwf8 h0 -> lay2 g src -> ctx2 src pos inp ->
    Km2 g src h0 wb pos inp aout tin m -> m_leave m = 0 -> m_mode m = X ->
    ok_out2 g src h0 wb pos inp aout tin (c m).

(* the kit: IHTDefs.ih_kit without the layout (lay2 is a hypothesis of the cases); proved in IHTKit*.v *)
Record g2_kit : Prop := {
  k2_bits : ih_bits_stmt;
  k2_nb : ih_nb_stmt;
  k2_zstr : ih_zstr_stmt;
  k2_put : ih_put_stmt;
  k2_crc : ih_crc_stmt;
  k2_in : ih_in_stmt }.

(* ---------------------------------------------------------------------------------------------- *)
(* The cases (each falls through into the next one: its statement assumes the next)               *)

Definition g2c_head_stmt : Prop := g2_kit -> case_ok2 HEAD c_HEAD2.
Definition g2c_flags_stmt : Prop := g2_kit -> case_ok2 TIME c_TIME2 -> case_ok2 FLAGS c_FLAGS2.
Definition g2c_time_stmt : Prop := g2_kit -> case_ok2 OS c_OS2 -> case_ok2 TIME c_TIME2.
Definition g2c_os_stmt : Prop := g2_kit -> case_ok2 EXLEN c_EXLEN2 -> case_ok2 OS c_OS2.
Definition g2c_exlen_stmt : Prop := g2_kit -> case_ok2 EXTRA c_EXTRA2 -> case_ok2 EXLEN c_EXLEN2.
Definition g2c_extra_stmt : Prop := g2_kit -> case_ok2 NAME c_NAME2 -> case_ok2 EXTRA c_EXTRA2.
Definition g2c_name_stmt : Prop := g2_kit -> case_ok2 COMMENT c_COMMENT2 -> case_ok2 NAME c_NAME2.
Definition g2c_comment_stmt : Prop := g2_kit -> case_ok2 HCRC c_HCRC -> case_ok2 COMMENT c_COMMENT2.
Definition g2c_hcrc_stmt : Prop := g2_kit -> case_ok2 HCRC c_HCRC.

(* all the header cases *)
Definition g2_cases_stmt : Prop :=
  case_ok2 HEAD c_HEAD2 /\ case_ok2 FLAGS c_FLAGS2 /\ case_ok2 TIME c_TIME2 /\ case_ok2 OS c_OS2 /\
  case_ok2 EXLEN c_EXLEN2 /\ case_ok2 EXTRA c_EXTRA2 /\ case_ok2 NAME c_NAME2 /\ case_ok2 COMMENT c_COMMENT2 /\
  case_ok2 HCRC c_HCRC.

(* ---------------------------------------------------------------------------------------------- *)
(* After the header: the decode theory                                                             *)

(* the decode context of O (RTIGDefs: any gzip header), entered with inflateInit2's windowBits 16 + wb *)
Definition g2_G (gh: DS.gzh) (xfl wb: Z) (bs: list F.block) (O: list Z) : Zlib.proof.rfc1951.DecodeDefs.dctx :=
  Zlib.proof.rfc1951.DecodeDefs.DCtx (F.WGzip (g2_H gh xfl)) wb [] bs (16 + wb) O.

(* a small gz_header (Inv.hwf) standing for the application's in the decode theory, which does not read it after
   the header (RTH8SimKit: the run is the same with any other header model there) *)
Definition g2_hc : hstate := HS 0 0 0 0 false 0 0 [] false 0 [] false 0 [] 0 0.
Definition g2_mc (m: mst) : mst := set_m_h m g2_hc.
