(* Law inflate_header: THE interface between the main of harness/inflate_header.c (IHMain*.v, VST) and the pure
   theory over the model (IHTheory*.v).  Pure Coq over Spec5's relations (inflate_rel over Model2.run2,
   init_live, inflateGetHeader_spec's live part).

   The harness draws the header fields (the ghost `ihg`: FLG, MTIME, XFL, OS, the extra field xf, the name nf
   and the comment cf without their zero bytes, delta) and builds the gzip member `ih_src g`.  Its loop keeps,
   besides the stream (z, L), pos (the input bytes consumed so far); w is the windowBits given to
   inflateInit2_ (accepted, and >= 16 once inflateGetHeader returned Z_OK); h0 is the gz_header main gave
   to inflateGetHeader (its maxima, its buffers' contents, h_xp/h_np/h_cp = the buffer is not Z_NULL).
   The theory chooses an invariant I g w h0 pos z L (existential: `ih_theory_stmt`) and proves the facts
   below; main is proved for ANY I with ih_facts I (`ih_main_stmt`, IHMainStmt.v). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Export Zlib.proof.inflate_api.Spec5.
Require Import Zlib.proof.adler32.Bytes.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* The member the harness builds                                                                  *)

Record ihg := IHG {
  g_flg : Z; g_mtime : Z; g_xfl : Z; g_os : Z;
  g_xf : list Z;      (* the extra field, XLEN = |xf| bytes *)
  g_nf : list Z;      (* the file name, without its zero byte *)
  g_cf : list Z;      (* the comment, without its zero byte *)
  g_delta : Z }.

Definition ih_ok (g: ihg) : Prop :=
  0 <= g_flg g <= 255 /\ 0 <= g_mtime g < 2 ^ 32 /\ 0 <= g_xfl g <= 255 /\ 0 <= g_os g <= 255 /\
  Zlength (g_xf g) <= 65535 /\ is_bytes (g_xf g) /\
  Zlength (g_nf g) <= 2 ^ 16 /\ Forall (fun b => 0 < b <= 255) (g_nf g) /\
  Zlength (g_cf g) <= 2 ^ 16 /\ Forall (fun b => 0 < b <= 255) (g_cf g) /\
  0 <= g_delta g < 2 ^ 32.

(* a flag bit of FLG *)
Definition fl (g: ihg) (bit: Z) : bool := negb (Z.land (g_flg g) bit =? 0).

(* the header: 1f 8b 08 FLG MTIME(4, little-endian) XFL OS [XLEN(2) extra] [name 0] [comment 0] *)
Definition ih_hdr (g: ihg) : list Z :=
  [31; 139; 8; g_flg g; g_mtime g mod 256; (g_mtime g / 256) mod 256; (g_mtime g / 65536) mod 256;
   (g_mtime g / 16777216) mod 256; g_xfl g; g_os g] ++
  (if fl g 4 then [Zlength (g_xf g) mod 256; Zlength (g_xf g) / 256] ++ g_xf g else []) ++
  (if fl g 8 then g_nf g ++ [0] else []) ++
  (if fl g 16 then g_cf g ++ [0] else []).

(* the stored header CRC: (the low 16 bits of the CRC-32 of the header) ^ delta, low 16 bits *)
Definition ih_stored (g: ihg) : Z :=
  Z.land (Z.lxor (Z.land (ref_crc32 0 (ih_hdr g)) 65535) (g_delta g)) 65535.

(* the member: header, [header CRC], an empty final stored block, CRC-32 and ISIZE of the empty data *)
Definition ih_src (g: ihg) : list Z :=
  ih_hdr g ++ (if fl g 2 then [ih_stored g mod 256; ih_stored g / 256] else []) ++
  [1; 0; 0; 255; 255] ++ Zrepeat 0 8.

Definition ih_reserved (g: ihg) : bool := negb (Z.land (g_flg g) 224 =? 0).
Definition ih_badcrc (g: ihg) : bool := fl g 2 && negb (Z.land (g_delta g) 65535 =? 0).

(* ---------------------------------------------------------------------------------------------- *)
(* The gz_header once done                                                                        *)

(* a header buffer b0 (|b0| = its maximum) after the field f was stored: the first min(|f|, |b0|) bytes
   of f, then the rest of b0 *)
Definition fbuf (b0 f: list Z) : list Z :=
  let k := Z.min (Zlength f) (Zlength b0) in sublist 0 k f ++ sublist k (Zlength b0) b0.

Definition ih_done_ok (g: ihg) (h0 h: hstate) : Prop :=
  h_done h = 1 /\ h_text h = Z.land (g_flg g) 1 /\ h_time h = g_mtime g /\ h_xflags h = g_xfl g /\
  h_os h = g_os g /\ h_hcrc h = Z.land (Z.shiftr (g_flg g) 1) 1 /\
  (if fl g 4 then h_extra_len h = Zlength (g_xf g) /\ h_xp h = h_xp h0 /\
                  (h_xp h0 = true -> h_xbuf h = fbuf (h_xbuf h0) (g_xf g))
   else h_xp h = false) /\
  (if fl g 8 then h_np h = h_np h0 /\ (h_np h0 = true -> h_nbuf h = fbuf (h_nbuf h0) (g_nf g ++ [0]))
   else h_np h = false) /\
  (if fl g 16 then h_cp h = h_cp h0 /\ (h_cp h0 = true -> h_cbuf h = fbuf (h_cbuf h0) (g_cf g ++ [0]))
   else h_cp h = false).

(* ---------------------------------------------------------------------------------------------- *)
(* The facts                                                                                      *)

(* the stream fields the harness sets before an inflate() call: next_in, avail_in, next_out, avail_out *)
Definition ih_zcall (z: zfields) (ni: val) (ai: Z) (no: val) (ao: Z) : zfields :=
  ZF ni ai (zf_tin z) no ao (zf_tout z) (zf_msg z) (zf_dt z) (zf_adler z) (zf_res z).

(* the live part after inflateGetHeader(&s, &h) on the stream inflateInit2_ made *)
Definition ih_L0 (sp: val) (w: Z) (h0: hstate) (headp: val) (hsh: share) (xb nb cb: val) : live :=
  let L := init_live sp w in
  set_l_head (set_l_s L (set_i_head (l_s L) true)) (set_h_done h0 0) headp hsh xb nb cb.

(* what the harness checks after an inflate() call (offered src[pos .. pos + ain)), and the invariant
   afterwards (unless Z_MEM_ERROR, which ends the run) *)
Definition ih_post (I: ihg -> Z -> hstate -> Z -> zfields -> live -> Prop)
    (g: ihg) (w: Z) (h0: hstate) (pos ain r: Z) (z': zfields) (L': live) : Prop :=
  let used := ain - zf_ai z' in
  (r = Z_OK \/ r = Z_BUF_ERROR \/ r = Z_STREAM_END \/ r = Z_DATA_ERROR \/ r = Z_MEM_ERROR) /\
  0 <= zf_ai z' <= ain /\
  (orb (ih_reserved g) (ih_badcrc g) = true -> r <> Z_STREAM_END) /\
  (orb (ih_reserved g) (ih_badcrc g) = false -> r <> Z_DATA_ERROR) /\
  (ih_reserved g = true -> r = Z_DATA_ERROR -> h_done (l_h L') = 0) /\
  (r <> Z_MEM_ERROR -> h_done (l_h L') <> 0 -> ih_done_ok g h0 (l_h L')) /\
  (r = Z_STREAM_END -> h_done (l_h L') = 1 /\ pos + used = Zlength (ih_src g) /\ zf_tout z' = 0) /\
  (r <> Z_MEM_ERROR -> I g w h0 (pos + used) z' L').

Record ih_facts (I: ihg -> Z -> hstate -> Z -> zfields -> live -> Prop) : Prop := {
  (* inflateGetHeader returns Z_STREAM_ERROR exactly for windowBits < 16 *)
  ihf_wrap : forall w sp, wbits_ok w = true ->
    (Z.land (i_wrap (l_s (init_live sp w))) 2 =? 0) = (w <? 16);
  (* after inflateInit2_ (Z_OK) and inflateGetHeader (Z_OK): z the stream fields then *)
  ihf_init : forall g w h0 z sp headp hsh xb nb cb,
    ih_ok g -> wbits_ok w = true -> 16 <= w -> Int.min_signed <= w <= Int.max_signed ->
    isptr sp -> zf_ok z -> zf_msg z = None -> zf_tout z = 0 ->
    hwf h0 -> writable_share hsh ->
    (h_xp h0 = true -> xb <> nullval) -> (h_np h0 = true -> nb <> nullval) -> (h_cp h0 = true -> cb <> nullval) ->
    I g w h0 0 z (ih_L0 sp w h0 headp hsh xb nb cb);
  (* the invariant's consequences main needs: inflate holds the header, whose maxima do not change *)
  ihf_live : forall g w h0 pos z L,
    I g w h0 pos z L ->
    i_head (l_s L) = true /\ h_extra_max (l_h L) = h_extra_max h0 /\ h_name_max (l_h L) = h_name_max h0 /\
    h_comm_max (l_h L) = h_comm_max h0;
  (* inflate(&s, flush) offered src[pos .. pos + ain) (a real object) and aout bytes of space *)
  ihf_inflate : forall g w h0 pos z L strmp flush ib inp o ain aout r z' st' ow,
    ih_ok g -> I g w h0 pos z L -> live_ok L -> zf_ok z -> strmp <> nullval ->
    0 <= pos -> 0 <= ain -> pos + ain <= Zlength (ih_src g) -> 0 <= aout <= 2 ^ 20 ->
    Int.min_signed <= flush <= Int.max_signed ->
    ib <> InNull -> inp = sublist pos (pos + ain) (ih_src g) ->
    inflate_rel flush strmp (ih_zcall z (in_ptr ib 0) ain (out_ptr o 0) aout) (Some L) ib inp (Some o)
      r z' st' ow ->
    exists L', st' = Some L' /\ ih_post I g w h0 pos ain r z' L'
}.

Definition ih_theory_stmt : Prop := exists I, ih_facts I.

(* inflate() keeps the pointers of the live part (main's frame) *)
Lemma ih_rel_live: forall flush strmp z L ib inp ob r z' st' ow,
  inflate_rel flush strmp z (Some L) ib inp ob r z' st' ow ->
  exists L', st' = Some L' /\ l_sp L' = l_sp L /\ l_headp L' = l_headp L /\ l_hsh L' = l_hsh L /\
             l_xb L' = l_xb L /\ l_nb L' = l_nb L /\ l_cb L' = l_cb L.
Proof.
  intros flush strmp z L ib inp ob r z' st' ow H.
  destruct H as [(_ & _ & _ & E & _) | (_ & L1 & o & res & winp & E1 & _ & _ & _ & _ & _ & _ & _ & E)].
  - subst st'. exists L; repeat split; reflexivity.
  - inversion E1; subst L1. subst st'. eexists; repeat split; reflexivity.
Qed.
