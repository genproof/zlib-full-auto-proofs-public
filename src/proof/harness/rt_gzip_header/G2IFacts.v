(* Law rt_gzip_header on the round-2 harness: THE interface between the inflate part of main (VST) and the model
   theory of inflate (pure Coq over Spec5.inflate_rel, i.e. Model2.run2 from Spec5.m_init).

   After the deflate loop ended with Z_STREAM_END, the bytes O are the gzip stream of no data with the header gh
   (RTFinal.dfinal [] 2 wbd (Some gh) [] O, G2DFacts.gd_call; RF is RTIIface's name of RTFinal).  The harness then calls inflateInit2(16 + wb) on a
   new stream, inflateGetHeader with a gz_header h whose three buffers have exactly the fields' sizes (extra:
   extra_len bytes, name and comment: their length + 1, whether the field is present in gh or not), and then
   inflate(Z_FINISH) in a loop:
     offer(&d, compressed, 0, room, 1);
     do { d.avail_in = clip(compressed_len - read); code = inflate(&d, Z_FINISH); if (code == Z_MEM_ERROR) return 0; }
     while (code == Z_BUF_ERROR && d.next_in != compressed + compressed_len);
   and checks that inflate's copy of the header holds every field of gh ([g2_hdr_out]).  The header (a name and a
   comment of up to 2^32 - 2 bytes) may span several calls.

   The theory chooses an invariant [P wb gh O h0 pos z L] of the loop head (pos: the bytes of O consumed, z / L: the
   application's fields and the live part of the stream, h0: the header given to inflateGetHeader), existential so
   that main and the theory are independent.  Each call is offered the object holding O from position pos on
   (clip(|O| - pos) bytes) and the same output space (one byte, never written: there is no data). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Export Zlib.proof.roundtrip.RTH9Spec.
Require Export Zlib.proof.roundtrip.RTIIface.
Require Export Zlib.proof.harness.rt_gzip_header.G2Defs.
Import ListNotations.
Local Open Scope Z_scope.

(* the gz_header given to inflateGetHeader: the three buffers present, of the sizes the harness allocates *)
Definition g2_bufs (gh : DS.gzh) (h : hstate) : Prop :=
  h_xp h = true /\ h_extra_max h = DS.gz_extra_len gh /\ Zlength (h_xbuf h) = h_extra_max h /\
  h_np h = true /\ 1 <= h_name_max h <= 4294967295 /\ Zlength (h_nbuf h) = h_name_max h /\
  (forall l, DS.gz_name gh = Some l -> h_name_max h = Zlength l) /\
  h_cp h = true /\ 1 <= h_comm_max h <= 4294967295 /\ Zlength (h_cbuf h) = h_comm_max h /\
  (forall l, DS.gz_comment gh = Some l -> h_comm_max h = Zlength l).

(* inflate's header (state s, header h) when the loop ends: still attached, past the header modes, every field of gh
   reported *)
Definition g2_hdr_out (gh : DS.gzh) (h0 : hstate) (s : istate) (h : hstate) : Prop :=
  i_head s = true /\ hdr_mode (i_mode s) = false /\ h_done h = 1 /\
  h_text h = (if DS.gz_text gh =? 0 then 0 else 1) /\ h_hcrc h = (if DS.gz_hcrc gh =? 0 then 0 else 1) /\
  h_os h = Z.land (DS.gz_os gh) 255 /\ h_time h = DS.gz_time gh /\
  h_extra_max h = h_extra_max h0 /\ h_name_max h = h_name_max h0 /\ h_comm_max h = h_comm_max h0 /\
  match DS.gz_extra gh with
  | None => h_xp h = false
  | Some x => h_xp h = true /\ fextra s = true /\ h_extra_len h = Zlength x /\ cxa h = Zlength x /\
              sublist 0 (Zlength x) (h_xbuf h) = x
  end /\
  match DS.gz_name gh with
  | None => h_np h = false
  | Some l => h_np h = true /\ cna h = Zlength l /\ sublist 0 (Zlength l) (h_nbuf h) = l
  end /\
  match DS.gz_comment gh with
  | None => h_cp h = false
  | Some l => h_cp h = true /\ cca h = Zlength l /\ sublist 0 (Zlength l) (h_cbuf h) = l
  end.

(* the stream fields the harness sets before a call: next_in, avail_in, next_out, avail_out *)
Definition offer_z (z: zfields) (ni: val) (ai: Z) (no: val) (ao: Z) : zfields :=
  ZF ni ai (zf_tin z) no ao (zf_tout z) (zf_msg z) (zf_dt z) (zf_adler z) (zf_res z).

(* a call of the loop: offered inp = O[pos .. pos + clip(|O| - pos)) (an object) and aout bytes of output space
   (an object), from a live stream with the fields z *)
Definition g2_call_pre (O: list Z) (pos: Z) (z: zfields) (L: live) (strmp: val) (ib: inbuf) (inp: list Z)
    (o: outbuf) (aout: Z) : Prop :=
  live_ok8 L /\ swfW (l_s L) /\ zf_ok z /\ strmp <> nullval /\ ib <> InNull /\ in_ok ib inp /\ out_ok o aout /\
  aout <= umax /\ Zlength inp = clipz (Zlength O - pos) /\ inp = sublist pos (pos + Zlength inp) O.

Definition g2_inv : Type := Z -> DS.gzh -> list Z -> hstate -> Z -> zfields -> live -> Prop.

Record g2_ifacts (P : g2_inv) : Prop := {
  (** what P says of the position *)
  gi_range : forall wb gh O h0 pos z L, P wb gh O h0 pos z L -> 0 <= pos <= Zlength O;
  (** after inflateInit2(16 + wb) (which sets total_out to 0) and inflateGetHeader(h) *)
  gi_init : forall wbd wb gh O sp z h headp hsh xb nb cb,
    RF.dfinal [] 2 wbd (Some gh) [] O -> g2_hdr_ok gh -> 9 <= wb <= 15 -> g2_bufs gh h ->
    Zlength O <= max_u64 ->
    live_ok8 (head_live (init_live sp (16 + wb)) h headp hsh xb nb cb) -> zf_ok z -> zf_tout z = 0 ->
    P wb gh O h 0 z (head_live (init_live sp (16 + wb)) h headp hsh xb nb cb);
  (** one call of the loop (inflate(Z_FINISH)) that did not run out of memory: the stream stays live, the input
      pointer moves on by the bytes consumed, nothing is written; Z_BUF_ERROR with input left keeps P; when the
      loop ends (another code, or all of O read) the header is complete *)
  gi_call : forall wb gh O h0 pos z L strmp ib inp o aout r z' st' ow,
    P wb gh O h0 pos z L -> g2_call_pre O pos z L strmp ib inp o aout ->
    inflate_rel Z_FINISH strmp (offer_z z (in_ptr ib 0) (Zlength inp) (out_ptr o 0) aout) (Some L) ib inp (Some o)
      r z' st' ow ->
    r <> Z_MEM_ERROR ->
    exists L', st' = Some L' /\ 0 <= zf_ai z' <= Zlength inp /\ zf_ni z' = in_ptr ib (Zlength inp - zf_ai z') /\
      zf_ao z' = aout /\ zf_no z' = out_ptr o 0 /\ ow = [] /\
      (r = Z_BUF_ERROR -> pos + (Zlength inp - zf_ai z') < Zlength O ->
         P wb gh O h0 (pos + (Zlength inp - zf_ai z')) z' L') /\
      (r <> Z_BUF_ERROR \/ pos + (Zlength inp - zf_ai z') = Zlength O ->
         g2_hdr_out gh h0 (l_s L') (l_h L'))
}.

Definition g2_ifacts_stmt : Prop := exists P, g2_ifacts P.
