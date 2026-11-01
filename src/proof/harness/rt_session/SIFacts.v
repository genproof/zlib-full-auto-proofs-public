(* Law rt_session (harness/rt_session.c): what main's inflate part needs from the model of inflate.c.

   After deflate's Z_STREAM_END the compressed bytes [O] are a finished stream of the data [D] with the
   session's dictionary and gzip header (SDFacts.sd_deflate: RTFinal.dfinal dict wrap wb gh D O).  The harness
   copies O into an input object [src] = O followed by any bytes (at most PTRDIFF_MAX in all), calls
   inflateInit2 with deflate's windowBits (8 changed to 9: IFacts.rts_iw), then
   - with a gzip header: inflateGetHeader with a gz_header whose buffers have exactly the fields' sizes
     ([sc_h0], G2IFacts.g2_bufs);
   - with a dictionary and the raw wrapper: inflateSetDictionary of a copy of the dictionary;
   and inflate() until Z_STREAM_END, each call offered the next piece of [src] (at most 2^32 - 1 bytes, empty
   ones included), any output space below 2^32 (none included) and any flush (any int); when a call returns
   Z_NEED_DICT, inflateSetDictionary of the copy of the dictionary right after it.  inflate()'s shared
   specifications (SpecW.inflate_specW without a header, RTH9Spec.inflate_spec9 with one) give a call as
   Spec5.inflate_rel: the model run Model2.run2 from Spec5.m_init; inflateSetDictionary's
   (SpecW.inflateSetDictionary_specW) is Spec5.setdict_f.

   [scase]: the choices of the session the inflate side depends on: deflate's windowBits, the dictionary ([] when
   none was set: the harness's dictionaries have at least one byte), the gzip header (None when none was set)
   and the gz_header given to inflateGetHeader (its buffers; meaningful with a header).  [sc_ok c D O]: what the
   deflate side and the harness's draws give.

   [ses_ifacts K P PN]: an invariant [P c D O src pos out asked L tout] between the calls ([pos] the bytes of
   [src] consumed, [out] the bytes produced, [asked] the harness's flag "Z_NEED_DICT was returned", [L] the live
   part of the stream, [tout] the field total_out) and an invariant [PN] right after the call that returned
   Z_NEED_DICT, for the sessions [c] with [K c].  A call returns Z_OK, Z_BUF_ERROR, Z_NEED_DICT or Z_STREAM_END
   (or Z_MEM_ERROR, which ends the run), produces the next bytes of [D]; Z_NEED_DICT only with a dictionary and
   the zlib wrapper and only once; Z_STREAM_END only having consumed exactly [O], produced exactly [D], with the
   header reported (G2IFacts.g2_hdr_out); a call offered neither input nor output space does not return Z_OK and
   moves nothing.  [K] lets each kind of session (plain, raw dictionary, zlib dictionary, gzip header) be proved
   on its own; SITheory.ses_itheory_join joins them.  P and PN are abstract: SITheory.v chooses them. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.roundtrip.RTK7.
Require Export Zlib.proof.harness.rt_gzip_header.G2IFacts.
Require Export Zlib.proof.harness.rt_stream.IFacts.
Require Import Zlib.proof.harness.rt_session.SDFacts.
Import ListNotations.
Local Open Scope Z_scope.

Record scase := SC {
  sc_wbits : Z;              (* deflateInit2's windowBits *)
  sc_dict : list Z;          (* the dictionary set on both sides, [] without one *)
  sc_gh : option DS7.gzh;    (* the gzip header given to deflateSetHeader *)
  sc_h0 : hstate }.          (* the gz_header given to inflateGetHeader *)

Definition sc_wrap (c : scase) : Z := rwrap_of (sc_wbits c).

(* the session: parameters deflateInit2 accepted, the finished stream, a dictionary only with the raw or zlib
   wrapper, a header only with the gzip wrapper, the header's fields and inflateGetHeader's buffers as the
   harness draws them *)
Definition sc_ok (c : scase) (D O : list Z) : Prop :=
  (exists level mem strategy, rparams_ok level 8 (sc_wbits c) mem strategy = true) /\
  dfinal (sc_dict c) (sc_wrap c) (rwbe (sc_wbits c)) (sc_gh c) D O /\
  (sc_dict c <> [] -> sc_wrap c <> 2 /\ rbytes (sc_dict c) /\ Zlength (sc_dict c) <= 4294967295) /\
  (sc_gh c <> None -> sc_wrap c = 2) /\
  (forall gh, sc_gh c = Some gh -> rhdr_ok7 gh /\ g2_bufs gh (sc_h0 c)) /\
  Zlength D <= max_size.

(* the input object: the stream O followed by any bytes *)
Definition src_ok (O src : list Z) : Prop :=
  Zlength O <= Zlength src <= max_size /\ sublist 0 (Zlength O) src = O /\ rbytes src.

(* the kinds of session *)
Definition sk_plain (c : scase) : Prop := sc_dict c = [] /\ sc_gh c = None.
Definition sk_raw (c : scase) : Prop := sc_dict c <> [] /\ sc_wrap c = 0.
Definition sk_zdict (c : scase) : Prop := sc_dict c <> [] /\ sc_wrap c = 1.
Definition sk_gz (c : scase) : Prop := sc_gh c <> None.

(* the live state's validity as the two specifications of inflate() give it *)
Definition live_c (c : scase) (L : live) : Prop :=
  match sc_gh c with None => live_ok L | Some _ => live_ok8 L end.

Definition ses_iinv : Type :=
  scase -> list Z -> list Z -> list Z -> Z -> list Z -> bool -> live -> Z -> Prop.
Definition ses_ninv : Type :=
  scase -> list Z -> list Z -> list Z -> Z -> list Z -> live -> Z -> Prop.

Record ses_ifacts (K : scase -> Prop) (P : ses_iinv) (PN : ses_ninv) : Prop := {
  (** inflateInit2(strm, rts_iw wbits) (which sets total_out to 0): valid windowBits (Z_OK unless Z_MEM_ERROR),
      the state's wide invariant swfW, and, without a header and without a raw dictionary, the invariant *)
  si_init : forall c D O src sp,
    K c -> sc_ok c D O -> src_ok O src ->
    wbits_ok (rts_iw (sc_wbits c)) = true /\ swfW (l_s (init_live sp (rts_iw (sc_wbits c)))) /\
    (sc_gh c = None -> ~ sk_raw c -> P c D O src 0 [] false (init_live sp (rts_iw (sc_wbits c))) 0);
  (** with a header: inflateGetHeader(strm, &got) on that state returns Z_OK (the wrap has the gzip bit) and
      gives the invariant *)
  si_head : forall c D O src sp gh headp hsh xb nb cb,
    K c -> sc_ok c D O -> src_ok O src -> sc_gh c = Some gh ->
    let L := head_live (init_live sp (rts_iw (sc_wbits c))) (sc_h0 c) headp hsh xb nb cb in
    live_ok8 L ->
    Z.land (i_wrap (l_s (init_live sp (rts_iw (sc_wbits c))))) 2 <> 0 /\ swfW (l_s L) /\
    P c D O src 0 [] false L 0;
  (** with a raw dictionary: inflateSetDictionary(strm, dict, |dict|) on that state returns Z_OK (the
      invariant, swfW) or Z_MEM_ERROR (no window: the run ends) *)
  si_rawdict : forall c D O src sp z alloc_ok winp,
    K c -> sc_ok c D O -> src_ok O src -> sk_raw c -> zf_tout z = 0 ->
    let L := init_live sp (rts_iw (sc_wbits c)) in
    live_ok L ->
    let sd := setdict_f (sc_dict c) alloc_ok winp z L in
    (fst3 sd = Z_OK \/ fst3 sd = Z_MEM_ERROR) /\
    (fst3 sd = Z_OK -> snd3 sd = z /\ swfW (l_s (thd3 sd)) /\ P c D O src 0 [] false (thd3 sd) 0);
  (** the header is attached exactly when the session has one *)
  si_shape : forall c D O src pos out asked L tout,
    K c -> P c D O src pos out asked L tout ->
    i_head (l_s L) = match sc_gh c with Some _ => true | None => false end;
  (** one inflate() call offered the next [Zlength inp] <= 2^32 - 1 bytes of [src] and [zf_ao z] <= 2^32 - 1
      bytes of output space, any flush; [winp]: the window after the call (inflate_rel) *)
  si_call : forall c D O src pos out asked L z inp flush res winp,
    K c -> sc_ok c D O -> src_ok O src ->
    P c D O src pos out asked L (zf_tout z) -> live_c c L -> swfW (l_s L) -> zf_ok z ->
    zf_ao z <= 4294967295 -> Zlength inp <= 4294967295 ->
    0 <= pos -> pos + Zlength inp <= Zlength src -> inp = sublist pos (pos + Zlength inp) src ->
    Zlib.proof.inflate.Model2.run2 flush lenfix_list distfix_list (m_init z L inp) res ->
    let m := r_m res in
    let L' := Live (l_sp L) winp (m_s m) (m_h m) (l_headp L) (l_hsh L) (l_xb L) (l_nb L) (l_cb L) in
    r_ret res = Z_MEM_ERROR \/
    ((r_ret res = Z_OK \/ r_ret res = Z_BUF_ERROR \/ r_ret res = Z_STREAM_END \/ r_ret res = Z_NEED_DICT) /\
     0 <= m_snx m <= Zlength inp /\ m_sow m = Zlength (m_ow m) /\ m_aout m = zf_ao z /\
     (exists rest, D = out ++ m_ow m ++ rest) /\
     (r_ret res = Z_OK \/ r_ret res = Z_BUF_ERROR ->
        P c D O src (pos + m_snx m) (out ++ m_ow m) asked L' (m_tout m)) /\
     (r_ret res = Z_NEED_DICT ->
        sk_zdict c /\ asked = false /\ PN c D O src (pos + m_snx m) (out ++ m_ow m) L' (m_tout m)) /\
     (r_ret res = Z_STREAM_END ->
        out ++ m_ow m = D /\ pos + m_snx m = Zlength O /\ (asked = true <-> sk_zdict c) /\
        (forall gh, sc_gh c = Some gh -> g2_hdr_out gh (sc_h0 c) (m_s m) (m_h m))) /\
     (* offered neither input nor output space: not Z_OK, nothing produced, the counters kept *)
     (Zlength inp = 0 -> zf_ao z = 0 ->
        r_ret res <> Z_OK /\ m_ow m = [] /\ m_tin m = zf_tin z /\ m_tout m = zf_tout z));
  (** right after Z_NEED_DICT: no header attached; inflateSetDictionary(strm, dict, |dict|) returns Z_OK (the
      invariant with [asked], swfW) or Z_MEM_ERROR (no window: the run ends) *)
  si_nshape : forall c D O src pos out L tout,
    K c -> PN c D O src pos out L tout -> i_head (l_s L) = false;
  si_setdict : forall c D O src pos out L tout z alloc_ok winp,
    K c -> sc_ok c D O -> src_ok O src ->
    PN c D O src pos out L tout -> live_ok L -> zf_tout z = tout ->
    let sd := setdict_f (sc_dict c) alloc_ok winp z L in
    (fst3 sd = Z_OK \/ fst3 sd = Z_MEM_ERROR) /\
    (fst3 sd = Z_OK -> snd3 sd = z /\ swfW (l_s (thd3 sd)) /\ P c D O src pos out true (thd3 sd) tout)
}.

Definition ses_itheory_stmt : Prop := exists P PN, ses_ifacts (fun _ => True) P PN.

(* the four kinds of session, each with its own invariants *)
Definition ses_itheory_plain_stmt : Prop := exists P PN, ses_ifacts sk_plain P PN.
Definition ses_itheory_raw_stmt : Prop := exists P PN, ses_ifacts sk_raw P PN.
Definition ses_itheory_zdict_stmt : Prop := exists P PN, ses_ifacts sk_zdict P PN.
Definition ses_itheory_gz_stmt : Prop := exists P PN, ses_ifacts sk_gz P PN.
