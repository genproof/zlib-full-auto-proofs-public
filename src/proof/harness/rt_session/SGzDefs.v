(* Law rt_session, the sessions with a gzip header given to inflateGetHeader (SIFacts.sk_gz): the invariant of the
   inflate side and the statements of its parts.

   The stream O (SIFacts.sc_ok: RTFinal.dfinal [] 2 wb (Some gh) D O) is the gzip header deflate wrote for gh
   (G2IDefs.g2_H gh xfl), deflate's blocks bs of the data D and the trailer; the input object src is O followed by any
   bytes.  As in law rt_gzip_header (G2ICall.v), between two calls the stream is either inside the header
   (G2ICall.g2_ph over src: the header state J2 at the position, nothing produced) or after it ([sgz_pd]: the decode
   invariant of the generalized decode theory, RTIGDefs.dinv, on the context [g2_G gh xfl wb bs src], whose data is D
   and whose stream ends at |O|, and the complete gz_header).  Unlike rt_gzip_header's harness, the calls are offered
   any pieces of src, any output space and any flush, and the stream has data. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Export Zlib.proof.harness.rt_session.SIFacts.
Require Export Zlib.proof.harness.rt_gzip_header.G2IDefs.
Require Export Zlib.proof.roundtrip.RTIGW.
Require Export Zlib.proof.harness.rt_gzip_header.G2ICall.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* What does not change during a session                                                          *)

(* deflate's side as the inflate theory reads it: inflateInit2 with 16 + wb, the header's ghost (g2_g) laid out at the
   start of src, ending inside O; the decode context of src after the header, with the data D and the stream O *)
Definition sgz_lay_ok (c: scase) (D O src: list Z) (gh: DS.gzh) (wb xfl: Z) (bs: list F.block) : Prop :=
  sc_gh c = Some gh /\ rts_iw (sc_wbits c) = 16 + wb /\ 9 <= wb <= 15 /\ g2_hdr_ok gh /\ g2_bufs gh (sc_h0 c) /\
  (xfl = 0 \/ xfl = 2 \/ xfl = 4) /\ g2h_ok (g2_g gh xfl) /\ lay2 (g2_g gh xfl) src /\
  ih_nh (g2_g gh xfl) = Zlength (F.gz_bytes (g2_H gh xfl)) /\ ih_nh (g2_g gh xfl) <= Zlength O /\
  rtigw_ok (g2_G gh xfl wb bs src) /\ full (g2_G gh xfl wb bs src) = D /\
  slen (g2_G gh xfl wb bs src) = Zlength O.

(* ... and the gz_header given to inflateGetHeader (which sets its done to 0) within RTH8Spec's ranges *)
Definition sgz_fix (c: scase) (D O src: list Z) (gh: DS.gzh) (wb xfl: Z) (bs: list F.block) : Prop :=
  sgz_lay_ok c D O src gh wb xfl bs /\ hwf8 (set_h_done (sc_h0 c) 0).

(* ---------------------------------------------------------------------------------------------- *)
(* The invariant                                                                                   *)

(* after the header: the decode invariant with the output so far, the gz_header complete *)
Definition sgz_pd (h0: hstate) (gh: DS.gzh) (wb xfl: Z) (bs: list F.block) (src: list Z) (pos: Z) (out: list Z)
    (s: istate) (h: hstate) (tout: Z) : Prop :=
  dinv (g2_G gh xfl wb bs src) pos out s tout /\ (exists rest, full (g2_G gh xfl wb bs src) = out ++ rest) /\
  i_head s = true /\
  ih_done_ok (g2_g gh xfl) (set_h_done h0 0) h /\
  h_extra_max h = h_extra_max h0 /\ h_name_max h = h_name_max h0 /\ h_comm_max h = h_comm_max h0.

Definition sgz_P : ses_iinv := fun c D O src pos out asked L tout =>
  exists gh wb xfl bs, sgz_fix c D O src gh wb xfl bs /\ asked = false /\ 0 <= pos /\
    ((out = [] /\ tout = 0 /\ g2_ph wb gh src (sc_h0 c) xfl pos (l_s L) (l_h L)) \/
     sgz_pd (sc_h0 c) gh wb xfl bs src pos out (l_s L) (l_h L) tout).

(* gzip never asks for a dictionary *)
Definition sgz_PN : ses_ninv := fun _ _ _ _ _ _ _ _ => False.

(* ---------------------------------------------------------------------------------------------- *)
(* The parts                                                                                       *)

(* deflate's finished gzip stream with a header, followed by any bytes *)
Definition sgz_lay_stmt : Prop := forall c D O src gh,
  sc_ok c D O -> src_ok O src -> sc_gh c = Some gh ->
  exists wb xfl bs, sgz_lay_ok c D O src gh wb xfl bs.

(* one call offered inp = src[pos .. pos + |inp|) from a state inside the header: it leaves inside the header having
   consumed all of its input, written nothing (Z_BUF_ERROR when offered nothing), or it passes the end of the header
   (having consumed some input) and decodes from there on: the decode invariant after the call, the gz_header
   complete *)
Definition sgz_call_h_stmt : Prop := forall gh xfl wb bs src h0 pos L z inp flush res,
  9 <= wb <= 15 -> g2_hdr_ok gh -> (xfl = 0 \/ xfl = 2 \/ xfl = 4) -> g2h_ok (g2_g gh xfl) -> lay2 (g2_g gh xfl) src ->
  ih_nh (g2_g gh xfl) = Zlength (F.gz_bytes (g2_H gh xfl)) -> rtigw_ok (g2_G gh xfl wb bs src) ->
  hwf8 (set_h_done h0 0) ->
  zf_tout z = 0 -> g2_ph wb gh src h0 xfl pos (l_s L) (l_h L) ->
  live_ok8 L -> swfW (l_s L) -> zf_ok z -> zf_ao z <= 4294967295 -> Zlength inp <= 4294967295 ->
  ctx2 src pos inp ->
  run2 flush lenfix_list distfix_list (m_init z L inp) res ->
  let m := r_m res in
  let G := g2_G gh xfl wb bs src in
  r_ret res = Z_MEM_ERROR \/
  (0 <= m_snx m <= Zlength inp /\ m_sow m = Zlength (m_ow m) /\ m_aout m = zf_ao z /\
   (((r_ret res = Z_OK \/ r_ret res = Z_BUF_ERROR) /\ m_snx m = Zlength inp /\ m_ow m = [] /\ m_tout m = 0 /\
     g2_ph wb gh src h0 xfl (pos + Zlength inp) (m_s m) (m_h m) /\
     (Zlength inp = 0 -> r_ret res = Z_BUF_ERROR /\ m_tin m = zf_tin z)) \/
    (Zlength inp <> 0 /\ (r_ret res = Z_OK \/ r_ret res = Z_BUF_ERROR \/ r_ret res = Z_STREAM_END) /\
     (exists rest, full G = m_ow m ++ rest) /\
     sgz_pd h0 gh wb xfl bs src (pos + m_snx m) (m_ow m) (m_s m) (m_h m) (m_tout m) /\
     (r_ret res = Z_STREAM_END -> m_ow m = full G /\ pos + m_snx m = slen G)))).

(* one call from a state after the header (the decode invariant, a gz_header of any size attached): RTIGW's decode
   theory with the gz_header kept *)
Definition sgz_call_d_stmt : Prop := forall G pos out L z inp flush res,
  rtigw_ok G -> dinv G pos out (l_s L) (zf_tout z) -> live_ok8 L -> zf_ok z ->
  zf_ao z <= 4294967295 -> Zlength inp <= 4294967295 ->
  0 <= pos -> pos + Zlength inp <= Zlength (dc_src G) -> inp = sublist pos (pos + Zlength inp) (dc_src G) ->
  (exists d0, out = dc_hist G ++ d0) -> (exists rest, full G = out ++ rest) ->
  run2 flush lenfix_list distfix_list (m_init z L inp) res ->
  let m := r_m res in
  r_ret res = Z_MEM_ERROR \/
  ((r_ret res = Z_OK \/ r_ret res = Z_BUF_ERROR \/ r_ret res = Z_STREAM_END) /\
   0 <= m_snx m <= Zlength inp /\ m_sow m = Zlength (m_ow m) /\ m_aout m = zf_ao z /\
   m_h m = l_h L /\ i_head (m_s m) = i_head (l_s L) /\
   (exists rest, full G = out ++ m_ow m ++ rest) /\
   dinv G (pos + m_snx m) (out ++ m_ow m) (m_s m) (m_tout m) /\
   (r_ret res = Z_STREAM_END -> out ++ m_ow m = full G /\ pos + m_snx m = slen G)).

(* a call after the header offered neither input nor output space: not Z_OK, nothing written, the counters kept
   (as rt_stream's UIIdle.ui_idle_call, with a gz_header attached) *)
Definition sgz_idle_d_stmt : Prop := forall G pos out L z flush res,
  rtigw_ok G -> dinv G pos out (l_s L) (zf_tout z) -> live_ok8 L -> zf_ok z -> zf_ao z = 0 ->
  0 <= pos -> pos <= Zlength (dc_src G) ->
  (exists d0, out = dc_hist G ++ d0) -> (exists rest, full G = out ++ rest) ->
  run2 flush lenfix_list distfix_list (m_init z L []) res ->
  r_ret res <> Z_OK /\ m_ow (r_m res) = [] /\
  (r_ret res <> Z_MEM_ERROR -> m_tin (r_m res) = zf_tin z /\ m_tout (r_m res) = zf_tout z).
