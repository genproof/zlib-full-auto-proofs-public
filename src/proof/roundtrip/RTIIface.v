(* The round-trip laws: THE interface of the inflate side, pure Coq over the model of inflate()
   (Model2.run2 from Spec5.m_init), of the API calls deflate_roundtrip makes (Spec5: init_live of inflateInit2_,
   inflateGetHeader's set_l_head, setdict_f of inflateSetDictionary) and of uncompress (UModel.uncompress_rel),
   on the bytes O of a finished deflate run ([RTFinal.dfinal]).

   - [ifacts]: harness/deflate_roundtrip.c's inflation: inflateInit2 with windowBits -wb (raw), 0 (zlib) or 32
     (gzip), then one inflate(Z_FINISH) call offered all of O and exactly |D| bytes of output space gives back D
     (Z_STREAM_END, all consumed, all space filled) or fails to allocate (Z_MEM_ERROR); with a raw dictionary set
     before; with a zlib dictionary: the first call stops at Z_NEED_DICT after the 6 header bytes with
     strm->adler = the dictionary's Adler-32, inflateSetDictionary succeeds, a second call decodes the rest;
     with a gzip header and inflateGetHeader (buffers of exactly the fields' sizes): the header is reported.
   - [ufacts]: harness/compress_roundtrip.c's uncompress calls on the zlib stream of compress2 (window bits 15,
     no dictionary): with |D| bytes of space it gives D back; with |D| - 1 bytes Z_BUF_ERROR; on a strict prefix
     never Z_OK.
   Both are proved (RTITheory.rt_ifacts, RTUTheory.rt_ufacts) from the decode theory's theorems
   (rfc1951/Decode.v decode_init_stmt, decode_call_stmt, proved by the inflate area); the gzip header and the
   zlib FCHECK = 31 / FDICT header need an extension of it (RTIGDefs.v, RTIGz*.v). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Export Zlib.proof.inflate_api.Spec5.
Require Export Zlib.proof.uncompr.UModel.
Require Zlib.proof.roundtrip.RTFinal.
Import ListNotations.
Local Open Scope Z_scope.

Module RF := Zlib.proof.roundtrip.RTFinal.
Module DS := Zlib.proof.deflate.DState.

(* deflate_roundtrip's inflateInit2 windowBits: -wb for raw, 0 for zlib (the header's), 32 for gzip *)
Definition iw_of (wrap wb : Z) : Z := if wrap =? 0 then - wb else if wrap =? 1 then 0 else 32.

(* a call offered inp and |D| bytes of space ended the stream with the output D, or failed to allocate *)
Definition rdone (inp D : list Z) (res : result) : Prop :=
  r_ret res = Z_MEM_ERROR \/
  (r_ret res = Z_STREAM_END /\ m_snx (r_m res) = Zlength inp /\ m_ow (r_m res) = D /\
   m_sow (r_m res) = Zlength D /\ m_aout (r_m res) = Zlength D).

(* the stream fields of such a call (input inp, |D| bytes of space, nothing produced before) *)
Definition zcall_ok (z : zfields) (inp D : list Z) : Prop :=
  zf_ok z /\ zf_ai z = Zlength inp /\ zf_ao z = Zlength D /\ zf_tout z = 0.

(* inflateGetHeader's live part (Spec5.inflateGetHeader_spec, on a gzip-capable stream) *)
Definition head_live (L : live) (h : hstate) (headp : val) (hsh : share) (xb nb cb : val) : live :=
  set_l_head (set_l_s L (set_i_head (l_s L) true)) (set_h_done h 0) headp hsh xb nb cb.

Record ifacts : Prop := {
  (** no dictionary, no gzip header given to inflateGetHeader *)
  if_plain : forall wrap wb D O sp z res,
    RF.dfinal [] wrap wb None D O -> Zlength D <= 1048576 -> Zlength O <= 4194304 ->
    live_ok (init_live sp (iw_of wrap wb)) -> zcall_ok z O D ->
    run2 4 lenfix_list distfix_list (m_init z (init_live sp (iw_of wrap wb)) O) res ->
    rdone O D res;
  (** raw with a dictionary set right after inflateInit2 *)
  if_rawdict : forall wb dict D O sp z0 alloc_ok winp,
    RF.dfinal dict 0 wb None D O -> dict <> [] -> Zlength dict <= 32768 ->
    Zlength D <= 1048576 -> Zlength O <= 4194304 -> live_ok (init_live sp (- wb)) ->
    let sd := setdict_f dict alloc_ok winp z0 (init_live sp (- wb)) in
    (fst3 sd = Z_OK \/ fst3 sd = Z_MEM_ERROR) /\
    (fst3 sd = Z_OK -> forall z res,
       live_ok (thd3 sd) -> zcall_ok z O D ->
       run2 4 lenfix_list distfix_list (m_init z (thd3 sd) O) res -> rdone O D res);
  (** zlib with a dictionary: Z_NEED_DICT after the 6 header bytes, inflateSetDictionary, the second call *)
  if_zdict : forall wb dict D O sp z res,
    RF.dfinal dict 1 wb None D O -> dict <> [] -> Zlength dict <= 32768 ->
    Zlength D <= 1048576 -> Zlength O <= 4194304 -> live_ok (init_live sp 0) -> zcall_ok z O D ->
    run2 4 lenfix_list distfix_list (m_init z (init_live sp 0) O) res ->
    r_ret res = Z_MEM_ERROR \/
    (r_ret res = Z_NEED_DICT /\ m_snx (r_m res) = 6 /\ m_ow (r_m res) = [] /\ m_sow (r_m res) = 0 /\
     m_aout (r_m res) = Zlength D /\ m_tout (r_m res) = 0 /\
     m_adler (r_m res) = Zlib.proof.adler32.Model.ref_adler32 1 dict /\
     forall L1 z1 alloc_ok winp,
       l_s L1 = m_s (r_m res) -> l_h L1 = m_h (r_m res) -> live_ok L1 ->
       let sd := setdict_f dict alloc_ok winp z1 L1 in
       (fst3 sd = Z_OK \/ fst3 sd = Z_MEM_ERROR) /\
       (fst3 sd = Z_OK -> forall z2 res2,
          live_ok (thd3 sd) -> zcall_ok z2 (sublist 6 (Zlength O) O) D ->
          run2 4 lenfix_list distfix_list (m_init z2 (thd3 sd) (sublist 6 (Zlength O) O)) res2 ->
          rdone (sublist 6 (Zlength O) O) D res2));
  (** gzip with deflateSetHeader's header gh (all three fields given, as the harness does) and inflateGetHeader
      with buffers of exactly the fields' sizes (any contents) *)
  if_gzhead : forall wb gh x nm cm D O sp z res h headp hsh xb nb cb,
    RF.dfinal [] 2 wb (Some gh) D O -> RF.rhdr_ok gh ->
    DS.gz_extra gh = Some x -> DS.gz_name gh = Some nm -> DS.gz_comment gh = Some cm ->
    Zlength D <= 1048576 -> Zlength O <= 4194304 ->
    h_xp h = true -> h_extra_max h = Zlength x -> Zlength (h_xbuf h) = Zlength x ->
    h_np h = true -> h_name_max h = Zlength nm -> Zlength (h_nbuf h) = Zlength nm ->
    h_cp h = true -> h_comm_max h = Zlength cm -> Zlength (h_cbuf h) = Zlength cm ->
    live_ok (head_live (init_live sp 32) h headp hsh xb nb cb) -> zcall_ok z O D ->
    run2 4 lenfix_list distfix_list (m_init z (head_live (init_live sp 32) h headp hsh xb nb cb) O) res ->
    rdone O D res /\
    (r_ret res = Z_STREAM_END ->
     let h' := m_h (r_m res) in
     h_done h' = 1 /\ h_text h' = DS.gz_text gh /\ h_time h' = DS.gz_time gh /\ h_os h' = DS.gz_os gh /\
     h_hcrc h' = DS.gz_hcrc gh /\ h_extra_len h' = DS.gz_extra_len gh /\
     h_xbuf h' = x /\ h_nbuf h' = nm /\ h_cbuf h' = cm)
}.

Record ufacts : Prop := {
  (** uncompress / uncompress2 with exactly |D| bytes of space *)
  uf_full : forall D O r slen dlen out,
    RF.dfinal [] 1 15 None D O -> Zlength D <= 1048576 -> Zlength O <= 2097152 ->
    uncompress_rel O (Zlength D) r slen dlen out ->
    r = Z_MEM_ERROR \/ (r = Z_OK /\ dlen = Zlength D /\ out = D /\ slen = Zlength O);
  (** one byte of space too few *)
  uf_short : forall D O r slen dlen out,
    RF.dfinal [] 1 15 None D O -> 0 < Zlength D <= 1048576 -> Zlength O <= 2097152 ->
    uncompress_rel O (Zlength D - 1) r slen dlen out ->
    r = Z_MEM_ERROR \/ (r = Z_BUF_ERROR /\ dlen <= Zlength D - 1);
  (** a strict prefix of the stream *)
  uf_prefix : forall D O k r slen dlen out,
    RF.dfinal [] 1 15 None D O -> Zlength D <= 1048576 -> Zlength O <= 2097152 -> 0 <= k < Zlength O ->
    uncompress_rel (sublist 0 k O) (Zlength D) r slen dlen out ->
    r = Z_MEM_ERROR \/ r = Z_DATA_ERROR \/ r = Z_BUF_ERROR
}.
