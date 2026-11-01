(* inflate decodes every well-formed stream (Format.v): THE theorems of the decode theory.  Model2's run2 (one inflate() call, Spec5.m_init) from a state satisfying `dinv`
   (DecodeDefs.v), offered the next bytes of the input and any output space, with any flush: it returns
   Z_OK, Z_BUF_ERROR or Z_STREAM_END (or Z_MEM_ERROR when the window allocation fails), its output is the
   next bytes of the data, the invariant holds again; at Z_STREAM_END all the data was produced and exactly
   the stream consumed; data_type's block-boundary and last-block bits are right; a call that stops early
   ran out of input or output space (or flush is Z_BLOCK / Z_TREES).  inflateInit2 with an accepting
   windowBits gives the invariant (no history). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.rfc1951.DecodeDefs.
Require Export Zlib.proof.inflate_api.Spec5.
Require Export Zlib.proof.inflate.CaseHyps5.
Import ListNotations.
Local Open Scope Z_scope.

Definition decode_init_stmt : Prop :=
  forall G sp, dctx_ok G -> dc_hist G = [] -> (forall wb fl did, dc_w G = WZlib wb fl did -> did = None) ->
    dinv G 0 [] (l_s (init_live sp (dc_iw G))) 0.

(* the data_type facts (zlib.h): bit 128 at a block boundary, bit 64 in or after the last block *)
Definition dtype_ok (G: dctx) (out: list Z) (dt: Z) : Prop :=
  (Z.land dt 128 <> 0 -> exists k, 0 <= k <= nblk G /\ out = outk G k) /\
  (Z.land dt 64 <> 0 -> Zlength (outk G (nblk G - 1)) <= Zlength out) /\
  (Z.land dt 64 = 0 -> Zlength out <= Zlength (outk G (nblk G - 1))).

Definition decode_call_stmt : Prop :=
  forall G pos out L z inp flush res,
    dctx_ok G -> dinv G pos out (l_s L) (zf_tout z) -> live_ok L -> zf_ok z -> zf_ao z <= 2 ^ 31 - 1 ->
    0 <= pos -> pos + Zlength inp <= Zlength (dc_src G) -> inp = sublist pos (pos + Zlength inp) (dc_src G) ->
    run2 flush lenfix_list distfix_list (m_init z L inp) res ->
    let m := r_m res in
    r_ret res = Z_MEM_ERROR \/
    ((r_ret res = Z_OK \/ r_ret res = Z_BUF_ERROR \/ r_ret res = Z_STREAM_END) /\
     0 <= m_snx m <= Zlength inp /\ m_sow m = Zlength (m_ow m) /\ m_aout m = zf_ao z /\
     (exists rest, full G = out ++ m_ow m ++ rest) /\
     dinv G (pos + m_snx m) (out ++ m_ow m) (m_s m) (m_tout m) /\
     (* the window beyond CHECK (law inflate_dict's inflateGetDictionary; not for gzip, whose LENGTH may stop a
        call after CHECK's out = left) *)
     ((forall h, dc_w G <> WGzip h) -> i_wsize (l_s L) <> 0 -> win_ok G (l_s L) out ->
      (r_ret res <> Z_STREAM_END \/ wrapped G = false) ->
      i_wsize (m_s m) <> 0 /\ win_ok G (m_s m) (out ++ m_ow m)) /\
     (r_ret res = Z_STREAM_END -> out ++ m_ow m = full G /\ pos + m_snx m = slen G) /\
     (r_ret res <> Z_STREAM_END ->
        (m_snx m = Zlength inp /\ pos + Zlength inp < slen G) \/
        (Zlength (m_ow m) = zf_ao z /\ Zlength (out ++ m_ow m) < Zlength (full G)) \/
        flush = Z_BLOCK \/ flush = Z_TREES) /\
     exists dt, r_dtype res = Some dt /\ dtype_ok G (out ++ m_ow m) dt).

(* the parts *)
Definition decode_parts : Prop :=
  dkit_stmt /\ tabdec_stmt /\ stepf2_mwf3_stmt /\
  (dkit_stmt -> decode_init_stmt) /\
  (dkit_stmt -> group_ok md_hdr) /\
  (dkit_stmt -> tabdec_stmt -> group_ok md_type) /\
  (dkit_stmt -> tabdec_stmt -> stepf2_mwf3_stmt -> group_ok md_dec -> group_ok md_tab) /\
  (dkit_stmt -> dfast_stmt -> group_ok md_dec) /\
  (dkit_stmt -> dfast_stmt) /\
  (dkit_stmt -> group_ok md_trl) /\
  (dkit_stmt -> stepf2_mwf3_stmt -> group_ok md_hdr -> group_ok md_type -> group_ok md_tab ->
     group_ok md_dec -> group_ok md_trl -> decode_call_stmt).

Theorem decode_of_parts : decode_parts -> decode_init_stmt /\ decode_call_stmt.
Proof.
  intros (K & T & S & I & H & Ty & Ta & De & Fa & Tr & C).
  split; [exact (I K)|].
  pose proof (De K (Fa K)) as DE.
  exact (C K S (H K) (Ty K T) (Ta K T S DE) DE (Tr K)).
Qed.
