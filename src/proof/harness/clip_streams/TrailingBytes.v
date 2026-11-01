(* Law rfc_trailing_bytes (harness/rfc_trailing_bytes.c): the compressed bytes followed by any bytes (as many as
   fit in one object with them; none when the stream is longer than PTRDIFF_MAX); inflate, fed all of it in calls
   of up to UINT_MAX bytes with any flush, stops exactly at the end of the stream: at Z_STREAM_END it has read the
   compressed bytes and none of the bytes after them.

   The deflate half is the one of the other clip laws (Laws.v); the inflate half is the decode theory for calls of
   any size (Decode7.v), whose source may be the stream followed by anything; the codes inflate() returns there
   are Z_OK, Z_BUF_ERROR and Z_STREAM_END (TBFacts.tl_call).  The hypotheses are the same as those of
   clip_stream_laws; laws_session.h's deflate_params_ok, which main calls since round 4, has its body proved in
   laws_session/Bodies.v. *)
Require Import QuickProof.Contract.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.contracts.rfc_trailing_bytes.
Require Import Zlib.proof.rfc1951.Decode7.
Require Import Zlib.proof.roundtrip.RTK7.
Require Zlib.proof.rfc1951.Decode7Step Zlib.proof.inflate_api.SpecWLib Zlib.proof.deflate.LawFactsW2.
Require Zlib.proof.harness.clip_streams.DTheory Zlib.proof.harness.clip_streams.DCtx.
Require Zlib.proof.harness.clip_streams.TBTheory Zlib.proof.harness.clip_streams.MainTB.
Require Zlib.proof.harness.clip_streams.AsmTB.
Require Zlib.proof.harness.laws_session.Bodies.

Lemma rfc_trailing_bytes_law : laws_common_ok -> rt_k7_stmt -> decode_init7_stmt -> decode_call7_stmt ->
  Zlib.proof.rfc1951.Decode7Step.decode7a_stmt -> Zlib.proof.inflate_api.SpecWLib.specw_lib_stmt ->
  Zlib.proof.deflate.LawFactsW2.bound_w_big_stmt ->
  harness_safe Zlib.contracts.rfc_trailing_bytes.whole_prog.
Proof.
  intros L K I7 C7 _ SW BW.
  destruct (Zlib.proof.harness.clip_streams.DTheory.clip_dtheory K BW) as [J0 [J DF]].
  destruct (Zlib.proof.harness.clip_streams.TBTheory.tb_theory
              Zlib.proof.harness.clip_streams.DCtx.clip_dctx I7 C7) as [P TF].
  exact (Zlib.proof.harness.clip_streams.AsmTB.clip_asm_tb L Zlib.proof.harness.laws_session.Bodies.laws_session_bodies SW
           (Zlib.proof.harness.clip_streams.MainTB.body_main_tb J0 J P DF TF)).
Qed.
