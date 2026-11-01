(* Three laws that compress data of any length (deflate in clip()-sized pieces, Z_FINISH with the last, into
   deflateBound_z bytes) and then inflate a proper prefix of the compressed bytes, or the bytes with a changed
   trailer, in calls of up to UINT_MAX bytes: rt_partial, rj_truncated, rj_bad_checksum.  They use the decode
   theory for calls of any size (Decode7.v).  The fourth law of this harness family, rfc_trailing_bytes, is
   TrailingBytes.v. *)
Require Import QuickProof.Contract.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.contracts.rt_partial.
Require Zlib.contracts.rj_truncated.
Require Zlib.contracts.rj_bad_checksum.
Require Import Zlib.proof.rfc1951.Decode7.
Require Import Zlib.proof.roundtrip.RTK7.
Require Zlib.proof.rfc1951.Decode7Step Zlib.proof.inflate_api.SpecWLib Zlib.proof.deflate.LawFactsW2.
Require Zlib.proof.harness.clip_streams.DTheory Zlib.proof.harness.clip_streams.DCtx Zlib.proof.harness.clip_streams.PfxTheory Zlib.proof.harness.clip_streams.BadTheory.
Require Zlib.proof.harness.clip_streams.MainRP Zlib.proof.harness.clip_streams.MainRT Zlib.proof.harness.clip_streams.MainBC Zlib.proof.harness.clip_streams.Asm.
Require Zlib.proof.harness.clip_streams.AsmRP.

Lemma clip_stream_laws : laws_common_ok -> rt_k7_stmt -> decode_init7_stmt -> decode_call7_stmt ->
  Zlib.proof.rfc1951.Decode7Step.decode7a_stmt -> Zlib.proof.inflate_api.SpecWLib.specw_lib_stmt ->
  Zlib.proof.deflate.LawFactsW2.bound_w_big_stmt ->
  harness_safe Zlib.contracts.rt_partial.whole_prog /\
  harness_safe Zlib.contracts.rj_truncated.whole_prog /\
  harness_safe Zlib.contracts.rj_bad_checksum.whole_prog.
Proof.
  intros L K I7 C7 D7a SW BW.
  pose proof (Zlib.proof.harness.clip_streams.DTheory.clip_dtheory K BW) as DF.
  pose proof (Zlib.proof.harness.clip_streams.PfxTheory.pfx_theory
                Zlib.proof.harness.clip_streams.DCtx.clip_dctx I7 C7) as PF.
  pose proof (Zlib.proof.harness.clip_streams.BadTheory.bad_theory
                Zlib.proof.harness.clip_streams.DCtx.clip_dctx D7a) as BF.
  destruct DF as [J0 [J DF]]. destruct PF as [P PF]. destruct BF as [Q BF].
  exact (conj (Zlib.proof.harness.clip_streams.AsmRP.clip_asm_rpc L SW
                 (Zlib.proof.harness.clip_streams.MainRP.body_main_rp J0 J P DF PF))
          (conj (Zlib.proof.harness.clip_streams.Asm.clip_asm_rt L SW
                   (Zlib.proof.harness.clip_streams.MainRT.body_main_rt J0 J P DF PF))
                (Zlib.proof.harness.clip_streams.Asm.clip_asm_bc L SW
                   (Zlib.proof.harness.clip_streams.MainBC.body_main_bc J0 J Q DF BF)))).
Qed.
