(* Law rt_stream_trailing (harness/rt_stream_trailing.c): deflate in any pieces with any flushes, then inflate fed
   the compressed bytes followed by any bytes, in any pieces with any flushes, accounts every call exactly, stops
   exactly at the end of the stream and gives back exactly the data.  The assembly (TAsm) of main's body (TMain),
   the globals (TGlobals), the deflate side's facts (rt_stream's UDTheory over RTK7Api, which needs fix F9:
   RTK7Nocut), the inflate side's (TITheory over the wide decode theory), deflate's body against DSpecV, inflate.c's
   bodies (SpecWLibProof) and the bodies of laws_session.h's helpers (laws_session.Bodies). *)
Require Import QuickProof.Contract.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.contracts.rt_stream_trailing.
Require Zlib.proof.roundtrip.RTK7Api.
Require Zlib.proof.roundtrip.RTK7Nocut.
Require Zlib.proof.wide.Decode7.
Require Zlib.proof.inflate_api.SpecWLibProof.
Require Zlib.proof.deflate.DSpecVBody.
Require Zlib.proof.harness.rt_stream.UDTheory.
Require Zlib.proof.harness.rt_stream_trailing.TITheory.
Require Zlib.proof.harness.rt_stream_trailing.TMain.
Require Zlib.proof.harness.rt_stream_trailing.TGlobals.
Require Zlib.proof.harness.rt_stream_trailing.TAsm.
Require Zlib.proof.harness.laws_session.Bodies.

Theorem rt_stream_trailing_law : laws_common_ok -> harness_safe Zlib.contracts.rt_stream_trailing.whole_prog.
Proof.
  intros L.
  destruct Zlib.proof.wide.Decode7.decode7 as [DI DC].
  exact (Zlib.proof.harness.rt_stream_trailing.TAsm.trl_asm L
    Zlib.proof.harness.laws_session.Bodies.laws_session_bodies
    (Zlib.proof.harness.rt_stream.UDTheory.urts_dtheory
       (Zlib.proof.roundtrip.RTK7Api.rtk7_api_deflate Zlib.proof.roundtrip.RTK7Nocut.comp_nocut7))
    (Zlib.proof.harness.rt_stream_trailing.TITheory.trl_itheory DI DC)
    Zlib.proof.harness.rt_stream_trailing.TMain.trl_main
    Zlib.proof.harness.rt_stream_trailing.TGlobals.trl_globals
    Zlib.proof.deflate.DSpecVBody.deflate_bodyV Zlib.proof.inflate_api.SpecWLibProof.specw_lib).
Qed.
