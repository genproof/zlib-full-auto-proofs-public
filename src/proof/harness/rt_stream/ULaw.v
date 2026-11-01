(* Law rt_stream (harness/rt_stream.c, data of any length): deflate in any pieces with any flushes, then inflate
   in any pieces with any flushes, gives back exactly the data and reads exactly the compressed bytes.  The
   assembly (UAsm) of main's body (UMain), the globals (Globals, unchanged from round 1), the deflate side's facts
   (UDTheory over RTK7Api, which needs fix F9: RTK7Nocut), the inflate side's (UITheory over the wide decode
   theory), deflate's body against DSpecV, inflate.c's bodies (SpecWLibProof) and the bodies of laws_session.h's
   helpers (laws_session.Bodies). *)
Require Import QuickProof.Contract.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.contracts.rt_stream.
Require Zlib.proof.roundtrip.RTK7Api.
Require Zlib.proof.roundtrip.RTK7Nocut.
Require Zlib.proof.wide.Decode7.
Require Zlib.proof.inflate_api.SpecWLibProof.
Require Zlib.proof.deflate.DSpecVBody.
Require Zlib.proof.harness.rt_stream.UDTheory.
Require Zlib.proof.harness.rt_stream.UITheory.
Require Zlib.proof.harness.rt_stream.UMain.
Require Zlib.proof.harness.rt_stream.Globals.
Require Zlib.proof.harness.rt_stream.UAsm.
Require Zlib.proof.harness.laws_session.Bodies.

Theorem urt_stream_law : laws_common_ok -> harness_safe Zlib.contracts.rt_stream.whole_prog.
Proof.
  intros L.
  destruct Zlib.proof.wide.Decode7.decode7 as [DI DC].
  exact (Zlib.proof.harness.rt_stream.UAsm.urts_asm L Zlib.proof.harness.laws_session.Bodies.laws_session_bodies
    (Zlib.proof.harness.rt_stream.UDTheory.urts_dtheory
       (Zlib.proof.roundtrip.RTK7Api.rtk7_api_deflate Zlib.proof.roundtrip.RTK7Nocut.comp_nocut7))
    (Zlib.proof.harness.rt_stream.UITheory.urts_itheory DI DC)
    Zlib.proof.harness.rt_stream.UMain.urts_main Zlib.proof.harness.rt_stream.Globals.rts_globals
    Zlib.proof.deflate.DSpecVBody.deflate_bodyV Zlib.proof.inflate_api.SpecWLibProof.specw_lib).
Qed.
