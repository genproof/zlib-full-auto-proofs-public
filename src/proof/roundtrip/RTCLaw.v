(* Round-trip laws, part RT-CL: the law compress_roundtrip (harness/compress_roundtrip.c) from the
   shared bodies (inflate area, uncompr, trees.c, deflate.c, compress.c (RTCSpec.v)) and the pure facts c2_ok (RTC2.v)
   (compress2 over the model, RTCTheory.v) and ufacts (uncompress on compress2's stream, RTUTheory.v). *)
Require Import QuickProof.Contract.
Require Zlib.contracts.x_compress_roundtrip.
Require Zlib.proof.inflate_api.LibStmt5 Zlib.proof.uncompr.UBodies5.
Require Zlib.proof.deflate.Obligations Zlib.proof.deflate.Obligations9.
Require Import Zlib.proof.roundtrip.RTC2 Zlib.proof.roundtrip.RTIIface Zlib.proof.roundtrip.RTCSpec.
Require Zlib.proof.roundtrip.RTCLAsm Zlib.proof.roundtrip.RTCLMain.

Theorem rt_compress_law :
  Zlib.proof.inflate_api.LibStmt5.inflate_lib5_stmt ->
  Zlib.proof.uncompr.UBodies5.uncompr_bodies5_stmt ->
  Zlib.proof.deflate.Obligations.trees_bodies_ok ->
  Zlib.proof.deflate.Obligations9.deflate_bodies_ok9 ->
  rt_compress_bodies_stmt -> c2_ok -> ufacts ->
  harness_safe Zlib.contracts.x_compress_roundtrip.whole_prog.
Proof.
  intros LI HU TB DB CB CF UF.
  exact (Zlib.proof.roundtrip.RTCLAsm.rt_compress_core Zlib.proof.roundtrip.RTCLMain.body_main
           LI HU TB DB CB CF UF).
Qed.
