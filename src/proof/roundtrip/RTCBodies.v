(* Round-trip laws, part RT-CB: the bodies of deflate.c's deflateInit_ and compress.c's compress2_z,
   compress2, compress_z, compress against their specifications (RTCSpec.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.proof.deflate.Obligations.
Require Import Zlib.proof.roundtrip.RTCSpec.
Require Import Zlib.proof.roundtrip.RTCBWrap Zlib.proof.roundtrip.RTCBC2z.

Theorem rt_compress_bodies : Zlib.proof.deflate.Obligations.ob_dstream_to_end -> rt_compress_bodies_stmt.
Proof.
  intros HDE. unfold rt_compress_bodies_stmt.
  split; [exact rtcb_deflateInit_ |].
  split; [exact (rtcb_compress2_z HDE) |].
  split; [exact rtcb_compress2 |].
  split; [exact rtcb_compress_z | exact rtcb_compress].
Qed.
