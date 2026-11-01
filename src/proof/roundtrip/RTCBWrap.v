(* Round-trip laws, part RT-CB: the bodies of deflate.c's deflateInit_ and of compress.c's wrappers
   compress2, compress_z, compress (RTCSpec.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.DSpec Zlib.proof.deflate.DSpec9.
Require Zlib.proof.compress.CSpec.
Require Zlib.units.Compress.
Require Zlib.deflate.code Zlib.compress.code.
Require Import Zlib.proof.roundtrip.RTDIface.
Require Import Zlib.proof.roundtrip.RTCSpec.
Local Open Scope logic.

Lemma rtcb_deflateInit_ : ob_deflateInit_.
Proof.
  unfold ob_deflateInit_.
  start_function.
  forward_call (strmp, level, 8, 15, 8, 0, vp, vsh, vers, ssize, ni, tin, tout, msgv, adler, op, dt, st0, gv).
  { unfold s32_ok; repeat split; rep_lia. }
  Intros vret. destruct vret as [[[[[a1 a2] a3] a4] a5] r]. simpl fst in *; simpl snd in *.
  forward.
  Exists a1 a2 a3 a4 a5 r. entailer!. Exists msgv'. entailer!.
Qed.

Section Wrappers.
#[local] Existing Instance Zlib.units.Compress.CS.

Lemma rtcb_compress_z : ob_compress_z.
Proof.
  unfold ob_compress_z, Gprog_compress_z, compress2_z_spec, compress_z_spec, c2_pre, c2_sep_pre, c2_sep_post.
  start_function.
  forward_call (gv, dp, dc, cap, dlp, ssh, sp, src, -1).
  Intros vret. destruct vret as [[[[[[a1 a2] a3] a4] a5] r] out].
  forward.
  Exists a1 a2 a3 a4 a5 r out. entailer!.
Qed.

Lemma rtcb_compress2 : ob_compress2.
Proof.
  unfold ob_compress2, Gprog_compress2, compress2_z_spec, compress2_spec, c2_pre, c2_sep_pre, c2_sep_post.
  start_function.
  forward.
  forward.
  forward_call (gv, dp, dc, cap, v_got, ssh, sp, src, level).
  Intros vret. destruct vret as [[[[[[a1 a2] a3] a4] a5] r] out].
  forward.
  forward.
  forward.
  Exists a1 a2 a3 a4 a5 r out. entailer!.
Qed.

Lemma rtcb_compress : ob_compress.
Proof.
  unfold ob_compress, Gprog_compress, compress2_spec, compress_spec, c2_pre, c2_sep_pre, c2_sep_post.
  start_function.
  forward_call (gv, dp, dc, cap, dlp, ssh, sp, src, -1).
  Intros vret. destruct vret as [[[[[[a1 a2] a3] a4] a5] r] out].
  forward.
  Exists a1 a2 a3 a4 a5 r out. entailer!.
Qed.

End Wrappers.
