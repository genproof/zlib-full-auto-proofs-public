(** * The bodies of compress.c's compress2_z and compress2 against their specifications for any sizes
    (RTCSpecW.v): compress2_z's loop over pieces of at most (uInt)-1 bytes of the source and of the destination,
    the source and the destination presented to deflate a piece at a time. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.roundtrip.RTCSpecW.
Require Import VST.floyd.library.
Require Zlib.units.Compress.
Require Import Zlib.compress.code.
Require Import Zlib.proof.roundtrip.RTCSpec.
Require Import Zlib.proof.roundtrip.RTCBC2zW.

Section Wrapper.
#[local] Existing Instance Zlib.units.Compress.CS.

(* compress2: compress2_z on a z_size_t copy of *destLen *)
Lemma rtcbw_compress2 : ob_compress2_w.
Proof.
  unfold ob_compress2_w, Gprog_compress2_w, compress2_z_spec_w, compress2_spec_w, c2w_pre, c2w_sep_pre,
    c2w_sep_post.
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

End Wrapper.

Theorem rtc_w_bodies : rtc_w_bodies_stmt.
Proof. split; [exact rtcbw_compress2_z | exact rtcbw_compress2]. Qed.
