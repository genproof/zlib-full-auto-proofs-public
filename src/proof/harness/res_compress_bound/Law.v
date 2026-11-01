(* Law res_compress_bound (harness/res_compress_bound.c): compress2_z of any data (up to PTRDIFF_MAX bytes) at
   any level -1..9 into compressBound_z(n) bytes returns Z_OK (or Z_MEM_ERROR), never Z_BUF_ERROR.  harness_safe
   of its program from the body of main, the laws_common.h helpers (laws_common_ok), compressBound_z
   (CSpec.compressBound_z_spec), compress2_z by its specification for any sizes (RTCSpecW.v) and the deflate.c
   bodies it reaches; the model fact: RTC2W.c2w_bound_stmt (the run exists and ends with Z_OK or Z_MEM_ERROR). *)
Require Import QuickProof.Contract.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.roundtrip.RTCSpecW Zlib.proof.roundtrip.RTC2W.
Require Zlib.contracts.res_compress_bound.
Require Zlib.proof.harness.res_compress_bound.LawAsm.

Theorem res_compress_bound_ok : laws_common_ok -> rtc_w_bodies_stmt -> c2w_bound_stmt ->
  harness_safe Zlib.contracts.res_compress_bound.whole_prog.
Proof.
  exact Zlib.proof.harness.res_compress_bound.LawAsm.rcb_law.
Qed.
