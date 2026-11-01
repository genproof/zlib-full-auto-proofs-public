(* Law api_reset (harness/api_reset.c): after any use, inflateReset makes a stream behave exactly like a new one
   from inflateInit2 with the same windowBits, call by call.  It holds with fix F8 (inflate.c: inflateReset2
   marks a window size that comes from the header, inflateReset then frees the window and sets wbits = 0). *)
Require Import QuickProof.Contract.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.contracts.api_reset.
Require Zlib.proof.inflate_api.SpecWLibProof.
Require Zlib.proof.harness.api_reset.ARBridge.
Require Zlib.proof.harness.api_reset.ARLawAsm.

Lemma api_reset_ok : laws_common_ok -> harness_safe Zlib.contracts.api_reset.whole_prog.
Proof.
  exact (Zlib.proof.harness.api_reset.ARLawAsm.ar_core Zlib.proof.inflate_api.SpecWLibProof.specw_lib
           Zlib.proof.harness.api_reset.ARBridge.ar_bridge).
Qed.
