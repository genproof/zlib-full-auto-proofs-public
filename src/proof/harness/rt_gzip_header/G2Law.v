(* Law rt_gzip_header (harness/rt_gzip_header.c, round 2: a name and a comment of up to 2^32 - 2 bytes, deflate and
   inflate in pieces of at most 2^32 - 1 bytes): every field given to deflateSetHeader comes back through
   inflateGetHeader.  Assembled (G2Asm.rtg2_core) from main's body (G2Main.v), the harness's helpers
   (G2Helpers.v), the header specifications of inflate / inflateGetHeader (RTH9Body.v), deflate() with
   next_in = Z_NULL (the body [deflate_bodyN] of DSpecNBody.v, given here as a hypothesis), the deflate side of the
   law (G2DTheory.v) and its inflate side (G2ITheory.v).  Round 1's files of src/proof/harness/rt_gzip_header/
   that are not named G2* are about the bounded harness and are superseded. *)
Require Import QuickProof.Contract.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.contracts.rt_gzip_header.
Require Zlib.proof.deflate.DSpecN.
Require Zlib.proof.roundtrip.RTH9Body.
Require Zlib.proof.harness.rt_gzip_header.G2Main Zlib.proof.harness.rt_gzip_header.G2Helpers.
Require Zlib.proof.harness.rt_gzip_header.G2ITheory Zlib.proof.harness.rt_gzip_header.G2DTheory.
Require Zlib.proof.harness.rt_gzip_header.G2Asm.

Lemma rt_gzip_header2_law : laws_common_ok -> Zlib.proof.deflate.DSpecN.deflate_bodyN_stmt ->
  harness_safe Zlib.contracts.rt_gzip_header.whole_prog.
Proof.
  intros L N.
  exact (Zlib.proof.harness.rt_gzip_header.G2Asm.rtg2_core Zlib.proof.harness.rt_gzip_header.G2Main.body_main2
           Zlib.proof.harness.rt_gzip_header.G2Helpers.rtg2_helpers L Zlib.proof.roundtrip.RTH9Body.rth9_body N
           Zlib.proof.harness.rt_gzip_header.G2DTheory.rtg2_dtheory
           Zlib.proof.harness.rt_gzip_header.G2ITheory.rtg2_itheory).
Qed.
