(* Round-trip laws, part RT-HS: the law deflate_roundtrip with inflate()'s and inflateGetHeader's
   specifications for a gz_header with undefined fields (RTHSpec.inflate_spec6 / inflateGetHeader_spec6, bodies in
   RTHSpec.rt_head6_stmt, proved by RTHTheory.rt_head6) and the inflate facts ifacts6 (RTHIfDefs; RTHIface.rt_ifacts6):
   the law of RTRSLaw.rts_deflate_law (its gzip-header segment: RTRSHdr.rms_hset1), with the law's G (and
   main's context) using the spec6 versions. *)
Require Import QuickProof.Contract.
Require Zlib.contracts.x_deflate_roundtrip.
Require Zlib.proof.inflate_api.LibStmt5.
Require Zlib.proof.deflate.Obligations Zlib.proof.deflate.Obligations9.
Require Import Zlib.proof.roundtrip.RTXFacts Zlib.proof.roundtrip.RTHSpec Zlib.proof.roundtrip.RTHIfDefs.
Require Zlib.proof.roundtrip.RTRSLaw.

Theorem rt_deflate_law6 :
  Zlib.proof.inflate_api.LibStmt5.inflate_lib5_stmt ->
  rt_head6_stmt ->
  Zlib.proof.deflate.Obligations.trees_bodies_ok ->
  Zlib.proof.deflate.Obligations9.deflate_bodies_ok9 ->
  (exists I Iend, api_facts I Iend /\ rt_extra I) -> ifacts6 ->
  harness_safe Zlib.contracts.x_deflate_roundtrip.whole_prog.
Proof.
  exact Zlib.proof.roundtrip.RTRSLaw.rts_deflate_law.
Qed.
