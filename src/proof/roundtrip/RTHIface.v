(* RT-H: deflate_roundtrip's inflate facts for the spec6 calls (RTHIfDefs.ifacts6), proved in
   RTHIfProof.v from the decode theory. *)
Require Export Zlib.proof.roundtrip.RTHIfDefs.
Require Zlib.proof.rfc1951.Decode.
Require Zlib.proof.roundtrip.RTHIfProof.

Theorem rt_ifacts6 : Zlib.proof.rfc1951.Decode.decode_parts -> ifacts6.
Proof. exact Zlib.proof.roundtrip.RTHIfProof.rt_ifacts6_proof. Qed.
