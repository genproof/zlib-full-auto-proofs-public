(* ======================================================================
   The checksum laws, with the names and the statements that
   quickproof/tools/new_contract.py generated in src/contracts/<law>.v
   (`Theorem <law> : harness_safe whole_prog`, there with that file's
   whole_prog).  They live here because their proofs Require those files
   for whole_prog: proving them in place would be a cycle.  Each is proved
   from the shared specification library (src/proof/adler32, src/proof/crc32)
   and the main of its harness (src/proof/<law>/).
   ====================================================================== *)

Require Import QuickProof.Contract.
Require Zlib.contracts.x_crc32_ref.
Require Zlib.proof.crc32_ref.Law.

Theorem x_crc32_ref : harness_safe Zlib.contracts.x_crc32_ref.whole_prog.
Proof. exact Zlib.proof.crc32_ref.Law.crc32_ref_ok. Qed.
