(* The laws res_free_inflate and res_memory_inflate from the parts they use:
   - the laws_common.h helpers (laws_common_ok), laws_session.h's (laws_session_ok: res_memory_inflate calls
     inflate_window_ok) and the counting allocator's bodies (counted_ok);
   - inflate.c's bodies with one specification per function for the counting allocator: the family
     [Acount] (the counting allocator of a struct count and the two functions, src/proof/harness/counted/)
     of USpec.v's uspecs, and that each uspec gives its members;
   - the model facts of the two laws (ModelStmt.v: the state between two inflate() calls, the window and the
     mode MEM).
   The other bodies the two programs reach (inflate_fixed, inflate_table, adler32, crc32, zmemcpy, zmemset)
   are the existing proofs of the default-allocator layer (they do not depend on the allocator). *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Contract.
Require Zlib.contracts.res_free_inflate Zlib.contracts.res_memory_inflate.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.counted.Spec.
Require Zlib.proof.harness.laws_session.Spec.
Require Import Zlib.proof.za.inflate_api.USpec.
Require Import Zlib.proof.harness.res_inflate.ModelStmt.
Require Zlib.proof.harness.res_inflate.ResIAsm Zlib.proof.harness.res_inflate.ResIFree
        Zlib.proof.harness.res_inflate.ResIMem.

(* the counting allocators, indexed by (the struct count, count_alloc, count_free) *)
Definition Acount (k : val * val * val) : zallocator :=
  let '(cp, za, zf) := k in counted cp za zf.

Lemma res_inflate_from :
  laws_common_ok -> Zlib.proof.harness.laws_session.Spec.laws_session_ok -> counted_ok ->
  za_inflate_ulib_stmt Acount -> za_uspec_sub_stmt Acount -> res_model_stmt ->
  harness_safe Zlib.contracts.res_free_inflate.whole_prog /\ harness_safe Zlib.contracts.res_memory_inflate.whole_prog.
Proof.
  intros HL HLS HC HU HS HM.
  apply (Zlib.proof.harness.res_inflate.ResIAsm.res_inflate_asm HL HLS HC HU HS).
  - exact (Zlib.proof.harness.res_inflate.ResIFree.body_main_free HM).
  - exact (Zlib.proof.harness.res_inflate.ResIMem.body_main_memory HM).
Qed.
