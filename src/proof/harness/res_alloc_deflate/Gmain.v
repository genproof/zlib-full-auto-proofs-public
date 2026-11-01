(* Laws res_free_deflate and res_memory_deflate: the contexts of the two mains' body proofs (their callees, with
   their shared specifications) and the globals main gets.  main is proved at the law's compspecs CSa (ACS.v): it has
   struct count and struct z_stream_s as locals.  count_alloc and count_free are in the context for their
   function pointers (make_func_ptr), which main hands to deflate.c as the allocator. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.counted.Spec.
Require Import Zlib.proof.harness.res_alloc_deflate.ACS Zlib.proof.harness.res_alloc_deflate.Specs.
Require Zlib.proof.harness.laws_session.Spec.

(* res_free_deflate's main: deflateInit2_, one deflate() and deflateEnd *)
Definition Gmain_free : funspecs :=
  [za_deflateInit2__spec_c; deflate_spec_c; za_deflateEnd_spec_c;
   any_bytes_spec; offer_spec;
   counted_stream_spec; count_alloc_spec; count_free_spec;
   (_quickproof_malloc, @malloc_spec' CSa); nondet_u32_spec; gp_assert_spec].

(* res_memory_deflate's main: the parameters' check (deflate_params_ok, gp_assume), deflateInit2_, then a loop of
   deflate() calls on pieces of the data (upto, clip), each with a fresh output space (malloc, free) *)
Definition Gmain_mem : funspecs :=
  [Zlib.proof.harness.laws_session.Spec.deflate_params_ok_spec; gp_assume_spec;
   za_deflateInit2__spec_c; deflate_spec_c;
   upto_spec; clip_spec; any_bytes_spec; offer_spec;
   counted_stream_spec; count_alloc_spec; count_free_spec;
   (_quickproof_malloc, @malloc_spec' CSa); (_quickproof_free, @free_spec' CSa);
   nondet_u8_spec; nondet_u32_spec; gp_assert_spec].

(* the globals main gets: deflate.c's (DSpec.deflate_globals) and the harness's string literal ZLIB_VERSION
   [lit] (the version argument of the deflateInit2 macro) *)
Definition Ra (lit : ident) (gv : globals) : mpred := (deflate_globals gv * version_at gv lit)%logic.
