(* Law rfc_level0_blocks (data of any length, deflate() in whole-block pieces): the statement of main's proof
   (L0B2Main.v): main of harness/rfc_level0_blocks.c against MainLib.main_core_spec R, at the compspecs of
   deflate.c + trees.c (DCS.CS; the body moves to the law's compspecs by entry_shared).  main draws the data and
   the parameters, calls deflateInit2_ (DSpec9's deflateInit2__spec_v9) and deflate() in a loop
   (DSpec.deflate_spec) through their shared specifications and the helpers of laws_common.h through theirs
   (laws_common/Spec.v), copies the data with copy_of before the calls, then walks the stored blocks after the
   wrapper header, checking each block's header byte, LEN, NLEN and (with bytes_eq) its data against the copy.  What main needs about the model runs is Level0Calls.l0_facts,
   for an invariant J of the loop that the model theory chooses. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DCS Zlib.proof.deflate.DSpec Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.deflate.Level0Calls.
Require Zlib.contracts.rfc_level0_blocks.
Require Import Zlib.harness.rfc_level0_blocks.code.

(* main's callees *)
Definition Gmain : funspecs :=
  [deflateInit2__spec_v9; deflate_spec; upto_spec; clip_spec; any_bytes_spec; copy_of_spec; bytes_eq_spec;
   new_stream_spec; (_quickproof_malloc, @malloc_spec' DCS.CS); nondet_u32_spec; gp_assert_spec].

Definition vlit : ident := ___stringlit_rfc_level0_blocks_1.

(* the globals main gets: deflate.c's and the harness's string literal ZLIB_VERSION *)
Definition R (gv : globals) : mpred := (deflate_globals gv * version_at gv vlit)%logic.

Definition l0b2_main_stmt : Prop :=
  forall J, l0_facts J ->
  @semax_body (QPvarspecs Zlib.contracts.rfc_level0_blocks.whole_prog) Gmain DCS.CS f_main (_main, main_core_spec R).
