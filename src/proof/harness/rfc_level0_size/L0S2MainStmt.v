(* Law rfc_level0_size (data of any length, deflate() in whole-block pieces): the statement of main's proof
   (L0S2Main.v): main of harness/rfc_level0_size.c against MainLib.main_core_spec R, at the compspecs of
   deflate.c + trees.c (DCS.CS; the body moves to the law's compspecs by entry_shared).  main draws the data and
   the parameters, calls deflateInit2_ (DSpec9's deflateInit2__spec_v9) and deflate() in a loop
   (DSpec.deflate_spec) through their shared specifications and the helpers of laws_common.h through theirs
   (laws_common/Spec.v), then checks the return code and total_out.  What main needs about the model runs is
   Level0CallsFit.l0_fit_facts for the harness's two parameters (the most blocks per call, l0s_kmax, and the
   least room beyond the size, l0s_slack), for an invariant J of the loop that the model theory chooses. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DCS Zlib.proof.deflate.DSpec Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.deflate.Level0CallsFit.
Require Zlib.contracts.rfc_level0_size.
Require Import Zlib.harness.rfc_level0_size.code.

(* main's callees *)
Definition Gmain : funspecs :=
  [deflateInit2__spec_v9; deflate_spec; upto_spec; clip_spec; any_bytes_spec; new_stream_spec;
   (_quickproof_malloc, @malloc_spec' DCS.CS); nondet_u32_spec; gp_assert_spec].

Definition vlit : ident := ___stringlit_rfc_level0_size_1.

(* the globals main gets: deflate.c's and the harness's string literal ZLIB_VERSION *)
Definition R (gv : globals) : mpred := (deflate_globals gv * version_at gv vlit)%logic.

(* the harness draws k = 1 + upto(65530) blocks per call and room = size + upto(SIZE_MAX - size) *)
Definition l0s_kmax : Z := 65531.
Definition l0s_slack : Z := 0.

Definition l0s2_main_stmt : Prop :=
  forall J, l0_fit_facts l0s_kmax l0s_slack J ->
  @semax_body (QPvarspecs Zlib.contracts.rfc_level0_size.whole_prog) Gmain DCS.CS f_main (_main, main_core_spec R).
