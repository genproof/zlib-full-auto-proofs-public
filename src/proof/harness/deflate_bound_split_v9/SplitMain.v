(* Law deflate_bound_split: the definitions for the main of harness/deflate_bound_split.c (its body:
   SplitBody.v), proved under DCS.CS (the composites of
   deflate.c + trees.c: z_stream_s, gz_header_s; QuickProof.Assembly moves it into the law's compspecs) against
   MainLib.main_core_spec with the resources of GlobalsInit (deflate_globals and the "1.3.2" literal), for ANY
   invariants Bpre Brun satisfying LawFacts.bound_facts. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DCS Zlib.proof.deflate.DSpec Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.deflate.LawFacts Zlib.proof.deflate.HarnessLib Zlib.proof.deflate.GlobalsInit.
Require Zlib.contracts.x_deflate_bound_split.
Require Zlib.proof.deflate.Obligations.
Require Import Zlib.harness.x_deflate_bound_split.code.
#[local] Existing Instance DCS.CS.

Definition p := Zlib.contracts.x_deflate_bound_split.whole_prog.

Definition vlit : ident := ___stringlit_x_deflate_bound_split_1.

(* main's resources: the globals of the shared specifications and the version literal *)
Definition Rm (gv : globals) : mpred := (deflate_globals gv * version_at gv vlit)%logic.

(* main's callees *)
Definition Gmain : funspecs :=
  [deflate_params_ok_spec; draw_nonzero_bytes_spec; stream_defaults_spec; exact_copy_spec; exact_space_spec;
   deflateInit2__spec_v9; deflateSetDictionary_spec; deflateSetHeader_spec; deflateBound_spec; deflate_spec;
   deflateEnd_spec;
   (_quickproof_malloc, malloc_spec'); (_quickproof_free, free_spec');
   nondet_u32_spec; nondet_u8_spec; nondet_bytes_spec; gp_assert_spec; gp_assume_spec].
