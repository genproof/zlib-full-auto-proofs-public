(* Laws res_free_inflate and res_memory_inflate: the compspecs of main's proof, [CSi], the composites of the
   law's program (z_stream_s, inflate_state, code, gz_header, struct count: the same for both programs, which
   link the same units), and the moves to it from the compspecs of the shared specifications: the inflate unit
   (inflate.c's specifications), the compress unit (laws_common's offer, counted_stream), the adler32 unit
   (laws_common's byte helpers) and the harness unit of the counting allocator (CS_count). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Assembly.
Require Zlib.contracts.res_free_inflate Zlib.contracts.res_memory_inflate.
Require Zlib.units.Inflate Zlib.units.Adler32 Zlib.units.Compress.
Require Zlib.proof.harness.counted.Spec.

Definition comps := ltac:(let x := eval vm_compute in (prog_composites Zlib.contracts.res_free_inflate.whole_prog)
  in exact x).
Definition cprog : Clight.program := Clightdefs.mkprogram comps nil nil 1%positive Logic.I.
#[export] Instance CSi : compspecs. make_compspecs cprog. Defined.

#[export] Instance CC_inflate : change_composite_env Zlib.units.Inflate.CS CSi.
  make_cs_preserve Zlib.units.Inflate.CS CSi. Defined.
#[export] Instance CC_compress : change_composite_env Zlib.units.Compress.CS CSi.
  make_cs_preserve Zlib.units.Compress.CS CSi. Defined.
#[export] Instance CC_adler32 : change_composite_env Zlib.units.Adler32.CS CSi.
  make_cs_preserve Zlib.units.Adler32.CS CSi. Defined.
#[export] Instance CC_count : change_composite_env Zlib.proof.harness.counted.Spec.CS_count CSi.
  make_cs_preserve Zlib.proof.harness.counted.Spec.CS_count CSi. Defined.

(* The two programs have the same composites: CSi is the compspecs of either. *)
Lemma comps_memory :
  prog_composites Zlib.contracts.res_memory_inflate.whole_prog = prog_composites Zlib.contracts.res_free_inflate.whole_prog.
Proof. vm_compute. reflexivity. Qed.
