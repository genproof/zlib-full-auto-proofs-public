(* Laws res_free_deflate and res_memory_deflate: the compspecs of main's proof, [CSa], the composites of the law's
   program (z_stream_s, the deflate_state's, struct count, ...: the same for both programs, which link the same
   units), and the moves to it from the compspecs of the shared specifications: deflate.c + trees.c (DCS.CS),
   the compress unit (laws_common's offer, counted_stream), the adler32 unit (laws_common's byte helpers) and
   the harness unit (the counting allocator, CS_count). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Assembly.
Require Zlib.contracts.res_free_deflate Zlib.contracts.res_memory_deflate.
Require Zlib.proof.deflate.DCS.
Require Zlib.units.Adler32 Zlib.units.Compress.
Require Zlib.proof.harness.counted.Spec.

Definition comps := ltac:(let x := eval vm_compute in (prog_composites Zlib.contracts.res_free_deflate.whole_prog)
  in exact x).
Definition cprog : Clight.program := Clightdefs.mkprogram comps nil nil 1%positive Logic.I.
#[export] Instance CSa : compspecs. make_compspecs cprog. Defined.

#[export] Instance CC_dcs : change_composite_env Zlib.proof.deflate.DCS.CS CSa.
  make_cs_preserve Zlib.proof.deflate.DCS.CS CSa. Defined.
#[export] Instance CC_compress : change_composite_env Zlib.units.Compress.CS CSa.
  make_cs_preserve Zlib.units.Compress.CS CSa. Defined.
#[export] Instance CC_adler32 : change_composite_env Zlib.units.Adler32.CS CSa.
  make_cs_preserve Zlib.units.Adler32.CS CSa. Defined.
#[export] Instance CC_count : change_composite_env Zlib.proof.harness.counted.Spec.CS_count CSa.
  make_cs_preserve Zlib.proof.harness.counted.Spec.CS_count CSa. Defined.

(* The two programs have the same composites: CSa is the compspecs of either. *)
Lemma comps_memory :
  prog_composites Zlib.contracts.res_memory_deflate.whole_prog = prog_composites Zlib.contracts.res_free_deflate.whole_prog.
Proof. vm_compute. reflexivity. Qed.
