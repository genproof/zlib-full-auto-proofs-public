(* Law deflate_bound: its program, its compspecs (the composites of the program: z_stream_s, gz_header_s, the
   deflate_state's) and the moves of the shared specifications' compspecs (DCS.CS: deflate.c + trees.c, the
   units' CS) to it. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Assembly.
Require Zlib.contracts.x_deflate_bound.
Require Zlib.proof.deflate.DCS.
Require Zlib.units.Adler32 Zlib.units.Crc32 Zlib.units.Zutil Zlib.units.Compress.

Definition p := Zlib.contracts.x_deflate_bound.whole_prog.
Definition comps := ltac:(let x := eval vm_compute in (prog_composites p) in exact x).
Definition cprog : Clight.program := Clightdefs.mkprogram comps nil nil 1%positive Logic.I.
#[export] Instance CS : compspecs. make_compspecs cprog. Defined.
#[export] Instance CC_dcs : change_composite_env Zlib.proof.deflate.DCS.CS CS.
  make_cs_preserve Zlib.proof.deflate.DCS.CS CS. Defined.
#[export] Instance CC_adler32 : change_composite_env Zlib.units.Adler32.CS CS.
  make_cs_preserve Zlib.units.Adler32.CS CS. Defined.
#[export] Instance CC_crc32 : change_composite_env Zlib.units.Crc32.CS CS.
  make_cs_preserve Zlib.units.Crc32.CS CS. Defined.
#[export] Instance CC_compress : change_composite_env Zlib.units.Compress.CS CS.
  make_cs_preserve Zlib.units.Compress.CS CS. Defined.

Lemma dcs_sub : cspecs_sub Zlib.proof.deflate.DCS.CS CS.
Proof. apply cspecs_sub_by_computation; vm_compute; reflexivity. Qed.
