(* Law rj_bad_level: its program, its compspecs (the composites of the program: z_stream_s and the
   deflate_state's) and the moves of the shared specifications' compspecs (deflate's DCS.CS, the units' CS:
   adler32's for laws_common.h's byte helpers, compress's for compress2) to it. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Assembly.
Require Zlib.contracts.rj_bad_level.
Require Zlib.proof.deflate.DCS.
Require Zlib.units.Adler32 Zlib.units.Crc32 Zlib.units.Zutil Zlib.units.Compress.

Definition p := Zlib.contracts.rj_bad_level.whole_prog.
Definition comps := ltac:(let x := eval vm_compute in (prog_composites p) in exact x).
Definition cprog : Clight.program := Clightdefs.mkprogram comps nil nil 1%positive Logic.I.
#[export] Instance CS : compspecs. make_compspecs cprog. Defined.
#[export] Instance CC_dcs : change_composite_env Zlib.proof.deflate.DCS.CS CS.
  make_cs_preserve Zlib.proof.deflate.DCS.CS CS. Defined.
#[export] Instance CC_adler32 : change_composite_env Zlib.units.Adler32.CS CS.
  make_cs_preserve Zlib.units.Adler32.CS CS. Defined.
#[export] Instance CC_crc32 : change_composite_env Zlib.units.Crc32.CS CS.
  make_cs_preserve Zlib.units.Crc32.CS CS. Defined.
#[export] Instance CC_zutil : change_composite_env Zlib.units.Zutil.CS CS.
  make_cs_preserve Zlib.units.Zutil.CS CS. Defined.
#[export] Instance CC_compress : change_composite_env Zlib.units.Compress.CS CS.
  make_cs_preserve Zlib.units.Compress.CS CS. Defined.
