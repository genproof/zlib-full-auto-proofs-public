(* Law api_inflate_any: its program and compspecs (the composites of the program), and the moves of the shared
   specifications' compspecs (the units' CS) to it; as inflate_pieces/LawCS.v does for the three laws of the
   same loop (rj_any_input, api_counters, api_untouched_output). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Assembly.
Require Zlib.contracts.api_inflate_any.
Require Zlib.units.Inflate.
Require Zlib.units.Adler32.
Require Zlib.units.Crc32.
Require Zlib.units.Zutil.
Require Zlib.units.Inffast.
Require Zlib.units.Inftrees.
Require Zlib.units.Compress.

Module Aia.
Definition p := Zlib.contracts.api_inflate_any.whole_prog.
Definition comps := ltac:(let x := eval vm_compute in (prog_composites p) in exact x).
Definition cprog : Clight.program := Clightdefs.mkprogram comps nil nil 1%positive Logic.I.
#[export] Instance CS : compspecs. make_compspecs cprog. Defined.
#[export] Instance CC_inflate : change_composite_env Zlib.units.Inflate.CS CS.
  make_cs_preserve Zlib.units.Inflate.CS CS. Defined.
#[export] Instance CC_adler32 : change_composite_env Zlib.units.Adler32.CS CS.
  make_cs_preserve Zlib.units.Adler32.CS CS. Defined.
#[export] Instance CC_crc32 : change_composite_env Zlib.units.Crc32.CS CS.
  make_cs_preserve Zlib.units.Crc32.CS CS. Defined.
#[export] Instance CC_zutil : change_composite_env Zlib.units.Zutil.CS CS.
  make_cs_preserve Zlib.units.Zutil.CS CS. Defined.
#[export] Instance CC_inffast : change_composite_env Zlib.units.Inffast.CS CS.
  make_cs_preserve Zlib.units.Inffast.CS CS. Defined.
#[export] Instance CC_inftrees : change_composite_env Zlib.units.Inftrees.CS CS.
  make_cs_preserve Zlib.units.Inftrees.CS CS. Defined.
#[export] Instance CC_compress : change_composite_env Zlib.units.Compress.CS CS.
  make_cs_preserve Zlib.units.Compress.CS CS. Defined.
End Aia.
