(* Law uncompress_any: its program and compspecs (the composites of the program), and the moves of the shared
   specifications' compspecs (the units' CS) to it (as inflate_codes/LawCS.v, plus the uncompr unit). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Assembly.
Require Zlib.contracts.x_uncompress_any.
Require Zlib.units.Inflate Zlib.units.Adler32 Zlib.units.Crc32 Zlib.units.Zutil Zlib.units.Inffast
        Zlib.units.Inftrees Zlib.units.Uncompr.

Definition p := Zlib.contracts.x_uncompress_any.whole_prog.
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
#[export] Instance CC_uncompr : change_composite_env Zlib.units.Uncompr.CS CS.
  make_cs_preserve Zlib.units.Uncompr.CS CS. Defined.
