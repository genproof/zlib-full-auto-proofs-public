(* Law rj_inflate_params: its program and compspecs (the composites of the program), and the moves of the
   shared specifications' compspecs to it: the inflate unit's (inflateInit2_) and the compress unit's, at which
   laws_common.h's new_stream is specified (struct z_stream_s only). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Assembly.
Require Zlib.contracts.rj_inflate_params.
Require Zlib.units.Inflate Zlib.units.Compress.

Definition p := Zlib.contracts.rj_inflate_params.whole_prog.
Definition comps := ltac:(let x := eval vm_compute in (prog_composites p) in exact x).
Definition cprog : Clight.program := Clightdefs.mkprogram comps nil nil 1%positive Logic.I.
#[export] Instance CS : compspecs. make_compspecs cprog. Defined.
#[export] Instance CC_inflate : change_composite_env Zlib.units.Inflate.CS CS.
  make_cs_preserve Zlib.units.Inflate.CS CS. Defined.
#[export] Instance CC_compress : change_composite_env Zlib.units.Compress.CS CS.
  make_cs_preserve Zlib.units.Compress.CS CS. Defined.
