(* Law api_deterministic (data of any length): its program, its compspecs (the composites of the program:
   z_stream_s, gz_header_s, the deflate_state's) and the moves of the shared specifications' compspecs to it (DCS.CS: deflate.c +
   trees.c; the units' CS; the compress unit's for laws_common.h's offer and new_stream, whose only struct is
   z_stream_s). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Assembly.
Require Zlib.contracts.api_deterministic.
Require Zlib.proof.deflate.DCS.
Require Zlib.units.Adler32.
Require Zlib.units.Crc32.
Require Zlib.units.Zutil.
Require Zlib.units.Compress.

Definition p := Zlib.contracts.api_deterministic.whole_prog.
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
(* main's body is proved at DCS.CS; it calls laws_common.h's helpers, specified at the compress unit's (offer,
   new_stream) and at the adler32 unit's compspecs (upto, any_bytes, copy_of, bytes_eq) *)
#[export] Instance CC_compress_dcs : change_composite_env Zlib.units.Compress.CS Zlib.proof.deflate.DCS.CS.
  make_cs_preserve Zlib.units.Compress.CS Zlib.proof.deflate.DCS.CS. Defined.
#[export] Instance CC_adler32_dcs : change_composite_env Zlib.units.Adler32.CS Zlib.proof.deflate.DCS.CS.
  make_cs_preserve Zlib.units.Adler32.CS Zlib.proof.deflate.DCS.CS. Defined.
