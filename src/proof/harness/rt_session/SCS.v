(* Law rt_session (harness/rt_session.c): its program, its compspecs (the composites of the program: z_stream_s,
   the deflate_state's, inflate_state, code, ...) and the moves of the shared specifications' compspecs to it
   (DCS.CS: deflate.c + trees.c; the units' CS of adler32.c, crc32.c, zutil.c, inflate.c, inffast.c, inftrees.c;
   Compress.CS for the laws_common.h helpers offer and new_stream; laws_session's CS_session for the helpers of
   laws_session.h: position_of, unmoved and accounted read the struct position main keeps on its stack). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Assembly.
Require Zlib.contracts.rt_session.
Require Zlib.proof.deflate.DCS.
Require Zlib.units.Adler32 Zlib.units.Crc32 Zlib.units.Zutil Zlib.units.Inflate Zlib.units.Inffast
        Zlib.units.Inftrees Zlib.units.Compress.
Require Zlib.proof.harness.laws_session.Spec.

Definition p := Zlib.contracts.rt_session.whole_prog.
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
#[export] Instance CC_inflate : change_composite_env Zlib.units.Inflate.CS CS.
  make_cs_preserve Zlib.units.Inflate.CS CS. Defined.
#[export] Instance CC_inffast : change_composite_env Zlib.units.Inffast.CS CS.
  make_cs_preserve Zlib.units.Inffast.CS CS. Defined.
#[export] Instance CC_inftrees : change_composite_env Zlib.units.Inftrees.CS CS.
  make_cs_preserve Zlib.units.Inftrees.CS CS. Defined.
#[export] Instance CC_compress : change_composite_env Zlib.units.Compress.CS CS.
  make_cs_preserve Zlib.units.Compress.CS CS. Defined.
#[export] Instance CC_session : change_composite_env Zlib.proof.harness.laws_session.Spec.CS_session CS.
  make_cs_preserve Zlib.proof.harness.laws_session.Spec.CS_session CS. Defined.

Lemma dcs_sub : cspecs_sub Zlib.proof.deflate.DCS.CS CS.
Proof. apply cspecs_sub_by_computation; vm_compute; reflexivity. Qed.

Lemma ics_sub : cspecs_sub Zlib.units.Inflate.CS CS.
Proof. apply cspecs_sub_by_computation; vm_compute; reflexivity. Qed.
