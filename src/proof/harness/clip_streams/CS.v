(* The laws rt_partial, rj_truncated, rj_bad_checksum and rfc_trailing_bytes: their programs and ONE compspecs for
   the four.  The four harnesses link the same units (adler32, crc32, deflate, trees, inflate, inffast, inftrees,
   zutil, libc) and define no struct of their own, so their programs have the same composites ([comps_same]);
   [CS] is built from them, with the moves of the shared specifications' compspecs (deflate's DCS.CS, the units'
   CS; Compress.CS for laws_common.h's new_stream) to it. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Assembly.
Require Zlib.contracts.rt_partial Zlib.contracts.rj_truncated Zlib.contracts.rj_bad_checksum.
Require Zlib.contracts.rfc_trailing_bytes.
Require Zlib.proof.deflate.DCS.
Require Zlib.units.Inflate Zlib.units.Adler32 Zlib.units.Crc32 Zlib.units.Zutil Zlib.units.Inffast
        Zlib.units.Inftrees Zlib.units.Compress.

Definition p_rp := Zlib.contracts.rt_partial.whole_prog.
Definition p_rt := Zlib.contracts.rj_truncated.whole_prog.
Definition p_bc := Zlib.contracts.rj_bad_checksum.whole_prog.
Definition p_tb := Zlib.contracts.rfc_trailing_bytes.whole_prog.

Definition comps := ltac:(let x := eval vm_compute in (prog_composites p_rp) in exact x).

Lemma comps_same :
  prog_composites p_rp = comps /\ prog_composites p_rt = comps /\
  prog_composites p_bc = comps /\ prog_composites p_tb = comps.
Proof. repeat split; vm_compute; reflexivity. Qed.

Definition cprog : Clight.program := Clightdefs.mkprogram comps nil nil 1%positive Logic.I.
#[export] Instance CS : compspecs. make_compspecs cprog. Defined.
#[export] Instance CC_dcs : change_composite_env Zlib.proof.deflate.DCS.CS CS.
  make_cs_preserve Zlib.proof.deflate.DCS.CS CS. Defined.
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

Lemma dcs_sub : cspecs_sub Zlib.proof.deflate.DCS.CS CS.
Proof. apply cspecs_sub_by_computation; vm_compute; reflexivity. Qed.
Lemma inflate_sub : cspecs_sub Zlib.units.Inflate.CS CS.
Proof. apply cspecs_sub_by_computation; vm_compute; reflexivity. Qed.
