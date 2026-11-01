(** * v9 obligations: deflateResetKeep, deflateReset, deflateInit2_ against the v9 specs (DSpec9.v)

    Obligations.v (v8) states every body obligation; v9 (compress2's uninitialised stream) changed the
    specs of these three functions.  [deflate_bodies_ok9] is [Obligations.deflate_bodies_ok] with the three v9
    obligations in place of the v8 ones; the laws are proved from it ([Laws9.deflate_laws9]). *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.DSpec Zlib.proof.deflate.DSpec9.
Require Export Zlib.proof.deflate.Obligations.
Require Zlib.deflate.code.

Definition ob_deflateResetKeep9 : Prop :=
  @semax_body DSpec.Vprog Gprog_deflateResetKeep_v9 DCS.CS Zlib.deflate.code.f_deflateResetKeep deflateResetKeep_spec_v9.
Definition ob_deflateReset9 : Prop :=
  @semax_body DSpec.Vprog Gprog_deflateReset_v9 DCS.CS Zlib.deflate.code.f_deflateReset deflateReset_spec_v9.
Definition ob_deflateInit2_9 : Prop :=
  @semax_body DSpec.Vprog Gprog_deflateInit2__v9 DCS.CS Zlib.deflate.code.f_deflateInit2_ deflateInit2__spec_v9.

Definition deflate_bodies_ok9 : Prop :=
  ob_read_buf /\
  ob_putShortMSB /\
  ob_flush_pending /\
  ob_slide_hash /\
  ob_longest_match /\
  ob_lm_init /\
  ob_fill_window /\
  ob_deflate_stored /\
  ob_deflate_fast /\
  ob_deflate_slow /\
  ob_deflate_rle /\
  ob_deflate_huff /\
  ob_deflateStateCheck /\
  ob_deflateResetKeep9 /\
  ob_deflateReset9 /\
  ob_deflateSetHeader /\
  ob_deflateTune /\
  ob_deflatePrime /\
  ob_deflateBound_z /\
  ob_deflateBound /\
  ob_deflateSetDictionary /\
  ob_deflateEnd /\
  ob_deflateInit2_9 /\
  ob_deflate /\
  ob_deflateParams /\
  ob_compressBound_z /\ ob_compressBound /\ ob_dstream_to_end.
