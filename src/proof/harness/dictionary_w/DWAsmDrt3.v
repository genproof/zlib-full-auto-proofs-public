(* The law rt_dictionary, its assembly (DWAsmG.v): the entries of the third piece of deflate.c. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.EnvBodies.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.deflate.Obligations9.
Require Zlib.proof.inflate_api.SpecWLib.
Require Import Zlib.proof.harness.dictionary_w.DWCS.
Require Import Zlib.proof.harness.dictionary_w.DWAsmG.
Require Import Zlib.proof.harness.clip_streams.CS.
Require Import Zlib.proof.harness.clip_streams.Asm.
Require Import Zlib.proof.harness.dictionary_w.DWAsmKit.
#[local] Existing Instance Zlib.proof.harness.clip_streams.CS.CS.

Lemma drt_entries_defl3 : SWL.specw_lib_stmt -> entries_drt G_defl3.
Proof.
  intros [_ BR].
  destruct clip_deflate_bodies9 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                                    _ & _ & _ & _ & _ & _ & D19 & D20 & D21 & D22 & D23 & D24 & D25 & _).
  unfold Zlib.proof.deflate.Obligations.ob_deflateBound_z, Zlib.proof.deflate.Obligations.ob_deflateBound,
    Zlib.proof.deflate.Obligations.ob_deflateSetDictionary, Zlib.proof.deflate.Obligations.ob_deflateEnd,
    ob_deflateInit2_9, Zlib.proof.deflate.Obligations.ob_deflate,
    Zlib.proof.deflate.Obligations.ob_deflateParams in *.
  unfold entries_drt, G_defl3.
  clip_entry D19 BR.
  clip_entry D20 BR.
  clip_entry D21 BR.
  dw_entry D22 BR.
  dw_entry D23 BR.
  clip_entry D24 BR.
  clip_entry D25 BR.
  apply Forall_nil.
Qed.
