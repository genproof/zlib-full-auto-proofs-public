(* The law rt_dictionary, its assembly (DWAsmG.v): the entries of the second piece of deflate.c. *)
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
#[local] Existing Instance Zlib.proof.harness.clip_streams.CS.CS.

Lemma drt_entries_defl2 : SWL.specw_lib_stmt -> entries_drt G_defl2.
Proof.
  intros [_ BR].
  destruct clip_deflate_bodies9 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                                    D13 & D14 & D15 & D16 & D17 & D18 & _).
  unfold Zlib.proof.deflate.Obligations.ob_deflateStateCheck, ob_deflateResetKeep9, ob_deflateReset9,
    Zlib.proof.deflate.Obligations.ob_deflateSetHeader, Zlib.proof.deflate.Obligations.ob_deflateTune,
    Zlib.proof.deflate.Obligations.ob_deflatePrime in *.
  unfold entries_drt, G_defl2.
  clip_entry D13 BR.
  clip_entry D14 BR.
  clip_entry D15 BR.
  clip_entry D16 BR.
  clip_entry D17 BR.
  clip_entry D18 BR.
  apply Forall_nil.
Qed.
