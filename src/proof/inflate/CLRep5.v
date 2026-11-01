(* case CODELENS: the repeat codes 16 / 17 / 18 with the variable NEEDBITS(here.bits + 2/3/7) (CLKit5.cl_rep, cl_rep_m) *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate.CLKit5.
Require Import Zlib.proof.inflate.CLRepNB5.
Require Import Zlib.proof.inflate.MwfLemmas.
Require Import Zlib.proof.inflate.CLRepBr5.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Lemma cl_rep_ok : cl_rep_stmt.
Proof.
  intros Espec F m here HF W HM HL HE HB HB15 HV HH.
  rewrite <- (cl_rep_post_eq F m here). rewrite cl_rep_eq.
  pose proof HE as (Eo & Eb & Ev).
  unfold loop_state_h at 1, loop_locals. unfold ent at 1. unfold cl_rep_post. abbreviate_semax.
  forward. { entailer!. rep_lia. }
  forward_if.
  - eapply semax_pre; [ | apply cl_r16_ok; auto].
    unfold loop_state_h, loop_locals. entailer!.
  - forward. forward_if.
    + eapply semax_pre; [ | apply cl_r17_ok; auto].
      unfold loop_state_h, loop_locals. entailer!.
    + eapply semax_pre; [ | apply cl_r18_ok; auto].
      unfold loop_state_h, loop_locals. entailer!.
Qed.
