(* RT-H: cases NAME, COMMENT (indices 6-7) with a partial gz_header attached (RTHCase.case_ok6). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.roundtrip.RTHSpec.
Require Import Zlib.proof.roundtrip.RTHCase.
Require Import Zlib.proof.roundtrip.RTHCaseNAME6.
Require Import Zlib.proof.roundtrip.RTHCaseCOMMENT6.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Lemma rth_nc : rth_nc_stmt.
Proof.
  intros Espec F FOK. split; [apply case_NAME6 | apply case_COMMENT6]; exact FOK.
Qed.
