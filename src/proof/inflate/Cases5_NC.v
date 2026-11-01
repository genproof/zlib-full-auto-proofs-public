(* inflate(), the switch cases NAME, COMMENT (6-7), version 5 (Delta_cases5, case_post2 over Model2.v, mwf3; header cases
   FLAGS .. COMMENT with the header buffers' tokens: CaseHyps5.v, CaseKitT5.v) *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate.CaseHyps5.
Require Import Zlib.proof.inflate.CaseNAME5.
Require Import Zlib.proof.inflate.CaseCOMMENT5.
#[local] Existing Instance Zlib.units.Inflate.CS.

Lemma cases5_NC {Espec: OracleKind} (F: frame) : frame_ok5 F -> 
  (case_okT5 F COMMENT 7 -> case_okT5 F NAME 6) /\ (case_ok5 F HCRC 8 -> case_okT5 F COMMENT 7).
Proof.
  intros FOK. split.
  - apply case_NAME5; exact FOK.
  - apply case_COMMENT5; exact FOK.
Qed.
