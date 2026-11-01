(* inflate(), the switch cases EXLEN, EXTRA (4-5), version 5 (Delta_cases5, case_post2 over Model2.v, mwf3; header cases
   FLAGS .. COMMENT with the header buffers' tokens: CaseHyps5.v, CaseKitT5.v) *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate.CaseHyps5.
Require Import Zlib.proof.inflate.CaseEXLEN5.
Require Import Zlib.proof.inflate.CaseEXTRA5.
#[local] Existing Instance Zlib.units.Inflate.CS.

Lemma cases5_EX {Espec: OracleKind} (F: frame) : frame_ok5 F -> 
  (case_okT5 F EXTRA 5 -> case_okT5 F EXLEN 4) /\ (case_okT5 F NAME 6 -> case_okT5 F EXTRA 5).
Proof.
  intros FOK. split.
  - apply case_EXLEN5; exact FOK.
  - apply case_EXTRA5; exact FOK.
Qed.
