(* inflate(), the switch cases STORED, COPY_, COPY (13-15), version 5 (Delta_cases5, case_post2 over Model2.v, mwf3; header cases
   FLAGS .. COMMENT with the header buffers' tokens: CaseHyps5.v, CaseKitT5.v) *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate.CaseHyps5.
Require Import Zlib.proof.inflate.CaseSTORED5 Zlib.proof.inflate.CaseCOPY5.
#[local] Existing Instance Zlib.units.Inflate.CS.

Lemma cases5_ST {Espec: OracleKind} (F: frame) : frame_ok5 F -> 
  (case_ok5 F COPY_ 14 -> case_ok5 F STORED 13) /\ (case_ok5 F COPY 15 -> case_ok5 F COPY_ 14) /\ case_ok5 F COPY 15.
Proof.
  intros HF. split; [ | split].
  - apply case_STORED5; exact HF.
  - apply case_COPY_5.
  - apply case_COPY5; exact HF.
Qed.
