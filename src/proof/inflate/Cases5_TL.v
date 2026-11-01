(* inflate(), the switch cases TABLE, LENLENS (16-17), version 5 (Delta_cases5, case_post2 over Model2.v, mwf3; header cases
   FLAGS .. COMMENT with the header buffers' tokens: CaseHyps5.v, CaseKitT5.v) *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate.CaseHyps5.
Require Import Zlib.proof.inflate.CaseTABLE5 Zlib.proof.inflate.CaseLENLENS5.
#[local] Existing Instance Zlib.units.Inflate.CS.

Lemma cases5_TL {Espec: OracleKind} (F: frame) : frame_ok5 F -> cover3_stmt ->
  (case_ok5 F LENLENS 17 -> case_ok5 F TABLE 16) /\ (case_ok5 F CODELENS 18 -> case_ok5 F LENLENS 17).
Proof.
  intros HF C3. split; [apply case_TABLE5; exact HF | apply case_LENLENS5; assumption].
Qed.
