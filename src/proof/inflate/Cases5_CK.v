(* inflate(), the switch cases CHECK, LENGTH (26-27), version 5 (Delta_cases5, case_post2 over Model2.v, mwf3; header cases
   FLAGS .. COMMENT with the header buffers' tokens: CaseHyps5.v, CaseKitT5.v) *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate.CaseHyps5.
Require Import Zlib.proof.inflate.CaseCHECK5 Zlib.proof.inflate.CaseLENGTH5.
#[local] Existing Instance Zlib.units.Inflate.CS.

Lemma cases5_CK {Espec: OracleKind} (F: frame) : frame_ok5 F -> 
  (case_ok5 F LENGTH 27 -> case_ok5 F CHECK 26) /\ (case_ok5 F DONE 28 -> case_ok5 F LENGTH 27).
Proof.
  intros FOK. split; [apply case_CHECK5 | apply case_LENGTH5]; exact FOK.
Qed.
