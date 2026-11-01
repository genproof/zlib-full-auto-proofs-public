(* inflate(), the switch cases FLAGS, TIME, OS (1-3), version 5 (Delta_cases5, case_post2 over Model2.v, mwf3; header cases
   FLAGS .. COMMENT with the header buffers' tokens: CaseHyps5.v, CaseKitT5.v) *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate.CaseHyps5.
Require Import Zlib.proof.inflate.CaseFLAGS5.
Require Import Zlib.proof.inflate.CaseTIME5.
Require Import Zlib.proof.inflate.CaseOS5.
#[local] Existing Instance Zlib.units.Inflate.CS.

Lemma cases5_FTO {Espec: OracleKind} (F: frame) : frame_ok5 F -> 
  (case_okT5 F TIME 2 -> case_okT5 F FLAGS 1) /\ (case_okT5 F OS 3 -> case_okT5 F TIME 2) /\ (case_okT5 F EXLEN 4 -> case_okT5 F OS 3).
Proof.
  intros FOK. split; [ | split].
  - apply case_FLAGS5; exact FOK.
  - apply case_TIME5; exact FOK.
  - apply case_OS5; exact FOK.
Qed.
