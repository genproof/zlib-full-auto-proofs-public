(* copy of cases5_DM for case LEN's fallthrough *)
(* inflate(), the switch cases DISTEXT, MATCH (23-24), version 5 (Delta_cases5, case_post2 over Model2.v, mwf3; header cases
   FLAGS .. COMMENT with the header buffers' tokens: CaseHyps5.v, CaseKitT5.v) *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate.CaseHyps5.
Require Import Zlib.proof.inflate.DmKit5 Zlib.proof.inflate.DxNb5 Zlib.proof.inflate.DxCase5
  Zlib.proof.inflate.MtLoopW5 Zlib.proof.inflate.MtLoopO5 Zlib.proof.inflate.CaseMATCH5.
#[local] Existing Instance Zlib.units.Inflate.CS.

Lemma ln_cases5_DM {Espec: OracleKind} (F: frame) : frame_ok5 F -> 
  (case_ok5 F MATCH 24 -> case_ok5 F DISTEXT 23) /\ case_ok5 F MATCH 24.
Proof.
  intros HF. split.
  - intros HM. exact (dx_case_ok dx_nb_ok Espec F HF HM).
  - exact (case_MATCH5 mt_loop_w_ok mt_loop_o_ok F HF).
Qed.
