(* RT-H: mechanical port of inflate/CaseHyps.v to the header-external loop state (RTHLoop.v); identifiers whose meaning changes carry the suffix H. *)
(* The hypotheses the case lemmas of inflate()'s switch may use (discharged by the body assembly), and
   the statement that every case is proved (cases_allH). *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Export Zlib.proof.roundtrip.RTHCaseKit.
Require Export Zlib.proof.inflate.CaseHyps.
#[local] Existing Instance Zlib.units.Inflate.CS.

(* the case lemma of every mode HEAD .. SYNC (index i = mode - HEAD) *)
Definition cases_allH : Prop :=
  forall {Espec: OracleKind} (F: frame), frame_ok F -> forall i, (i < 32)%nat -> case_okH F (HEAD + Z.of_nat i) i.
