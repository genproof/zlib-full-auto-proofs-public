(* The switch cases CHECK, LENGTH of inflate() in the allocator-generic port: the generated Cases5_CK.v (patches in docs/port-za/inflate/cases_ck.py). *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.za.inflate.CaseHyps5.
Require Import Zlib.proof.zutil.ZAlloc.
Require Import Zlib.proof.za.inflate.ZAV.
Require Zlib.proof.za.inflate.Cases5_CK.
#[local] Existing Instance Zlib.units.Inflate.CS.

Section ZAlloc.
Context {ZA : zallocator} {ZAV : adler_cell}.

Lemma za_cases5_CK {Espec: OracleKind} (F: frame) : frame_ok5 F ->
  (case_ok5_za F LENGTH 27 -> case_ok5_za F CHECK 26) /\ (case_ok5_za F DONE 28 -> case_ok5_za F LENGTH 27).
Proof. exact (@Zlib.proof.za.inflate.Cases5_CK.cases5_CK_za ZA ZAV Espec F). Qed.

End ZAlloc.
