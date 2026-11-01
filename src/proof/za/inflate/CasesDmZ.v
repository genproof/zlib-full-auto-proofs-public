(* The switch cases DISTEXT, MATCH of inflate() in the allocator-generic port: the generated Cases5_DM.v (patches in docs/port-za/inflate/cases_dm.py). *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.za.inflate.CaseHyps5.
Require Import Zlib.proof.zutil.ZAlloc.
Require Import Zlib.proof.za.inflate.ZAV.
Require Zlib.proof.za.inflate.Cases5_DM.
#[local] Existing Instance Zlib.units.Inflate.CS.

Section ZAlloc.
Context {ZA : zallocator} {ZAV : adler_cell}.

Lemma za_cases5_DM {Espec: OracleKind} (F: frame) : frame_ok5 F ->
  (case_ok5_za F MATCH 24 -> case_ok5_za F DISTEXT 23) /\ case_ok5_za F MATCH 24.
Proof. exact (Zlib.proof.za.inflate.Cases5_DM.cases5_DM_za (ZA:=ZA) (ZAV:=ZAV) F). Qed.

End ZAlloc.
