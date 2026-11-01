(* The switch cases TABLE, LENLENS of inflate() in the allocator-generic port: the generated Cases5_TL.v (patches in docs/port-za/inflate/cases_tl.py). *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.za.inflate.CaseHyps5.
Require Import Zlib.proof.zutil.ZAlloc.
Require Import Zlib.proof.za.inflate.ZAV.
Require Zlib.proof.za.inflate.Cases5_TL.
#[local] Existing Instance Zlib.units.Inflate.CS.

Section ZAlloc.
Context {ZA : zallocator} {ZAV : adler_cell}.

Lemma za_cases5_TL {Espec: OracleKind} (F: frame) : frame_ok5 F -> cover3_stmt ->
  (case_ok5_za F LENLENS 17 -> case_ok5_za F TABLE 16) /\ (case_ok5_za F CODELENS 18 -> case_ok5_za F LENLENS 17).
Proof. exact (Zlib.proof.za.inflate.Cases5_TL.cases5_TL_za (ZA:=ZA) (ZAV:=ZAV) F). Qed.

End ZAlloc.
