(* The switch case CODELENS of inflate() in the allocator-generic port: the generated Cases5_CL.v (patches in docs/port-za/inflate/cases_cl.py). *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.za.inflate.CaseHyps5.
Require Import Zlib.proof.zutil.ZAlloc.
Require Import Zlib.proof.za.inflate.ZAV.
Require Zlib.proof.za.inflate.Cases5_CL.
#[local] Existing Instance Zlib.units.Inflate.CS.

Section ZAlloc.
Context {ZA : zallocator} {ZAV : adler_cell}.

Lemma za_cases5_CL {Espec: OracleKind} (F: frame) : frame_ok5 F -> cover3_stmt ->
  (case_ok5_za F LEN_ 19 -> case_ok5_za F CODELENS 18).
Proof.
  exact (@Zlib.proof.za.inflate.Cases5_CL.cases5_CL_za ZA ZAV Espec F).
Qed.

End ZAlloc.
