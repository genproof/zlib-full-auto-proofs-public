(* The switch cases TYPE, TYPEDO of inflate() in the allocator-generic port: the generated Cases5_TY.v (patches in docs/port-za/inflate/cases_ty.py). *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.za.inflate.CaseHyps5.
Require Import Zlib.proof.zutil.ZAlloc.
Require Import Zlib.proof.za.inflate.ZAV.
Require Zlib.proof.za.inflate.Cases5_TY.
#[local] Existing Instance Zlib.units.Inflate.CS.

Section ZAlloc.
Context {ZA : zallocator} {ZAV : adler_cell}.

Lemma za_cases5_TY {Espec: OracleKind} (F: frame) : frame_ok5 F -> fixed_ok5 ->
  case_ok5_za F Zlib.proof.inflate.Model.TYPE 11 /\ case_ok5_za F TYPEDO 12.
Proof. exact (@Zlib.proof.za.inflate.Cases5_TY.cases5_TY_za ZA ZAV Espec F). Qed.

End ZAlloc.
