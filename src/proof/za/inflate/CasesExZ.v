(* The switch cases EXLEN, EXTRA of inflate() in the allocator-generic port: the generated Cases5_EX.v (patches in docs/port-za/inflate/cases_ex.py). *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.za.inflate.CaseHyps5.
Require Import Zlib.proof.zutil.ZAlloc.
Require Import Zlib.proof.za.inflate.ZAV.
Require Zlib.proof.za.inflate.Cases5_EX.
#[local] Existing Instance Zlib.units.Inflate.CS.

Section ZAlloc.
Context {ZA : zallocator} {ZAV : adler_cell}.

Lemma za_cases5_EX {Espec: OracleKind} (F: frame) : frame_ok5 F ->
  (case_okT5_za F EXTRA 5 -> case_okT5_za F EXLEN 4) /\ (case_okT5_za F NAME 6 -> case_okT5_za F EXTRA 5).
Proof. exact (Zlib.proof.za.inflate.Cases5_EX.cases5_EX_za (ZA:=ZA) (ZAV:=ZAV) F). Qed.

End ZAlloc.
