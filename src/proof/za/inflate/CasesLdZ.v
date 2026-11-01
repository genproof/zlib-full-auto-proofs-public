(* The switch cases LENEXT, DIST of inflate() in the allocator-generic port: the generated Cases5_LD.v (patches in docs/port-za/inflate/cases_ld.py). *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.za.inflate.CaseHyps5.
Require Import Zlib.proof.zutil.ZAlloc.
Require Import Zlib.proof.za.inflate.ZAV.
Require Zlib.proof.za.inflate.Cases5_LD.
#[local] Existing Instance Zlib.units.Inflate.CS.

Section ZAlloc.
Context {ZA : zallocator} {ZAV : adler_cell}.

Lemma za_cases5_LD {Espec: OracleKind} (F: frame) : frame_ok5 F ->
  (case_ok5_za F DIST 22 -> case_ok5_za F LENEXT 21) /\ (case_ok5_za F DISTEXT 23 -> case_ok5_za F DIST 22).
Proof. exact (Zlib.proof.za.inflate.Cases5_LD.cases5_LD_za (ZA:=ZA) (ZAV:=ZAV) F). Qed.

End ZAlloc.
