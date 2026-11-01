(* The switch cases FLAGS, TIME, OS of inflate() in the allocator-generic port: the generated Cases5_FTO.v (patches in docs/port-za/inflate/cases_fto.py). *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.za.inflate.CaseHyps5.
Require Import Zlib.proof.zutil.ZAlloc.
Require Import Zlib.proof.za.inflate.ZAV.
Require Zlib.proof.za.inflate.Cases5_FTO.
#[local] Existing Instance Zlib.units.Inflate.CS.

Section ZAlloc.
Context {ZA : zallocator} {ZAV : adler_cell}.

Lemma za_cases5_FTO {Espec: OracleKind} (F: frame) : frame_ok5 F ->
  (case_okT5_za F TIME 2 -> case_okT5_za F FLAGS 1) /\ (case_okT5_za F OS 3 -> case_okT5_za F TIME 2) /\
  (case_okT5_za F EXLEN 4 -> case_okT5_za F OS 3).
Proof. exact (Zlib.proof.za.inflate.Cases5_FTO.cases5_FTO_za (ZA:=ZA) (ZAV:=ZAV) F). Qed.

End ZAlloc.
