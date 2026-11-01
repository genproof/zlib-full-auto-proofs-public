(* The switch cases NAME, COMMENT of inflate() in the allocator-generic port: the generated Cases5_NC.v (patches in docs/port-za/inflate/cases_nc.py). *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.za.inflate.CaseHyps5.
Require Import Zlib.proof.zutil.ZAlloc.
Require Import Zlib.proof.za.inflate.ZAV.
Require Zlib.proof.za.inflate.Cases5_NC.
#[local] Existing Instance Zlib.units.Inflate.CS.

Section ZAlloc.
Context {ZA : zallocator} {ZAV : adler_cell}.

Lemma za_cases5_NC {Espec: OracleKind} (F: frame) : frame_ok5 F ->
  (case_okT5_za F COMMENT 7 -> case_okT5_za F NAME 6) /\ (case_ok5_za F HCRC 8 -> case_okT5_za F COMMENT 7).
Proof. exact (Zlib.proof.za.inflate.Cases5_NC.cases5_NC_za (ZA:=ZA) (ZAV:=ZAV) F). Qed.

End ZAlloc.
