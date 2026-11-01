(* The switch cases STORED, COPY_, COPY of inflate() in the allocator-generic port: the generated Cases5_ST.v (patches in docs/port-za/inflate/cases_st.py). *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.za.inflate.CaseHyps5.
Require Import Zlib.proof.zutil.ZAlloc.
Require Import Zlib.proof.za.inflate.ZAV.
Require Zlib.proof.za.inflate.Cases5_ST.
#[local] Existing Instance Zlib.units.Inflate.CS.

Section ZAlloc.
Context {ZA : zallocator} {ZAV : adler_cell}.

Lemma za_cases5_ST {Espec: OracleKind} (F: frame) : frame_ok5 F ->
  (case_ok5_za F COPY_ 14 -> case_ok5_za F STORED 13) /\ (case_ok5_za F COPY 15 -> case_ok5_za F COPY_ 14) /\
  case_ok5_za F COPY 15.
Proof.
  exact (@Zlib.proof.za.inflate.Cases5_ST.cases5_ST_za ZA ZAV Espec F).
Qed.

End ZAlloc.
