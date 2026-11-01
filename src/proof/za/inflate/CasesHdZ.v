(* The switch cases HCRC, DICTID, DICT of inflate() in the allocator-generic port: the generated Cases5_HD.v (patches in docs/port-za/inflate/cases_hd.py). *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.za.inflate.CaseHyps5.
Require Import Zlib.proof.zutil.ZAlloc.
Require Import Zlib.proof.za.inflate.ZAV.
Require Zlib.proof.za.inflate.Cases5_HD.
#[local] Existing Instance Zlib.units.Inflate.CS.

Section ZAlloc.
Context {ZA : zallocator} {ZAV : adler_cell}.

Lemma za_cases5_HD {Espec: OracleKind} (F: frame) : frame_ok5 F ->
  case_ok5_za F HCRC 8 /\ (case_ok5_za F DICT 10 -> case_ok5_za F DICTID 9) /\
  (case_ok5_za F Zlib.proof.inflate.Model.TYPE 11 -> case_ok5_za F DICT 10).
Proof.
  exact (@Zlib.proof.za.inflate.Cases5_HD.cases5_HD_za ZA ZAV Espec F).
Qed.

End ZAlloc.
