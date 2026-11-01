(* The switch case HEAD of inflate() in the allocator-generic port: the generated Cases5_HEAD.v (patches in docs/port-za/inflate/cases_head.py). *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.za.inflate.CaseHyps5.
Require Import Zlib.proof.zutil.ZAlloc.
Require Import Zlib.proof.za.inflate.ZAV.
Require Zlib.proof.za.inflate.Cases5_HEAD.
#[local] Existing Instance Zlib.units.Inflate.CS.

Section ZAlloc.
Context {ZA : zallocator} {ZAV : adler_cell}.

Lemma za_cases5_HEAD {Espec: OracleKind} (F: frame) : frame_ok5 F ->
  case_ok5_za F HEAD 0.
Proof.
  exact (Zlib.proof.za.inflate.Cases5_HEAD.cases5_HEAD_za F).
Qed.

End ZAlloc.
