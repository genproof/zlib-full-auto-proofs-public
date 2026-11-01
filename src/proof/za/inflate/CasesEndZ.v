(* The switch cases LEN_ (falling through into LEN), LIT and the cases that only return (DONE, BAD, MEM, SYNC) of inflate() in the allocator-generic port: the generated CaseLEN_5.v, CaseLIT5.v, CaseEnd5.v (patches in docs/port-za/inflate/cases_end.py). *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.za.inflate.CaseHyps5.
Require Import Zlib.proof.zutil.ZAlloc.
Require Import Zlib.proof.za.inflate.ZAV.
Require Zlib.proof.za.inflate.CaseLEN_5.
Require Zlib.proof.za.inflate.CaseLIT5.
Require Zlib.proof.za.inflate.CaseEnd5.
#[local] Existing Instance Zlib.units.Inflate.CS.

Section ZAlloc.
Context {ZA : zallocator} {ZAV : adler_cell}.

Lemma za_cases5_end {Espec: OracleKind} (F: frame) : frame_ok5 F ->
  (case_ok5_za F LEN 20 -> case_ok5_za F LEN_ 19) /\
  case_ok5_za F LIT 25 /\ case_ok5_za F DONE 28 /\ case_ok5_za F BAD 29 /\ case_ok5_za F MEM 30 /\
  case_ok5_za F SYNC 31.
Proof.
  intros _.
  split; [exact (Zlib.proof.za.inflate.CaseLEN_5.case_LEN_5_za F) | ].
  split; [intros m A B [W _]; apply (Zlib.proof.za.inflate.CaseLIT5.case_LIT5_za (ZA:=ZA) (ZAV:=ZAV)); auto | ].
  split; [intros m A B [W _]; apply (Zlib.proof.za.inflate.CaseEnd5.case_DONE5_za (ZA:=ZA) (ZAV:=ZAV)); auto | ].
  split; [intros m A B [W _]; apply (Zlib.proof.za.inflate.CaseEnd5.case_BAD5_za (ZA:=ZA) (ZAV:=ZAV)); auto | ].
  split; [intros m A B [W _]; apply (Zlib.proof.za.inflate.CaseEnd5.case_MEM5_za (ZA:=ZA) (ZAV:=ZAV)); auto | ].
  intros m A B [W _]; apply (Zlib.proof.za.inflate.CaseEnd5.case_SYNC5_za (ZA:=ZA) (ZAV:=ZAV)); auto.
Qed.

End ZAlloc.
