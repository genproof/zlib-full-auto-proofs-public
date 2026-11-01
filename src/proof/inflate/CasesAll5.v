(* Every case of inflate()'s switch (CaseHyps5.cases_all5), from the groups Cases5_<G>.v, CaseLIT5, CaseEnd5,
   CaseLEN_5, chained backwards along the fallthroughs. *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate.CaseHyps5.
Require Import Zlib.proof.inflate.InvQ5.
Require Zlib.proof.inflate.Cases5_HEAD.
Require Zlib.proof.inflate.Cases5_FTO.
Require Zlib.proof.inflate.Cases5_EX.
Require Zlib.proof.inflate.Cases5_NC.
Require Zlib.proof.inflate.Cases5_HD.
Require Zlib.proof.inflate.Cases5_TY.
Require Zlib.proof.inflate.Cases5_ST.
Require Zlib.proof.inflate.Cases5_TL.
Require Zlib.proof.inflate.Cases5_CL.
Require Zlib.proof.inflate.Cases5_LEN.
Require Zlib.proof.inflate.Cases5_LD.
Require Zlib.proof.inflate.Cases5_DM.
Require Zlib.proof.inflate.Cases5_CK.
Require Zlib.proof.inflate.CaseLIT5.
Require Zlib.proof.inflate.CaseEnd5.
Require Zlib.proof.inflate.CaseLEN_5.
#[local] Existing Instance Zlib.units.Inflate.CS.

Lemma cases_all5_proof : cases_all5.
Proof.
  intros Espec F HF.
  pose proof cover3_proof as C3. pose proof fixed_ok5_proof as FX.
  destruct (Zlib.proof.inflate.Cases5_DM.cases5_DM F HF) as [DM1 MAT].
  pose proof (DM1 MAT) as DEX.
  destruct (Zlib.proof.inflate.Cases5_LD.cases5_LD F HF) as [LD1 LD2].
  pose proof (LD2 DEX) as DST. pose proof (LD1 DST) as LXT.
  pose proof (Zlib.proof.inflate.Cases5_LEN.cases5_LEN F HF) as LN.
  pose proof (Zlib.proof.inflate.CaseLEN_5.case_LEN_5 F LN) as LN_.
  pose proof (Zlib.proof.inflate.Cases5_CL.cases5_CL F HF C3 LN_) as CL.
  destruct (Zlib.proof.inflate.Cases5_TL.cases5_TL F HF C3) as [TL1 TL2].
  pose proof (TL2 CL) as LL. pose proof (TL1 LL) as TB.
  destruct (Zlib.proof.inflate.Cases5_ST.cases5_ST F HF) as (ST1 & ST2 & CP).
  pose proof (ST2 CP) as CP_. pose proof (ST1 CP_) as STD.
  destruct (Zlib.proof.inflate.Cases5_TY.cases5_TY F HF FX) as [TY TYD].
  destruct (Zlib.proof.inflate.Cases5_HD.cases5_HD F HF) as (HC & HD2 & HD3).
  pose proof (HD3 TY) as DCT. pose proof (HD2 DCT) as DID.
  destruct (Zlib.proof.inflate.Cases5_NC.cases5_NC F HF) as [NC1 NC2].
  pose proof (NC2 HC) as CMT. pose proof (NC1 CMT) as NAM.
  destruct (Zlib.proof.inflate.Cases5_EX.cases5_EX F HF) as [EX1 EX2].
  pose proof (EX2 NAM) as EXT. pose proof (EX1 EXT) as EXL.
  destruct (Zlib.proof.inflate.Cases5_FTO.cases5_FTO F HF) as (F1 & F2 & F3).
  pose proof (F3 EXL) as OS. pose proof (F2 OS) as TM. pose proof (F1 TM) as FL.
  pose proof (Zlib.proof.inflate.Cases5_HEAD.cases5_HEAD F HF) as HD.
  assert (DN: case_ok5 F DONE 28)
    by (intros m A B [W _]; apply Zlib.proof.inflate.CaseEnd5.case_DONE5; auto).
  assert (BD: case_ok5 F BAD 29)
    by (intros m A B [W _]; apply Zlib.proof.inflate.CaseEnd5.case_BAD5; auto).
  assert (MM: case_ok5 F MEM 30)
    by (intros m A B [W _]; apply Zlib.proof.inflate.CaseEnd5.case_MEM5; auto).
  assert (SY: case_ok5 F SYNC 31)
    by (intros m A B [W _]; apply Zlib.proof.inflate.CaseEnd5.case_SYNC5; auto).
  assert (LT: case_ok5 F LIT 25)
    by (intros m A B [W _]; apply Zlib.proof.inflate.CaseLIT5.case_LIT5; auto).
  destruct (Zlib.proof.inflate.Cases5_CK.cases5_CK F HF) as [CK1 CK2].
  pose proof (CK2 DN) as LG. pose proof (CK1 LG) as CK.
  split.
  - intros i Hi Hr.
    do 32 (destruct i as [|i]; [first [exfalso; lia | eassumption] | ]).
    exfalso; lia.
  - intros i Hi.
    do 8 (destruct i as [|i]; [first [exfalso; lia | eassumption] | ]).
    exfalso; lia.
Qed.
