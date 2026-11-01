(* The switch cases of inflate() in the allocator-generic port (src/proof/za/inflate_api/Stmt.v,
   za_cases_stmt): CasesAll5's assembly (src/proof/inflate/CasesAll5.v) over the generated case lemmas, for
   every allocator and adler cell. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.za.inflate_api.Stmt.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.za.inflate.CaseHyps5.
Require Import Zlib.proof.inflate.InvQ5.
Require Import Zlib.proof.za.inflate.CasesHeadZ Zlib.proof.za.inflate.CasesFtoZ Zlib.proof.za.inflate.CasesExZ
  Zlib.proof.za.inflate.CasesNcZ Zlib.proof.za.inflate.CasesHdZ Zlib.proof.za.inflate.CasesTyZ
  Zlib.proof.za.inflate.CasesStZ Zlib.proof.za.inflate.CasesTlZ
  Zlib.proof.za.inflate.CasesClZ Zlib.proof.za.inflate.CasesLenZ Zlib.proof.za.inflate.CasesLdZ
  Zlib.proof.za.inflate.CasesDmZ Zlib.proof.za.inflate.CasesCkZ Zlib.proof.za.inflate.CasesEndZ.
#[local] Existing Instance Zlib.units.Inflate.CS.

(* the cases chained backwards along the fallthroughs, from MATCH (which only returns or loops) and DONE;
   the facts on inflate_table's tables (cover3) and the fixed tables are the allocator-free ones of InvQ5 *)
Lemma za_cases_proof : za_cases_stmt.
Proof.
  intros ZA ZAV Espec F HF.
  pose proof cover3_proof as C3. pose proof fixed_ok5_proof as FX.
  destruct (za_cases5_DM F HF) as [DM1 MAT].
  pose proof (DM1 MAT) as DEX.
  destruct (za_cases5_LD F HF) as [LD1 LD2].
  pose proof (LD2 DEX) as DST. pose proof (LD1 DST) as LXT.
  pose proof (za_cases5_LEN_next F HF LXT) as LN.
  destruct (za_cases5_end F HF) as (LEN_ & LT & DN & BD & MM & SY).
  pose proof (LEN_ LN) as LN_.
  pose proof (za_cases5_CL F HF C3 LN_) as CL.
  destruct (za_cases5_TL F HF C3) as [TL1 TL2].
  pose proof (TL2 CL) as LL. pose proof (TL1 LL) as TB.
  destruct (za_cases5_ST F HF) as (ST1 & ST2 & CP).
  pose proof (ST2 CP) as CP_. pose proof (ST1 CP_) as STD.
  destruct (za_cases5_TY F HF FX) as [TY TYD].
  destruct (za_cases5_HD F HF) as (HC & HD2 & HD3).
  pose proof (HD3 TY) as DCT. pose proof (HD2 DCT) as DID.
  destruct (za_cases5_NC F HF) as [NC1 NC2].
  pose proof (NC2 HC) as CMT. pose proof (NC1 CMT) as NAM.
  destruct (za_cases5_EX F HF) as [EX1 EX2].
  pose proof (EX2 NAM) as EXT. pose proof (EX1 EXT) as EXL.
  destruct (za_cases5_FTO F HF) as (F1 & F2 & F3).
  pose proof (F3 EXL) as OS. pose proof (F2 OS) as TM. pose proof (F1 TM) as FL.
  pose proof (za_cases5_HEAD F HF) as HD.
  destruct (za_cases5_CK F HF) as [CK1 CK2].
  pose proof (CK2 DN) as LG. pose proof (CK1 LG) as CK.
  split.
  - intros i Hi Hr.
    do 32 (destruct i as [|i]; [first [exfalso; lia | eassumption] | ]).
    exfalso; lia.
  - intros i Hi.
    do 8 (destruct i as [|i]; [first [exfalso; lia | eassumption] | ]).
    exfalso; lia.
Qed.
