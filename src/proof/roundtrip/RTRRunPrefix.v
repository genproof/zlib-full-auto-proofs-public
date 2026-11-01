(* Law deflate_api, deflate_run: the draws, the allocations and R's fields, up to stream_defaults (RunKit.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.deflate.LawFacts Zlib.proof.deflate.HarnessLib Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.roundtrip.RTRCS Zlib.proof.roundtrip.RTRRunSpec
               Zlib.proof.roundtrip.RTRApiConv Zlib.proof.roundtrip.RTRRunKit.
Require Import Zlib.proof.roundtrip.RTRRunPrefixPad.
Require Import Zlib.harness.x_deflate_roundtrip.code.
#[local] Existing Instance RTRCS.CS.
Local Open Scope logic.

Lemma run_prefix_ok {Espec : OracleKind} I Iend Rp sp api vosn gv :
  (forall rs, semax Delta_r (A1 I Iend Rp sp api vosn gv rs) rsuf45 (POST_r Iend Rp sp gv)) ->
  semax Delta_r (PRE0 I Iend Rp sp api vosn gv) run_body (POST_r Iend Rp sp gv).
Proof.
  (* kit v2: A1 is RunPrefixPad.A1p (drun_rest carries drun_pad) *)
  intros H. apply run_prefix_pad. exact H.
Qed.
