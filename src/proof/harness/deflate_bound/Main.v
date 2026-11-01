(* Law deflate_bound: the body of main (harness/deflate_bound.c) against MainLib.main_core_spec, from the parts
   of MainKit.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Zlib.contracts.x_deflate_bound.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DCS Zlib.proof.deflate.Rep Zlib.proof.deflate.DSpec.
Require Zlib.proof.compress.CSpec.
Require Import Zlib.proof.deflate.LawFacts Zlib.proof.deflate.HarnessLib Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.deflate.Obligations.
Require Import Zlib.proof.harness.deflate_bound.MainKit.
Require Import Zlib.harness.x_deflate_bound.code.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.

Require Import Zlib.proof.harness.deflate_bound.MainPre Zlib.proof.harness.deflate_bound.MainInit
  Zlib.proof.harness.deflate_bound.MainDict Zlib.proof.harness.deflate_bound.MainHead
  Zlib.proof.harness.deflate_bound.MainBnd Zlib.proof.harness.deflate_bound.MainRun.

Lemma body_main (Bpre : bpre_inv) (Brun : brun_inv) :
  bound_facts Bpre Brun -> ob_dstream_to_end ->
  semax_body (QPvarspecs Zlib.contracts.x_deflate_bound.whole_prog) Gmain f_main (_main, main_core_spec R).
Proof.
  intros BF TO.
  start_function.
  change (semax Delta_m (PRE0 gv v_s v_h) msuf0 POST_m).
  apply part_pre; intros bs.
  apply (part_init Bpre Brun); auto; intros st.
  apply part_dict; intros st1.
  apply part_head; intros st2 ghp hx Hr.
  apply part_bound; auto; intros b obp.
  apply part_run; auto.
Qed.
