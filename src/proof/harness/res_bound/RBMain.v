(* Law res_bound: the body of main (harness/res_bound.c) against MainLib.main_core_spec R, from the parts of
   RBKit.v.  The first part (RBPre.part_pre: the sizes drawn with upto() and the objects allocated, statements
   0-16) is a hypothesis here: it is the only part that depends on the harness's size limits (RBKit.str_max). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DCS Zlib.proof.deflate.Rep Zlib.proof.deflate.DSpec Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.deflate.LawFacts Zlib.proof.deflate.LawFactsW Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.deflate.Obligations.
Require Zlib.proof.harness.bound_common.BoundKit Zlib.proof.harness.deflate_bound.MainKit.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.res_bound.RBCS Zlib.proof.harness.res_bound.RBString Zlib.proof.harness.res_bound.RBKit.
Require Import Zlib.harness.res_bound.code.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.

Require Import Zlib.proof.harness.res_bound.RBStores Zlib.proof.harness.res_bound.RBInit Zlib.proof.harness.res_bound.RBHead Zlib.proof.harness.res_bound.RBDict Zlib.proof.harness.res_bound.RBBnd Zlib.proof.harness.res_bound.RBRun.

Lemma body_main_of_pre : part_pre_stmt -> body_main_stmt.
Proof.
  intros part_pre Bpre Brun I Iend BF OA AF TE.
  start_function.
  change (semax Delta_m (PRE0 gv v_head v_strm) msuf0 POST_m).
  apply part_pre; intros rs.
  apply part_stores; intros hv.
  apply (part_init Espec Bpre Brun I Iend); auto; intros st.
  apply (part_head Espec Bpre Brun); auto; intros st1 ghp hx Hr.
  apply (part_dict Espec Bpre Brun); auto; intros st2.
  apply (part_bound Espec Bpre Brun); auto; intros b obp.
  apply (part_run Espec Bpre Brun); auto.
Qed.
