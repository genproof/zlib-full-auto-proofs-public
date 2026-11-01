(* Law rj_bad_block: main (harness/rj_bad_block.c) against MainLib.main_core_spec R_bb, from the theory of the
   calls (BBWTheory.v) and the three segments of its body (BBWSetup.v, BBWLoop.v, BBWTail.v), chained through
   their continuation-passing statements (BBWKit.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5 Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.bit_writer.BWSpec.
Require Import Zlib.proof.harness.bit_writer.BBWDefs.
Require Import Zlib.proof.harness.bit_writer.BWLawCS Zlib.proof.harness.bit_writer.BWGlobals.
Require Import Zlib.proof.harness.bit_writer.BBWKit.
Require Zlib.proof.harness.bit_writer.BBWTheory.
Require Zlib.proof.harness.bit_writer.BBWSetup.
Require Zlib.proof.harness.bit_writer.BBWLoop.
Require Zlib.proof.harness.bit_writer.BBWTail.

Lemma bbw_body_main :
  @semax_body (QPvarspecs BB.p) Gmain_bbW BB.CS BBC.f_main (BBC._main, main_core_spec R_bb).
Proof.
  destruct Zlib.proof.harness.bit_writer.BBWTheory.bbw_theory as [J FJ].
  start_function.
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
  apply semax_seq with FF; [ | apply semax_ff].
  change (semax bbw_Delta
    (PROP () LOCAL (lvar BBC._strm t_zsb v_strm; lvar BBC._btype (tarray tuint 5) v_btype;
                    lvar BBC._bit tulong v_bit; gvars gv)
     SEP (data_at_ Tsh t_zsb v_strm; data_at_ Tsh (tarray tuint 5) v_btype; data_at_ Tsh tulong v_bit;
          mem_mgr gv; R_bb gv))
    bbw_seg1 POST_B).
  apply (Zlib.proof.harness.bit_writer.BBWSetup.bbw_setup _ J gv v_strm v_btype v_bit FJ).
  intros S0 kind which lits room flush strp outp A.
  apply (Zlib.proof.harness.bit_writer.BBWLoop.bbw_loop _ J); auto.
  apply Zlib.proof.harness.bit_writer.BBWTail.bbw_tail; auto.
Qed.
