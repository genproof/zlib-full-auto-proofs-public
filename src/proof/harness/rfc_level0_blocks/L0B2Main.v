(* Law rfc_level0_blocks: main of harness/rfc_level0_blocks.c against main_core_spec R (statement in
   L0B2MainStmt.v), from the facts Level0Calls.l0_facts of the deflate loop.  The body is cut into four
   segments (L0B2Kit.v), proved in L0B2SegIn.v (the inputs, the data, its copy and the output object),
   L0B2SegInit.v (new_stream, deflateInit2_, next_in / next_out), L0B2SegLoop.v (the do-while of deflate()
   calls) and L0B2SegEnd.v (the check of the stored blocks against the copy, L0B2Loop.v, and the return),
   chained here through their CPS statements. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.rfc_level0_blocks.L0B2MainStmt.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.harness.rfc_level0_blocks.L0B2Kit.
Require Import Zlib.proof.harness.rfc_level0_blocks.L0B2SegIn.
Require Import Zlib.proof.harness.rfc_level0_blocks.L0B2SegInit.
Require Import Zlib.proof.harness.rfc_level0_blocks.L0B2SegLoop.
Require Import Zlib.proof.harness.rfc_level0_blocks.L0B2SegEnd.
Require Import Zlib.harness.rfc_level0_blocks.code.
#[local] Existing Instance DCS.CS.

Lemma body_main2 : l0b2_main_stmt.
Proof.
  intros J LF. unfold l0b2_main_stmt.
  start_function.
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
  apply semax_seq with FF; [ | apply semax_ff].
  change (semax Delta_l0
    (PROP () LOCAL (lvar _strm t_zsl v_strm; gvars gv) SEP (data_at_ Tsh t_zsl v_strm; mem_mgr gv; R gv))
    l0_seg1 POST_B).
  eapply semax_pre; [ | apply (seg_inputs_ok _ gv v_strm)].
  { unfold l0_A0. entailer!. }
  intros n D dp ep cp wbits mem strategy room.
  apply (seg_init_ok _ J); auto.
  apply (seg_loop_ok _ J); auto.
  apply seg_end_ok.
Qed.
