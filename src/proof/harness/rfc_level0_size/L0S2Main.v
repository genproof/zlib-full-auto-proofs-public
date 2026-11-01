(* Law rfc_level0_size: main of harness/rfc_level0_size.c against main_core_spec R (statement in
   L0S2MainStmt.v), from the facts Level0CallsFit.l0_fit_facts of the deflate loop (at the harness's
   parameters).  The body is cut into four segments (L0S2Kit.v), proved in L0S2SegIn.v (the inputs and the two objects), L0S2SegInit.v (new_stream,
   deflateInit2_, next_in / next_out), L0S2SegLoop.v (the do-while of deflate() calls) and L0S2SegEnd.v (the
   check and the return), chained here through their CPS statements. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.rfc_level0_size.L0S2MainStmt.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.harness.rfc_level0_size.L0S2Kit.
Require Import Zlib.proof.harness.rfc_level0_size.L0S2SegIn.
Require Import Zlib.proof.harness.rfc_level0_size.L0S2SegInit.
Require Import Zlib.proof.harness.rfc_level0_size.L0S2SegLoop.
Require Import Zlib.proof.harness.rfc_level0_size.L0S2SegEnd.
Require Import Zlib.harness.rfc_level0_size.code.
#[local] Existing Instance DCS.CS.

Lemma body_main2 : l0s2_main_stmt.
Proof.
  intros J LF. unfold l0s2_main_stmt.
  start_function.
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
  apply semax_seq with FF; [ | apply semax_ff].
  change (semax Delta_l0
    (PROP () LOCAL (lvar _strm t_zsl v_strm; gvars gv) SEP (data_at_ Tsh t_zsl v_strm; mem_mgr gv; R gv))
    l0_seg1 POST_B).
  eapply semax_pre; [ | apply (seg_inputs_ok _ gv v_strm)].
  { unfold l0_A0. entailer!. }
  intros n D dp cp wbits mem strategy room.
  apply (seg_init_ok _ J); auto.
  apply (seg_loop_ok _ J); auto.
  apply seg_end_ok.
Qed.
