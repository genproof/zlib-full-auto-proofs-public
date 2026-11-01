(* Law rj_bad_block, main: statement 11 of main's body (BBWSetKit.bbs_null_stmt), the NULL check of the objects
   stream, literal and out: any NULL returns 0, otherwise the three objects are there (BBWSetKit.bbs_A1). *)
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
Require Import Zlib.proof.harness.bit_writer.BBWHelp.
Require Import Zlib.proof.harness.bit_writer.BBWSetKit.

Lemma bbs_null : bbs_null_stmt.
Proof.
  intros Espec gv vs vbt vbit w kind which lits S0 room stream literal out K.
  unfold bbs_A10, bbw_seg11, POST_B, bbw_POST. abbreviate_semax.
  Intros.
  (* if (stream == NULL || literal == NULL || out == NULL) return 0; *)
  destruct (eq_dec stream nullval) as [PS | PS].
  { subst stream.
    ifpost BBC._t'11 (Int.repr 1); [forward; entailer! | bb_infeas | ].
    ifpost BBC._t'12 (Int.repr 1); [forward; entailer! | discriminate | ].
    forward_if False; [ret0 | bb_infeas]. }
  Intros. pose proof (bb_isptr stream PNstream PS) as Pstream.
  destruct (eq_dec literal nullval) as [PL | PL].
  { subst literal.
    ifpost BBC._t'11 (Int.repr 1); [bb_infeas | forward; entailer! | ].
    ifpost BBC._t'12 (Int.repr 1); [forward; entailer! | discriminate | ].
    forward_if False; [ret0 | bb_infeas]. }
  Intros. pose proof (bb_isptr literal PNliteral PL) as Pliteral.
  destruct (eq_dec out nullval) as [PO | PO].
  { subst out.
    ifpost BBC._t'11 (Int.repr 0);
      [bb_infeas | forward; entailer!; destruct literal; simpl in Pliteral; try tauto; reflexivity | ].
    ifpost BBC._t'12 (Int.repr 1); [bb_infeas | forward; entailer! | ].
    forward_if False; [ret0 | bb_infeas]. }
  Intros. pose proof (bb_isptr out PNout PO) as Pout.
  ifpost BBC._t'11 (Int.repr 0);
    [bb_infeas | forward; entailer!; destruct literal; simpl in Pliteral; try tauto; reflexivity | ].
  ifpost BBC._t'12 (Int.repr 0);
    [bb_infeas | forward; entailer!; destruct out; simpl in Pout; try tauto; reflexivity | ].
  forward_if True; [bb_infeas | forward; entailer! | ].
  (* the rest from bbs_A1 *)
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
  eapply semax_pre; [ | apply K].
  unfold bbs_A1. entailer!.
Qed.
