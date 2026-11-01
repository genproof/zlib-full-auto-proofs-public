(* Law rj_bad_block, main: the test of the do-while of inflate() calls (BBWLKit.bbl_test_stmt): after a call
   that returned Z_OK or Z_BUF_ERROR and was clipped, the loop goes on from its invariant; otherwise it is left
   in BBWKit.bbw_AT. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5 Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.bit_writer.BWSpec.
Require Import Zlib.proof.harness.bit_writer.BBWDefs.
Require Import Zlib.proof.harness.bit_writer.BWLawCS Zlib.proof.harness.bit_writer.BWGlobals.
Require Import Zlib.proof.harness.bit_writer.BBWKit.
Require Import Zlib.proof.harness.bit_writer.BBWHelp.
Require Import Zlib.proof.harness.bit_writer.BBWLKit.
Local Open Scope logic.

Lemma bbl_test_ok : bbl_test_stmt.
Proof.
  intros Espec J gv vs vbt vbit S0 kind which lits room flush strp outp A.
  unfold bbl_test, bbl_R, bbw_C, POST_B, bbw_POST. abbreviate_semax.
  Intros ir or code pos ob z L oc.
  match goal with H: bbw_cpost _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H into C end.
  destruct C as [Hd | (Hc & HJ & Hsw & Hhd & Hpos & Hob & Hni & Hno & Hnc)].
  - (* Z_DATA_ERROR: the loop is left *)
    subst code.
    bb_if BBC._t'15 (Vint (Int.repr 0)); [bb_infeas | forward; entailer! | ].
    bb_if BBC._t'16 (Vint (Int.repr 0)); [bb_infeas | forward; entailer! | ].
    forward_if; [bb_infeas | ].
    forward.
    unfold bbw_AT. Exists Z_DATA_ERROR pos ob z L oc. entailer!.
  - (* Z_OK or Z_BUF_ERROR: the loop goes on when a piece was clipped *)
    bb_if BBC._t'15 (Vint (Int.repr 1)).
    { forward. entailer!. }
    { forward. entailer!. destruct Hc as [-> | ->]; [contradiction | reflexivity]. }
    bb_if BBC._t'16 (Vint (Int.repr (if orb (Z.ltb Int.max_unsigned ir) (Z.ltb Int.max_unsigned or) then 1 else 0))).
    { forward_if.
      - forward. entailer!.
        rewrite Int.unsigned_repr in H3 by rep_lia.
        replace (Int.max_unsigned <? ir) with true by (symmetry; apply Z.ltb_lt; rep_lia). reflexivity.
      - forward. forward. entailer!.
        rewrite Int.unsigned_repr in H3 by rep_lia.
        replace (Int.max_unsigned <? ir) with false by (symmetry; apply Z.ltb_ge; rep_lia). simpl orb.
        unfold Int64.cmpu, Int64.ltu. rewrite !Int64.unsigned_repr by rep_lia.
        destruct (zlt _ _), (Z.ltb_spec Int.max_unsigned or); try reflexivity; rep_lia. }
    { bb_infeas. }
    destruct (orb (Z.ltb Int.max_unsigned ir) (Z.ltb Int.max_unsigned or)) eqn:Ec.
    + (* a piece was clipped: the next iteration *)
      forward_if; [ | bb_infeas].
      forward. unfold bbw_inv. Exists pos ob z L oc. entailer!.
    + (* nothing was clipped: the call was offered everything *)
      forward_if; [bb_infeas | ].
      forward.
      apply orb_false_iff in Ec. destruct Ec as [E1 E2]. apply Z.ltb_ge in E1, E2.
      destruct (Hnc ltac:(lia) ltac:(lia)) as (Hok & Hfl & Hai & Hao & Hx).
      unfold bbw_AT. Exists code pos ob z L oc. entailer!.
      right. repeat (split; [auto | ]). auto.
Qed.
