(* Law rj_bad_block, main: the body of the do-while of inflate() calls up to the call (BBWLKit.bbl_pre_stmt):
   the rests of the stream and of the room, the clip() pieces stored into avail_in / avail_out; the stream and
   the two objects are then in inflate()'s view (BBWLKit.bbl_mid). *)
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

Lemma bbl_pre_ok : bbl_pre_stmt.
Proof.
  intros Espec J gv vs vbt vbit S0 kind which lits room flush strp outp A HC.
  destruct A as (Hok & Hroom & Hfl & Pstrp & Poutp).
  destruct (bb_bytes_ok _ _ _ _ Hok) as [LS BS].
  unfold bbl_R, POST_B, bbw_POST in HC.
  unfold bbl_body, bbw_inv, bbl_R, POST_B, bbw_POST. abbreviate_semax.
  Intros pos ob z L oc.
  rename H into HJ, H0 into Hsw, H1 into Hhd, H2 into Hpos, H3 into Hob, H4 into Hoc, H5 into Hni, H6 into Hno.
  rewrite bbl_istreamA_unfold. Intros.
  unfold bbl_tup. rewrite Hni, Hno.
  set (S := bb_bytes S0 kind which lits) in *.
  assert (H64: Zlength S0 <= Int64.max_signed) by (destruct Hok as (_ & _ & _ & _ & _ & Hz & _); lia).
  (* in_rest = stream_len - (next_in - stream), out_rest = room - (next_out - out) *)
  forward.
  forward.
  { entailer!. apply prop_right. apply bbl_sameblock; auto. }
  rewrite bbl_rest by (auto; rep_lia).
  forward.
  forward.
  { entailer!. apply prop_right. apply bbl_sameblock; auto. }
  rewrite bbl_rest by (auto; rep_lia).
  (* avail_in = clip(in_rest), avail_out = clip(out_rest) *)
  forward_call (Zlength S0 - pos).
  forward.
  forward_call (room - Zlength ob).
  forward.
  (* the rest of the body is the call: bbl_mid *)
  eapply semax_pre; [ | unfold MORE_COMMANDS, POSTCONDITION, abbreviate; exact HC].
  pose proof (Zlength_nonneg ob).
  sep_apply (bbl_offer_fold gv vs z L (offset_val pos strp) (offset_val (Zlength ob) outp)
               (Z.min (Zlength S0 - pos) Int.max_unsigned) (Z.min (room - Zlength ob) Int.max_unsigned));
    auto; try rep_lia.
  sep_apply (bbl_bufs_pre vs L strp (Zlength S0) pos S outp room (Zlength ob) oc); auto; try lia.
  subst S. unfold bbl_mid. Exists pos ob z L oc. entailer!.
Qed.
