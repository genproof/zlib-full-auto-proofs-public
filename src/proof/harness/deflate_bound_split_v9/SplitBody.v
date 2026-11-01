(* Law deflate_bound_split: the body of main from its parts (SplitKit.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DCS Zlib.proof.deflate.DSpec Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.deflate.LawFacts Zlib.proof.deflate.HarnessLib Zlib.proof.deflate.GlobalsInit.
Require Zlib.proof.deflate.Obligations.
Require Import Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.harness.x_deflate_bound_split.code.
Require Import Zlib.proof.harness.deflate_bound_split_v9.SplitMain Zlib.proof.harness.deflate_bound_split_v9.SplitKit.
Require Import Zlib.proof.harness.deflate_bound_split_v9.SplitDraws Zlib.proof.harness.deflate_bound_split_v9.SplitFill
               Zlib.proof.harness.deflate_bound_split_v9.SplitInit Zlib.proof.harness.deflate_bound_split_v9.SplitDict
               Zlib.proof.harness.deflate_bound_split_v9.SplitHead Zlib.proof.harness.deflate_bound_split_v9.SplitBound
               Zlib.proof.harness.deflate_bound_split_v9.SplitL1 Zlib.proof.harness.deflate_bound_split_v9.SplitL2
               Zlib.proof.harness.deflate_bound_split_v9.SplitL3 Zlib.proof.harness.deflate_bound_split_v9.SplitEnd
               Zlib.proof.harness.deflate_bound_split_v9.SplitMem.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.

Lemma body_main Bpre Brun : bound_facts Bpre Brun -> Obligations.ob_dstream_to_end ->
  semax_body (QPvarspecs p) Gmain f_main (_main, main_core_spec Rm).
Proof.
  intros BF TE.
  start_function.
  change Delta with Delta_m. change POSTCONDITION with POST_m.
  change MORE_COMMANDS with (Sreturn (Some (Econst_int (Int.repr 0) tint))).
  apply semax_seq with FF.
  2: { apply semax_ff. }
  fold Rm_ret.
  eapply semax_pre; [ | apply (part_draws Bpre Brun v_s v_h v_osnap gv) ].
  { unfold PRE0. entailer!. }
  intros bd. apply part_fill. intros bs f dt Ebd. apply part_init. intros s f1.
  apply part_dict. intros s2 f2. apply part_head. intros s3 f3. apply part_bound. intros b s4 f4.
  rewrite msuf42_eq.
  apply semax_seq with (E_inv v_s v_h v_osnap gv bs).
  - apply semax_pre with (J_inv Bpre Brun v_s v_h v_osnap gv bs b).
    { apply andp_left2. unfold J_inv. Exists 0 false s4 f4. apply derives_refl. }
    apply semax_loop with (J_inv Bpre Brun v_s v_h v_osnap gv bs b).
    + unfold J_inv at 1. Intros pos fin s5 f5.
      apply part_l1; [ apply split_mem | ]. intros ci. apply part_l2. intros s' z' code msgv'. apply part_l3.
    + eapply semax_post; [ | | | | apply semax_skip ]; intros; simpl_ret_assert;
        try apply andp_left2; try apply derives_refl; try apply FF_left.
  - unfold E_inv. Intros s6 f6. apply part_end.
Qed.
