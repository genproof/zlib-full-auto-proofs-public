(* Law api_deterministic (data of any length): main of harness/api_deterministic.c against main_core_spec R
   (statement in DetMainStmt2.v), from the parts of DetKit2.v: the prefix up to the loop, the loop body's four
   parts, the loop test and the return after Z_STREAM_END. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.deflate.DetFacts2.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.api_deterministic.DetCS2.
Require Import Zlib.proof.harness.api_deterministic.DetMainStmt2.
Require Import Zlib.proof.harness.api_deterministic.DetKit2.
Require Import Zlib.proof.harness.api_deterministic.DetPrefix2.
Require Import Zlib.proof.harness.api_deterministic.DetPre2.
Require Import Zlib.proof.harness.api_deterministic.DetParams2.
Require Import Zlib.proof.harness.api_deterministic.DetCall2.
Require Import Zlib.proof.harness.api_deterministic.DetCheck2.
Require Import Zlib.harness.api_deterministic.code.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.

Lemma body_main_of_parts :
  det_prefix_stmt -> det_pre_stmt -> det_params_stmt -> det_call_stmt -> det_check_stmt -> det_main2_stmt.
Proof.
  intros Hprefix Hpre Hparams Hcall Hcheck DT. unfold det_main2_stmt.
  start_function.
  unfold R. Intros.
  (* main's body always returns: its normal postcondition is FF *)
  eapply semax_seq with (Q := FF); [ | apply semax_ff ].
  eapply semax_post with (R' := POST_m); [ | | | | ].
  all: try (intros; unfold POST_m; simpl; normalize; fail).
  { intros. subst POSTCONDITION. unfold abbreviate, POST_m. simpl. intro x. apply andp_left2.
    apply derives_refl. }
  eapply semax_pre; [ | apply (Hprefix _ v_first v_second gv DT) ].
  { unfold PRE0. entailer!. }
  intros J n data datap sp1 sp2 ls.
  rewrite msuf17_eq.
  eapply semax_seq with (Q := E_inv n data datap v_first v_second sp1 sp2 gv).
  - eapply semax_pre with (P' := J_inv J n data datap v_first v_second sp1 sp2 gv).
    { unfold J_inv. Exists ls. apply ENTAIL_refl. }
    apply semax_loop with (Q' := T_inv J n data datap v_first v_second sp1 sp2 gv).
    + unfold J_inv at 1. Intros ls'.
      apply Hpre. intros ci. apply Hparams. intros c. apply Hcall. intros d. apply Hcheck.
    + (* the loop test: continue unless Z_STREAM_END *)
      unfold T_inv, T_at, J_loc. Intros code ls'.
      unfold ltest. forward_if.
      * forward. unfold J_inv, J_at, J_loc. Exists ls'. entailer!.
        apply H0. intros E. subst code. contradiction.
      * forward. unfold E_inv. Exists ls'. entailer!.
  - (* return 0 *)
    unfold E_inv. Intros ls'. unfold J_sep.
    sep_apply (det_shead_back v_first). sep_apply (det_shead_back v_second).
    forward. Exists (Int.repr 0). entailer!.
Qed.

Lemma body_main : det_main2_stmt.
Proof. exact (body_main_of_parts det_prefix det_pre det_params det_call det_check). Qed.
