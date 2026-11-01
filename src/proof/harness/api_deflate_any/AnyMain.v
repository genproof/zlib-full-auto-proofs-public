(* Law api_deflate_any: main of harness/api_deflate_any.c against main_core_spec R (statement in AnyMainStmt.v),
   from the parts of AnyKit.v: the prefix up to the loop, the loop body's four parts, the loop test (continue
   unless deflate returned Z_STREAM_END, and nondet_u8() says so) and the return after the loop. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Rep.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.harness.api_deflate_any.AnyFacts.
Require Zlib.proof.harness.api_deflate_any.AnyCodes.
Require Zlib.proof.deflate.DModel5.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.proof.harness.api_deterministic.DetMem2.
Require Zlib.proof.harness.api_deterministic.DetMem2b.
Require Zlib.proof.harness.api_deterministic.DetKit2.
Require Import Zlib.proof.harness.api_deflate_any.AnyCS.
Require Import Zlib.proof.harness.api_deflate_any.AnyMainStmt.
Require Import Zlib.proof.harness.api_deflate_any.AnyKit.
Require Import Zlib.harness.api_deflate_any.code.
Require Import Zlib.proof.harness.api_deflate_any.AnyPrefix.
Require Import Zlib.proof.harness.api_deflate_any.AnyPre.
Require Import Zlib.proof.harness.api_deflate_any.AnyParams.
Require Import Zlib.proof.harness.api_deflate_any.AnyCall.
Require Import Zlib.proof.harness.api_deflate_any.AnyCheck.
Require Import Zlib.proof.harness.api_deflate_any.AnyAt.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.

Lemma body_main_of_parts :
  any_prefix_stmt -> any_pre_stmt -> any_params_stmt -> any_call_stmt -> any_check_stmt -> any_main_stmt.
Proof.
  intros Hprefix Hpre Hparams Hcall Hcheck AT. unfold any_main_stmt.
  start_function.
  unfold R. Intros.
  (* main's body always returns: its normal postcondition is FF *)
  eapply semax_seq with (Q := FF); [ | apply semax_ff ].
  eapply semax_post with (R' := POST_m); [ | | | | ].
  all: try (intros; unfold POST_m; simpl; normalize; fail).
  { intros. subst POSTCONDITION. unfold abbreviate, POST_m. simpl. intro x. apply andp_left2.
    apply derives_refl. }
  eapply semax_pre; [ | apply (Hprefix _ v_strm gv v_at AT) ].
  { unfold PRE0. rewrite any_strm_cs, any_at_cs. entailer!. }
  intros J n data datap sp ls.
  rewrite msuf15_eq.
  eapply semax_seq with (Q := E_inv n data datap v_strm sp gv v_at).
  - eapply semax_pre with (P' := J_inv J n data datap v_strm sp gv v_at).
    { unfold J_inv. Exists ls. apply ENTAIL_refl. }
    apply semax_loop with (Q' := T_inv J n data datap v_strm sp gv v_at).
    + unfold J_inv at 1. Intros ls'.
      apply Hpre. intros ci. apply Hparams. intros c. apply Hcall. intros d. apply Hcheck.
    + (* the loop test: continue unless Z_STREAM_END, then as nondet_u8() says *)
      unfold T_inv, T_at, J_loc. Intros code ls'.
      unfold ltest.
      abbreviate_semax.
      forward_if (EX b : bool, PROPx [setup_ok J n data datap; b = true -> J_ok J n data datap ls']
        (LOCALx (temp _t'9 (Val.of_bool b) :: temp _code (vi code) :: J_loc n datap v_strm gv v_at ls')
         (SEPx (J_sep n data datap v_strm sp gv v_at ls')))).
      * forward_call tt. Intros x. forward. Exists (negb (Z.eqb x 0)). unfold J_loc. entailer!.
        split. { intros _. apply H0. intros E; subst code. apply H1. reflexivity. }
        destruct (zeq x 0) as [->|Hx]; [reflexivity | rewrite (proj2 (Z.eqb_neq x 0) Hx); reflexivity].
      * forward. Exists false. unfold J_loc. entailer!.
      * Intros b. unfold J_loc.
        forward_if.
        -- forward. unfold J_inv, J_at, J_loc. Exists ls'. entailer!.
           apply H1. destruct b; [reflexivity | inversion H2].
        -- forward. unfold E_inv. Exists ls'. entailer!.
  - (* return 0: main's two locals back at the law's compspecs *)
    unfold E_inv. Intros ls'. unfold J_sep.
    sep_apply (DK.det_shead_back v_strm).
    forward. Exists (Int.repr 0). entailer!.
    rewrite any_at_cs. cancel.
Qed.

Lemma body_main : any_main_stmt.
Proof. exact (body_main_of_parts any_prefix any_pre any_params any_call any_check). Qed.
