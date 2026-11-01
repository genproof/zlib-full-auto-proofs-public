(* Law api_deflate_any: the checks of deflate's code (AnyCheck.any_check): bad_flush = flush < Z_NO_FLUSH ||
   flush > Z_BLOCK; gp_assert((code == Z_STREAM_ERROR) == bad_flush); gp_assert(code is Z_OK, Z_BUF_ERROR,
   Z_STREAM_ERROR or Z_STREAM_END); gp_assert(code != Z_STREAM_END || flush == Z_FINISH).  All three hold by
   dr_ok (the codes of AnyCodes.v).  The checks do not change the memory, so the assertion after them is D_at
   with main's bad_flush (Dq_at; the unmoved check reads it). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Rep.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.harness.api_deflate_any.AnyFacts.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.proof.harness.api_deterministic.DetKit2.
Require Import Zlib.proof.harness.api_deflate_any.AnyCS.
Require Import Zlib.proof.harness.api_deflate_any.AnyMainStmt.
Require Import Zlib.proof.harness.api_deflate_any.AnyKit.
Require Import Zlib.proof.harness.api_deflate_any.AnyCheckNext.
Require Import Zlib.harness.api_deflate_any.code.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.

Ltac simplify_remove_localdef_temp ::=
  repeat first [ rewrite rlt_nil | rewrite rlt_gvars | rewrite rlt_lvar | rewrite rlt_same
               | rewrite rlt_cons by (let X := fresh in intro X; discriminate X) ].

(* a goal on deflate's code [dr_code d], one of the four codes by dr_ok: one case per code, each closed by
   computation or by the contradiction of the branch condition *)
Ltac code_cases Hcodes :=
  let E := fresh "E" in
  destruct Hcodes as [E | [E | [E | E]]]; rewrite E in *;
  unfold Z_OK, Z_BUF_ERROR, Z_STREAM_ERROR, Z_STREAM_END, Z_FINISH in *;
  first
    [ reflexivity
    | exfalso; match goal with
               | H : Int.repr ?a = Int.repr ?b |- _ =>
                   apply (f_equal Int.signed) in H; rewrite !Int.signed_repr in H by rep_lia; lia
               | H : Int.repr ?a <> Int.repr ?a |- _ => apply H; reflexivity
               | H : (if _ then _ else _) <> 0 |- _ => apply H; reflexivity
               | H : (if _ then _ else _) = 0 |- _ => simpl in H; discriminate H
               | H : Int.repr _ = Int.zero |- _ => simpl in H; discriminate H
               end ].

Lemma any_check_code : any_check_code_stmt.
Proof.
  intros Espec J n data datap v sp gv ap ls ci c d HK.
  unfold lsuf12.
  match goal with |- semax _ _ (Ssequence ?a (Ssequence ?b (Ssequence ?e (Ssequence ?f ?rest)))) _ =>
    change rest with lsuf16 end.
  unfold D_at, D_sep, B_loc, Rbody, POST_m, Delta_m, Gmain in *. simplify_func_tycontext.
  abbreviate_semax. Intros.
  pose proof H2 as (_ & _ & _ & Hbad & Hcodes & Hend & _).
  pose proof H0 as (_ & _ & Hfl & _).
  rewrite <- seq_assoc.
  forward_if (temp _t'31 (vi (if orb (ci_flush ci <? 0) (5 <? ci_flush ci) then 1 else 0))).
  { forward. entailer!.
    destruct (Z.ltb_spec (ci_flush ci) 0); [ reflexivity | lia ]. }
  { forward. entailer!.
    destruct (Z.ltb_spec (ci_flush ci) 0); [ lia | ].
    destruct (Z.ltb_spec 5 (ci_flush ci)), (zlt 5 (ci_flush ci)); try lia; reflexivity. }
  forward.
  (* (code == Z_STREAM_ERROR) == bad_flush *)
  forward_call (Int.repr 1).
  { entailer!.
    assert (Hb : dr_code d = Z_STREAM_ERROR <-> ((ci_flush ci <? 0) || (5 <? ci_flush ci))%bool = true)
      by (rewrite Hbad, Bool.orb_true_iff, !Z.ltb_lt; tauto).
    unfold Z_STREAM_ERROR in Hb.
    destruct ((ci_flush ci <? 0) || (5 <? ci_flush ci))%bool.
    - rewrite (proj2 Hb eq_refl). reflexivity.
    - destruct Hcodes as [E | [E | [E | E]]]; rewrite E in *; unfold Z_OK, Z_BUF_ERROR, Z_STREAM_ERROR, Z_STREAM_END in *;
        try (exfalso; pose proof (proj1 Hb eq_refl); discriminate); reflexivity. }
  (* code is Z_OK, Z_BUF_ERROR, Z_STREAM_ERROR or Z_STREAM_END *)
  repeat rewrite <- seq_assoc.
  forward_if (temp _t'32 (vi (if ((dr_code d =? 0) || (dr_code d =? -5))%bool then 1 else 0))).
  { forward. entailer!. clear HK. code_cases Hcodes. }
  { forward. entailer!. clear HK. code_cases Hcodes. }
  repeat rewrite <- seq_assoc.
  forward_if (temp _t'33
    (vi (if ((dr_code d =? 0) || (dr_code d =? -5) || (dr_code d =? -2))%bool then 1 else 0))).
  { forward. entailer!. clear HK. code_cases Hcodes. }
  { forward. entailer!. clear HK. code_cases Hcodes. }
  repeat rewrite <- seq_assoc.
  forward_if (temp _t'34
    (vi (if ((dr_code d =? 0) || (dr_code d =? -5) || (dr_code d =? -2) || (dr_code d =? 1))%bool
         then 1 else 0))).
  { forward. entailer!. clear HK. code_cases Hcodes. }
  { forward. entailer!. clear HK. code_cases Hcodes. }
  forward_call (Int.repr 1).
  { entailer!. clear HK. code_cases Hcodes. }
  (* code != Z_STREAM_END || flush == Z_FINISH *)
  repeat rewrite <- seq_assoc.
  forward_if (temp _t'35 (vi 1)).
  { forward. entailer!. }
  { forward. entailer!. clear HK.
    assert (E : dr_code d = 1)
      by (clear - H3 Hcodes; unfold Z_OK, Z_BUF_ERROR, Z_STREAM_ERROR, Z_STREAM_END in *;
          destruct Hcodes as [E | [E | [E | E]]]; rewrite E in *; auto;
          apply (f_equal Int.signed) in H3; rewrite !Int.signed_repr in H3 by rep_lia; lia).
    rewrite (Hend E). reflexivity. }
  forward_call (Int.repr 1).
  (* the state is D_at's, with bad_flush's value *)
  eapply semax_pre; [ | exact HK ].
  unfold Dq_at, D_sep, B_loc. entailer!.
  unfold bad_b. destruct ((ci_flush ci <? 0) || (5 <? ci_flush ci))%bool; reflexivity.
Qed.
