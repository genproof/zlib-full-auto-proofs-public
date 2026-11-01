(* A `return e;` inside a case (with dead statements after it) against case_post's return part:
   the model returns r with machine m'. *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Export Zlib.proof.inflate.CaseCommon.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Lemma ret_type_inflate: ret_type Delta_inflate = tint.
Proof. reflexivity. Qed.

Lemma semax_case_return {Espec: OracleKind} (F: frame) (m m': mst) (r: Z) (e: expr) (P: environ -> mpred)
    (c: statement):
  stepf (f_flush F) lenfix_list distfix_list m = IRet r m' ->
  (forall rho, eval_expr (Ecast e tint) rho = Vint (Int.repr r)) ->
  ENTAIL Delta_inflate, P |-- tc_expr Delta_inflate (Ecast e tint) ->
  ENTAIL Delta_inflate, P |-- (fun _ => mem_rep F m' * locals_rep F) ->
  semax Delta_inflate P (Ssequence (Sreturn (Some e)) c) (switch_ret_assert (case_post F m)).
Proof.
  intros Hs He Htc HP.
  eapply semax_seq; [ | apply semax_ff].
  eapply semax_pre; [ | apply semax_return ].
  rewrite ret_type_inflate.
  apply andp_right; [ exact Htc | ].
  intro rho. specialize (HP rho). cbv beta in HP.
  assert (E: cast_expropt (Some e) tint rho = Some (Vint (Int.repr r))).
  { change (cast_expropt (Some e) tint rho) with (Some (eval_expr (Ecast e tint) rho)). rewrite He. reflexivity. }
  change (liftx (RA_return (overridePost FF (switch_ret_assert (case_post F m)))) (cast_expropt (Some e) tint) id rho)
    with (RA_return (overridePost FF (switch_ret_assert (case_post F m))) (cast_expropt (Some e) tint rho) (id rho)).
  rewrite E. simpl RA_return.
  apply exp_right with r. apply exp_right with m'.
  apply andp_right.
  - apply prop_right. split; auto.
  - exact HP.
Qed.
