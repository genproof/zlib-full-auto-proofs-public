(* RT-H: mechanical port of inflate/Loop2.v to the header-external loop state (RTHLoop.v); identifiers whose meaning changes carry the suffix H. *)
(* Loop.v's case_postH over the corrected model (Model2.v stepf2). *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Export Zlib.proof.roundtrip.RTHLoop.
Require Export Zlib.proof.inflate.Model2.
Require Export Zlib.proof.inflate.Loop2.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Definition case_post2H (F: frame) (m: mst) : ret_assert :=
  {| RA_normal := EX m': mst,
       !! (stepf2 (f_flush F) lenfix_list distfix_list m = IBrk m') && loop_stateH F m';
     RA_break := FF;
     RA_continue := FF;
     RA_return := fun vl _ => EX r: Z, EX m': mst,
       !! (stepf2 (f_flush F) lenfix_list distfix_list m = IRet r m' /\ vl = Some (zv r)) &&
       (mem_repH F m' * locals_rep F) |}.

Lemma case_post2_eqH: forall F m m',
  stepf2 (f_flush F) lenfix_list distfix_list m = stepf2 (f_flush F) lenfix_list distfix_list m' ->
  case_post2H F m = case_post2H F m'.
Proof. intros F m m' E. unfold case_post2H. rewrite E. reflexivity. Qed.
