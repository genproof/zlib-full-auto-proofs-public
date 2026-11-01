(* Loop.v's case_post over the corrected model (Model2.v stepf2). *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Export Zlib.proof.inflate.Loop.
Require Export Zlib.proof.inflate.Model2.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Definition case_post2 (F: frame) (m: mst) : ret_assert :=
  {| RA_normal := EX m': mst,
       !! (stepf2 (f_flush F) lenfix_list distfix_list m = IBrk m') && loop_state F m';
     RA_break := FF;
     RA_continue := FF;
     RA_return := fun vl _ => EX r: Z, EX m': mst,
       !! (stepf2 (f_flush F) lenfix_list distfix_list m = IRet r m' /\ vl = Some (zv r)) &&
       (mem_rep F m' * locals_rep F) |}.

Lemma case_post2_eq: forall F m m',
  stepf2 (f_flush F) lenfix_list distfix_list m = stepf2 (f_flush F) lenfix_list distfix_list m' ->
  case_post2 F m = case_post2 F m'.
Proof. intros F m m' E. unfold case_post2. rewrite E. reflexivity. Qed.
