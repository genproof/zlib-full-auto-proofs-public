(* Callees3.v with the right global variables: Callees3's Delta_cases3 / Delta_inflate3 picked up
   Zlib.proof.zutil.Libc.Vprog (shadowing) instead of inflate's (string literals, order[]). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Export Zlib.proof.inflate.Callees3.
Require Export Zlib.proof.inflate.Loop2.
Require VST.veric.semax_prog.

#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Definition Vprog_inflate : varspecs := Zlib.proof.inflate.CaseCommon.Vprog.

Definition Delta_cases5 : tycontext := func_tycontext f_inflate Vprog_inflate Gprog_cases3 nil.
Definition Delta_inflate5 : tycontext := func_tycontext f_inflate Vprog_inflate Gprog_inflate3 nil.

Lemma Vprog_inflate_globals: In ___stringlit_inflate_14 (map fst Vprog_inflate) /\ In _order (map fst Vprog_inflate).
Proof. vm_compute. split; intuition. Qed.

Lemma sub_cases_inflate5 : tycontext_sub Delta_cases5 Delta_inflate5.
Proof.
  apply VST.veric.semax_prog.func_tycontext_sub.
  - apply incl_refl.
  - unfold Gprog_inflate3. apply incl_appl. apply incl_refl.
  - apply list_norepet_NoDup. apply compute_list_norepet_e. vm_compute. reflexivity.
Qed.

Lemma semax_cases_inflate5 {Espec: OracleKind}: forall P c R,
  semax Delta_cases5 P c R -> semax Delta_inflate5 P c R.
Proof. intros. eapply semax_Delta_subsumption; [apply sub_cases_inflate5 | auto]. Qed.
