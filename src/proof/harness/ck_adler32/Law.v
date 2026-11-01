(* Law ck_adler32: harness_safe of its program, from the shared library (the body of adler32_z, the bodies
   of the laws_common.h helpers upto and any_bytes, given as the hypothesis laws_common_ok) and the main of
   harness/ck_adler32.c (Main.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Zlib.contracts.ck_adler32.
Require Import Zlib.harness.ck_adler32.code.
Require Import Zlib.proof.adler32.Spec Zlib.proof.adler32.Body_adler32_z Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.ck_adler32.Main.

(* adler32.c has no globals. *)
Lemma W_vars : QPprog_vars p = [].
Proof. vm_compute; reflexivity. Qed.

Lemma W_globs gv : (forall i b o, gv i = Vptr b o -> o = Ptrofs.zero) ->
  globvars2pred gv (QPprog_vars p) |-- R gv * TT.
Proof.
  intros _. rewrite W_vars. unfold globvars2pred, R. simpl. cancel.
Qed.

Definition G : funspecs :=
  [(_main, QPmain_spec_ext' p tt main_post_TT); upto_spec; any_bytes_spec; adler32_z_spec;
   (_quickproof_malloc, malloc_spec'); nondet_size_spec; nondet_bytes_spec; gp_assert_spec].

Theorem ck_adler32_ok : laws_common_ok -> harness_safe p.
Proof.
  intros (B_upto & _ & B_any_bytes & _).
  harness_safe_by_specs CS G main_post_TT.
  - reflexivity.
  - entry_shared (semax_body_main_core _ _ p _ _ R W_globs body_main eq_refl).
    entry_shared B_upto.
    entry_shared B_any_bytes.
    entry_shared body_adler32_z.
    entry_external (@external_ok_malloc CS).
    entry_external (@external_ok_size CS).
    entry_external (@external_ok_bytes CS).
    entry_external (@external_ok_assert CS).
    apply Forall_nil.
Qed.
