(* Law adler32_combine_ref: harness_safe of its program, from the shared library (bodies of adler32.c, the
   harness reference function ref_adler32) and the main and `valid` of harness/adler32_combine_ref.c (Main.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Zlib.contracts.x_adler32_combine_ref.
Require Import Zlib.harness.x_adler32_combine_ref.code.
Require Import Zlib.proof.adler32.Spec Zlib.proof.adler32.HarnessRef.
Require Import Zlib.proof.adler32.Body_adler32_z Zlib.proof.adler32.Body_adler32_combine.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.adler32_combine_ref.Main.

(* No globals: adler32.c has none. *)
Lemma W_vars : QPprog_vars p = [].
Proof. vm_compute; reflexivity. Qed.

Lemma W_globs gv : (forall i b o, gv i = Vptr b o -> o = Ptrofs.zero) ->
  globvars2pred gv (QPprog_vars p) |-- R gv * TT.
Proof. intros _. rewrite W_vars. unfold globvars2pred, R. simpl. cancel. Qed.

Definition G : funspecs :=
  [(_main, QPmain_spec_ext' p tt main_post_TT); adler32_z_spec; adler32_combine_spec; adler32_combine__spec;
   ref_adler32_spec; valid_spec;
   (_quickproof_malloc, malloc_spec'); (_quickproof_free, free_spec');
   nondet_u32_spec; nondet_bytes_spec; gp_assert_spec; gp_assume_spec].

Theorem adler32_combine_ref_ok : harness_safe p.
Proof.
  harness_safe_by_specs CS G main_post_TT.
  - reflexivity.
  - entry_shared (semax_body_main_core _ _ p _ _ R W_globs body_main eq_refl).
    entry_shared body_adler32_z.
    entry_shared body_adler32_combine.
    entry_shared body_adler32_combine_.
    entry_shared body_ref_adler32.
    entry_shared body_valid.
    entry_external (@external_ok_malloc CS).
    entry_external (@external_ok_free CS).
    entry_external (@external_ok_u32 CS).
    entry_external (@external_ok_bytes CS).
    entry_external (@external_ok_assert CS).
    entry_external (@external_ok_assume CS).
    apply Forall_nil.
Qed.
