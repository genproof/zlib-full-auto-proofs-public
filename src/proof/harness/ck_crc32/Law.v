(* Law ck_crc32: harness_safe of its program, from the shared library (crc32_z's body, the bodies of the
   laws_common.h helpers upto and any_bytes, given as the hypothesis laws_common_ok) and the main of
   harness/ck_crc32.c (Main.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Zlib.contracts.ck_crc32.
Require Import Zlib.harness.ck_crc32.code.
Require Import Zlib.proof.crc32.Spec Zlib.proof.crc32.Globals Zlib.proof.crc32.Body_crc32_z.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.ck_crc32.Main.

(* The globals of the program: crc32.c's two tables; main needs crc_table. *)
Lemma W_vars : QPprog_vars p =
  [(Zlib.crc32.code._crc_table, Zlib.crc32.code.v_crc_table); (Zlib.crc32.code._x2n_table, Zlib.crc32.code.v_x2n_table)].
Proof. vm_compute; reflexivity. Qed.

Lemma W_globs gv : (forall i b o, gv i = Vptr b o -> o = Ptrofs.zero) ->
  globvars2pred gv (QPprog_vars p) |-- R gv * TT.
Proof.
  intros HP. rewrite W_vars. unfold globvars2pred, R. simpl map; simpl fold_right.
  sep_apply (crc_table_of_globvar gv (HP _)). cancel.
Qed.

Definition G : funspecs :=
  [(_main, QPmain_spec_ext' p tt main_post_TT); upto_spec; any_bytes_spec; crc32_z_spec;
   (_quickproof_malloc, malloc_spec'); nondet_size_spec; nondet_u32_spec; nondet_bytes_spec; gp_assert_spec].

Theorem ck_crc32_ok : laws_common_ok -> harness_safe p.
Proof.
  intros (B_upto & _ & B_any_bytes & _).
  harness_safe_by_specs CS G main_post_TT.
  - reflexivity.
  - entry_shared (semax_body_main_core _ _ p _ _ R W_globs body_main eq_refl).
    entry_shared B_upto.
    entry_shared B_any_bytes.
    entry_shared body_crc32_z.
    entry_external (@external_ok_malloc CS).
    entry_external (@external_ok_size CS).
    entry_external (@external_ok_u32 CS).
    entry_external (@external_ok_bytes CS).
    entry_external (@external_ok_assert CS).
    apply Forall_nil.
Qed.
