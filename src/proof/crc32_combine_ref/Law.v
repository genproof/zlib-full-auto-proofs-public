(* Law crc32_combine_ref: harness_safe of its program, from the shared library (bodies of crc32.c, the
   harness reference functions) and the main of harness/crc32_combine_ref.c (Main.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Zlib.contracts.x_crc32_combine_ref.
Require Import Zlib.harness.x_crc32_combine_ref.code.
Require Import Zlib.proof.crc32.SpecCombine Zlib.proof.crc32.Globals.
Require Import Zlib.proof.crc32.Body_crc32_z Zlib.proof.crc32.Body_combine Zlib.proof.crc32.Body_multmodp
  Zlib.proof.crc32.Body_x2nmodp Zlib.proof.crc32.HarnessRef.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.crc32_combine_ref.Main.

(* The globals of the program: crc32.c's two tables. *)
Lemma W_vars : QPprog_vars p =
  [(Zlib.crc32.code._crc_table, Zlib.crc32.code.v_crc_table); (Zlib.crc32.code._x2n_table, Zlib.crc32.code.v_x2n_table)].
Proof. vm_compute; reflexivity. Qed.

Lemma W_globs gv : (forall i b o, gv i = Vptr b o -> o = Ptrofs.zero) ->
  globvars2pred gv (QPprog_vars p) |-- R gv * TT.
Proof.
  intros HP. rewrite W_vars. unfold globvars2pred, R. simpl map; simpl fold_right.
  sep_apply (crc_table_of_globvar gv (HP _)). sep_apply (x2n_table_of_globvar gv (HP _)). cancel.
Qed.

Definition G : funspecs :=
  [(_main, QPmain_spec_ext' p tt main_post_TT); crc32_z_spec;
   crc32_combine_spec; crc32_combine64_spec; crc32_combine_gen_spec; crc32_combine_gen64_spec;
   crc32_combine_op_spec; multmodp_spec; x2nmodp_spec;
   ref_crc32_spec; ref_crc_byte_spec;
   (_quickproof_malloc, malloc_spec'); (_quickproof_free, free_spec');
   nondet_u32_spec; nondet_bytes_spec; gp_assert_spec; gp_assume_spec].

Theorem crc32_combine_ref_ok : harness_safe p.
Proof.
  harness_safe_by_specs CS G main_post_TT.
  - reflexivity.
  - entry_shared (semax_body_main_core _ _ p _ _ R W_globs body_main eq_refl).
    entry_shared body_crc32_z.
    entry_shared body_crc32_combine.
    entry_shared body_crc32_combine64.
    entry_shared body_crc32_combine_gen.
    entry_shared body_crc32_combine_gen64.
    entry_shared body_crc32_combine_op.
    entry_shared body_multmodp.
    entry_shared body_x2nmodp.
    entry_shared body_ref_crc32.
    entry_shared body_ref_crc_byte.
    entry_external (@external_ok_malloc CS).
    entry_external (@external_ok_free CS).
    entry_external (@external_ok_u32 CS).
    entry_external (@external_ok_bytes CS).
    entry_external (@external_ok_assert CS).
    entry_external (@external_ok_assume CS).
    apply Forall_nil.
Qed.
