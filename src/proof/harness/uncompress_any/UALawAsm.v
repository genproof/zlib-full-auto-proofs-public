(* Law uncompress_any: the assembly of harness_safe from the shared bodies (the inflate area's, in the
   hypothesis inflate_lib5_stmt; uncompr's, in the hypothesis uncompr_bodies5_stmt; zutil, libc, adler32, crc32,
   inftrees; the harness helpers), main (UAMain.v) and the theory (UATheory.v and its parts).  As
   inflate_check/IKLawAsm.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.inflate_api.LibStmt5.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.HarnessRef
               Zlib.proof.adler32.MainLib.
Require Zlib.proof.adler32.Spec Zlib.proof.adler32.Body_adler32 Zlib.proof.adler32.Body_adler32_z.
Require Zlib.proof.crc32.Spec Zlib.proof.crc32.Body_crc32 Zlib.proof.crc32.Body_crc32_z.
Require Zlib.proof.zutil.Spec Zlib.proof.zutil.Libc.
Require Zlib.proof.inftrees.spec Zlib.proof.inftrees.verif_inflate_table Zlib.proof.inftrees.part_loop_facts
        Zlib.proof.inftrees.part_seg_counts Zlib.proof.inftrees.part_seg_max0 Zlib.proof.inftrees.part_seg_check
        Zlib.proof.inftrees.part_seg_sort Zlib.proof.inftrees.part_seg_init Zlib.proof.inftrees.part_seg_loop
        Zlib.proof.inftrees.part_seg_fin.
Require Import Zlib.proof.harness.inflate_common.HarnessLib.
Require Import Zlib.proof.uncompr.USpec5 Zlib.proof.uncompr.UBodies5.
Require Import Zlib.proof.harness.uncompress_any.UALawCS Zlib.proof.harness.uncompress_any.UAGlobals
               Zlib.proof.harness.uncompress_any.UAFacts Zlib.proof.harness.uncompress_any.UATheoryDefs
               Zlib.proof.harness.uncompress_any.UALive Zlib.proof.harness.uncompress_any.UAFdict
               Zlib.proof.harness.uncompress_any.UATheory Zlib.proof.harness.uncompress_any.UAMain.
Require Import Zlib.harness.x_uncompress_any.code.

Definition G : funspecs :=
  [(_main, QPmain_spec_ext' p tt main_post_TT);
   uncompress2_z_spec; uncompress2_spec; uncompress_spec;
   inflateInit__spec; inflateInit2__spec; inflate_spec; inflateEnd_spec;
   inflateReset2_spec; inflateReset_spec; inflateResetKeep_spec; inflateStateCheck_spec;
   updatewindow_spec3; inflate_fast_spec3; inflate_fixed_spec; Zlib.proof.inftrees.spec.inflate_table_spec;
   Zlib.proof.adler32.Spec.adler32_spec; Zlib.proof.adler32.Spec.adler32_z_spec;
   Zlib.proof.crc32.Spec.crc32_spec; Zlib.proof.crc32.Spec.crc32_z_spec;
   zcalloc_i; zcfree_i; memcpy_i; memset_i;
   ref_adler32_spec; bytes_copy_spec; bytes_same_spec; be32_spec; exact_space_spec;
   (_quickproof_malloc, malloc_spec'); (_quickproof_free, free_spec');
   nondet_u32_spec; nondet_bytes_spec; gp_assert_spec; gp_assume_spec].

(* env_spec_sub, robust to transport lemmas whose side conditions unification already closed *)
Ltac env_spec_sub' :=
  first [ apply funspec_sub_refl
        | apply nondet_bytes_spec_cs
        | apply malloc_spec'_sub;
          try (apply cspecs_sub_by_computation; vm_compute; reflexivity);
          try (apply preserved_by_computation; vm_compute; reflexivity)
        | apply free_spec'_sub;
          try (apply cspecs_sub_by_computation; vm_compute; reflexivity);
          try (apply preserved_by_computation; vm_compute; reflexivity) ].

Ltac ctx_sub_tac' :=
  let i := fresh "i" in let phi := fresh "phi" in let E := fresh "E" in
  intros i phi E; simpl in E;
  repeat (if_tac in E; [ inv E; eexists; split; [ reflexivity | env_spec_sub' ] | ]);
  try discriminate.

Ltac entry_shared' B :=
  lazymatch type of B with
  | @semax_body _ _ ?cs1 ?f ?spec =>
    apply Forall_cons;
    [ eapply (entry_moved _ _ cs1 _ _ _ _ (fst spec) (snd spec) f B);
      [ reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
      | find_ids_V | vm_compute; reflexivity | vm_compute; reflexivity | ctx_sub_tac' ]
    | ]
  end.

Lemma body_inflate_table : Zlib.proof.inftrees.spec.body_inflate_table_stmt.
Proof.
  pose proof Zlib.proof.inftrees.part_loop_facts.loop_facts_ok as LF.
  apply Zlib.proof.inftrees.verif_inflate_table.body_from_segs.
  - apply Zlib.proof.inftrees.part_seg_counts.seg_counts_ok; exact LF.
  - apply Zlib.proof.inftrees.part_seg_max0.seg_max0_ok; exact LF.
  - apply Zlib.proof.inftrees.part_seg_check.seg_check_ok; exact LF.
  - apply Zlib.proof.inftrees.part_seg_sort.seg_sort_ok; exact LF.
  - apply Zlib.proof.inftrees.part_seg_init.seg_init_ok; exact LF.
  - apply Zlib.proof.inftrees.part_seg_loop.seg_loop_ok; exact LF.
  - apply Zlib.proof.inftrees.part_seg_fin.seg_fin_ok; exact LF.
Qed.

Lemma ua_theory : ua_facts_stmt.
Proof. exact (ua_theory_of ua_live ua_fdict). Qed.

Lemma ua_law_core : inflate_lib5_stmt -> uncompr_bodies5_stmt -> harness_safe p.
Proof.
  intros (Hinit & Hreset & Hdict & Hmisc & Hsync & Hbody & Hfast & Hupd & Hfixed & Hcheck) HU.
  destruct Hreset as [_ Hreset].
  destruct (Hinit NullExtension.Espec) as [B_init2 B_init].
  destruct (Hreset NullExtension.Espec) as (B_resetkeep & B_reset & B_reset2 & B_end).
  pose proof (Hbody NullExtension.Espec) as B_inflate.
  pose proof (Hfast NullExtension.Espec) as B_fast.
  pose proof (Hupd NullExtension.Espec) as B_upd.
  pose proof (Hfixed NullExtension.Espec) as B_fixed.
  pose proof (Hcheck NullExtension.Espec) as B_check.
  destruct (HU NullExtension.Espec) as (B_unc2z & B_unc2 & B_unc).
  pose proof (body_inflate_table NullExtension.Espec) as B_table.
  destruct harness_bytes_bodies as (B_be32 & _ & B_space & _ & _).
  harness_safe_by_specs CS G main_post_TT.
  - reflexivity.
  - entry_shared (semax_body_main_core _ _ p _ _ R globals_ok (body_main ua_theory) eq_refl).
    entry_shared B_unc2z.
    entry_shared B_unc2.
    entry_shared B_unc.
    entry_shared B_init.
    entry_shared B_init2.
    entry_shared B_inflate.
    entry_shared B_end.
    entry_shared B_reset2.
    entry_shared B_reset.
    entry_shared B_resetkeep.
    entry_shared B_check.
    entry_shared B_upd.
    entry_shared B_fast.
    entry_shared B_fixed.
    (* inflate_table's context has inftrees' PROP-False inflate_fixed_spec (never called): G's real one is a
       subspecification of it *)
    apply Forall_cons;
    [ eapply (entry_moved _ _ Zlib.units.Inftrees.CS _ _ _ _ _ _ _ B_table);
      [ reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
      | find_ids_V | vm_compute; reflexivity | vm_compute; reflexivity | ] | ].
    { intros i phi E; simpl in E.
      if_tac in E; [ inv E; eexists; split; [ reflexivity | apply funspec_sub_refl ] | ].
      if_tac in E; [ | discriminate ].
      inv E. eexists; split; [ reflexivity | ].
      apply NDsubsume_subsume; [ split; reflexivity | split; [ split; reflexivity | ] ];
        intros x [ge args]; simpl; unfold PROPx; simpl; normalize. }
    entry_shared Zlib.proof.adler32.Body_adler32.body_adler32.
    entry_shared Zlib.proof.adler32.Body_adler32_z.body_adler32_z.
    entry_shared Zlib.proof.crc32.Body_crc32.body_crc32.
    entry_shared Zlib.proof.crc32.Body_crc32_z.body_crc32_z.
    entry_shared (@Zlib.proof.zutil.Spec.body_zcalloc Zlib.units.Inflate.CS).
    entry_shared (@Zlib.proof.zutil.Spec.body_zcfree Zlib.units.Inflate.CS).
    entry_shared (@Zlib.proof.zutil.Libc.body_memcpy Zlib.units.Inflate.CS).
    entry_shared (@Zlib.proof.zutil.Libc.body_memset Zlib.units.Inflate.CS).
    entry_shared body_ref_adler32.
    entry_shared body_bytes_copy.
    entry_shared body_bytes_same.
    entry_shared B_be32.
    entry_shared' B_space.
    entry_external (@external_ok_malloc CS).
    entry_external (@external_ok_free CS).
    entry_external (@external_ok_u32 CS).
    entry_external (@external_ok_bytes CS).
    entry_external (@external_ok_assert CS).
    entry_external (@external_ok_assume CS).
    apply Forall_nil.
Qed.
