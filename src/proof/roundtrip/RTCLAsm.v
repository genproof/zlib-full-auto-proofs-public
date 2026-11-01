(* Law compress_roundtrip, part RT-CL: the assembly of harness_safe from main (RTCLMainDefs.body_main_stmt),
   the shared bodies of trees.c and deflate.c (Obligations9.v), compress.c (RTCSpec.v and Obligations9's
   compressBound), the inflate area (LibStmt5.v), uncompr.c (UBodies5.v), inftrees.c, adler32.c, crc32.c,
   zutil.c, libc.c, the harness's bytes_same and the environment.  As uncompress_any/UALawAsm.v and
   deflate_api9/Law.v.  zcalloc / zcfree / memcpy / memset have ONE specification in G, at the law's compspecs
   (their bodies hold for every compspecs); the units' entries (deflate's at DCS.CS, inflate's at Inflate.CS) are
   subsumed by zutil's zcalloc_spec_sub / zcfree_spec_sub and libc's memcpy_spec_sub / memset_spec_sub. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.inflate_api.LibStmt5.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.MainLib.
Require Zlib.proof.adler32.Spec Zlib.proof.adler32.Body_adler32 Zlib.proof.adler32.Body_adler32_z.
Require Zlib.proof.crc32.Spec Zlib.proof.crc32.Body_crc32 Zlib.proof.crc32.Body_crc32_z.
Require Zlib.proof.zutil.Spec Zlib.proof.zutil.Libc.
Require Zlib.proof.inftrees.spec Zlib.proof.inftrees.verif_inflate_table Zlib.proof.inftrees.part_loop_facts
        Zlib.proof.inftrees.part_seg_counts Zlib.proof.inftrees.part_seg_max0 Zlib.proof.inftrees.part_seg_check
        Zlib.proof.inftrees.part_seg_sort Zlib.proof.inftrees.part_seg_init Zlib.proof.inftrees.part_seg_loop
        Zlib.proof.inftrees.part_seg_fin.
Require Import Zlib.proof.uncompr.USpec5 Zlib.proof.uncompr.UBodies5.
Require Import Zlib.proof.deflate.DSpec Zlib.proof.deflate.DSpec9 Zlib.proof.deflate.Obligations9.
Require Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.MainCoreCfg.
Require Import Zlib.proof.compress.CSpec.
Require Import Zlib.proof.roundtrip.RTCSpec.
Require Import Zlib.proof.roundtrip.RTC2 Zlib.proof.roundtrip.RTIIface.
Require Import Zlib.proof.roundtrip.RTCLCS Zlib.proof.roundtrip.RTCLGlobals Zlib.proof.roundtrip.RTCLMainDefs.
Require Import Zlib.harness.x_compress_roundtrip.code.
#[local] Existing Instance RTCLCS.CS.

Definition G : funspecs :=
  [(_main, QPmain_spec_ext' p tt main_post_TT);
   (* compress.c *)
   compress2_z_spec; compress2_spec; compress_z_spec; compress_spec; compressBound_z_spec; compressBound_spec;
   (* trees.c *)
   bi_reverse_spec; bi_flush_spec; bi_windup_spec; tr_flush_bits_spec; tr_align_spec; tr_stored_block_spec;
   gen_codes_spec; pqdownheap_spec; gen_bitlen_spec; build_tree_spec; scan_tree_spec; build_bl_tree_spec;
   detect_data_type_spec; init_block_spec; send_tree_spec; send_all_trees_spec; compress_block_spec;
   tr_static_init_spec; tr_init_spec; tr_flush_block_spec;
   (* deflate.c *)
   read_buf_spec; putShortMSB_spec; flush_pending_spec; slide_hash_spec; longest_match_spec; lm_init_spec;
   fill_window_spec; deflate_stored_spec; deflate_fast_spec; deflate_slow_spec; deflate_rle_spec;
   deflate_huff_spec; deflateStateCheck_spec; deflateResetKeep_spec_v9; deflateReset_spec_v9;
   deflateEnd_spec; deflateInit2__spec_v9; deflateInit__spec; deflate_spec;
   (* uncompr.c, inflate.c, inffast.c, inftrees.c *)
   uncompress2_z_spec; uncompress2_spec; uncompress_spec;
   inflateInit__spec; inflateInit2__spec; inflate_spec; inflateEnd_spec;
   inflateReset2_spec; inflateReset_spec; inflateResetKeep_spec; inflateStateCheck_spec;
   updatewindow_spec3; inflate_fast_spec3; inflate_fixed_spec; Zlib.proof.inftrees.spec.inflate_table_spec;
   (* adler32.c, crc32.c, zutil.c, libc.c *)
   Zlib.proof.adler32.Spec.adler32_spec; Zlib.proof.adler32.Spec.adler32_z_spec;
   Zlib.proof.crc32.Spec.crc32_spec; Zlib.proof.crc32.Spec.crc32_z_spec;
   @Zlib.proof.zutil.Spec.zcalloc_spec CS; @Zlib.proof.zutil.Spec.zcfree_spec CS;
   @Zlib.proof.zutil.Libc.memcpy_spec CS; @Zlib.proof.zutil.Libc.memset_spec CS;
   (* the harness and the environment *)
   bytes_same_spec;
   (_quickproof_malloc, malloc_spec'); (_quickproof_free, free_spec');
   nondet_u32_spec; nondet_u8_spec; nondet_bytes_spec; gp_assert_spec; gp_assume_spec].

(* env_spec_sub (QuickProof.Assembly), robust to transport lemmas whose side conditions unification already
   closed, with the zutil / libc moves of the units' specifications to the law's compspecs *)
Ltac env_spec_sub' :=
  first [ apply funspec_sub_refl
        | apply nondet_bytes_spec_cs
        | apply malloc_spec'_sub;
          try (apply cspecs_sub_by_computation; vm_compute; reflexivity);
          try (apply preserved_by_computation; vm_compute; reflexivity)
        | apply free_spec'_sub;
          try (apply cspecs_sub_by_computation; vm_compute; reflexivity);
          try (apply preserved_by_computation; vm_compute; reflexivity)
        | apply Zlib.proof.zutil.Spec.zcalloc_spec_sub;
          try (apply cspecs_sub_by_computation; vm_compute; reflexivity);
          try (apply preserved_by_computation; vm_compute; reflexivity)
        | apply Zlib.proof.zutil.Spec.zcfree_spec_sub;
          try (apply cspecs_sub_by_computation; vm_compute; reflexivity);
          try (apply preserved_by_computation; vm_compute; reflexivity)
        | apply Zlib.proof.zutil.Libc.memcpy_spec_sub
        | apply Zlib.proof.zutil.Libc.memset_spec_sub ].

Ltac ctx_sub_tac' :=
  let i := fresh "i" in let phi := fresh "phi" in let E := fresh "E" in
  intros i phi E; simpl in E;
  repeat (if_tac in E; [ inv E; eexists; split; [ reflexivity | env_spec_sub' ] | ]);
  try discriminate.

(* find_ids_V of Assembly unfolds QPvarspecs per variable (minutes): one boolean check instead (deflate_api9) *)
Lemma find_ids_b (V W : varspecs) :
  forallb (fun x => match initial_world.find_id (fst x) W with Some t => eqb_type t (snd x) | None => false end) V = true ->
  Forall (fun x => initial_world.find_id (fst x) W = Some (snd x)) V.
Proof.
  intros H. rewrite forallb_forall in H. rewrite Forall_forall. intros x IN. specialize (H x IN).
  destruct (initial_world.find_id (fst x) W) as [t|]; [ | discriminate]. apply eqb_type_spec in H. subst; reflexivity.
Qed.

Ltac entry_shared' B :=
  lazymatch type of B with
  | @semax_body _ _ ?cs1 ?f ?spec =>
    apply Forall_cons;
    [ eapply (entry_moved _ _ cs1 _ _ _ _ (fst spec) (snd spec) f B);
      [ reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
      | apply find_ids_b; vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
      | ctx_sub_tac' ]
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

Lemma main_entry :
  body_main_stmt -> c2_ok -> ufacts ->
  semax_body (QPvarspecs p) Gmain f_main (_main, QPmain_spec_ext' p tt main_post_TT).
Proof.
  intros BM CF UF.
  eapply (semax_body_main_core_cfg _ _ p cfg_funs _ _ R).
  - intros gv H1 H2. apply globals_ok; auto.
  - apply BM; auto.
  - reflexivity.
Qed.

Theorem rt_compress_core :
  body_main_stmt ->
  inflate_lib5_stmt -> uncompr_bodies5_stmt -> trees_bodies_ok -> deflate_bodies_ok9 ->
  rt_compress_bodies_stmt -> c2_ok -> ufacts ->
  harness_safe Zlib.contracts.x_compress_roundtrip.whole_prog.
Proof.
  intros BMS LI HU TB DB CB CF UF.
  destruct LI as (Hinit & Hreset & Hdict & Hmisc & Hsync & Hbody & Hfast & Hupd & Hfixed & Hcheck).
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
  destruct TB as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & T10 & T11 & T12 & T13 & T14 & T15 & T16 &
                  T17 & T18 & T19 & T20).
  destruct DB as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14 & D15 & D16 &
                  D17 & D18 & D19 & D20 & D21 & D22 & D23 & D24 & D25 & D26 & D27 & _).
  destruct CB as (C1 & C2 & C3 & C4 & C5).
  unfold ob_bi_reverse, ob_bi_flush, ob_bi_windup, ob_tr_flush_bits, ob_tr_align, ob_tr_stored_block,
    ob_gen_codes, ob_pqdownheap, ob_gen_bitlen, ob_build_tree, ob_scan_tree, ob_build_bl_tree,
    ob_detect_data_type, ob_init_block, ob_send_tree, ob_send_all_trees, ob_compress_block, ob_tr_static_init,
    ob_tr_init, ob_tr_flush_block, ob_read_buf, ob_putShortMSB, ob_flush_pending, ob_slide_hash,
    ob_longest_match, ob_lm_init, ob_fill_window, ob_deflate_stored, ob_deflate_fast, ob_deflate_slow,
    ob_deflate_rle, ob_deflate_huff, ob_deflateStateCheck, ob_deflateResetKeep9, ob_deflateReset9,
    ob_deflateSetHeader, ob_deflateTune, ob_deflatePrime, ob_deflateBound_z, ob_deflateBound,
    ob_deflateSetDictionary, ob_deflateEnd, ob_deflateInit2_9, ob_deflate, ob_deflateParams,
    ob_compressBound_z, ob_compressBound,
    ob_deflateInit_, ob_compress2_z, ob_compress2, ob_compress_z, ob_compress in *.
  pose proof (main_entry BMS CF UF) as BM.
  change Zlib.contracts.x_compress_roundtrip.whole_prog with p.
  harness_safe_by_specs CS G main_post_TT.
  - reflexivity.
  - entry_shared' BM.
    entry_shared' C2. entry_shared' C3. entry_shared' C4. entry_shared' C5. entry_shared' D26. entry_shared' D27.
    entry_shared' T1. entry_shared' T2. entry_shared' T3. entry_shared' T4. entry_shared' T5.
    entry_shared' T6. entry_shared' T7. entry_shared' T8. entry_shared' T9. entry_shared' T10.
    entry_shared' T11. entry_shared' T12. entry_shared' T13. entry_shared' T14. entry_shared' T15.
    entry_shared' T16. entry_shared' T17. entry_shared' T18. entry_shared' T19. entry_shared' T20.
    entry_shared' D1. entry_shared' D2. entry_shared' D3. entry_shared' D4. entry_shared' D5.
    entry_shared' D6. entry_shared' D7. entry_shared' D8. entry_shared' D9. entry_shared' D10.
    entry_shared' D11. entry_shared' D12. entry_shared' D13. entry_shared' D14. entry_shared' D15.
    entry_shared' D22. entry_shared' D23. entry_shared' C1. entry_shared' D24.
    entry_shared' B_unc2z.
    entry_shared' B_unc2.
    entry_shared' B_unc.
    entry_shared' B_init.
    entry_shared' B_init2.
    entry_shared' B_inflate.
    entry_shared' B_end.
    entry_shared' B_reset2.
    entry_shared' B_reset.
    entry_shared' B_resetkeep.
    entry_shared' B_check.
    entry_shared' B_upd.
    entry_shared' B_fast.
    entry_shared' B_fixed.
    (* inflate_table's context has inftrees' PROP-False inflate_fixed_spec (never called): G's real one is a
       subspecification of it *)
    apply Forall_cons;
    [ eapply (entry_moved _ _ Zlib.units.Inftrees.CS _ _ _ _ _ _ _ B_table);
      [ reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
      | apply find_ids_b; vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | ] | ].
    { intros i phi E; simpl in E.
      if_tac in E; [ inv E; eexists; split; [ reflexivity | apply funspec_sub_refl ] | ].
      if_tac in E; [ | discriminate ].
      inv E. eexists; split; [ reflexivity | ].
      apply NDsubsume_subsume; [ split; reflexivity | split; [ split; reflexivity | ] ];
        intros x [ge args]; simpl; unfold PROPx; simpl; normalize. }
    entry_shared' Zlib.proof.adler32.Body_adler32.body_adler32.
    entry_shared' Zlib.proof.adler32.Body_adler32_z.body_adler32_z.
    entry_shared' Zlib.proof.crc32.Body_crc32.body_crc32.
    entry_shared' Zlib.proof.crc32.Body_crc32_z.body_crc32_z.
    entry_shared' (@Zlib.proof.zutil.Spec.body_zcalloc CS).
    entry_shared' (@Zlib.proof.zutil.Spec.body_zcfree CS).
    entry_shared' (@Zlib.proof.zutil.Libc.body_memcpy CS).
    entry_shared' (@Zlib.proof.zutil.Libc.body_memset CS).
    entry_shared' body_bytes_same.
    entry_external (@external_ok_malloc CS).
    entry_external (@external_ok_free CS).
    entry_external (@external_ok_u32 CS).
    entry_external (@external_ok_u8 CS).
    entry_external (@external_ok_bytes CS).
    entry_external (@external_ok_assert CS).
    entry_external (@external_ok_assume CS).
    apply Forall_nil.
Qed.
