(* Law deflate_roundtrip, gzip header: the assembly of the law, with main's context RTRSKit.GmI and
   inflate / inflateGetHeader in G with THE intersections of their Spec5 and v6 specifications
   (RTRSKit.inflate_specI, inflateGetHeader_specI; bodies: LibStmt5's and RTHSpec.rt_head6_stmt's, combined by
   semax_body_binaryintersection''); main's body RTRSMain.rt_main6 (the gzip-header segment proved). *)
Require Import QuickProof.Contract.
Require Zlib.contracts.x_deflate_roundtrip.
Require Zlib.proof.inflate_api.LibStmt5.
Require Zlib.proof.deflate.Obligations Zlib.proof.deflate.Obligations9.
Require Import Zlib.proof.roundtrip.RTXFacts Zlib.proof.roundtrip.RTIIface Zlib.proof.roundtrip.RTHSpec Zlib.proof.roundtrip.RTHIfDefs.

Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.HarnessRef.
Require Import Zlib.proof.adler32.MainLib Zlib.proof.deflate.MainCoreCfg.
Require Zlib.proof.adler32.Spec Zlib.proof.adler32.Body_adler32 Zlib.proof.adler32.Body_adler32_z.
Require Zlib.proof.crc32.Spec Zlib.proof.crc32.Body_crc32 Zlib.proof.crc32.Body_crc32_z.
Require Zlib.proof.zutil.Spec Zlib.proof.zutil.Libc.
Require Zlib.proof.inftrees.spec Zlib.proof.inftrees.verif_inflate_table Zlib.proof.inftrees.part_loop_facts
        Zlib.proof.inftrees.part_seg_counts Zlib.proof.inftrees.part_seg_max0 Zlib.proof.inftrees.part_seg_check
        Zlib.proof.inftrees.part_seg_sort Zlib.proof.inftrees.part_seg_init Zlib.proof.inftrees.part_seg_loop
        Zlib.proof.inftrees.part_seg_fin.
Require Import Zlib.proof.deflate.DSpec Zlib.proof.deflate.DSpec9 Zlib.proof.deflate.Obligations9.
Require Import Zlib.proof.deflate.LawFacts Zlib.proof.deflate.HarnessLib Zlib.proof.deflate.GlobalsInit.
Require Zlib.proof.deflate.GlobalsFixed.
Require Zlib.proof.inflate_api.Spec5 Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.roundtrip.RTRCS Zlib.proof.roundtrip.RTRRunSpec Zlib.proof.roundtrip.RTRRun Zlib.proof.roundtrip.RTRMainSpec Zlib.proof.roundtrip.RTRGlobals.
Require Import Zlib.proof.roundtrip.RTRSKit Zlib.proof.roundtrip.RTRSMain.
Require Import Zlib.harness.x_deflate_roundtrip.code.
#[local] Existing Instance RTRCS.CS.

Module S5 := Zlib.proof.inflate_api.Spec5.

Definition G6 (I : api_inv) (Iend : dstate -> Prop) : funspecs :=
  [(_main, QPmain_spec_ext' p tt main_post_TT); deflate_run_spec I Iend;
   (* trees.c *)
   bi_reverse_spec; bi_flush_spec; bi_windup_spec; tr_flush_bits_spec; tr_align_spec; tr_stored_block_spec;
   gen_codes_spec; pqdownheap_spec; gen_bitlen_spec; build_tree_spec; scan_tree_spec; build_bl_tree_spec;
   detect_data_type_spec; init_block_spec; send_tree_spec; send_all_trees_spec; compress_block_spec;
   tr_static_init_spec; tr_init_spec; tr_flush_block_spec;
   (* deflate.c *)
   read_buf_spec; putShortMSB_spec; flush_pending_spec; slide_hash_spec; longest_match_spec; lm_init_spec;
   fill_window_spec; deflate_stored_spec; deflate_fast_spec; deflate_slow_spec; deflate_rle_spec;
   deflate_huff_spec; deflateStateCheck_spec; deflateResetKeep_spec_v9; deflateReset_spec_v9; deflateSetHeader_spec;
   deflateTune_spec; deflatePrime_spec; deflateBound_z_spec; deflateBound_spec; deflateSetDictionary_spec;
   deflateEnd_spec; deflateInit2__spec_v9; deflate_spec; deflateParams_spec;
   (* inflate.c, inffast.c, inftrees.c *)
   S5.inflateInit2__spec; inflate_specI; S5.inflateSetDictionary_spec; inflateGetHeader_specI;
   S5.inflateEnd_spec; S5.inflateReset_spec; S5.inflateReset2_spec; S5.inflateResetKeep_spec;
   Zlib.proof.inflate.Callees.inflateStateCheck_spec; Zlib.proof.inflate.Callees3.updatewindow_spec3;
   Zlib.proof.inflate.Callees3.inflate_fast_spec3; Zlib.proof.inflate.Callees.inflate_fixed_spec;
   Zlib.proof.inftrees.spec.inflate_table_spec;
   (* adler32.c, crc32.c, zutil.c, libc.c: the allocator and the byte functions at the law's compspecs *)
   Zlib.proof.adler32.Spec.adler32_spec; Zlib.proof.adler32.Spec.adler32_z_spec;
   Zlib.proof.crc32.Spec.crc32_spec; Zlib.proof.crc32.Spec.crc32_z_spec;
   @Zlib.proof.zutil.Spec.zcalloc_spec CS; @Zlib.proof.zutil.Spec.zcfree_spec CS;
   @Zlib.proof.zutil.Libc.memcpy_spec CS; @Zlib.proof.zutil.Libc.memset_spec CS;
   (* the harness *)
   exact_copy_spec; exact_space_spec; stream_defaults_spec; deflate_params_ok_spec;
   draw_nonzero_bytes_spec; bytes_copy_spec; bytes_same_spec; ref_adler32_spec;
   (* the environment *)
   (_quickproof_malloc, malloc_spec'); (_quickproof_free, free_spec');
   nondet_u32_spec; nondet_u8_spec; nondet_bytes_spec; gp_assert_spec; gp_assume_spec].

(* env_spec_sub, robust to transport lemmas whose side conditions unification already closed; plus the moves of
   zcalloc / zcfree / memcpy / memset from a unit's compspecs to the law's *)
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

(* find_ids_V of Assembly unfolds QPvarspecs per variable (minutes): one boolean check instead *)
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

Lemma main_entry6 I Iend :
  api_facts I Iend -> rt_extra I -> ifacts6 -> Zlib.proof.deflate.Obligations.ob_dstream_to_end ->
  semax_body (QPvarspecs p) (GmI I Iend) f_main (_main, QPmain_spec_ext' p tt main_post_TT).
Proof.
  intros AF RX IF DE.
  eapply (semax_body_main_core_cfg _ _ p Zlib.proof.deflate.GlobalsFixed.cfg_funs _ _ Rm).
  - exact rt_globals.
  - apply rt_main6; auto.
  - reflexivity.
Qed.

(* the bodies of the intersections *)
Lemma body_inflateI :
  @semax_body Zlib.proof.inflate.Callees5.Vprog_inflate Zlib.proof.inflate.Callees3.Gprog_inflate3 Zlib.units.Inflate.CS Zlib.inflate.code.f_inflate S5.inflate_spec ->
  @semax_body Zlib.proof.inflate.Callees5.Vprog_inflate Zlib.proof.inflate.Callees3.Gprog_inflate3 Zlib.units.Inflate.CS Zlib.inflate.code.f_inflate inflate_spec6 ->
  @semax_body Zlib.proof.inflate.Callees5.Vprog_inflate Zlib.proof.inflate.Callees3.Gprog_inflate3 Zlib.units.Inflate.CS Zlib.inflate.code.f_inflate inflate_specI.
Proof. intros B5 B6. exact (semax_body_binaryintersection'' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ B5 B6 eq_refl eq_refl). Qed.

Lemma body_inflateGetHeaderI :
  @semax_body Zlib.proof.inflate.Callees5.Vprog_inflate Zlib.proof.inflate_api.Bodies5.Gp_check Zlib.units.Inflate.CS Zlib.inflate.code.f_inflateGetHeader S5.inflateGetHeader_spec ->
  @semax_body Zlib.proof.inflate.Callees5.Vprog_inflate Zlib.proof.inflate_api.Bodies5.Gp_check Zlib.units.Inflate.CS Zlib.inflate.code.f_inflateGetHeader inflateGetHeader_spec6 ->
  @semax_body Zlib.proof.inflate.Callees5.Vprog_inflate Zlib.proof.inflate_api.Bodies5.Gp_check Zlib.units.Inflate.CS Zlib.inflate.code.f_inflateGetHeader inflateGetHeader_specI.
Proof. intros B5 B6. exact (semax_body_binaryintersection'' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ B5 B6 eq_refl eq_refl). Qed.

Theorem rts_deflate_law :
  Zlib.proof.inflate_api.LibStmt5.inflate_lib5_stmt ->
  rt_head6_stmt ->
  Zlib.proof.deflate.Obligations.trees_bodies_ok ->
  Zlib.proof.deflate.Obligations9.deflate_bodies_ok9 ->
  (exists I Iend, api_facts I Iend /\ rt_extra I) -> ifacts6 ->
  harness_safe Zlib.contracts.x_deflate_roundtrip.whole_prog.
Proof.
  intros IL HH6 TB DB [I [Iend [AF RX]]] IF.
  destruct (HH6 NullExtension.Espec) as [B6_gethead B6_inflate].
  destruct IL as (Hinit & Hreset & Hdict & Hmisc & _ & Hbody & Hfast & Hupd & Hfixed & Hcheck).
  destruct Hreset as [_ Hreset].
  destruct (Hinit NullExtension.Espec) as [B_init2 _].
  destruct (Hreset NullExtension.Espec) as (B_resetkeep & B_reset & B_reset2 & B_end).
  destruct (Hdict NullExtension.Espec) as [_ B_setdict].
  destruct (Hmisc NullExtension.Espec) as [B5_gethead _].
  pose proof (Hbody NullExtension.Espec) as B5_inflate.
  pose proof (body_inflateI B5_inflate B6_inflate) as B_inflate.
  pose proof (body_inflateGetHeaderI B5_gethead B6_gethead) as B_gethead.
  pose proof (Hfast NullExtension.Espec) as B_fast.
  pose proof (Hupd NullExtension.Espec) as B_upd.
  pose proof (Hfixed NullExtension.Espec) as B_fixed.
  pose proof (Hcheck NullExtension.Espec) as B_check.
  pose proof (body_inflate_table NullExtension.Espec) as B_table.
  destruct TB as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & T10 & T11 & T12 & T13 & T14 & T15 & T16 &
                  T17 & T18 & T19 & T20).
  destruct DB as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14 & D15 & D16 &
                  D17 & D18 & D19 & D20 & D21 & D22 & D23 & D24 & D25 & _ & _ & DE).
  destruct harness_lib_bodies as (_ & _ & H3 & H4 & H5 & H6 & H7).
  unfold Zlib.proof.deflate.Obligations.ob_bi_reverse, Zlib.proof.deflate.Obligations.ob_bi_flush,
    Zlib.proof.deflate.Obligations.ob_bi_windup, Zlib.proof.deflate.Obligations.ob_tr_flush_bits,
    Zlib.proof.deflate.Obligations.ob_tr_align, Zlib.proof.deflate.Obligations.ob_tr_stored_block,
    Zlib.proof.deflate.Obligations.ob_gen_codes, Zlib.proof.deflate.Obligations.ob_pqdownheap,
    Zlib.proof.deflate.Obligations.ob_gen_bitlen, Zlib.proof.deflate.Obligations.ob_build_tree,
    Zlib.proof.deflate.Obligations.ob_scan_tree, Zlib.proof.deflate.Obligations.ob_build_bl_tree,
    Zlib.proof.deflate.Obligations.ob_detect_data_type, Zlib.proof.deflate.Obligations.ob_init_block,
    Zlib.proof.deflate.Obligations.ob_send_tree, Zlib.proof.deflate.Obligations.ob_send_all_trees,
    Zlib.proof.deflate.Obligations.ob_compress_block, Zlib.proof.deflate.Obligations.ob_tr_static_init,
    Zlib.proof.deflate.Obligations.ob_tr_init, Zlib.proof.deflate.Obligations.ob_tr_flush_block,
    Zlib.proof.deflate.Obligations.ob_read_buf, Zlib.proof.deflate.Obligations.ob_putShortMSB,
    Zlib.proof.deflate.Obligations.ob_flush_pending, Zlib.proof.deflate.Obligations.ob_slide_hash,
    Zlib.proof.deflate.Obligations.ob_longest_match, Zlib.proof.deflate.Obligations.ob_lm_init,
    Zlib.proof.deflate.Obligations.ob_fill_window, Zlib.proof.deflate.Obligations.ob_deflate_stored,
    Zlib.proof.deflate.Obligations.ob_deflate_fast, Zlib.proof.deflate.Obligations.ob_deflate_slow,
    Zlib.proof.deflate.Obligations.ob_deflate_rle, Zlib.proof.deflate.Obligations.ob_deflate_huff,
    Zlib.proof.deflate.Obligations.ob_deflateStateCheck, ob_deflateResetKeep9, ob_deflateReset9,
    Zlib.proof.deflate.Obligations.ob_deflateSetHeader, Zlib.proof.deflate.Obligations.ob_deflateTune,
    Zlib.proof.deflate.Obligations.ob_deflatePrime, Zlib.proof.deflate.Obligations.ob_deflateBound_z,
    Zlib.proof.deflate.Obligations.ob_deflateBound, Zlib.proof.deflate.Obligations.ob_deflateSetDictionary,
    Zlib.proof.deflate.Obligations.ob_deflateEnd, ob_deflateInit2_9, Zlib.proof.deflate.Obligations.ob_deflate,
    Zlib.proof.deflate.Obligations.ob_deflateParams in *.
  pose proof (main_entry6 I Iend AF RX IF DE) as BM.
  pose proof (body_deflate_run I Iend) as BR.
  change Zlib.contracts.x_deflate_roundtrip.whole_prog with p.
  harness_safe_by_specs CS (G6 I Iend) main_post_TT.
  - reflexivity.
  - entry_shared' BM.
    entry_shared' BR.
    entry_shared' T1. entry_shared' T2. entry_shared' T3. entry_shared' T4. entry_shared' T5.
    entry_shared' T6. entry_shared' T7. entry_shared' T8. entry_shared' T9. entry_shared' T10.
    entry_shared' T11. entry_shared' T12. entry_shared' T13. entry_shared' T14. entry_shared' T15.
    entry_shared' T16. entry_shared' T17. entry_shared' T18. entry_shared' T19. entry_shared' T20.
    entry_shared' D1. entry_shared' D2. entry_shared' D3. entry_shared' D4. entry_shared' D5.
    entry_shared' D6. entry_shared' D7. entry_shared' D8. entry_shared' D9. entry_shared' D10.
    entry_shared' D11. entry_shared' D12. entry_shared' D13. entry_shared' D14. entry_shared' D15.
    entry_shared' D16. entry_shared' D17. entry_shared' D18. entry_shared' D19. entry_shared' D20.
    entry_shared' D21. entry_shared' D22. entry_shared' D23. entry_shared' D24. entry_shared' D25.
    entry_shared' B_init2.
    entry_shared' B_inflate.
    entry_shared' B_setdict.
    entry_shared' B_gethead.
    entry_shared' B_end.
    entry_shared' B_reset.
    entry_shared' B_reset2.
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
    entry_shared' H3. entry_shared' H4. entry_shared' H5. entry_shared' H6. entry_shared' H7.
    entry_shared' body_bytes_copy.
    entry_shared' body_bytes_same.
    entry_shared' body_ref_adler32.
    entry_external (@external_ok_malloc CS).
    entry_external (@external_ok_free CS).
    entry_external (@external_ok_u32 CS).
    entry_external (@external_ok_u8 CS).
    entry_external (@external_ok_bytes CS).
    entry_external (@external_ok_assert CS).
    entry_external (@external_ok_assume CS).
    apply Forall_nil.
Qed.
