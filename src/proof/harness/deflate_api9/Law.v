(* Law deflate_api: the assembly of harness_safe from main (Main.v), deflate_run (Run.v), the bodies of trees.c and
   deflate.c (Obligations.v), the harness helpers (HarnessLib.v, adler32/HarnessBytes.v, the reference functions),
   adler32.c, crc32.c, zutil.c, libc.c and the environment. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.HarnessRef.
Require Import Zlib.proof.adler32.MainLib Zlib.proof.deflate.MainCoreCfg.
Require Zlib.proof.crc32.HarnessRef.
Require Zlib.proof.adler32.Spec Zlib.proof.adler32.Body_adler32 Zlib.proof.adler32.Body_adler32_z.
Require Zlib.proof.crc32.Spec Zlib.proof.crc32.Body_crc32 Zlib.proof.crc32.Body_crc32_z.
Require Zlib.proof.zutil.Spec Zlib.proof.zutil.Libc.
Require Import Zlib.proof.deflate.DSpec Zlib.proof.deflate.DSpec9 Zlib.proof.deflate.Obligations9.
Require Import Zlib.proof.deflate.LawFacts Zlib.proof.deflate.HarnessLib Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.harness.deflate_api.ApiCS Zlib.proof.harness.deflate_api9.RunSpec
               Zlib.proof.harness.deflate_api9.RunKit Zlib.proof.harness.deflate_api9.MainKit
               Zlib.proof.harness.deflate_api9.RunMem Zlib.proof.harness.deflate_api9.Run
               Zlib.proof.harness.deflate_api9.Main.
Require Import Zlib.harness.x_deflate_api.code.
#[local] Existing Instance ApiCS.CS.

Definition G (I : api_inv) (Iend : dstate -> Prop) : funspecs :=
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
   (* adler32.c, crc32.c, zutil.c, libc.c *)
   Zlib.proof.adler32.Spec.adler32_spec; Zlib.proof.adler32.Spec.adler32_z_spec;
   Zlib.proof.crc32.Spec.crc32_spec; Zlib.proof.crc32.Spec.crc32_z_spec;
   @Zlib.proof.zutil.Spec.zcalloc_spec DCS.CS; @Zlib.proof.zutil.Spec.zcfree_spec DCS.CS;
   @Zlib.proof.zutil.Libc.memcpy_spec DCS.CS; @Zlib.proof.zutil.Libc.memset_spec DCS.CS;
   (* the harness *)
   be32_spec; le32_spec; exact_copy_spec; exact_space_spec; stream_defaults_spec; deflate_params_ok_spec;
   draw_nonzero_bytes_spec; bytes_copy_spec; bytes_same_spec; ref_adler32_spec;
   Zlib.proof.crc32.HarnessRef.ref_crc32_spec; Zlib.proof.crc32.HarnessRef.ref_crc_byte_spec;
   (* the environment *)
   (_quickproof_malloc, malloc_spec'); (_quickproof_free, free_spec');
   nondet_u32_spec; nondet_u8_spec; nondet_bytes_spec; gp_assert_spec; gp_assume_spec].

(* env_spec_sub, robust to transport lemmas whose side conditions unification already closed (as in the
   inflate_codes law) *)
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

Lemma main_entry I Iend :
  api_facts I Iend -> ob_dstream_to_end -> globals_of p vlit ->
  semax_body (QPvarspecs p) (Gmain I Iend) f_main (_main, QPmain_spec_ext' p tt main_post_TT).
Proof.
  intros AF DE Ga.
  eapply (semax_body_main_core_cfg _ _ p
            [Zlib.deflate.code._deflate_stored; Zlib.deflate.code._deflate_fast; Zlib.deflate.code._deflate_slow]
            _ _ Rm).
  - intros gv H1 H2. unfold Rm. apply Ga; auto.
  - apply body_main; auto. exact run_mem.
  - reflexivity.
Qed.

Theorem deflate_api_core :
  (exists I Iend, api_facts I Iend) -> trees_bodies_ok -> deflate_bodies_ok9 -> harness_lib_ok -> globals_ok ->
  harness_safe Zlib.contracts.x_deflate_api.whole_prog.
Proof.
  intros [I [Iend AF]] TB DB HL GL.
  destruct TB as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & T10 & T11 & T12 & T13 & T14 & T15 & T16 &
                  T17 & T18 & T19 & T20).
  destruct DB as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14 & D15 & D16 &
                  D17 & D18 & D19 & D20 & D21 & D22 & D23 & D24 & D25 & _ & _ & DE).
  destruct HL as (H1 & H2 & H3 & H4 & H5 & H6 & H7).
  destruct GL as [Ga _].
  unfold ob_bi_reverse, ob_bi_flush, ob_bi_windup, ob_tr_flush_bits, ob_tr_align, ob_tr_stored_block,
    ob_gen_codes, ob_pqdownheap, ob_gen_bitlen, ob_build_tree, ob_scan_tree, ob_build_bl_tree,
    ob_detect_data_type, ob_init_block, ob_send_tree, ob_send_all_trees, ob_compress_block, ob_tr_static_init,
    ob_tr_init, ob_tr_flush_block, ob_read_buf, ob_putShortMSB, ob_flush_pending, ob_slide_hash,
    ob_longest_match, ob_lm_init, ob_fill_window, ob_deflate_stored, ob_deflate_fast, ob_deflate_slow,
    ob_deflate_rle, ob_deflate_huff, ob_deflateStateCheck, ob_deflateResetKeep9, ob_deflateReset9,
    ob_deflateSetHeader, ob_deflateTune, ob_deflatePrime, ob_deflateBound_z, ob_deflateBound,
    ob_deflateSetDictionary, ob_deflateEnd, ob_deflateInit2_9, ob_deflate, ob_deflateParams in *.
  pose proof (main_entry I Iend AF DE Ga) as BM.
  pose proof (body_deflate_run I Iend) as BR.
  change Zlib.contracts.x_deflate_api.whole_prog with p.
  harness_safe_by_specs CS (G I Iend) main_post_TT.
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
    entry_shared' Zlib.proof.adler32.Body_adler32.body_adler32.
    entry_shared' Zlib.proof.adler32.Body_adler32_z.body_adler32_z.
    entry_shared' Zlib.proof.crc32.Body_crc32.body_crc32.
    entry_shared' Zlib.proof.crc32.Body_crc32_z.body_crc32_z.
    entry_shared' (@Zlib.proof.zutil.Spec.body_zcalloc DCS.CS).
    entry_shared' (@Zlib.proof.zutil.Spec.body_zcfree DCS.CS).
    entry_shared' (@Zlib.proof.zutil.Libc.body_memcpy DCS.CS).
    entry_shared' (@Zlib.proof.zutil.Libc.body_memset DCS.CS).
    entry_shared' H1. entry_shared' H2. entry_shared' H3. entry_shared' H4. entry_shared' H5.
    entry_shared' H6. entry_shared' H7.
    entry_shared' body_bytes_copy.
    entry_shared' body_bytes_same.
    entry_shared' body_ref_adler32.
    entry_shared' Zlib.proof.crc32.HarnessRef.body_ref_crc32.
    entry_shared' Zlib.proof.crc32.HarnessRef.body_ref_crc_byte.
    entry_external (@external_ok_malloc CS).
    entry_external (@external_ok_free CS).
    entry_external (@external_ok_u32 CS).
    entry_external (@external_ok_u8 CS).
    entry_external (@external_ok_bytes CS).
    entry_external (@external_ok_assert CS).
    entry_external (@external_ok_assume CS).
    apply Forall_nil.
Qed.
