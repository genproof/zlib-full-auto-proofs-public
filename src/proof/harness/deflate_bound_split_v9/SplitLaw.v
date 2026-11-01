(* Law deflate_bound_split: the assembly.  harness_safe of the program from main (SplitMain.v, moved from DCS.CS
   to the law's compspecs) and the shared bodies: the harness helpers (HarnessLib, HarnessBytes), deflate.c and
   trees.c (Obligations), adler32.c, crc32.c, zutil.c, libc.c, and the environment. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DCS Zlib.proof.deflate.DSpec Zlib.proof.deflate.DSpec9 Zlib.proof.deflate.Obligations9.
Require Import Zlib.proof.deflate.LawFacts Zlib.proof.deflate.HarnessLib Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.deflate.MainCoreCfg.
Require Zlib.proof.adler32.Spec Zlib.proof.adler32.Body_adler32 Zlib.proof.adler32.Body_adler32_z.
Require Zlib.proof.crc32.Spec Zlib.proof.crc32.Body_crc32 Zlib.proof.crc32.Body_crc32_z.
Require Zlib.proof.zutil.Spec Zlib.proof.zutil.Libc.
Require Zlib.contracts.x_deflate_bound_split.
Require Import Zlib.harness.x_deflate_bound_split.code.
Require Import Zlib.proof.harness.deflate_bound_split_v9.SplitMain Zlib.proof.harness.deflate_bound_split_v9.SplitBody.

Definition comps := ltac:(let x := eval vm_compute in (prog_composites p) in exact x).
Definition cprog : Clight.program := Clightdefs.mkprogram comps nil nil 1%positive Logic.I.
#[export] Instance CS : compspecs. make_compspecs cprog. Defined.

Definition G : funspecs :=
  [(_main, QPmain_spec_ext' p tt main_post_TT);
   (* the harness *)
   deflate_params_ok_spec; draw_nonzero_bytes_spec; stream_defaults_spec; exact_copy_spec; exact_space_spec;
   bytes_copy_spec;
   (* deflate.c *)
   deflateInit2__spec_v9; deflateSetDictionary_spec; deflateSetHeader_spec; deflateBound_spec; deflate_spec;
   deflateEnd_spec; deflateBound_z_spec; deflateStateCheck_spec; deflateReset_spec_v9; deflateResetKeep_spec_v9;
   lm_init_spec; fill_window_spec; slide_hash_spec; read_buf_spec; flush_pending_spec; putShortMSB_spec;
   longest_match_spec; deflate_stored_spec; deflate_fast_spec; deflate_slow_spec; deflate_rle_spec;
   deflate_huff_spec;
   (* trees.c *)
   tr_init_spec; tr_static_init_spec; init_block_spec; tr_flush_bits_spec; bi_flush_spec; tr_align_spec;
   tr_stored_block_spec; bi_windup_spec; tr_flush_block_spec; detect_data_type_spec; build_tree_spec;
   pqdownheap_spec; gen_bitlen_spec; gen_codes_spec; bi_reverse_spec; build_bl_tree_spec; scan_tree_spec;
   compress_block_spec; send_all_trees_spec; send_tree_spec;
   (* adler32.c, crc32.c, zutil.c, libc.c *)
   Zlib.proof.adler32.Spec.adler32_spec; Zlib.proof.adler32.Spec.adler32_z_spec;
   Zlib.proof.crc32.Spec.crc32_spec; Zlib.proof.crc32.Spec.crc32_z_spec;
   @Zlib.proof.zutil.Spec.zcalloc_spec DCS.CS; @Zlib.proof.zutil.Spec.zcfree_spec DCS.CS;
   @Zlib.proof.zutil.Libc.memcpy_spec DCS.CS; @Zlib.proof.zutil.Libc.memset_spec DCS.CS;
   (* the environment *)
   (_quickproof_malloc, @malloc_spec' CS); (_quickproof_free, @free_spec' CS);
   nondet_u32_spec; nondet_u8_spec; @nondet_bytes_spec CS; gp_assert_spec; gp_assume_spec].

Theorem split_law_of_parts :
  (exists Bpre Brun, bound_facts Bpre Brun) -> trees_bodies_ok -> deflate_bodies_ok9 -> harness_lib_ok ->
  globals_ok -> harness_safe p.
Proof.
  intros [Bpre [Brun BF]] TB DB HL GL.
  destruct GL as [_ [_ Gs]].
  destruct TB as (T_bi_reverse & T_bi_flush & T_bi_windup & T_tr_flush_bits & T_tr_align & T_tr_stored_block &
    T_gen_codes & T_pqdownheap & T_gen_bitlen & T_build_tree & T_scan_tree & T_build_bl_tree &
    T_detect_data_type & T_init_block & T_send_tree & T_send_all_trees & T_compress_block & T_tr_static_init &
    T_tr_init & T_tr_flush_block).
  destruct DB as (D_read_buf & D_putShortMSB & D_flush_pending & D_slide_hash & D_longest_match & D_lm_init &
    D_fill_window & D_deflate_stored & D_deflate_fast & D_deflate_slow & D_deflate_rle & D_deflate_huff &
    D_deflateStateCheck & D_deflateResetKeep & D_deflateReset & D_deflateSetHeader & D_deflateTune &
    D_deflatePrime & D_deflateBound_z & D_deflateBound & D_deflateSetDictionary & D_deflateEnd &
    D_deflateInit2_ & D_deflate & D_deflateParams & D_compressBound_z & D_compressBound & D_to_end).
  destruct HL as (H_be32 & H_le32 & H_exact_copy & H_exact_space & H_stream_defaults & H_deflate_params_ok &
    H_draw_nonzero_bytes).
  unfold ob_bi_reverse, ob_bi_flush, ob_bi_windup, ob_tr_flush_bits, ob_tr_align, ob_tr_stored_block, ob_gen_codes, ob_pqdownheap, ob_gen_bitlen, ob_build_tree, ob_scan_tree, ob_build_bl_tree, ob_detect_data_type, ob_init_block, ob_send_tree, ob_send_all_trees, ob_compress_block, ob_tr_static_init, ob_tr_init, ob_tr_flush_block, ob_read_buf, ob_putShortMSB, ob_flush_pending, ob_slide_hash, ob_longest_match, ob_lm_init, ob_fill_window, ob_deflate_stored, ob_deflate_fast, ob_deflate_slow, ob_deflate_rle, ob_deflate_huff, ob_deflateStateCheck, ob_deflateResetKeep9, ob_deflateReset9, ob_deflateSetHeader, ob_deflateTune, ob_deflatePrime, ob_deflateBound_z, ob_deflateBound, ob_deflateSetDictionary, ob_deflateEnd, ob_deflateInit2_9, ob_deflate, ob_deflateParams, ob_compressBound_z, ob_compressBound in *.
  assert (GLs : forall gv, (forall i b o, gv i = Vptr b o -> o = Ptrofs.zero) ->
    (forall f, In f [Zlib.deflate.code._deflate_stored; Zlib.deflate.code._deflate_fast;
                     Zlib.deflate.code._deflate_slow] -> gv f = Vundef \/ isptr (gv f)) ->
    globvars2pred gv (QPprog_vars p) |-- Rm gv * TT).
  { intros gv H1 H2. unfold Rm. apply Gs; auto. }
  pose proof (semax_body_main_core_cfg _ _ p
    [Zlib.deflate.code._deflate_stored; Zlib.deflate.code._deflate_fast; Zlib.deflate.code._deflate_slow]
    _ _ Rm GLs (body_main Bpre Brun BF D_to_end) eq_refl) as M.
  harness_safe_by_specs CS G main_post_TT.
  - reflexivity.
  - entry_shared M.
    entry_shared H_deflate_params_ok.
    entry_shared H_draw_nonzero_bytes.
    entry_shared H_stream_defaults.
    entry_shared H_exact_copy.
    entry_shared H_exact_space.
    entry_shared body_bytes_copy.
    entry_shared D_deflateInit2_.
    entry_shared D_deflateSetDictionary.
    entry_shared D_deflateSetHeader.
    entry_shared D_deflateBound.
    entry_shared D_deflate.
    entry_shared D_deflateEnd.
    entry_shared D_deflateBound_z.
    entry_shared D_deflateStateCheck.
    entry_shared D_deflateReset.
    entry_shared D_deflateResetKeep.
    entry_shared D_lm_init.
    entry_shared D_fill_window.
    entry_shared D_slide_hash.
    entry_shared D_read_buf.
    entry_shared D_flush_pending.
    entry_shared D_putShortMSB.
    entry_shared D_longest_match.
    entry_shared D_deflate_stored.
    entry_shared D_deflate_fast.
    entry_shared D_deflate_slow.
    entry_shared D_deflate_rle.
    entry_shared D_deflate_huff.
    entry_shared T_tr_init.
    entry_shared T_tr_static_init.
    entry_shared T_init_block.
    entry_shared T_tr_flush_bits.
    entry_shared T_bi_flush.
    entry_shared T_tr_align.
    entry_shared T_tr_stored_block.
    entry_shared T_bi_windup.
    entry_shared T_tr_flush_block.
    entry_shared T_detect_data_type.
    entry_shared T_build_tree.
    entry_shared T_pqdownheap.
    entry_shared T_gen_bitlen.
    entry_shared T_gen_codes.
    entry_shared T_bi_reverse.
    entry_shared T_build_bl_tree.
    entry_shared T_scan_tree.
    entry_shared T_compress_block.
    entry_shared T_send_all_trees.
    entry_shared T_send_tree.
    entry_shared Zlib.proof.adler32.Body_adler32.body_adler32.
    entry_shared Zlib.proof.adler32.Body_adler32_z.body_adler32_z.
    entry_shared Zlib.proof.crc32.Body_crc32.body_crc32.
    entry_shared Zlib.proof.crc32.Body_crc32_z.body_crc32_z.
    entry_shared (@Zlib.proof.zutil.Spec.body_zcalloc DCS.CS).
    entry_shared (@Zlib.proof.zutil.Spec.body_zcfree DCS.CS).
    entry_shared (@Zlib.proof.zutil.Libc.body_memcpy DCS.CS).
    entry_shared (@Zlib.proof.zutil.Libc.body_memset DCS.CS).
    entry_external (@external_ok_malloc CS).
    entry_external (@external_ok_free CS).
    entry_external (@external_ok_u32 CS).
    entry_external (@external_ok_u8 CS).
    entry_external (@external_ok_bytes CS).
    entry_external (@external_ok_assert CS).
    entry_external (@external_ok_assume CS).
    apply Forall_nil.
Qed.
