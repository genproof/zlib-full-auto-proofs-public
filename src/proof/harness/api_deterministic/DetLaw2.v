(* Law api_deterministic (data of any length): harness_safe of its program from the body of main
   (DetMainStmt2.det_main2_stmt, at DCS.CS, lifted to harness_safe's main by MainCoreCfg.semax_body_main_core_cfg
   with the globals of DetGlobals2.v), the model facts (DetFacts2.det_theory2_stmt) and the shared library:
   QuickProof.Assembly.harness_safe_by_specs with entry_shared for every body reached (laws_common.h's helpers,
   laws_session.h's deflate_params_ok; the trees.c / deflate.c bodies of Obligations and Obligations9; adler32 /
   crc32 / zutil / libc bodies) and entry_external for the environment.  As src/proof/harness/deflate_bound/Law.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.EnvBodies.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.deflate.DSpec9.
Require Zlib.proof.deflate.DetFacts2.
Require Import Zlib.proof.deflate.Obligations.
Require Import Zlib.proof.deflate.Obligations9.
Require Import Zlib.proof.deflate.MainCoreCfg.
Require Zlib.proof.deflate.GlobalsFixed.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.proof.harness.laws_session.Spec.
Require Zlib.proof.harness.deflate_bound.Law.
Require Import Zlib.proof.harness.api_deterministic.DetCS2.
Require Import Zlib.proof.harness.api_deterministic.DetGlobals2.
Require Import Zlib.proof.harness.api_deterministic.DetMainStmt2.
Require Zlib.contracts.api_deterministic.
Require Import Zlib.harness.api_deterministic.code.
Require Zlib.proof.adler32.Spec.
Require Zlib.proof.adler32.Body_adler32.
Require Zlib.proof.adler32.Body_adler32_z.
Require Zlib.proof.crc32.Spec.
Require Zlib.proof.crc32.Body_crc32.
Require Zlib.proof.crc32.Body_crc32_z.
Require Zlib.proof.zutil.Spec.
Require Zlib.proof.zutil.Libc.

Ltac entry_shared_b B := Zlib.proof.harness.deflate_bound.Law.entry_shared_b B.

(* The specifications of the law: main, then every function main reaches, with the shared specifications of
   the bodies' contexts. *)
Definition G : funspecs :=
  [(_main, QPmain_spec_ext' p tt main_post_TT);
   (* the harness (laws_common.h) *)
   upto_spec; clip_spec; any_bytes_spec; copy_of_spec; bytes_eq_spec; offer_spec; new_stream_spec;
   (* the harness (laws_session.h) *)
   Zlib.proof.harness.laws_session.Spec.deflate_params_ok_spec;
   (* deflate.c *)
   deflateInit2__spec_v9; deflateParams_spec; deflate_spec; deflateEnd_spec; deflateStateCheck_spec; deflateReset_spec_v9;
   deflateResetKeep_spec_v9; lm_init_spec; fill_window_spec; slide_hash_spec; read_buf_spec;
   flush_pending_spec; putShortMSB_spec; longest_match_spec; deflate_stored_spec; deflate_fast_spec;
   deflate_slow_spec; deflate_rle_spec; deflate_huff_spec;
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
   nondet_size_spec; nondet_bytes_spec; nondet_u32_spec; nondet_u8_spec; gp_assert_spec; gp_assume_spec].

Theorem law_of_main2 :
  det_main2_stmt -> Zlib.proof.deflate.DetFacts2.det_theory2_stmt -> trees_bodies_ok -> deflate_bodies_ok9 ->
  laws_common_ok -> Zlib.proof.harness.laws_session.Spec.laws_session_ok ->
  harness_safe Zlib.contracts.api_deterministic.whole_prog.
Proof.
  intros HM AF TB DB LC LS.
  destruct TB as (T_bi_reverse & T_bi_flush & T_bi_windup & T_tr_flush_bits & T_tr_align & T_tr_stored_block &
    T_gen_codes & T_pqdownheap & T_gen_bitlen & T_build_tree & T_scan_tree & T_build_bl_tree &
    T_detect_data_type & T_init_block & T_send_tree & T_send_all_trees & T_compress_block & T_tr_static_init &
    T_tr_init & T_tr_flush_block).
  destruct DB as (D_read_buf & D_putShortMSB & D_flush_pending & D_slide_hash & D_longest_match & D_lm_init &
    D_fill_window & D_deflate_stored & D_deflate_fast & D_deflate_slow & D_deflate_rle & D_deflate_huff &
    D_deflateStateCheck & D_deflateResetKeep & D_deflateReset & D_deflateSetHeader & D_deflateTune &
    D_deflatePrime & D_deflateBound_z & D_deflateBound & D_deflateSetDictionary & D_deflateEnd &
    D_deflateInit2_ & D_deflate & D_deflateParams & D_compressBound_z & D_compressBound & D_to_end).
  destruct LC as (B_upto & B_clip & B_any_bytes & B_copy_of & B_bytes_eq & B_offer & B_new).
  destruct LS as (S_params & _).
  unfold ob_bi_reverse, ob_bi_flush, ob_bi_windup, ob_tr_flush_bits, ob_tr_align, ob_tr_stored_block,
    ob_gen_codes, ob_pqdownheap, ob_gen_bitlen, ob_build_tree, ob_scan_tree, ob_build_bl_tree,
    ob_detect_data_type, ob_init_block, ob_send_tree, ob_send_all_trees, ob_compress_block, ob_tr_static_init,
    ob_tr_init, ob_tr_flush_block, ob_read_buf, ob_putShortMSB, ob_flush_pending, ob_slide_hash,
    ob_longest_match, ob_lm_init, ob_fill_window, ob_deflate_stored, ob_deflate_fast, ob_deflate_slow,
    ob_deflate_rle, ob_deflate_huff, ob_deflateStateCheck, ob_deflateResetKeep9, ob_deflateReset9,
    ob_deflateEnd, ob_deflateInit2_9, ob_deflate, ob_deflateParams in *.
  assert (GLs : forall gv, (forall i b o, gv i = Vptr b o -> o = Ptrofs.zero) ->
    (forall f, In f Zlib.proof.deflate.GlobalsFixed.cfg_funs -> gv f = Vundef \/ isptr (gv f)) ->
    globvars2pred gv (QPprog_vars p) |-- R gv * TT).
  { intros gv H1 H2. unfold R. apply globals_det; auto. }
  pose proof (semax_body_main_core_cfg _ _ p Zlib.proof.deflate.GlobalsFixed.cfg_funs
    _ _ R GLs (HM AF) eq_refl) as M.
  harness_safe_by_specs CS G main_post_TT.
  - reflexivity.
  - entry_shared_b M.
    entry_shared_b B_upto.
    entry_shared_b B_clip.
    entry_shared_b B_any_bytes.
    entry_shared_b B_copy_of.
    entry_shared_b B_bytes_eq.
    entry_shared_b B_offer.
    entry_shared_b B_new.
    entry_shared_b S_params.
    entry_shared_b D_deflateInit2_.
    entry_shared_b D_deflateParams.
    entry_shared_b D_deflate.
    entry_shared_b D_deflateEnd.
    entry_shared_b D_deflateStateCheck.
    entry_shared_b D_deflateReset.
    entry_shared_b D_deflateResetKeep.
    entry_shared_b D_lm_init.
    entry_shared_b D_fill_window.
    entry_shared_b D_slide_hash.
    entry_shared_b D_read_buf.
    entry_shared_b D_flush_pending.
    entry_shared_b D_putShortMSB.
    entry_shared_b D_longest_match.
    entry_shared_b D_deflate_stored.
    entry_shared_b D_deflate_fast.
    entry_shared_b D_deflate_slow.
    entry_shared_b D_deflate_rle.
    entry_shared_b D_deflate_huff.
    entry_shared_b T_tr_init.
    entry_shared_b T_tr_static_init.
    entry_shared_b T_init_block.
    entry_shared_b T_tr_flush_bits.
    entry_shared_b T_bi_flush.
    entry_shared_b T_tr_align.
    entry_shared_b T_tr_stored_block.
    entry_shared_b T_bi_windup.
    entry_shared_b T_tr_flush_block.
    entry_shared_b T_detect_data_type.
    entry_shared_b T_build_tree.
    entry_shared_b T_pqdownheap.
    entry_shared_b T_gen_bitlen.
    entry_shared_b T_gen_codes.
    entry_shared_b T_bi_reverse.
    entry_shared_b T_build_bl_tree.
    entry_shared_b T_scan_tree.
    entry_shared_b T_compress_block.
    entry_shared_b T_send_all_trees.
    entry_shared_b T_send_tree.
    entry_shared_b Zlib.proof.adler32.Body_adler32.body_adler32.
    entry_shared_b Zlib.proof.adler32.Body_adler32_z.body_adler32_z.
    entry_shared_b Zlib.proof.crc32.Body_crc32.body_crc32.
    entry_shared_b Zlib.proof.crc32.Body_crc32_z.body_crc32_z.
    entry_shared_b (@Zlib.proof.zutil.Spec.body_zcalloc DCS.CS).
    entry_shared_b (@Zlib.proof.zutil.Spec.body_zcfree DCS.CS).
    entry_shared_b (@Zlib.proof.zutil.Libc.body_memcpy DCS.CS).
    entry_shared_b (@Zlib.proof.zutil.Libc.body_memset DCS.CS).
    entry_external (@external_ok_malloc CS).
    entry_external (@external_ok_free CS).
    entry_external (@external_ok_size CS).
    entry_external (@external_ok_bytes CS).
    entry_external (@external_ok_u32 CS).
    entry_external (@external_ok_u8 CS).
    entry_external (@external_ok_assert CS).
    entry_external (@external_ok_assume CS).
    apply Forall_nil.
Qed.
