(* Law deflate_bound: harness_safe of its program from the body of main (MainKit.v's Gmain, main_core_spec R; Main.v)
   and the shared library: QuickProof.Assembly.harness_safe_by_specs with entry_shared for every body reached
   (main via MainLib.semax_body_main_core and GlobalsInit.globals_ok; the harness helpers of HarnessLib; the
   trees.c / deflate.c / compress.c bodies of Obligations; adler32 / crc32 / zutil / libc bodies) and
   entry_external for the environment (template: src/proof/crc32_ref/Law.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DCS Zlib.proof.deflate.DSpec Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.deflate.LawFacts Zlib.proof.deflate.HarnessLib Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.deflate.Obligations9.
Require Import Zlib.proof.harness.deflate_bound.BoundCS Zlib.proof.harness.deflate_bound.MainKit.
Require Zlib.contracts.x_deflate_bound.
Require Import Zlib.harness.x_deflate_bound.code.
Require Import Zlib.proof.deflate.MainCoreCfg.
Require Zlib.proof.compress.CSpec.
Require Zlib.proof.adler32.Spec Zlib.proof.adler32.Body_adler32 Zlib.proof.adler32.Body_adler32_z.
Require Zlib.proof.crc32.Spec Zlib.proof.crc32.Body_crc32 Zlib.proof.crc32.Body_crc32_z.
Require Zlib.proof.zutil.Spec Zlib.proof.zutil.Libc.

(* The variables of a body's context are the program's, by ONE computation (Assembly's find_ids_V unfolds
   QPvarspecs of the whole program once per variable, minutes for main's context). *)
Lemma find_ids_b (V W : varspecs) :
  forallb (fun x => match initial_world.find_id (fst x) W with Some t => eqb_type t (snd x) | None => false end) V = true ->
  Forall (fun x => initial_world.find_id (fst x) W = Some (snd x)) V.
Proof.
  intros H. rewrite forallb_forall in H. rewrite Forall_forall. intros x IN. specialize (H x IN).
  destruct (initial_world.find_id (fst x) W) as [t|]; [ | discriminate]. apply eqb_type_spec in H. subst; reflexivity.
Qed.

(* Assembly.entry_shared with find_ids_b. *)
Ltac entry_shared_b B :=
  lazymatch type of B with
  | @semax_body _ _ ?cs1 ?f ?spec =>
    apply Forall_cons;
    [ eapply (entry_moved _ _ cs1 _ _ _ _ (fst spec) (snd spec) f B);
      [ reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
      | apply find_ids_b; vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
      | ctx_sub_tac ]
    | ]
  end.

(* The specifications of the law: main, then every function main reaches, with the shared specifications of
   the bodies' contexts. *)
Definition G : funspecs :=
  [(_main, QPmain_spec_ext' BoundCS.p tt main_post_TT);
   (* the harness *)
   deflate_params_ok_spec; draw_nonzero_bytes_spec; stream_defaults_spec;
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
   (* compress.c *)
   CSpec.compressBound_spec; CSpec.compressBound_z_spec;
   (* adler32.c, crc32.c, zutil.c, libc.c *)
   Zlib.proof.adler32.Spec.adler32_spec; Zlib.proof.adler32.Spec.adler32_z_spec;
   Zlib.proof.crc32.Spec.crc32_spec; Zlib.proof.crc32.Spec.crc32_z_spec;
   @Zlib.proof.zutil.Spec.zcalloc_spec DCS.CS; @Zlib.proof.zutil.Spec.zcfree_spec DCS.CS;
   @Zlib.proof.zutil.Libc.memcpy_spec DCS.CS; @Zlib.proof.zutil.Libc.memset_spec DCS.CS;
   (* the environment *)
   (_quickproof_malloc, @malloc_spec' BoundCS.CS); (_quickproof_free, @free_spec' BoundCS.CS);
   nondet_u32_spec; nondet_u8_spec; @nondet_bytes_spec BoundCS.CS; gp_assert_spec; gp_assume_spec].

Theorem law_of_main :
  (forall Bpre Brun, bound_facts Bpre Brun -> ob_dstream_to_end ->
     @semax_body (QPvarspecs Zlib.contracts.x_deflate_bound.whole_prog) Gmain DCS.CS f_main
       (_main, main_core_spec R)) ->
  (exists Bpre Brun, bound_facts Bpre Brun) -> trees_bodies_ok -> deflate_bodies_ok9 -> harness_lib_ok ->
  globals_ok -> harness_safe Zlib.contracts.x_deflate_bound.whole_prog.
Proof.
  intros HM [Bpre [Brun BF]] TB DB HL GL.
  destruct GL as [_ [Gs _]].
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
  unfold ob_bi_reverse, ob_bi_flush, ob_bi_windup, ob_tr_flush_bits, ob_tr_align, ob_tr_stored_block,
    ob_gen_codes, ob_pqdownheap, ob_gen_bitlen, ob_build_tree, ob_scan_tree, ob_build_bl_tree,
    ob_detect_data_type, ob_init_block, ob_send_tree, ob_send_all_trees, ob_compress_block, ob_tr_static_init,
    ob_tr_init, ob_tr_flush_block, ob_read_buf, ob_putShortMSB, ob_flush_pending, ob_slide_hash,
    ob_longest_match, ob_lm_init, ob_fill_window, ob_deflate_stored, ob_deflate_fast, ob_deflate_slow,
    ob_deflate_rle, ob_deflate_huff, ob_deflateStateCheck, ob_deflateResetKeep9, ob_deflateReset9,
    ob_deflateSetHeader, ob_deflateTune, ob_deflatePrime, ob_deflateBound_z, ob_deflateBound,
    ob_deflateSetDictionary, ob_deflateEnd, ob_deflateInit2_9, ob_deflate, ob_deflateParams, ob_compressBound_z,
    ob_compressBound in *.
  assert (GLs : forall gv, (forall i b o, gv i = Vptr b o -> o = Ptrofs.zero) ->
    (forall f, In f [Zlib.deflate.code._deflate_stored; Zlib.deflate.code._deflate_fast;
                     Zlib.deflate.code._deflate_slow] -> gv f = Vundef \/ isptr (gv f)) ->
    globvars2pred gv (QPprog_vars BoundCS.p) |-- R gv * TT).
  { intros gv H1 H2. unfold R. apply Gs; auto. }
  pose proof (semax_body_main_core_cfg _ _ BoundCS.p
    [Zlib.deflate.code._deflate_stored; Zlib.deflate.code._deflate_fast; Zlib.deflate.code._deflate_slow]
    _ _ R GLs (HM Bpre Brun BF D_to_end) eq_refl) as M.
  harness_safe_by_specs BoundCS.CS G main_post_TT.
  - reflexivity.
  - entry_shared_b M.
    entry_shared_b H_deflate_params_ok.
    entry_shared_b H_draw_nonzero_bytes.
    entry_shared_b H_stream_defaults.
    entry_shared_b D_deflateInit2_.
    entry_shared_b D_deflateSetDictionary.
    entry_shared_b D_deflateSetHeader.
    entry_shared_b D_deflateBound.
    entry_shared_b D_deflate.
    entry_shared_b D_deflateEnd.
    entry_shared_b D_deflateBound_z.
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
    entry_shared_b D_compressBound.
    entry_shared_b D_compressBound_z.
    entry_shared_b Zlib.proof.adler32.Body_adler32.body_adler32.
    entry_shared_b Zlib.proof.adler32.Body_adler32_z.body_adler32_z.
    entry_shared_b Zlib.proof.crc32.Body_crc32.body_crc32.
    entry_shared_b Zlib.proof.crc32.Body_crc32_z.body_crc32_z.
    entry_shared_b (@Zlib.proof.zutil.Spec.body_zcalloc DCS.CS).
    entry_shared_b (@Zlib.proof.zutil.Spec.body_zcfree DCS.CS).
    entry_shared_b (@Zlib.proof.zutil.Libc.body_memcpy DCS.CS).
    entry_shared_b (@Zlib.proof.zutil.Libc.body_memset DCS.CS).
    entry_external (@external_ok_malloc BoundCS.CS).
    entry_external (@external_ok_free BoundCS.CS).
    entry_external (@external_ok_u32 BoundCS.CS).
    entry_external (@external_ok_u8 BoundCS.CS).
    entry_external (@external_ok_bytes BoundCS.CS).
    entry_external (@external_ok_assert BoundCS.CS).
    entry_external (@external_ok_assume BoundCS.CS).
    apply Forall_nil.
Qed.
