(* Law res_compress_bound: the assembly of harness_safe from main (Main.v), the laws_common.h helpers it calls
   (upto, any_bytes: laws_common_ok), compress.c's compressBound_z (Obligations9) and compress2_z for any sizes
   (RTCSpecW.rtc_w_bodies_stmt), deflate.c's deflateInit_ (RTCBWrap) and the deflate.c / trees.c bodies
   compress2_z reaches (Obligations.trees_bodies_ok, Obligations9.deflate_bodies_ok9; deflate and its
   input-carrying callees with a Z_NULL input allowed, DSpecN / DSpecNBody, as compress2_z's context has
   them), adler32.c, crc32.c,
   zutil.c, libc.c and the environment.  As harness/deflate_bound/Law.v and roundtrip/RTCLAsm.v.  The functions
   of the program that main does not reach (compress, compress2, compress_z, compressBound, deflateBound,
   deflateParams, ...) get vacuous specifications (harness_safe_by_specs). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DCS Zlib.proof.deflate.DSpec Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.deflate.Obligations Zlib.proof.deflate.Obligations9.
Require Import Zlib.proof.deflate.MainCoreCfg.
Require Zlib.proof.compress.CSpec.
Require Zlib.proof.adler32.Spec Zlib.proof.adler32.Body_adler32 Zlib.proof.adler32.Body_adler32_z.
Require Zlib.proof.crc32.Spec Zlib.proof.crc32.Body_crc32 Zlib.proof.crc32.Body_crc32_z.
Require Zlib.proof.zutil.Spec Zlib.proof.zutil.Libc.
Require Zlib.proof.trees.Body_bits Zlib.proof.trees.Body_build Zlib.proof.trees.Body_scan
        Zlib.proof.trees.Body_send Zlib.proof.trees.Body_flush.
Require Zlib.proof.deflate.Body_leaf Zlib.proof.deflate.Body_window Zlib.proof.deflate.Body_stored
        Zlib.proof.deflate.Body_compress Zlib.proof.deflate.Body_api Zlib.proof.deflate.Body_api9
        Zlib.proof.deflate.Body_deflate.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.roundtrip.RTCSpec Zlib.proof.roundtrip.RTCSpecW Zlib.proof.roundtrip.RTC2W.
Require Zlib.proof.roundtrip.RTCBWrap.
Require Zlib.proof.deflate.DSpecN Zlib.proof.deflate.DSpecNBody.
Require Import Zlib.proof.harness.res_compress_bound.LawCS Zlib.proof.harness.res_compress_bound.Globals
               Zlib.proof.harness.res_compress_bound.Main.
Require Zlib.contracts.res_compress_bound.
Require Import Zlib.harness.res_compress_bound.code.

(* the trees.c and deflate.c bodies (as src/contracts/suite.v gathers them) *)
Lemma rcb_trees_bodies : trees_bodies_ok.
Proof.
  unfold trees_bodies_ok.
  destruct Zlib.proof.trees.Body_bits.trees_bits as (? & ? & ? & ?).
  destruct Zlib.proof.trees.Body_build.trees_build as (? & ? & ? & ?).
  destruct Zlib.proof.trees.Body_scan.trees_scan as (? & ? & ? & ? & ? & ?).
  destruct Zlib.proof.trees.Body_send.trees_send as (? & ? & ? & ? & ?).
  pose proof Zlib.proof.trees.Body_flush.trees_flush.
  repeat (split; [assumption | ]); assumption.
Qed.

Lemma rcb_deflate_bodies9 : deflate_bodies_ok9.
Proof.
  unfold deflate_bodies_ok9.
  destruct Zlib.proof.deflate.Body_leaf.deflate_leaf as (? & ? & ? & ? & ? & ?).
  destruct Zlib.proof.deflate.Body_window.deflate_window as (? & ?).
  pose proof Zlib.proof.deflate.Body_stored.deflate_stored_body.
  destruct Zlib.proof.deflate.Body_compress.deflate_compress as (? & ? & ? & ?).
  destruct Zlib.proof.deflate.Body_api.deflate_api_bodies as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?).
  destruct Zlib.proof.deflate.Body_api9.deflate_api_bodies9 as (? & ? & ?).
  destruct Zlib.proof.deflate.Body_deflate.deflate_main_bodies as (? & ?).
  repeat (split; [assumption | ]); assumption.
Qed.

Module DN := Zlib.proof.dnull.deflate.DSpec_N.
Module ON := Zlib.proof.dnull.deflate.Obligations_N.

(* The specifications of the law: main, then every function main reaches, with the shared specifications of
   the bodies' contexts. *)
Definition G : funspecs :=
  [(_main, QPmain_spec_ext' p tt main_post_TT);
   (* laws_common.h *)
   upto_spec; any_bytes_spec;
   (* compress.c *)
   CSpec.compressBound_z_spec; compress2_z_spec_w;
   (* deflate.c *)
   deflateInit__spec; deflateInit2__spec_v9; Zlib.proof.deflate.DSpecN.deflate_specN; deflateEnd_spec;
   deflateStateCheck_spec; deflateReset_spec_v9; deflateResetKeep_spec_v9;
   lm_init_spec; DN.fill_window_spec_N; slide_hash_spec; DN.read_buf_spec_N; DN.flush_pending_spec_N;
   putShortMSB_spec; longest_match_spec; DN.deflate_stored_spec_N; DN.deflate_fast_spec_N;
   DN.deflate_slow_spec_N; DN.deflate_rle_spec_N; DN.deflate_huff_spec_N;
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
   nondet_size_spec; @nondet_bytes_spec CS; gp_assert_spec].

(* The variables of a body's context are the program's, by ONE computation (as deflate_bound/Law.v). *)
Lemma find_ids_b (V W : varspecs) :
  forallb (fun x => match initial_world.find_id (fst x) W with Some t => eqb_type t (snd x) | None => false end) V = true ->
  Forall (fun x => initial_world.find_id (fst x) W = Some (snd x)) V.
Proof.
  intros H. rewrite forallb_forall in H. rewrite Forall_forall. intros x IN. specialize (H x IN).
  destruct (initial_world.find_id (fst x) W) as [t|]; [ | discriminate]. apply eqb_type_spec in H. subst; reflexivity.
Qed.

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

Theorem rcb_law : laws_common_ok -> rtc_w_bodies_stmt -> c2w_bound_stmt ->
  harness_safe Zlib.contracts.res_compress_bound.whole_prog.
Proof.
  intros LC RW CB.
  destruct LC as (L_upto & _ & L_any_bytes & _).
  destruct RW as (C_compress2_z & _).
  pose proof Zlib.proof.roundtrip.RTCBWrap.rtcb_deflateInit_ as D_deflateInit_.
  pose proof rcb_trees_bodies as TB. pose proof rcb_deflate_bodies9 as DB.
  destruct TB as (T_bi_reverse & T_bi_flush & T_bi_windup & T_tr_flush_bits & T_tr_align & T_tr_stored_block &
    T_gen_codes & T_pqdownheap & T_gen_bitlen & T_build_tree & T_scan_tree & T_build_bl_tree &
    T_detect_data_type & T_init_block & T_send_tree & T_send_all_trees & T_compress_block & T_tr_static_init &
    T_tr_init & T_tr_flush_block).
  destruct DB as (D_read_buf & D_putShortMSB & D_flush_pending & D_slide_hash & D_longest_match & D_lm_init &
    D_fill_window & D_deflate_stored & D_deflate_fast & D_deflate_slow & D_deflate_rle & D_deflate_huff &
    D_deflateStateCheck & D_deflateResetKeep & D_deflateReset & _ & _ & _ & _ & _ & _ & D_deflateEnd &
    D_deflateInit2_ & D_deflate & _ & D_compressBound_z & _ & _).
  unfold ob_bi_reverse, ob_bi_flush, ob_bi_windup, ob_tr_flush_bits, ob_tr_align, ob_tr_stored_block,
    ob_gen_codes, ob_pqdownheap, ob_gen_bitlen, ob_build_tree, ob_scan_tree, ob_build_bl_tree,
    ob_detect_data_type, ob_init_block, ob_send_tree, ob_send_all_trees, ob_compress_block, ob_tr_static_init,
    ob_tr_init, ob_tr_flush_block, ob_read_buf, ob_putShortMSB, ob_flush_pending, ob_slide_hash,
    ob_longest_match, ob_lm_init, ob_fill_window, ob_deflate_stored, ob_deflate_fast, ob_deflate_slow,
    ob_deflate_rle, ob_deflate_huff, ob_deflateStateCheck, ob_deflateResetKeep9, ob_deflateReset9,
    ob_deflateEnd, ob_deflateInit2_9, ob_deflate, ob_compressBound_z, ob_deflateInit_, ob_compress2_z_w in *.
  pose proof Zlib.proof.dnull.deflate.Body_read_buf_N.body_read_buf_N as N_read_buf.
  pose proof Zlib.proof.dnull.deflate.Body_flush_pending_N.body_flush_pending_N as N_flush_pending.
  pose proof Zlib.proof.dnull.PartFillWindow.dn_fill_window as N_fill_window.
  pose proof Zlib.proof.dnull.PartStored.dn_deflate_stored as N_deflate_stored.
  pose proof Zlib.proof.dnull.PartFast.dn_deflate_fast as N_deflate_fast.
  pose proof Zlib.proof.dnull.PartSlow.dn_deflate_slow as N_deflate_slow.
  pose proof Zlib.proof.dnull.PartRle.dn_deflate_rle as N_deflate_rle.
  pose proof Zlib.proof.dnull.PartHuff.dn_deflate_huff as N_deflate_huff.
  pose proof Zlib.proof.dnull.PartDeflate.dn_deflate as N_deflate.
  unfold ON.ob_read_buf_N, ON.ob_flush_pending_N, ON.ob_fill_window_N, ON.ob_deflate_stored_N,
    ON.ob_deflate_fast_N, ON.ob_deflate_slow_N, ON.ob_deflate_rle_N, ON.ob_deflate_huff_N, ON.ob_deflate_N in *.
  pose proof (semax_body_main_core_cfg _ _ p cfg_funs _ _ R globals_ok (body_main CB) eq_refl) as M.
  change Zlib.contracts.res_compress_bound.whole_prog with p.
  harness_safe_by_specs CS G main_post_TT.
  - reflexivity.
  - entry_shared_b M.
    entry_shared_b L_upto.
    entry_shared_b L_any_bytes.
    entry_shared_b D_compressBound_z.
    entry_shared_b C_compress2_z.
    entry_shared_b D_deflateInit_.
    entry_shared_b D_deflateInit2_.
    entry_shared_b N_deflate.
    entry_shared_b D_deflateEnd.
    entry_shared_b D_deflateStateCheck.
    entry_shared_b D_deflateReset.
    entry_shared_b D_deflateResetKeep.
    entry_shared_b D_lm_init.
    entry_shared_b N_fill_window.
    entry_shared_b D_slide_hash.
    entry_shared_b N_read_buf.
    entry_shared_b N_flush_pending.
    entry_shared_b D_putShortMSB.
    entry_shared_b D_longest_match.
    entry_shared_b N_deflate_stored.
    entry_shared_b N_deflate_fast.
    entry_shared_b N_deflate_slow.
    entry_shared_b N_deflate_rle.
    entry_shared_b N_deflate_huff.
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
    entry_external (@external_ok_assert CS).
    apply Forall_nil.
Qed.
