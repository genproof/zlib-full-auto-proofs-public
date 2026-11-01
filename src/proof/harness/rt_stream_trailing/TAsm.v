(* Law rt_stream_trailing (harness/rt_stream_trailing.c): the assembly of the law from its parts, as rt_stream's
   UAsm.v (whose lemmas and entry tactics it reuses: the program links the same units and has the same composites,
   so the law is at rt_stream's compspecs LawCS.CS): main's body (TMainStmt.trl_main_stmt) for the invariants of
   the model facts (rt_stream's UDFacts, TIFacts), the globals (TMainStmt.trl_globals_stmt), the bodies of deflate.c
   / trees.c with deflate() against DSpecV.deflate_specV, inflate.c's (SpecWLib.specw_lib_stmt), adler32.c,
   crc32.c, zutil.c, the laws_common.h helpers and the laws_session.h helpers main calls (deflate_params_ok,
   position_of, unmoved, accounted: laws_session.Spec's specifications and bodies), in one G with one
   specification per function. *)
Require Import QuickProof.Contract.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.proof.harness.laws_session.Spec.
Require Zlib.contracts.rt_stream_trailing.
Require Import Zlib.proof.deflate.DSpecV.
Require Import Zlib.proof.inflate_api.SpecWLib.
Require Import Zlib.proof.harness.rt_stream.UDFacts.
Require Import Zlib.proof.harness.rt_stream_trailing.TIFacts.
Require Import Zlib.proof.harness.rt_stream_trailing.TMainStmt.

Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Env.
Require Import QuickProof.EnvBodies.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.MainCoreCfg.
Require Zlib.proof.adler32.Spec.
Require Zlib.proof.crc32.Spec.
Require Zlib.proof.zutil.Spec.
Require Zlib.proof.zutil.Libc.
Require Zlib.proof.inftrees.spec.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.deflate.Obligations9.
Require Zlib.proof.deflate.GlobalsFixed.
Require Zlib.proof.inflate_api.Spec5.
Require Zlib.proof.inflate.Callees.
Require Import Zlib.proof.harness.rt_stream.LawCS.
Require Import Zlib.proof.harness.rt_stream.UAsm.
Require Zlib.harness.rt_stream_trailing.code.
#[local] Existing Instance Zlib.proof.harness.rt_stream.LawCS.CS.
Notation CS := Zlib.proof.harness.rt_stream.LawCS.CS.

Module S5 := Zlib.proof.inflate_api.Spec5.
Module SWL := Zlib.proof.inflate_api.SpecWLib.
Module ZU := Zlib.proof.za.inflate_api.USpec.

(* One specification per function of the program: rt_stream's G (UAsm.G) with this program's main and
   laws_session.h's accounted() *)
Definition G_t : funspecs :=
  [(Zlib.harness.rt_stream_trailing.code._main, QPmain_spec_ext' p_t tt main_post_TT);
   upto_spec; clip_spec; any_bytes_spec; copy_of_spec; bytes_eq_spec; offer_spec; new_stream_spec;
   (* laws_session.h *)
   Zlib.proof.harness.laws_session.Spec.deflate_params_ok_spec; Zlib.proof.harness.laws_session.Spec.position_of_spec;
   Zlib.proof.harness.laws_session.Spec.unmoved_spec; Zlib.proof.harness.laws_session.Spec.accounted_spec;
   (* trees.c *)
   bi_reverse_spec; bi_flush_spec; bi_windup_spec; tr_flush_bits_spec; tr_align_spec; tr_stored_block_spec;
   gen_codes_spec; pqdownheap_spec; gen_bitlen_spec; build_tree_spec; scan_tree_spec; build_bl_tree_spec;
   detect_data_type_spec; init_block_spec; send_tree_spec; send_all_trees_spec; compress_block_spec;
   tr_static_init_spec; tr_init_spec; tr_flush_block_spec;
   (* deflate.c *)
   read_buf_spec; putShortMSB_spec; flush_pending_spec; slide_hash_spec; longest_match_spec; lm_init_spec;
   fill_window_spec; deflate_stored_spec; deflate_fast_spec; deflate_slow_spec; deflate_rle_spec;
   deflate_huff_spec; deflateStateCheck_spec; deflateResetKeep_spec_v9; deflateReset_spec_v9;
   deflateBound_z_spec; deflateBound_spec; deflateSetDictionary_spec;
   deflateEnd_spec; deflateInit2__spec_v9; Zlib.proof.deflate.DSpecV.deflate_specV;
   (* inflate.c, inffast.c, inftrees.c *)
   S5.inflateInit2__spec; S5.inflateReset2_spec; S5.inflateReset_spec; S5.inflateResetKeep_spec;
   @ZU.inflateStateCheck_uspec globals SWL.zc_alloc; @ZU.inflate_uspec globals SWL.zc_alloc;
   @ZU.inflate_fast_uspec globals SWL.zc_alloc; @ZU.updatewindow_uspec globals SWL.zc_alloc;
   Zlib.proof.inflate.Callees.inflate_fixed_spec; Zlib.proof.inftrees.spec.inflate_table_spec;
   (* adler32.c, crc32.c, zutil.c, libc.c *)
   Zlib.proof.adler32.Spec.adler32_spec; Zlib.proof.adler32.Spec.adler32_z_spec;
   Zlib.proof.crc32.Spec.crc32_spec; Zlib.proof.crc32.Spec.crc32_z_spec;
   @Zlib.proof.zutil.Spec.zcalloc_spec CS; @Zlib.proof.zutil.Spec.zcfree_spec CS;
   @Zlib.proof.zutil.Libc.memcpy_spec CS; @Zlib.proof.zutil.Libc.memset_spec CS;
   (* the environment *)
   (_quickproof_malloc, @malloc_spec' CS); (_quickproof_free, @free_spec' CS);
   nondet_size_spec; @nondet_bytes_spec CS; nondet_u32_spec; gp_assert_spec; gp_assume_spec].

Theorem trl_asm : laws_common_ok -> Zlib.proof.harness.laws_session.Spec.laws_session_ok -> urts_dtheory_stmt ->
  trl_itheory_stmt -> trl_main_stmt -> trl_globals_stmt -> deflate_bodyV_stmt -> specw_lib_stmt ->
  harness_safe Zlib.contracts.rt_stream_trailing.whole_prog.
Proof.
  intros (B_upto & B_clip & B_any & B_copy & B_eq & B_offer & B_new) (S_params & _ & S_pos & S_unmoved & S_acc & _)
    [J DF] [P IF] MB GL BV [ZL BR].
  pose proof rts_trees_bodies as TB. pose proof rts_deflate_bodies9 as DB.
  unfold deflate_bodyV_stmt in BV.
  assert (BM : semax_body (QPvarspecs p_t) Gmain_t Zlib.harness.rt_stream_trailing.code.f_main
                 (Zlib.harness.rt_stream_trailing.code._main, QPmain_spec_ext' p_t tt main_post_TT)).
  { eapply (semax_body_main_core_cfg _ _ p_t Zlib.proof.deflate.GlobalsFixed.cfg_funs _ _ Rm_t).
    - exact GL.
    - exact (MB J P DF IF).
    - vm_compute; reflexivity. }
  change Zlib.contracts.rt_stream_trailing.whole_prog with p_t.
  harness_safe_by_specs CS G_t main_post_TT.
  - reflexivity.
  - rts_entry BM BR.
    rts_entry B_upto BR. rts_entry B_clip BR. rts_entry B_any BR. rts_entry B_copy BR. rts_entry B_eq BR.
    rts_entry B_offer BR. rts_entry B_new BR.
    rts_entry S_params BR. rts_entry S_pos BR. rts_entry S_unmoved BR. rts_entry S_acc BR.
    rts_trees_entries BR TB.
    rts_deflate_entries1 BR DB.
    rts_deflate_entries2 BR DB.
    rts_entry BV BR.
    rts_inflate_entries BR ZL.
    rts_env_entries.
    apply Forall_nil.
Qed.
