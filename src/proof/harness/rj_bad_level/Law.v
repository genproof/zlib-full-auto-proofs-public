(* Law rj_bad_level (harness/rj_bad_level.c): compress2 with a level outside -1..9, any data and any output space
   (up to PTRDIFF_MAX bytes each, destLen possibly 0) returns Z_STREAM_ERROR.  harness_safe of its program from
   the body of main, the laws_common.h helpers (laws_common_ok), compress2 / compress2_z by their specifications
   for any sizes (RTCSpecW.v) and the deflate.c bodies they reach (deflateInit_, deflate, deflateEnd; deflate and
   its input-carrying callees with a Z_NULL input allowed, DSpecN / DSpecNBody, as compress2_z's context has it); the model
   fact: deflateInit2_ rejects the level for every allocation outcome (LawFacts.af_init, LawTheory). *)
Require Import QuickProof.Contract.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.roundtrip.RTCSpecW.
Require Zlib.contracts.rj_bad_level.

(* The assembly: QuickProof.Assembly.harness_safe_by_specs with main (RJLMain.v, through
   MainCoreCfg.semax_body_main_core_cfg and RJLGlobals.globals_ok), the shared bodies of compress.c (the
   hypothesis rtc_w_bodies_stmt; deflateInit_ of RTCBWrap.v), deflate.c and trees.c (their Body_* files),
   adler32.c, crc32.c, zutil.c, libc.c, laws_common.h's upto and any_bytes (the hypothesis laws_common_ok) and
   the environment; every function the law does not reach is vacuous. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DCS Zlib.proof.deflate.DSpec Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.deflate.Obligations Zlib.proof.deflate.Obligations9.
Require Import Zlib.proof.deflate.MainCoreCfg.
Require Import Zlib.proof.roundtrip.RTCSpec.
Require Zlib.proof.roundtrip.RTCBWrap.
Require Zlib.proof.deflate.DSpecN Zlib.proof.deflate.DSpecNBody.
Require Zlib.proof.trees.Body_bits Zlib.proof.trees.Body_build Zlib.proof.trees.Body_scan
        Zlib.proof.trees.Body_send Zlib.proof.trees.Body_flush.
Require Zlib.proof.deflate.Body_leaf Zlib.proof.deflate.Body_window Zlib.proof.deflate.Body_stored
        Zlib.proof.deflate.Body_compress Zlib.proof.deflate.Body_api Zlib.proof.deflate.Body_api9
        Zlib.proof.deflate.Body_deflate.
Require Zlib.proof.adler32.Spec Zlib.proof.adler32.Body_adler32 Zlib.proof.adler32.Body_adler32_z.
Require Zlib.proof.crc32.Spec Zlib.proof.crc32.Body_crc32 Zlib.proof.crc32.Body_crc32_z.
Require Zlib.proof.zutil.Spec Zlib.proof.zutil.Libc Zlib.proof.deflate.GlobalsFixed.
Require Import Zlib.proof.harness.rj_bad_level.RJLCS Zlib.proof.harness.rj_bad_level.RJLGlobals
               Zlib.proof.harness.rj_bad_level.RJLMainStmt Zlib.proof.harness.rj_bad_level.RJLMain.
Require Import Zlib.harness.rj_bad_level.code.

(* The variables of a body's context are the program's, by ONE computation (as deflate_bound/Law.v). *)
Lemma find_ids_b (V W : varspecs) :
  forallb (fun x => match initial_world.find_id (fst x) W with Some t => eqb_type t (snd x) | None => false end) V = true ->
  Forall (fun x => initial_world.find_id (fst x) W = Some (snd x)) V.
Proof.
  intros H. rewrite forallb_forall in H. rewrite Forall_forall. intros x IN. specialize (H x IN).
  destruct (initial_world.find_id (fst x) W) as [t|]; [ | discriminate]. apply eqb_type_spec in H. subst; reflexivity.
Qed.

(* Assembly.ctx_sub_tac, with the zutil / libc moves of the units' specifications to the law's compspecs *)
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

Ltac entry_shared_b B :=
  lazymatch type of B with
  | @semax_body _ _ ?cs1 ?f ?spec =>
    apply Forall_cons;
    [ eapply (entry_moved _ _ cs1 _ _ _ _ (fst spec) (snd spec) f B);
      [ reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
      | apply find_ids_b; vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
      | ctx_sub_tac' ]
    | ]
  end.

Module DN := Zlib.proof.dnull.deflate.DSpec_N.
Module ON := Zlib.proof.dnull.deflate.Obligations_N.

(* The specifications of the law: main, then every function main reaches. *)
Definition G : funspecs :=
  [(_main, QPmain_spec_ext' p tt main_post_TT);
   (* the harness (laws_common.h) *)
   upto_spec; any_bytes_spec;
   (* compress.c *)
   compress2_spec_w; compress2_z_spec_w;
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
   (_quickproof_malloc, @malloc_spec' RJLCS.CS); (_quickproof_free, @free_spec' RJLCS.CS);
   nondet_u32_spec; nondet_size_spec; @nondet_bytes_spec RJLCS.CS; gp_assert_spec; gp_assume_spec].

Theorem rj_bad_level_ok : laws_common_ok -> rtc_w_bodies_stmt ->
  harness_safe Zlib.contracts.rj_bad_level.whole_prog.
Proof.
  intros LC [C_compress2_z C_compress2].
  destruct LC as (L_upto & _ & L_any_bytes & _).
  unfold ob_compress2_z_w, ob_compress2_w in *.
  pose proof Zlib.proof.roundtrip.RTCBWrap.rtcb_deflateInit_ as D_deflateInit_.
  unfold ob_deflateInit_ in D_deflateInit_.
  destruct Zlib.proof.trees.Body_bits.trees_bits as (T1 & T2 & T3 & T4).
  destruct Zlib.proof.trees.Body_build.trees_build as (T5 & T6 & T7 & T8).
  destruct Zlib.proof.trees.Body_scan.trees_scan as (T9 & T10 & T11 & T12 & T13 & T14).
  destruct Zlib.proof.trees.Body_send.trees_send as (T15 & T16 & T17 & T18 & T19).
  pose proof Zlib.proof.trees.Body_flush.trees_flush as T20.
  destruct Zlib.proof.deflate.Body_leaf.deflate_leaf as (D1 & D2 & D3 & D4 & D5 & D6).
  destruct Zlib.proof.deflate.Body_window.deflate_window as (D7 & D8).
  pose proof Zlib.proof.deflate.Body_stored.deflate_stored_body as D9.
  destruct Zlib.proof.deflate.Body_compress.deflate_compress as (D10 & D11 & D12 & D13).
  destruct Zlib.proof.deflate.Body_api.deflate_api_bodies as (D14 & D15 & D16 & D17 & D18 & D19 & D20 & D21 &
    D22 & D23 & D24 & D25 & D26).
  destruct Zlib.proof.deflate.Body_api9.deflate_api_bodies9 as (D27 & D28 & D29).
  destruct Zlib.proof.deflate.Body_deflate.deflate_main_bodies as (D30 & D31).
  unfold ob_bi_reverse, ob_bi_flush, ob_bi_windup, ob_tr_flush_bits, ob_tr_align, ob_tr_stored_block,
    ob_gen_codes, ob_pqdownheap, ob_gen_bitlen, ob_build_tree, ob_scan_tree, ob_build_bl_tree,
    ob_detect_data_type, ob_init_block, ob_send_tree, ob_send_all_trees, ob_compress_block, ob_tr_static_init,
    ob_tr_init, ob_tr_flush_block, ob_read_buf, ob_putShortMSB, ob_flush_pending, ob_slide_hash,
    ob_longest_match, ob_lm_init, ob_fill_window, ob_deflate_stored, ob_deflate_fast, ob_deflate_slow,
    ob_deflate_rle, ob_deflate_huff, ob_deflateStateCheck, ob_deflateResetKeep9, ob_deflateReset9,
    ob_deflateEnd, ob_deflateInit2_9, ob_deflate in *.
  pose proof Zlib.proof.dnull.deflate.Body_read_buf_N.body_read_buf_N as N1.
  pose proof Zlib.proof.dnull.deflate.Body_flush_pending_N.body_flush_pending_N as N3.
  pose proof Zlib.proof.dnull.PartFillWindow.dn_fill_window as N7.
  pose proof Zlib.proof.dnull.PartStored.dn_deflate_stored as N9.
  pose proof Zlib.proof.dnull.PartFast.dn_deflate_fast as N10.
  pose proof Zlib.proof.dnull.PartSlow.dn_deflate_slow as N11.
  pose proof Zlib.proof.dnull.PartRle.dn_deflate_rle as N12.
  pose proof Zlib.proof.dnull.PartHuff.dn_deflate_huff as N13.
  pose proof Zlib.proof.dnull.PartDeflate.dn_deflate as N30.
  unfold ON.ob_read_buf_N, ON.ob_flush_pending_N, ON.ob_fill_window_N, ON.ob_deflate_stored_N,
    ON.ob_deflate_fast_N, ON.ob_deflate_slow_N, ON.ob_deflate_rle_N, ON.ob_deflate_huff_N, ON.ob_deflate_N in *.
  pose proof body_main as BM. unfold rjl_main_stmt in BM.
  pose proof (semax_body_main_core_cfg _ _ p Zlib.proof.deflate.GlobalsFixed.cfg_funs _ _ R globals_ok BM eq_refl) as M.
  change Zlib.contracts.rj_bad_level.whole_prog with p.
  harness_safe_by_specs RJLCS.CS G main_post_TT.
  - reflexivity.
  - entry_shared_b M.
    entry_shared_b L_upto.
    entry_shared_b L_any_bytes.
    entry_shared_b C_compress2.
    entry_shared_b C_compress2_z.
    entry_shared_b D_deflateInit_.
    entry_shared_b D29.
    entry_shared_b N30.
    entry_shared_b D22.
    entry_shared_b D6.
    entry_shared_b D28.
    entry_shared_b D27.
    entry_shared_b D5.
    entry_shared_b N7.
    entry_shared_b D4.
    entry_shared_b N1.
    entry_shared_b N3.
    entry_shared_b D2.
    entry_shared_b D8.
    entry_shared_b N9.
    entry_shared_b N10.
    entry_shared_b N11.
    entry_shared_b N12.
    entry_shared_b N13.
    entry_shared_b T14.
    entry_shared_b T13.
    entry_shared_b T12.
    entry_shared_b T4.
    entry_shared_b T2.
    entry_shared_b T18.
    entry_shared_b T19.
    entry_shared_b T3.
    entry_shared_b T20.
    entry_shared_b T11.
    entry_shared_b T8.
    entry_shared_b T6.
    entry_shared_b T7.
    entry_shared_b T5.
    entry_shared_b T1.
    entry_shared_b T10.
    entry_shared_b T9.
    entry_shared_b T17.
    entry_shared_b T16.
    entry_shared_b T15.
    entry_shared_b Zlib.proof.adler32.Body_adler32.body_adler32.
    entry_shared_b Zlib.proof.adler32.Body_adler32_z.body_adler32_z.
    entry_shared_b Zlib.proof.crc32.Body_crc32.body_crc32.
    entry_shared_b Zlib.proof.crc32.Body_crc32_z.body_crc32_z.
    entry_shared_b (@Zlib.proof.zutil.Spec.body_zcalloc DCS.CS).
    entry_shared_b (@Zlib.proof.zutil.Spec.body_zcfree DCS.CS).
    entry_shared_b (@Zlib.proof.zutil.Libc.body_memcpy DCS.CS).
    entry_shared_b (@Zlib.proof.zutil.Libc.body_memset DCS.CS).
    entry_external (@external_ok_malloc RJLCS.CS).
    entry_external (@external_ok_free RJLCS.CS).
    entry_external (@external_ok_u32 RJLCS.CS).
    entry_external (@external_ok_size RJLCS.CS).
    entry_external (@external_ok_bytes RJLCS.CS).
    entry_external (@external_ok_assert RJLCS.CS).
    entry_external (@external_ok_assume RJLCS.CS).
    apply Forall_nil.
Qed.
