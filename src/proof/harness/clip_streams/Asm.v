(* The laws rt_partial, rj_truncated and rj_bad_checksum: the assembly of each program from the shared
   specifications (QuickProof.Assembly.harness_safe_by_specs with CS.CS): main against main_core_spec R_x
   (MainDefs.v, for the invariants the theory gives), the laws_common.h helpers (laws_common_ok), deflate.c and
   trees.c (their proved bodies, Obligations / Obligations9), inflate.c (SpecWLib.specw_lib_stmt: the port's
   bodies and the bridge to SpecW's inflate_specW; Spec5's inflateInit2_ and reset functions from
   LibStmt5.inflate_lib5_stmt), adler32 / crc32 / zutil, the environment; the globals (GlobalsOk.v). *)
Require Import QuickProof.Contract.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.clip_streams.CS Zlib.proof.harness.clip_streams.DFacts
               Zlib.proof.harness.clip_streams.IFacts Zlib.proof.harness.clip_streams.MainDefs.
Require Zlib.proof.inflate_api.SpecWLib.

Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib Zlib.proof.deflate.MainCoreCfg.
Require Zlib.proof.adler32.Spec Zlib.proof.adler32.Body_adler32 Zlib.proof.adler32.Body_adler32_z.
Require Zlib.proof.crc32.Spec Zlib.proof.crc32.Body_crc32 Zlib.proof.crc32.Body_crc32_z.
Require Zlib.proof.zutil.Spec Zlib.proof.zutil.Libc.
Require Zlib.proof.inftrees.spec.
Require Import Zlib.proof.deflate.DSpec Zlib.proof.deflate.DSpec9 Zlib.proof.deflate.Obligations9.
Require Zlib.proof.deflate.GlobalsFixed.
Require Zlib.proof.inflate_api.Spec5 Zlib.proof.inflate_api.LibStmt5 Zlib.proof.inflate_api.LibProof5.
Require Zlib.proof.trees.Body_bits Zlib.proof.trees.Body_build Zlib.proof.trees.Body_scan
        Zlib.proof.trees.Body_send Zlib.proof.trees.Body_flush.
Require Zlib.proof.deflate.Body_leaf Zlib.proof.deflate.Body_window Zlib.proof.deflate.Body_stored
        Zlib.proof.deflate.Body_compress Zlib.proof.deflate.Body_api Zlib.proof.deflate.Body_api9
        Zlib.proof.deflate.Body_deflate.
Require Zlib.proof.roundtrip.RTRSLaw.
Require Import Zlib.proof.harness.clip_streams.Globals Zlib.proof.harness.clip_streams.GlobalsOk.
Require Zlib.harness.rt_partial.code Zlib.harness.rj_truncated.code Zlib.harness.rj_bad_checksum.code.
#[local] Existing Instance Zlib.proof.harness.clip_streams.CS.CS.

Module S5 := Zlib.proof.inflate_api.Spec5.
Module SWL := Zlib.proof.inflate_api.SpecWLib.
Module ZU := Zlib.proof.za.inflate_api.USpec.

(* The bodies of trees.c, proved in src/proof/trees/. *)
Lemma clip_trees_bodies : Zlib.proof.deflate.Obligations.trees_bodies_ok.
Proof.
  unfold Zlib.proof.deflate.Obligations.trees_bodies_ok.
  destruct Zlib.proof.trees.Body_bits.trees_bits as (? & ? & ? & ?).
  destruct Zlib.proof.trees.Body_build.trees_build as (? & ? & ? & ?).
  destruct Zlib.proof.trees.Body_scan.trees_scan as (? & ? & ? & ? & ? & ?).
  destruct Zlib.proof.trees.Body_send.trees_send as (? & ? & ? & ? & ?).
  pose proof Zlib.proof.trees.Body_flush.trees_flush.
  repeat (split; [assumption | ]); assumption.
Qed.

(* The bodies of deflate.c (deflateInit2_ / deflateReset with their v9 specifications), proved in
   src/proof/deflate/. *)
Lemma clip_deflate_bodies9 : deflate_bodies_ok9.
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

(* The specifications of the library functions the three programs reach (after main's and the harness's):
   trees.c, deflate.c, inflate.c (the port's at zlib's default allocator SpecWLib.zc_alloc for inflate,
   inflate_fast, updatewindow and inflateStateCheck; Spec5's for inflateInit2_ and the reset functions),
   inffast.c, inftrees.c, adler32.c, crc32.c, and zutil.c / libc.c at the law's compspecs (deflate and inflate
   both call them). *)
Definition G_lib : funspecs :=
  [(* trees.c *)
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
   S5.inflateInit2__spec; S5.inflateReset2_spec; S5.inflateReset_spec; S5.inflateResetKeep_spec;
   @ZU.inflateStateCheck_uspec globals SWL.zc_alloc; @ZU.inflate_uspec globals SWL.zc_alloc;
   @ZU.inflate_fast_uspec globals SWL.zc_alloc; @ZU.updatewindow_uspec globals SWL.zc_alloc;
   Zlib.proof.inflate.Callees.inflate_fixed_spec; Zlib.proof.inftrees.spec.inflate_table_spec;
   (* adler32.c, crc32.c, zutil.c, libc.c *)
   Zlib.proof.adler32.Spec.adler32_spec; Zlib.proof.adler32.Spec.adler32_z_spec;
   Zlib.proof.crc32.Spec.crc32_spec; Zlib.proof.crc32.Spec.crc32_z_spec;
   @Zlib.proof.zutil.Spec.zcalloc_spec CS; @Zlib.proof.zutil.Spec.zcfree_spec CS;
   @Zlib.proof.zutil.Libc.memcpy_spec CS; @Zlib.proof.zutil.Libc.memset_spec CS].

(* the environment functions the programs declare (gp_assume only in rj_bad_checksum) *)
Definition G_env : funspecs :=
  [(_quickproof_malloc, @malloc_spec' CS); (_quickproof_free, @free_spec' CS);
   nondet_size_spec; @nondet_bytes_spec CS; nondet_u32_spec; gp_assert_spec].

Definition G_rp : funspecs :=
  [(Zlib.harness.rt_partial.code._main, QPmain_spec_ext' p_rp tt main_post_TT);
   upto_spec; clip_spec; any_bytes_spec; bytes_eq_spec; offer_spec; new_stream_spec] ++ G_lib ++ G_env.
Definition G_rt : funspecs :=
  [(Zlib.harness.rj_truncated.code._main, QPmain_spec_ext' p_rt tt main_post_TT);
   upto_spec; clip_spec; any_bytes_spec; offer_spec; new_stream_spec] ++ G_lib ++ G_env.
Definition G_bc : funspecs :=
  [(Zlib.harness.rj_bad_checksum.code._main, QPmain_spec_ext' p_bc tt main_post_TT);
   upto_spec; clip_spec; any_bytes_spec; offer_spec; new_stream_spec] ++ G_lib ++ G_env ++ [gp_assume_spec].

(* ctx_sub: the environment's and zutil / libc's moves between compspecs (RTRSLaw.env_spec_sub'), and the
   bridge from the port's inflate specifications to SpecW's / Spec5's *)
Ltac clip_spec_sub BR :=
  first [ Zlib.proof.roundtrip.RTRSLaw.env_spec_sub'
        | apply (proj1 BR) | apply (proj1 (proj2 BR)) | apply (proj2 (proj2 BR)) ].

Ltac clip_ctx_sub BR :=
  let i := fresh "i" in let phi := fresh "phi" in let E := fresh "E" in
  intros i phi E; simpl in E;
  repeat (if_tac in E; [ inv E; eexists; split; [ reflexivity | clip_spec_sub BR ] | ]);
  try discriminate.

Ltac clip_entry B BR :=
  lazymatch type of B with
  | @semax_body _ _ ?cs1 ?f ?spec =>
    apply Forall_cons;
    [ eapply (entry_moved _ _ cs1 _ _ _ _ (fst spec) (snd spec) f B);
      [ reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
      | apply Zlib.proof.roundtrip.RTRSLaw.find_ids_b; vm_compute; reflexivity
      | vm_compute; reflexivity | vm_compute; reflexivity | clip_ctx_sub BR ]
    | ]
  end.

(* inflate_table's context lists inftrees' inflate_fixed_spec (precondition False): the entry by
   NDsubsume_subsume *)
Ltac clip_entry_table B :=
  apply Forall_cons;
  [ eapply (entry_moved _ _ Zlib.units.Inftrees.CS _ _ _ _ _ _ _ B);
    [ reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
    | apply Zlib.proof.roundtrip.RTRSLaw.find_ids_b; vm_compute; reflexivity
    | vm_compute; reflexivity | vm_compute; reflexivity | ]
  | ];
  [ intros i phi E; simpl in E;
    if_tac in E; [ inv E; eexists; split; [ reflexivity | apply funspec_sub_refl ] | ];
    if_tac in E; [ | discriminate ];
    inv E; eexists; split; [ reflexivity | ];
    apply NDsubsume_subsume; [ split; reflexivity | split; [ split; reflexivity | ] ];
      intros x [ge args]; simpl; unfold PROPx; simpl; normalize
  | ].

(* The entries of G_lib, in its order, in three parts (each part one sentence of moderate cost): trees.c's
   bodies (TB), deflate.c's (DB), inflate.c's (LibProof5's for inflateInit2_ and the reset functions, the port's
   ZL for inflate, inflate_fast, updatewindow, inflateStateCheck), inftrees.c's, adler32.c's, crc32.c's and
   zutil.c / libc.c's at the law's compspecs. *)
Ltac clip_trees_entries BR TB :=
  let T1 := fresh "T" in let T2 := fresh "T" in let T3 := fresh "T" in let T4 := fresh "T" in
  let T5 := fresh "T" in let T6 := fresh "T" in let T7 := fresh "T" in let T8 := fresh "T" in
  let T9 := fresh "T" in let T10 := fresh "T" in let T11 := fresh "T" in let T12 := fresh "T" in
  let T13 := fresh "T" in let T14 := fresh "T" in let T15 := fresh "T" in let T16 := fresh "T" in
  let T17 := fresh "T" in let T18 := fresh "T" in let T19 := fresh "T" in let T20 := fresh "T" in
  destruct TB as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & T10 & T11 & T12 & T13 & T14 &
                  T15 & T16 & T17 & T18 & T19 & T20);
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
    Zlib.proof.deflate.Obligations.ob_deflateParams in *;
  clip_entry T1 BR; clip_entry T2 BR; clip_entry T3 BR; clip_entry T4 BR; clip_entry T5 BR; clip_entry T6 BR;
  clip_entry T7 BR; clip_entry T8 BR; clip_entry T9 BR; clip_entry T10 BR; clip_entry T11 BR;
  clip_entry T12 BR; clip_entry T13 BR; clip_entry T14 BR; clip_entry T15 BR; clip_entry T16 BR;
  clip_entry T17 BR; clip_entry T18 BR; clip_entry T19 BR; clip_entry T20 BR.

(* deflate.c's bodies in two sentences: the first twelve of DB (DB keeps the rest), then the others *)
Ltac clip_deflate_entries1 BR DB :=
  let D1 := fresh "D" in let D2 := fresh "D" in let D3 := fresh "D" in let D4 := fresh "D" in
  let D5 := fresh "D" in let D6 := fresh "D" in let D7 := fresh "D" in let D8 := fresh "D" in
  let D9 := fresh "D" in let D10 := fresh "D" in let D11 := fresh "D" in let D12 := fresh "D" in
  destruct DB as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & DB);
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
    Zlib.proof.deflate.Obligations.ob_deflateParams in *;
  clip_entry D1 BR; clip_entry D2 BR; clip_entry D3 BR; clip_entry D4 BR; clip_entry D5 BR; clip_entry D6 BR;
  clip_entry D7 BR; clip_entry D8 BR; clip_entry D9 BR; clip_entry D10 BR; clip_entry D11 BR;
  clip_entry D12 BR.

Ltac clip_deflate_entries2 BR DB :=
  let D13 := fresh "D" in let D14 := fresh "D" in let D15 := fresh "D" in let D16 := fresh "D" in
  let D17 := fresh "D" in let D18 := fresh "D" in let D19 := fresh "D" in let D20 := fresh "D" in
  let D21 := fresh "D" in let D22 := fresh "D" in let D23 := fresh "D" in let D24 := fresh "D" in
  let D25 := fresh "D" in
  destruct DB as (D13 & D14 & D15 & D16 & D17 & D18 & D19 & D20 & D21 & D22 & D23 & D24 & D25 & _);
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
    Zlib.proof.deflate.Obligations.ob_deflateParams in *;
  clip_entry D13 BR; clip_entry D14 BR; clip_entry D15 BR; clip_entry D16 BR; clip_entry D17 BR;
  clip_entry D18 BR; clip_entry D19 BR; clip_entry D20 BR; clip_entry D21 BR; clip_entry D22 BR;
  clip_entry D23 BR; clip_entry D24 BR; clip_entry D25 BR.

Ltac clip_inflate_entries BR ZL :=
  let Hinit := fresh "Hinit" in let Hreset := fresh "Hreset" in let Hfixed := fresh "Hfixed" in
  let Hreset' := fresh "Hreset" in
  let B_init2 := fresh "B_init2" in let B_resetkeep := fresh "B_resetkeep" in let B_reset := fresh "B_reset" in
  let B_reset2 := fresh "B_reset2" in let B_fixed := fresh "B_fixed" in let B_table := fresh "B_table" in
  let U_inflate := fresh "U_inflate" in let U_fast := fresh "U_fast" in let U_upd := fresh "U_upd" in
  let U_check := fresh "U_check" in
  destruct Zlib.proof.inflate_api.LibProof5.inflate_lib5_proof
    as (Hinit & Hreset & _ & _ & _ & _ & _ & _ & Hfixed & _);
  destruct Hreset as [_ Hreset'];
  destruct (Hinit NullExtension.Espec) as [B_init2 _];
  destruct (Hreset' NullExtension.Espec) as (B_resetkeep & B_reset & B_reset2 & _);
  pose proof (Hfixed NullExtension.Espec) as B_fixed;
  destruct (ZL NullExtension.Espec) as (U_inflate & U_fast & U_upd & U_check & _);
  pose proof (Zlib.proof.roundtrip.RTRSLaw.body_inflate_table NullExtension.Espec) as B_table;
  clip_entry B_init2 BR; clip_entry B_reset2 BR; clip_entry B_reset BR; clip_entry B_resetkeep BR;
  clip_entry U_check BR; clip_entry U_inflate BR; clip_entry U_fast BR; clip_entry U_upd BR;
  clip_entry B_fixed BR;
  clip_entry_table B_table;
  clip_entry Zlib.proof.adler32.Body_adler32.body_adler32 BR;
  clip_entry Zlib.proof.adler32.Body_adler32_z.body_adler32_z BR;
  clip_entry Zlib.proof.crc32.Body_crc32.body_crc32 BR;
  clip_entry Zlib.proof.crc32.Body_crc32_z.body_crc32_z BR;
  clip_entry (@Zlib.proof.zutil.Spec.body_zcalloc CS) BR;
  clip_entry (@Zlib.proof.zutil.Spec.body_zcfree CS) BR;
  clip_entry (@Zlib.proof.zutil.Libc.body_memcpy CS) BR;
  clip_entry (@Zlib.proof.zutil.Libc.body_memset CS) BR.

Ltac clip_env_entries :=
  entry_external (@external_ok_malloc CS);
  entry_external (@external_ok_free CS);
  entry_external (@external_ok_size CS);
  entry_external (@external_ok_bytes CS);
  entry_external (@external_ok_u32 CS);
  entry_external (@external_ok_assert CS).

Lemma clip_asm_rp : laws_common_ok -> SWL.specw_lib_stmt ->
  semax_body (QPvarspecs p_rp) Gmain_rp Zlib.harness.rt_partial.code.f_main
    (Zlib.harness.rt_partial.code._main, main_core_spec R_rp) ->
  harness_safe p_rp.
Proof.
  intros (B_upto & B_clip & B_any & _ & B_eq & B_offer & B_new) [ZL BR] BM.
  pose proof clip_trees_bodies as TB. pose proof clip_deflate_bodies9 as DB.
  assert (BM' : semax_body (QPvarspecs p_rp) Gmain_rp Zlib.harness.rt_partial.code.f_main
                  (Zlib.harness.rt_partial.code._main, QPmain_spec_ext' p_rp tt main_post_TT)).
  { eapply (semax_body_main_core_cfg _ _ p_rp Zlib.proof.deflate.GlobalsFixed.cfg_funs _ _ R_rp).
    - exact (proj1 clip_globals).
    - exact BM.
    - vm_compute; reflexivity. }
  harness_safe_by_specs CS G_rp main_post_TT.
  - reflexivity.
  - clip_entry BM' BR.
    clip_entry B_upto BR. clip_entry B_clip BR. clip_entry B_any BR. clip_entry B_eq BR.
    clip_entry B_offer BR. clip_entry B_new BR.
    clip_trees_entries BR TB.
    clip_deflate_entries1 BR DB.
    clip_deflate_entries2 BR DB.
    clip_inflate_entries BR ZL.
    clip_env_entries.
    apply Forall_nil.
Qed.

Lemma clip_asm_rt : laws_common_ok -> SWL.specw_lib_stmt ->
  semax_body (QPvarspecs p_rt) Gmain_rt Zlib.harness.rj_truncated.code.f_main
    (Zlib.harness.rj_truncated.code._main, main_core_spec R_rt) ->
  harness_safe p_rt.
Proof.
  intros (B_upto & B_clip & B_any & _ & _ & B_offer & B_new) [ZL BR] BM.
  pose proof clip_trees_bodies as TB. pose proof clip_deflate_bodies9 as DB.
  assert (BM' : semax_body (QPvarspecs p_rt) Gmain_rt Zlib.harness.rj_truncated.code.f_main
                  (Zlib.harness.rj_truncated.code._main, QPmain_spec_ext' p_rt tt main_post_TT)).
  { eapply (semax_body_main_core_cfg _ _ p_rt Zlib.proof.deflate.GlobalsFixed.cfg_funs _ _ R_rt).
    - exact (proj1 (proj2 clip_globals)).
    - exact BM.
    - vm_compute; reflexivity. }
  harness_safe_by_specs CS G_rt main_post_TT.
  - reflexivity.
  - clip_entry BM' BR.
    clip_entry B_upto BR. clip_entry B_clip BR. clip_entry B_any BR.
    clip_entry B_offer BR. clip_entry B_new BR.
    clip_trees_entries BR TB.
    clip_deflate_entries1 BR DB.
    clip_deflate_entries2 BR DB.
    clip_inflate_entries BR ZL.
    clip_env_entries.
    apply Forall_nil.
Qed.

Lemma clip_asm_bc : laws_common_ok -> SWL.specw_lib_stmt ->
  semax_body (QPvarspecs p_bc) Gmain_bc Zlib.harness.rj_bad_checksum.code.f_main
    (Zlib.harness.rj_bad_checksum.code._main, main_core_spec R_bc) ->
  harness_safe p_bc.
Proof.
  intros (B_upto & B_clip & B_any & _ & _ & B_offer & B_new) [ZL BR] BM.
  pose proof clip_trees_bodies as TB. pose proof clip_deflate_bodies9 as DB.
  assert (BM' : semax_body (QPvarspecs p_bc) Gmain_bc Zlib.harness.rj_bad_checksum.code.f_main
                  (Zlib.harness.rj_bad_checksum.code._main, QPmain_spec_ext' p_bc tt main_post_TT)).
  { eapply (semax_body_main_core_cfg _ _ p_bc Zlib.proof.deflate.GlobalsFixed.cfg_funs _ _ R_bc).
    - exact (proj1 (proj2 (proj2 clip_globals))).
    - exact BM.
    - vm_compute; reflexivity. }
  harness_safe_by_specs CS G_bc main_post_TT.
  - reflexivity.
  - clip_entry BM' BR.
    clip_entry B_upto BR. clip_entry B_clip BR. clip_entry B_any BR.
    clip_entry B_offer BR. clip_entry B_new BR.
    clip_trees_entries BR TB.
    clip_deflate_entries1 BR DB.
    clip_deflate_entries2 BR DB.
    clip_inflate_entries BR ZL.
    clip_env_entries.
    entry_external (@external_ok_assume CS).
    apply Forall_nil.
Qed.

Lemma clip_asm : laws_common_ok -> Zlib.proof.inflate_api.SpecWLib.specw_lib_stmt ->
  main_rp_stmt -> main_rt_stmt -> main_bc_stmt -> clip_dfacts_stmt -> pfx_stmt -> bad_stmt ->
  harness_safe p_rp /\ harness_safe p_rt /\ harness_safe p_bc.
Proof.
  intros L SW MRP MRT MBC [J0 [J DF]] [P PF] [Q BF].
  exact (conj (clip_asm_rp L SW (MRP J0 J P DF PF))
          (conj (clip_asm_rt L SW (MRT J0 J P DF PF)) (clip_asm_bc L SW (MBC J0 J Q DF BF)))).
Qed.
