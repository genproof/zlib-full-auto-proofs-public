(* Law rt_roundtrip (data of any length): the specifications of the assembly and its tactics.

   [G] gives one specification to every function of the program that main reaches, in six parts that the files
   WAsmTop.v, WAsmTrees.v, WAsmDefl1.v, WAsmDefl2.v and WAsmInfl.v prove one after the other (each part is a
   Forall over its entries, [w_entries]):
   - [G_top]: main (harness_safe's specification), the helpers of laws_common.h that main calls (upto,
     alloc_any_bytes, copy_of and bytes_eq with arguments that may be Z_NULL when the length is 0), compress.c
     (compressBound(_z) of CSpec, compress2(_z) for any sizes of RTCSpecW), deflate.c's deflateInit_ (RTCSpec) and
     uncompr.c's uncompress2(_z) for any sizes (USpecW);
   - [G_trees], [G_defl1], [G_defl2]: trees.c and the functions of deflate.c that deflateInit_, deflate and
     deflateEnd reach (the specifications of Obligations / Obligations9), as round 1's Asm.v; deflate and its
     input-carrying callees (read_buf, flush_pending, fill_window, the five compressors) with a Z_NULL input
     allowed (DSpecN.deflate_specN and the dnull port's specifications), as compress2_z's context has deflate;
   - [G_infl]: inflate.c (Spec5's inflateInit_, inflateInit2_, the reset functions and inflateEnd; inflate()
     against SpecWSelf.inflate_specW_s; the allocator-generic port's inflateStateCheck, inflate_fast and
     updatewindow at zlib's default allocator SpecWLib.zc_alloc, as inflate()'s body takes them), inftrees.c,
     adler32.c, crc32.c, zutil.c and libc.c at the law's compspecs;
   - [G_env]: the environment.
   The functions main does not reach (compress / compress_z, uncompress / uncompress_z, deflate.c's and
   inflate.c's other entry points) get vacuous specifications (harness_safe_by_specs). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.EnvBodies.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.MainCoreCfg.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.deflate.DSpec9.
Require Zlib.proof.compress.CSpec.
Require Zlib.proof.roundtrip.RTCSpec.
Require Zlib.proof.roundtrip.RTCSpecW.
Require Zlib.proof.deflate.DSpecN Zlib.proof.deflate.DSpecNBody.
Require Zlib.proof.adler32.Spec.
Require Zlib.proof.crc32.Spec.
Require Zlib.proof.zutil.Spec.
Require Zlib.proof.zutil.Libc.
Require Zlib.zutil.code.
Require Zlib.proof.inftrees.spec.
Require Zlib.proof.inflate.Callees.
Require Zlib.proof.inflate_api.Spec5.
Require Zlib.proof.inflate_api.SpecWLib.
Require Zlib.proof.inflate_api.SpecWSelf.
Require Zlib.proof.za.inflate_api.USpec.
Require Import Zlib.proof.uncompr.USpecW.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.laws_common.CopyOfNull Zlib.proof.harness.laws_common.BytesEqNull.
Require Import Zlib.proof.roundtrip.RTC2W.
Require Import Zlib.proof.roundtrip.RTC2WFinal.
Require Import Zlib.proof.uncompr.UTheoryW.
Require Import Zlib.proof.harness.rt_roundtrip.WCS.
Require Import Zlib.proof.harness.rt_roundtrip.WGlobals.
Require Import Zlib.proof.harness.rt_roundtrip.WMainDefs.
Require Zlib.proof.roundtrip.RTRSLaw.
Require Import Zlib.harness.rt_roundtrip.code.

Local Notation CSW := Zlib.proof.harness.rt_roundtrip.WCS.CS.
#[local] Existing Instance CSW.

Module S5 := Zlib.proof.inflate_api.Spec5.
Module SWL := Zlib.proof.inflate_api.SpecWLib.
Module ZU := Zlib.proof.za.inflate_api.USpec.

Definition G_top : funspecs :=
  [(_main, QPmain_spec_ext' p tt main_post_TT);
   (* laws_common.h *)
   upto_spec; any_bytes_spec; copy_of_spec_n; bytes_eq_spec_n;
   (* compress.c, deflate.c's deflateInit_, uncompr.c *)
   Zlib.proof.compress.CSpec.compressBound_z_spec; Zlib.proof.compress.CSpec.compressBound_spec;
   Zlib.proof.roundtrip.RTCSpecW.compress2_z_spec_w; Zlib.proof.roundtrip.RTCSpecW.compress2_spec_w;
   Zlib.proof.roundtrip.RTCSpec.deflateInit__spec;
   uncompress2_z_spec_w; uncompress2_spec_w].

Definition G_trees : funspecs :=
  [bi_reverse_spec; bi_flush_spec; bi_windup_spec; tr_flush_bits_spec; tr_align_spec; tr_stored_block_spec;
   gen_codes_spec; pqdownheap_spec; gen_bitlen_spec; build_tree_spec; scan_tree_spec; build_bl_tree_spec;
   detect_data_type_spec; init_block_spec; send_tree_spec; send_all_trees_spec; compress_block_spec;
   tr_static_init_spec; tr_init_spec; tr_flush_block_spec].

Module DN := Zlib.proof.dnull.deflate.DSpec_N.

Definition G_defl1 : funspecs :=
  [DN.read_buf_spec_N; putShortMSB_spec; DN.flush_pending_spec_N; slide_hash_spec; longest_match_spec;
   lm_init_spec; DN.fill_window_spec_N; DN.deflate_stored_spec_N; DN.deflate_fast_spec_N; deflateEnd_spec].

Definition G_defl2 : funspecs :=
  [DN.deflate_slow_spec_N; DN.deflate_rle_spec_N; DN.deflate_huff_spec_N; deflateStateCheck_spec;
   deflateResetKeep_spec_v9; deflateReset_spec_v9; deflateInit2__spec_v9; Zlib.proof.deflate.DSpecN.deflate_specN].

Definition G_infl : funspecs :=
  [S5.inflateInit__spec; S5.inflateInit2__spec; S5.inflateReset2_spec; S5.inflateReset_spec;
   S5.inflateResetKeep_spec; S5.inflateEnd_spec;
   @ZU.inflateStateCheck_uspec globals SWL.zc_alloc; Zlib.proof.inflate_api.SpecWSelf.inflate_specW_s;
   @ZU.inflate_fast_uspec globals SWL.zc_alloc; @ZU.updatewindow_uspec globals SWL.zc_alloc;
   Zlib.proof.inflate.Callees.inflate_fixed_spec; Zlib.proof.inftrees.spec.inflate_table_spec;
   Zlib.proof.adler32.Spec.adler32_spec; Zlib.proof.adler32.Spec.adler32_z_spec;
   Zlib.proof.crc32.Spec.crc32_spec; Zlib.proof.crc32.Spec.crc32_z_spec;
   @Zlib.proof.zutil.Spec.zcalloc_spec CSW; @Zlib.proof.zutil.Spec.zcfree_spec CSW;
   @Zlib.proof.zutil.Libc.memcpy_spec CSW; @Zlib.proof.zutil.Libc.memset_spec CSW].

Definition G_env : funspecs :=
  [(_quickproof_malloc, @malloc_spec' CSW); (_quickproof_free, @free_spec' CSW);
   nondet_size_spec; @nondet_bytes_spec CSW; gp_assert_spec].

Definition G : funspecs := G_top ++ G_trees ++ G_defl1 ++ G_defl2 ++ G_infl ++ G_env.

(* the obligation of the entries of a part of G (harness_safe_of_specs's ENTRIES restricted to it) *)
Definition w_entries (Gk : funspecs) : Prop :=
  Forall (entry_of_prog (@HonestEspec CSW) CSW p (G ++ vacuous_internals p G)) Gk.

Lemma w_entries_G : w_entries G_top -> w_entries G_trees -> w_entries G_defl1 -> w_entries G_defl2 ->
  w_entries G_infl -> w_entries G_env -> w_entries G.
Proof. unfold w_entries, G; intros; repeat (apply Forall_app; split); assumption. Qed.

(* main against WMainDefs.main_core_spec R is main against harness_safe's specification of main *)
Lemma main_entry :
  body_main_w_stmt -> c2w_bound_stmt -> c2w_final_stmt -> uw_theory_stmt ->
  semax_body (QPvarspecs p) Gmain f_main (_main, QPmain_spec_ext' p tt main_post_TT).
Proof.
  intros BM CB CF UT.
  eapply (semax_body_main_core_cfg _ _ p cfg_funs _ _ R).
  - intros gv H1 H2. apply globals_ok; auto.
  - exact (BM CB CF UT).
  - vm_compute; reflexivity.
Qed.

(* An entry from a shared body B (as clip_streams/Asm.v's clip_entry): entry_moved with the computable side
   conditions closed and the context's specifications matched against G, by identity, by the environment's
   moves between compspecs (RTRSLaw.env_spec_sub': malloc, free, nondet_bytes, zcalloc, zcfree, memcpy,
   memset), or by the bridge BR (SpecWLib.specw_bridge_stmt: the port's inflateStateCheck at zc_alloc gives
   Spec5's inflateStateCheck_spec, which the bodies of inflateInit2_, the resets and inflateEnd call). *)
Ltac w_spec_sub BR :=
  first [ Zlib.proof.roundtrip.RTRSLaw.env_spec_sub'
        | apply (proj1 BR) | apply (proj1 (proj2 BR)) | apply (proj2 (proj2 BR)) ].

(* zcalloc and zcfree, at a unit's compspecs in the context, go straight to their moves to the law's compspecs
   (chosen by the callee's identifier, before inv E substitutes it): w_spec_sub would first try
   funspec_sub_refl, whose failure across two compspecs takes about 20 s. *)
Ltac w_ctx_entry E BR :=
  lazymatch goal with
  | H : _ = Zlib.zutil.code._zcalloc |- _ =>
      inv E; eexists; split;
      [ reflexivity
      | apply Zlib.proof.zutil.Spec.zcalloc_spec_sub;
        try (apply cspecs_sub_by_computation; vm_compute; reflexivity);
        try (apply preserved_by_computation; vm_compute; reflexivity) ]
  | H : _ = Zlib.zutil.code._zcfree |- _ =>
      inv E; eexists; split;
      [ reflexivity
      | apply Zlib.proof.zutil.Spec.zcfree_spec_sub;
        try (apply cspecs_sub_by_computation; vm_compute; reflexivity);
        try (apply preserved_by_computation; vm_compute; reflexivity) ]
  | _ => inv E; eexists; split; [ reflexivity | w_spec_sub BR ]
  end.

Ltac w_ctx_sub BR :=
  let i := fresh "i" in let phi := fresh "phi" in let E := fresh "E" in
  intros i phi E; simpl in E;
  repeat (if_tac in E; [ w_ctx_entry E BR | ]);
  try discriminate.

Ltac w_entry B BR :=
  lazymatch type of B with
  | @semax_body _ _ ?cs1 ?f ?spec =>
    apply Forall_cons;
    [ eapply (entry_moved _ _ cs1 _ _ _ _ (fst spec) (snd spec) f B);
      [ reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
      | apply Zlib.proof.roundtrip.RTRSLaw.find_ids_b; vm_compute; reflexivity
      | vm_compute; reflexivity | vm_compute; reflexivity | w_ctx_sub BR ]
    | ]
  end.
