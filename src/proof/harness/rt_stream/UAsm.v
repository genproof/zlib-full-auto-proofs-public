(* Law rt_stream (harness/rt_stream.c, data of any length): the assembly of the law from its parts (as round 1's
   Asm.v): main's body (UMainStmt.urts_main_stmt) for the invariants of the model facts (UDFacts, UIFacts), the
   globals (MainStmt.rts_globals_stmt), the bodies of deflate.c / trees.c with deflate() against
   DSpecV.deflate_specV, inflate.c's (SpecWLib.specw_lib_stmt), adler32.c, crc32.c, zutil.c, the laws_common.h
   helpers (with clip() and copy_of()) and the laws_session.h helpers main calls (deflate_params_ok, position_of,
   unmoved: laws_session.Spec's specifications and bodies), in one G with one specification per function. *)
Require Import QuickProof.Contract.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.proof.harness.laws_session.Spec.
Require Zlib.contracts.rt_stream.
Require Import Zlib.proof.deflate.DSpecV.
Require Import Zlib.proof.inflate_api.SpecWLib.
Require Import Zlib.proof.harness.rt_stream.UDFacts.
Require Import Zlib.proof.harness.rt_stream.UIFacts.
Require Import Zlib.proof.harness.rt_stream.UMainStmt.

Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Env.
Require Import QuickProof.EnvBodies.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.MainCoreCfg.
Require Zlib.proof.adler32.Spec.
Require Zlib.proof.adler32.Body_adler32.
Require Zlib.proof.adler32.Body_adler32_z.
Require Zlib.proof.crc32.Spec.
Require Zlib.proof.crc32.Body_crc32.
Require Zlib.proof.crc32.Body_crc32_z.
Require Zlib.proof.zutil.Spec.
Require Zlib.proof.zutil.Libc.
Require Zlib.proof.inftrees.spec.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.deflate.Obligations9.
Require Zlib.proof.deflate.GlobalsFixed.
Require Zlib.proof.inflate_api.Spec5.
Require Zlib.proof.inflate_api.LibStmt5.
(* the bodies of inflate.c's functions main reaches, one by one (LibProof5's bundle also holds inflateSync's,
   which main does not call) *)
Require Zlib.proof.inflate_api.Body5_init.
Require Zlib.proof.inflate_api.Body5_reset.
Require Zlib.proof.inflate.BodySmall.
Require Zlib.proof.trees.Body_bits.
Require Zlib.proof.trees.Body_build.
Require Zlib.proof.trees.Body_scan.
Require Zlib.proof.trees.Body_send.
Require Zlib.proof.trees.Body_flush.
Require Zlib.proof.deflate.Body_leaf.
Require Zlib.proof.deflate.Body_window.
Require Zlib.proof.deflate.Body_stored.
Require Zlib.proof.deflate.Body_compress.
Require Zlib.proof.deflate.Body_api.
Require Zlib.proof.deflate.Body_api9.
Require Zlib.proof.deflate.Body_deflate.
Require Zlib.proof.roundtrip.RTRSLaw.
Require Import Zlib.proof.harness.rt_stream.LawCS.
Require Zlib.harness.rt_stream.code.
#[local] Existing Instance Zlib.proof.harness.rt_stream.LawCS.CS.
Notation CS := Zlib.proof.harness.rt_stream.LawCS.CS.
Notation lp := Zlib.proof.harness.rt_stream.LawCS.p.

Module S5 := Zlib.proof.inflate_api.Spec5.
Module SWL := Zlib.proof.inflate_api.SpecWLib.
Module ZU := Zlib.proof.za.inflate_api.USpec.

(* The bodies of trees.c, proved in src/proof/trees/. *)
Lemma rts_trees_bodies : Zlib.proof.deflate.Obligations.trees_bodies_ok.
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
Lemma rts_deflate_bodies9 : deflate_bodies_ok9.
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

(* One specification per function of the program: main's, the laws_common.h helpers main calls (upto, clip,
   any_bytes, copy_of, bytes_eq, new_stream; and offer,
   which new_stream calls), then the library functions main reaches: trees.c, deflate.c (deflate against
   DSpecV.deflate_specV, deflateInit2_ / the reset functions v9; deflateSetHeader, deflateTune, deflatePrime and
   deflateParams are not reached), inflate.c (the port's specifications at zlib's default allocator
   SpecWLib.zc_alloc for inflate, inflate_fast, updatewindow and inflateStateCheck; Spec5's for inflateInit2_
   and the reset functions), inffast.c, inftrees.c, adler32.c, crc32.c, zutil.c / libc.c at the law's
   compspecs (deflate and inflate both call them); the environment. *)
Definition G : funspecs :=
  [(Zlib.harness.rt_stream.code._main, QPmain_spec_ext' lp tt main_post_TT);
   upto_spec; clip_spec; any_bytes_spec; copy_of_spec; bytes_eq_spec; offer_spec; new_stream_spec;
   (* laws_session.h *)
   Zlib.proof.harness.laws_session.Spec.deflate_params_ok_spec; Zlib.proof.harness.laws_session.Spec.position_of_spec;
   Zlib.proof.harness.laws_session.Spec.unmoved_spec;
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

(* zcalloc / zcfree at the compspecs of deflate.c (DCS.CS) and of inflate.c are subspecifications of theirs at
   the law's: proved once here (each move otherwise recomputes the comparison of the composite environments) *)
Lemma dcs_pres : preserved_b Zlib.proof.deflate.DCS.CS CS = true.
Proof. vm_compute; reflexivity. Qed.
Lemma ics_pres : preserved_b Zlib.units.Inflate.CS CS = true.
Proof. vm_compute; reflexivity. Qed.

Lemma zcalloc_dcs : funspec_sub (snd (@Zlib.proof.zutil.Spec.zcalloc_spec CS))
                                (snd (@Zlib.proof.zutil.Spec.zcalloc_spec Zlib.proof.deflate.DCS.CS)).
Proof.
  apply (Zlib.proof.zutil.Spec.zcalloc_spec_sub Zlib.proof.deflate.DCS.CS CS);
    first [ exact Zlib.proof.harness.rt_stream.LawCS.dcs_sub | exact (preserved_by_computation _ _ dcs_pres) ].
Qed.
Lemma zcfree_dcs : funspec_sub (snd (@Zlib.proof.zutil.Spec.zcfree_spec CS))
                               (snd (@Zlib.proof.zutil.Spec.zcfree_spec Zlib.proof.deflate.DCS.CS)).
Proof.
  apply (Zlib.proof.zutil.Spec.zcfree_spec_sub Zlib.proof.deflate.DCS.CS CS);
    first [ exact Zlib.proof.harness.rt_stream.LawCS.dcs_sub | exact (preserved_by_computation _ _ dcs_pres) ].
Qed.
Lemma zcalloc_ics : funspec_sub (snd (@Zlib.proof.zutil.Spec.zcalloc_spec CS))
                                (snd (@Zlib.proof.zutil.Spec.zcalloc_spec Zlib.units.Inflate.CS)).
Proof.
  apply (Zlib.proof.zutil.Spec.zcalloc_spec_sub Zlib.units.Inflate.CS CS);
    first [ exact Zlib.proof.harness.rt_stream.LawCS.ics_sub | exact (preserved_by_computation _ _ ics_pres) ].
Qed.
Lemma zcfree_ics : funspec_sub (snd (@Zlib.proof.zutil.Spec.zcfree_spec CS))
                               (snd (@Zlib.proof.zutil.Spec.zcfree_spec Zlib.units.Inflate.CS)).
Proof.
  apply (Zlib.proof.zutil.Spec.zcfree_spec_sub Zlib.units.Inflate.CS CS);
    first [ exact Zlib.proof.harness.rt_stream.LawCS.ics_sub | exact (preserved_by_computation _ _ ics_pres) ].
Qed.

(* ctx_sub: the environment's and zutil / libc's moves between compspecs (RTRSLaw.env_spec_sub'), and the
   bridge from the port's inflate specifications to SpecW's / Spec5's *)
Ltac rts_spec_sub BR :=
  first [ Zlib.proof.roundtrip.RTRSLaw.env_spec_sub'
        | apply (proj1 BR) | apply (proj1 (proj2 BR)) | apply (proj2 (proj2 BR)) ].

(* the entry of the context for identifier X of a body at compspecs cs1: zcalloc / zcfree by the lemmas above
   (deflate.c's bodies have them at DCS.CS, the others at inflate.c's), the rest by rts_spec_sub; dispatching
   on the identifier avoids trying the lemmas on other specifications (a failing conversion is slow) *)
Ltac rts_spec_sub_at BR cs1 X :=
  let x := eval compute in X in
  let zc := eval compute in Zlib.inflate.code._zcalloc in
  let zf := eval compute in Zlib.inflate.code._zcfree in
  tryif constr_eq x zc then
    (tryif constr_eq cs1 Zlib.proof.deflate.DCS.CS then exact zcalloc_dcs else exact zcalloc_ics)
  else tryif constr_eq x zf then
    (tryif constr_eq cs1 Zlib.proof.deflate.DCS.CS then exact zcfree_dcs else exact zcfree_ics)
  else rts_spec_sub BR.

Ltac rts_ctx_sub BR cs1 :=
  let i := fresh "i" in let phi := fresh "phi" in let E := fresh "E" in
  intros i phi E; simpl in E;
  repeat (lazymatch type of E with
          | (if Memory.EqDec_ident _ ?X then _ else _) = _ =>
            if_tac in E; [ inv E; eexists; split; [ reflexivity | rts_spec_sub_at BR cs1 X ] | ]
          end);
  try discriminate.

Ltac rts_entry B BR :=
  lazymatch type of B with
  | @semax_body _ _ ?cs1 ?f ?spec =>
    apply Forall_cons;
    [ eapply (entry_moved _ _ cs1 _ _ _ _ (fst spec) (snd spec) f B);
      [ reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
      | apply Zlib.proof.roundtrip.RTRSLaw.find_ids_b; vm_compute; reflexivity
      | vm_compute; reflexivity | vm_compute; reflexivity | rts_ctx_sub BR cs1 ]
    | ]
  end.

(* inflate_table's context lists inftrees' inflate_fixed_spec (precondition False): the entry by
   NDsubsume_subsume *)
Ltac rts_entry_table B :=
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

(* The entries of the library part of G, in its order, in parts (each one sentence of moderate cost): trees.c's
   bodies (TB), deflate.c's (DB), inflate.c's (LibProof5's for inflateInit2_ and the reset functions, the port's
   ZL for inflate, inflate_fast, updatewindow, inflateStateCheck), inftrees.c's, adler32.c's, crc32.c's and
   zutil.c / libc.c's at the law's compspecs. *)
Ltac rts_trees_entries BR TB :=
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
  rts_entry T1 BR; rts_entry T2 BR; rts_entry T3 BR; rts_entry T4 BR; rts_entry T5 BR; rts_entry T6 BR;
  rts_entry T7 BR; rts_entry T8 BR; rts_entry T9 BR; rts_entry T10 BR; rts_entry T11 BR;
  rts_entry T12 BR; rts_entry T13 BR; rts_entry T14 BR; rts_entry T15 BR; rts_entry T16 BR;
  rts_entry T17 BR; rts_entry T18 BR; rts_entry T19 BR; rts_entry T20 BR.

(* deflate.c's bodies in two sentences: the first twelve of DB (DB keeps the rest), then the others main reaches
   (deflate's own body, against deflate_specV, is entered separately) *)
Ltac rts_deflate_entries1 BR DB :=
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
  rts_entry D1 BR; rts_entry D2 BR; rts_entry D3 BR; rts_entry D4 BR; rts_entry D5 BR; rts_entry D6 BR;
  rts_entry D7 BR; rts_entry D8 BR; rts_entry D9 BR; rts_entry D10 BR; rts_entry D11 BR;
  rts_entry D12 BR.

Ltac rts_deflate_entries2 BR DB :=
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
  rts_entry D13 BR; rts_entry D14 BR; rts_entry D15 BR; rts_entry D19 BR; rts_entry D20 BR;
  rts_entry D21 BR; rts_entry D22 BR; rts_entry D23 BR.

Ltac rts_inflate_entries BR ZL :=
  let Hinit := fresh "Hinit" in let Hreset := fresh "Hreset" in let Hfixed := fresh "Hfixed" in
  let Hreset' := fresh "Hreset" in
  let B_init2 := fresh "B_init2" in let B_resetkeep := fresh "B_resetkeep" in let B_reset := fresh "B_reset" in
  let B_reset2 := fresh "B_reset2" in let B_fixed := fresh "B_fixed" in let B_table := fresh "B_table" in
  let U_inflate := fresh "U_inflate" in let U_fast := fresh "U_fast" in let U_upd := fresh "U_upd" in
  let U_check := fresh "U_check" in
  pose proof Zlib.proof.inflate_api.Body5_init.api5_init as Hinit;
  pose proof Zlib.proof.inflate_api.Body5_reset.api5_reset as Hreset;
  pose proof (fun Espec => @Zlib.proof.inflate.BodySmall.body_inflate_fixed Espec) as Hfixed;
  destruct Hreset as [_ Hreset'];
  destruct (Hinit NullExtension.Espec) as [B_init2 _];
  destruct (Hreset' NullExtension.Espec) as (B_resetkeep & B_reset & B_reset2 & _);
  pose proof (Hfixed NullExtension.Espec) as B_fixed;
  destruct (ZL NullExtension.Espec) as (U_inflate & U_fast & U_upd & U_check & _);
  pose proof (Zlib.proof.roundtrip.RTRSLaw.body_inflate_table NullExtension.Espec) as B_table;
  rts_entry B_init2 BR; rts_entry B_reset2 BR; rts_entry B_reset BR; rts_entry B_resetkeep BR;
  rts_entry U_check BR; rts_entry U_inflate BR; rts_entry U_fast BR; rts_entry U_upd BR;
  rts_entry B_fixed BR;
  rts_entry_table B_table;
  rts_entry Zlib.proof.adler32.Body_adler32.body_adler32 BR;
  rts_entry Zlib.proof.adler32.Body_adler32_z.body_adler32_z BR;
  rts_entry Zlib.proof.crc32.Body_crc32.body_crc32 BR;
  rts_entry Zlib.proof.crc32.Body_crc32_z.body_crc32_z BR;
  rts_entry (@Zlib.proof.zutil.Spec.body_zcalloc CS) BR;
  rts_entry (@Zlib.proof.zutil.Spec.body_zcfree CS) BR;
  rts_entry (@Zlib.proof.zutil.Libc.body_memcpy CS) BR;
  rts_entry (@Zlib.proof.zutil.Libc.body_memset CS) BR.

Ltac rts_env_entries :=
  entry_external (@external_ok_malloc CS);
  entry_external (@external_ok_free CS);
  entry_external (@external_ok_size CS);
  entry_external (@external_ok_bytes CS);
  entry_external (@external_ok_u32 CS);
  entry_external (@external_ok_assert CS);
  entry_external (@external_ok_assume CS).

Theorem urts_asm : laws_common_ok -> Zlib.proof.harness.laws_session.Spec.laws_session_ok -> urts_dtheory_stmt -> urts_itheory_stmt -> urts_main_stmt ->
  rts_globals_stmt -> deflate_bodyV_stmt -> specw_lib_stmt -> harness_safe Zlib.contracts.rt_stream.whole_prog.
Proof.
  intros (B_upto & B_clip & B_any & B_copy & B_eq & B_offer & B_new) (S_params & _ & S_pos & S_unmoved & _)
    [J DF] [P IF] MB GL BV [ZL BR].
  pose proof rts_trees_bodies as TB. pose proof rts_deflate_bodies9 as DB.
  unfold deflate_bodyV_stmt in BV.
  assert (BM : semax_body (QPvarspecs lp) Gmain_u Zlib.harness.rt_stream.code.f_main
                 (Zlib.harness.rt_stream.code._main, QPmain_spec_ext' lp tt main_post_TT)).
  { eapply (semax_body_main_core_cfg _ _ lp Zlib.proof.deflate.GlobalsFixed.cfg_funs _ _ Rm).
    - exact GL.
    - exact (MB J P DF IF).
    - vm_compute; reflexivity. }
  change Zlib.contracts.rt_stream.whole_prog with lp.
  harness_safe_by_specs CS G main_post_TT.
  - reflexivity.
  - rts_entry BM BR.
    rts_entry B_upto BR. rts_entry B_clip BR. rts_entry B_any BR. rts_entry B_copy BR. rts_entry B_eq BR.
    rts_entry B_offer BR. rts_entry B_new BR.
    rts_entry S_params BR. rts_entry S_pos BR. rts_entry S_unmoved BR.
    rts_trees_entries BR TB.
    rts_deflate_entries1 BR DB.
    rts_deflate_entries2 BR DB.
    rts_entry BV BR.
    rts_inflate_entries BR ZL.
    rts_env_entries.
    apply Forall_nil.
Qed.
