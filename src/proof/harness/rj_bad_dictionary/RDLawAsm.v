(* Law rj_bad_dictionary: the assembly of harness_safe from the shared bodies (inflate.c through
   SpecWLib.specw_lib_stmt and LibStmt5's inflate_lib5_stmt; zutil, libc, adler32, crc32, inftrees; the helpers
   of laws_common.h), main (RDMain.v), the theory of its inflate() call (RDTheory.v) and the globals
   (RDGlobals.v).  As bit_writer/BWLawAsm.v.

   inflate.c's functions get the allocator-generic specifications of the port at zlib's default allocator
   (SpecWLib.zc_alloc) for inflate, inflate_fast, updatewindow, inflateStateCheck and inflateSetDictionary, and
   Spec5's for inflateInit2_ and the reset functions; main's callee specifications (SpecW's inflate_specW and
   inflateSetDictionary_specW) and the reset functions' (Spec5.inflateStateCheck_spec) are moved to them by the
   bridge (specw_bridge_stmt). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.EnvBodies.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.LibStmt5.
Require Zlib.proof.inflate_api.LibProof5.
Require Import Zlib.proof.inflate_api.SpecWLib.
Require Zlib.proof.adler32.Spec.
Require Zlib.proof.adler32.Body_adler32.
Require Zlib.proof.adler32.Body_adler32_z.
Require Zlib.proof.crc32.Spec.
Require Zlib.proof.crc32.Body_crc32.
Require Zlib.proof.crc32.Body_crc32_z.
Require Zlib.proof.zutil.Spec.
Require Zlib.proof.zutil.Libc.
Require Zlib.proof.inftrees.spec.
Require Zlib.proof.inftrees.verif_inflate_table.
Require Zlib.proof.inftrees.part_loop_facts.
Require Zlib.proof.inftrees.part_seg_counts.
Require Zlib.proof.inftrees.part_seg_max0.
Require Zlib.proof.inftrees.part_seg_check.
Require Zlib.proof.inftrees.part_seg_sort.
Require Zlib.proof.inftrees.part_seg_init.
Require Zlib.proof.inftrees.part_seg_loop.
Require Zlib.proof.inftrees.part_seg_fin.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rj_bad_dictionary.RDLawCS.
Require Import Zlib.proof.harness.rj_bad_dictionary.RDGlobals.
Require Zlib.proof.harness.rj_bad_dictionary.RDTheory.
Require Zlib.proof.harness.rj_bad_dictionary.RDMain.
Require Zlib.harness.rj_bad_dictionary.code.

(* inflate_table's body (the inftrees proof, from its segments) *)
Lemma rbd_body_inflate_table : Zlib.proof.inftrees.spec.body_inflate_table_stmt.
Proof.
  pose proof Zlib.proof.inftrees.part_loop_facts.loop_facts_ok as LF.
  apply Zlib.proof.inftrees.verif_inflate_table.body_from_segs.
  - apply Zlib.proof.inftrees.part_seg_counts.seg_counts_ok; exact LF.
  - apply Zlib.proof.inftrees.part_seg_max0.seg_max0_ok; exact LF.
  - apply Zlib.proof.inftrees.part_seg_check.seg_check_ok; exact LF.
  - apply Zlib.proof.inftrees.part_seg_sort.seg_sort_ok; exact LF.
  - apply Zlib.proof.inftrees.part_seg_init.seg_init_ok; exact LF.
  - apply Zlib.proof.inftrees.part_seg_loop.seg_loop_ok; exact LF.
  - apply Zlib.proof.inftrees.part_seg_fin.seg_fin_ok; exact LF.
Qed.

(* the specifications of the functions main reaches *)
Definition G : funspecs :=
  [(Zlib.harness.rj_bad_dictionary.code._main, QPmain_spec_ext' p tt main_post_TT);
   upto_spec; clip_spec; any_bytes_spec; offer_spec; new_stream_spec;
   inflateInit2__spec; inflateReset2_spec; inflateReset_spec; inflateResetKeep_spec;
   @inflateStateCheck_uspec globals zc_alloc; @inflate_uspec globals zc_alloc;
   @inflate_fast_uspec globals zc_alloc; @updatewindow_uspec globals zc_alloc;
   @inflateSetDictionary_uspec globals zc_alloc;
   inflate_fixed_spec; Zlib.proof.inftrees.spec.inflate_table_spec;
   Zlib.proof.adler32.Spec.adler32_spec; Zlib.proof.adler32.Spec.adler32_z_spec;
   Zlib.proof.crc32.Spec.crc32_spec; Zlib.proof.crc32.Spec.crc32_z_spec;
   zcalloc_i; zcfree_i; memcpy_i; memset_i;
   (_quickproof_malloc, @malloc_spec' CS); (_quickproof_free, @free_spec' CS);
   nondet_size_spec; @nondet_bytes_spec CS; nondet_u32_spec; gp_assert_spec; gp_assume_spec].

(* ctx_sub with, besides the environment's transports, the bridge's funspec_subs *)
Ltac rbd_spec_sub BR :=
  first [ env_spec_sub
        | apply (proj1 BR) | apply (proj1 (proj2 BR)) | apply (proj2 (proj2 BR)) ].

Ltac rbd_ctx_sub BR :=
  let i := fresh "i" in let phi := fresh "phi" in let E := fresh "E" in
  intros i phi E; simpl in E;
  repeat (if_tac in E; [ inv E; eexists; split; [ reflexivity | rbd_spec_sub BR ] | ]);
  try discriminate.

Ltac rbd_entry B BR :=
  lazymatch type of B with
  | @semax_body _ _ ?cs1 ?f ?spec =>
    apply Forall_cons;
    [ eapply (entry_moved _ _ cs1 _ _ _ _ (fst spec) (snd spec) f B);
      [ reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
      | find_ids_V | vm_compute; reflexivity | vm_compute; reflexivity | rbd_ctx_sub BR ]
    | ]
  end.

(* main's entry: its varspecs are all of the program's globals, so their find_id facts come from In and the
   norepet of their names (one computation) instead of find_ids_V's computation per global *)
Ltac rbd_entry_main B BR :=
  lazymatch type of B with
  | @semax_body _ _ ?cs1 ?f ?spec =>
    apply Forall_cons;
    [ eapply (entry_moved _ _ cs1 _ _ _ _ (fst spec) (snd spec) f B);
      [ reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
      | rewrite Forall_forall; intros [i t] Hin; apply initial_world.find_id_i;
        [ exact Hin | apply compute_list_norepet_e; vm_compute; reflexivity ]
      | vm_compute; reflexivity | vm_compute; reflexivity | rbd_ctx_sub BR ]
    | ]
  end.

(* inflate_table's context lists inftrees' inflate_fixed_spec (precondition False): the entry by
   NDsubsume_subsume *)
Ltac rbd_entry_table B :=
  apply Forall_cons;
  [ eapply (entry_moved _ _ Zlib.units.Inftrees.CS _ _ _ _ _ _ _ B);
    [ reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
    | find_ids_V | vm_compute; reflexivity | vm_compute; reflexivity | ]
  | ];
  [ intros i phi E; simpl in E;
    if_tac in E; [ inv E; eexists; split; [ reflexivity | apply funspec_sub_refl ] | ];
    if_tac in E; [ | discriminate ];
    inv E; eexists; split; [ reflexivity | ];
    apply NDsubsume_subsume; [ split; reflexivity | split; [ split; reflexivity | ] ];
      intros x [ge args]; simpl; unfold PROPx; simpl; normalize
  | ].

Lemma rbd_core : specw_lib_stmt -> laws_common_ok -> harness_safe Zlib.contracts.rj_bad_dictionary.whole_prog.
Proof.
  intros [ZL BR] (B_upto & B_clip & B_any & _ & _ & B_offer & B_new).
  destruct Zlib.proof.inflate_api.LibProof5.inflate_lib5_proof
    as (Hinit & Hreset & _ & _ & _ & _ & _ & _ & Hfixed & _).
  destruct Hreset as [_ Hreset].
  destruct (Hinit NullExtension.Espec) as [B_init2 _].
  destruct (Hreset NullExtension.Espec) as (B_resetkeep & B_reset & B_reset2 & _).
  pose proof (Hfixed NullExtension.Espec) as B_fixed.
  destruct (ZL NullExtension.Espec) as (U_inflate & U_fast & U_upd & U_check & U_setdict & _).
  pose proof (rbd_body_inflate_table NullExtension.Espec) as B_table.
  pose proof (Zlib.proof.harness.rj_bad_dictionary.RDMain.body_main
                Zlib.proof.harness.rj_bad_dictionary.RDTheory.rbd_theory) as B_main.
  change Zlib.contracts.rj_bad_dictionary.whole_prog with p.
  harness_safe_by_specs CS G main_post_TT.
  - reflexivity.
  - rbd_entry_main (semax_body_main_core _ _ p _ _ R globals_ok B_main eq_refl) BR.
    rbd_entry B_upto BR.
    rbd_entry B_clip BR.
    rbd_entry B_any BR.
    rbd_entry B_offer BR.
    rbd_entry B_new BR.
    rbd_entry B_init2 BR.
    rbd_entry B_reset2 BR.
    rbd_entry B_reset BR.
    rbd_entry B_resetkeep BR.
    rbd_entry U_check BR.
    rbd_entry U_inflate BR.
    rbd_entry U_fast BR.
    rbd_entry U_upd BR.
    rbd_entry U_setdict BR.
    rbd_entry B_fixed BR.
    rbd_entry_table B_table.
    rbd_entry Zlib.proof.adler32.Body_adler32.body_adler32 BR.
    rbd_entry Zlib.proof.adler32.Body_adler32_z.body_adler32_z BR.
    rbd_entry Zlib.proof.crc32.Body_crc32.body_crc32 BR.
    rbd_entry Zlib.proof.crc32.Body_crc32_z.body_crc32_z BR.
    rbd_entry (@Zlib.proof.zutil.Spec.body_zcalloc Zlib.units.Inflate.CS) BR.
    rbd_entry (@Zlib.proof.zutil.Spec.body_zcfree Zlib.units.Inflate.CS) BR.
    rbd_entry (@Zlib.proof.zutil.Libc.body_memcpy Zlib.units.Inflate.CS) BR.
    rbd_entry (@Zlib.proof.zutil.Libc.body_memset Zlib.units.Inflate.CS) BR.
    entry_external (@external_ok_malloc CS).
    entry_external (@external_ok_free CS).
    entry_external (@external_ok_size CS).
    entry_external (@external_ok_bytes CS).
    entry_external (@external_ok_u32 CS).
    entry_external (@external_ok_assert CS).
    entry_external (@external_ok_assume CS).
    apply Forall_nil.
Qed.
