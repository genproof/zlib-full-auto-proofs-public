(* The laws rj_bad_block and rj_far_back: the assembly of harness_safe of each program from the shared bodies
   (inflate.c through SpecWLib.specw_lib_stmt and LibStmt5's inflate_lib5_stmt; zutil, libc, adler32, crc32,
   inftrees; the helpers of laws_common.h; the bit writer, BWBodies.v), the two mains (BBMain.v, FBMain.v), their
   theories (BBTheory.v, BBSow.v, FBTheory.v over FRTheory.v and BWBits.v) and the globals (BWGlobals.v).

   inflate.c's functions get, in each program's context, the allocator-generic specifications of the port at
   zlib's default allocator (SpecWLib.zc_alloc) for inflate, inflate_fast, updatewindow and inflateStateCheck,
   and Spec5's for inflateInit2_ and the reset functions; main's (SpecW.inflate_specW) and the reset functions'
   (Spec5.inflateStateCheck_spec) callee specifications are moved to them by the bridge (specw_bridge_stmt). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.LibStmt5.
Require Zlib.proof.inflate_api.LibProof5.
Require Import Zlib.proof.inflate_api.SpecWLib.
Require Zlib.proof.adler32.Spec Zlib.proof.adler32.Body_adler32 Zlib.proof.adler32.Body_adler32_z.
Require Zlib.proof.crc32.Spec Zlib.proof.crc32.Body_crc32 Zlib.proof.crc32.Body_crc32_z.
Require Zlib.proof.zutil.Spec Zlib.proof.zutil.Libc.
Require Zlib.proof.inftrees.spec Zlib.proof.inftrees.verif_inflate_table Zlib.proof.inftrees.part_loop_facts
        Zlib.proof.inftrees.part_seg_counts Zlib.proof.inftrees.part_seg_max0 Zlib.proof.inftrees.part_seg_check
        Zlib.proof.inftrees.part_seg_sort Zlib.proof.inftrees.part_seg_init Zlib.proof.inftrees.part_seg_loop
        Zlib.proof.inftrees.part_seg_fin.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.bit_writer.BWSpec Zlib.proof.harness.bit_writer.BWBodies.
Require Import Zlib.proof.harness.bit_writer.BWLawCS Zlib.proof.harness.bit_writer.BWGlobals.
Require Zlib.proof.harness.bit_writer.FRTheory Zlib.proof.harness.bit_writer.BWBits.
Require Zlib.proof.harness.bit_writer.BBTheory Zlib.proof.harness.bit_writer.BBSow.
Require Zlib.proof.harness.bit_writer.FBTheory.
Require Zlib.proof.harness.bit_writer.BBMain Zlib.proof.harness.bit_writer.FBMain.
Require Zlib.contracts.rj_bad_block Zlib.contracts.rj_far_back.
Require Zlib.harness.rj_bad_block.code Zlib.harness.rj_far_back.code.

(* inflate_table's body (the inftrees proof, from its segments) *)
Lemma bw_body_inflate_table : Zlib.proof.inftrees.spec.body_inflate_table_stmt.
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

(* the specifications of inflate.c's functions every program here links (after main's and the harness's) *)
Definition G_inflate : funspecs :=
  [inflateInit2__spec; inflateReset2_spec; inflateReset_spec; inflateResetKeep_spec;
   @inflateStateCheck_uspec globals zc_alloc; @inflate_uspec globals zc_alloc;
   @inflate_fast_uspec globals zc_alloc; @updatewindow_uspec globals zc_alloc;
   inflate_fixed_spec; Zlib.proof.inftrees.spec.inflate_table_spec;
   Zlib.proof.adler32.Spec.adler32_spec; Zlib.proof.adler32.Spec.adler32_z_spec;
   Zlib.proof.crc32.Spec.crc32_spec; Zlib.proof.crc32.Spec.crc32_z_spec;
   zcalloc_i; zcfree_i; memcpy_i; memset_i].

(* ctx_sub with, besides the environment's transports, the bridge's funspec_subs *)
Ltac bw_spec_sub BR :=
  first [ env_spec_sub
        | apply (proj1 BR) | apply (proj1 (proj2 BR)) | apply (proj2 (proj2 BR)) ].

Ltac bw_ctx_sub BR :=
  let i := fresh "i" in let phi := fresh "phi" in let E := fresh "E" in
  intros i phi E; simpl in E;
  repeat (if_tac in E; [ inv E; eexists; split; [ reflexivity | bw_spec_sub BR ] | ]);
  try discriminate.

Ltac bw_entry B BR :=
  lazymatch type of B with
  | @semax_body _ _ ?cs1 ?f ?spec =>
    apply Forall_cons;
    [ eapply (entry_moved _ _ cs1 _ _ _ _ (fst spec) (snd spec) f B);
      [ reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
      | find_ids_V | vm_compute; reflexivity | vm_compute; reflexivity | bw_ctx_sub BR ]
    | ]
  end.

(* inflate_table's context lists inftrees' inflate_fixed_spec (precondition False): the entry by
   NDsubsume_subsume *)
Ltac bw_entry_table B :=
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

Definition G_bb : funspecs :=
  [(Zlib.harness.rj_bad_block.code._main, QPmain_spec_ext' BB.p tt main_post_TT);
   put_bits_spec; put_literal_spec; upto_spec; clip_spec; any_bytes_spec; offer_spec; new_stream_spec] ++
  G_inflate ++
  [(_quickproof_malloc, @malloc_spec' BB.CS); (_quickproof_free, @free_spec' BB.CS);
   nondet_size_spec; @nondet_bytes_spec BB.CS; nondet_u8_spec; nondet_u32_spec; gp_assert_spec; gp_assume_spec].

Definition G_fb : funspecs :=
  [(Zlib.harness.rj_far_back.code._main, QPmain_spec_ext' FB.p tt main_post_TT);
   put_bits_spec; put_literal_spec; upto_spec; clip_spec; any_bytes_spec; copy_of_spec; offer_spec;
   new_stream_spec] ++ G_inflate ++
  [(_quickproof_malloc, @malloc_spec' FB.CS); (_quickproof_free, @free_spec' FB.CS);
   nondet_size_spec; @nondet_bytes_spec FB.CS; nondet_u8_spec; nondet_u32_spec; gp_assert_spec; gp_assume_spec].

Lemma bb_core : specw_lib_stmt -> laws_common_ok -> harness_safe Zlib.contracts.rj_bad_block.whole_prog.
Proof.
  intros [ZL BR] (B_upto & B_clip & B_any & _ & _ & B_offer & B_new).
  destruct Zlib.proof.inflate_api.LibProof5.inflate_lib5_proof
    as (Hinit & Hreset & _ & _ & _ & _ & _ & _ & Hfixed & _).
  destruct Hreset as [_ Hreset].
  destruct (Hinit NullExtension.Espec) as [B_init2 _].
  destruct (Hreset NullExtension.Espec) as (B_resetkeep & B_reset & B_reset2 & _).
  pose proof (Hfixed NullExtension.Espec) as B_fixed.
  destruct (ZL NullExtension.Espec) as (U_inflate & U_fast & U_upd & U_check & _).
  pose proof (bw_body_inflate_table NullExtension.Espec) as B_table.
  destruct bit_writer_bodies as [B_pb B_pl].
  pose proof (Zlib.proof.harness.bit_writer.BBMain.bb_body_main
    (Zlib.proof.harness.bit_writer.BBTheory.bb_theory Zlib.proof.harness.bit_writer.FRTheory.fr_theory
       (proj1 Zlib.proof.harness.bit_writer.BWBits.bw_bits))
    (Zlib.proof.harness.bit_writer.BBSow.bb_sow Zlib.proof.harness.bit_writer.FRTheory.fr_theory
       (proj1 Zlib.proof.harness.bit_writer.BWBits.bw_bits))) as B_main.
  harness_safe_by_specs BB.CS G_bb main_post_TT.
  - reflexivity.
  - bw_entry (semax_body_main_core _ _ BB.p _ _ R_bb globals_ok_bb B_main eq_refl) BR.
    bw_entry B_pb BR.
    bw_entry B_pl BR.
    bw_entry B_upto BR.
    bw_entry B_clip BR.
    bw_entry B_any BR.
    bw_entry B_offer BR.
    bw_entry B_new BR.
    bw_entry B_init2 BR.
    bw_entry B_reset2 BR.
    bw_entry B_reset BR.
    bw_entry B_resetkeep BR.
    bw_entry U_check BR.
    bw_entry U_inflate BR.
    bw_entry U_fast BR.
    bw_entry U_upd BR.
    bw_entry B_fixed BR.
    bw_entry_table B_table.
    bw_entry Zlib.proof.adler32.Body_adler32.body_adler32 BR.
    bw_entry Zlib.proof.adler32.Body_adler32_z.body_adler32_z BR.
    bw_entry Zlib.proof.crc32.Body_crc32.body_crc32 BR.
    bw_entry Zlib.proof.crc32.Body_crc32_z.body_crc32_z BR.
    bw_entry (@Zlib.proof.zutil.Spec.body_zcalloc Zlib.units.Inflate.CS) BR.
    bw_entry (@Zlib.proof.zutil.Spec.body_zcfree Zlib.units.Inflate.CS) BR.
    bw_entry (@Zlib.proof.zutil.Libc.body_memcpy Zlib.units.Inflate.CS) BR.
    bw_entry (@Zlib.proof.zutil.Libc.body_memset Zlib.units.Inflate.CS) BR.
    entry_external (@external_ok_malloc BB.CS).
    entry_external (@external_ok_free BB.CS).
    entry_external (@external_ok_size BB.CS).
    entry_external (@external_ok_bytes BB.CS).
    entry_external (@external_ok_u8 BB.CS).
    entry_external (@external_ok_u32 BB.CS).
    entry_external (@external_ok_assert BB.CS).
    entry_external (@external_ok_assume BB.CS).
    apply Forall_nil.
Qed.

Lemma fb_core : specw_lib_stmt -> laws_common_ok -> harness_safe Zlib.contracts.rj_far_back.whole_prog.
Proof.
  intros [ZL BR] (B_upto & B_clip & B_any & B_copy & _ & B_offer & B_new).
  destruct Zlib.proof.inflate_api.LibProof5.inflate_lib5_proof
    as (Hinit & Hreset & _ & _ & _ & _ & _ & _ & Hfixed & _).
  destruct Hreset as [_ Hreset].
  destruct (Hinit NullExtension.Espec) as [B_init2 _].
  destruct (Hreset NullExtension.Espec) as (B_resetkeep & B_reset & B_reset2 & _).
  pose proof (Hfixed NullExtension.Espec) as B_fixed.
  destruct (ZL NullExtension.Espec) as (U_inflate & U_fast & U_upd & U_check & _).
  pose proof (bw_body_inflate_table NullExtension.Espec) as B_table.
  destruct bit_writer_bodies as [B_pb B_pl].
  pose proof (Zlib.proof.harness.bit_writer.FBMain.fb_body_main
    (Zlib.proof.harness.bit_writer.FBTheory.fb_theory Zlib.proof.harness.bit_writer.FRTheory.fr_theory
       (proj2 Zlib.proof.harness.bit_writer.BWBits.bw_bits))) as B_main.
  harness_safe_by_specs FB.CS G_fb main_post_TT.
  - reflexivity.
  - bw_entry (semax_body_main_core _ _ FB.p _ _ R_fb globals_ok_fb B_main eq_refl) BR.
    bw_entry B_pb BR.
    bw_entry B_pl BR.
    bw_entry B_upto BR.
    bw_entry B_clip BR.
    bw_entry B_any BR.
    bw_entry B_copy BR.
    bw_entry B_offer BR.
    bw_entry B_new BR.
    bw_entry B_init2 BR.
    bw_entry B_reset2 BR.
    bw_entry B_reset BR.
    bw_entry B_resetkeep BR.
    bw_entry U_check BR.
    bw_entry U_inflate BR.
    bw_entry U_fast BR.
    bw_entry U_upd BR.
    bw_entry B_fixed BR.
    bw_entry_table B_table.
    bw_entry Zlib.proof.adler32.Body_adler32.body_adler32 BR.
    bw_entry Zlib.proof.adler32.Body_adler32_z.body_adler32_z BR.
    bw_entry Zlib.proof.crc32.Body_crc32.body_crc32 BR.
    bw_entry Zlib.proof.crc32.Body_crc32_z.body_crc32_z BR.
    bw_entry (@Zlib.proof.zutil.Spec.body_zcalloc Zlib.units.Inflate.CS) BR.
    bw_entry (@Zlib.proof.zutil.Spec.body_zcfree Zlib.units.Inflate.CS) BR.
    bw_entry (@Zlib.proof.zutil.Libc.body_memcpy Zlib.units.Inflate.CS) BR.
    bw_entry (@Zlib.proof.zutil.Libc.body_memset Zlib.units.Inflate.CS) BR.
    entry_external (@external_ok_malloc FB.CS).
    entry_external (@external_ok_free FB.CS).
    entry_external (@external_ok_size FB.CS).
    entry_external (@external_ok_bytes FB.CS).
    entry_external (@external_ok_u8 FB.CS).
    entry_external (@external_ok_u32 FB.CS).
    entry_external (@external_ok_assert FB.CS).
    entry_external (@external_ok_assume FB.CS).
    apply Forall_nil.
Qed.

Lemma bw_core : specw_lib_stmt -> laws_common_ok ->
  harness_safe Zlib.contracts.rj_bad_block.whole_prog /\ harness_safe Zlib.contracts.rj_far_back.whole_prog.
Proof.
  intros SW LC. exact (conj (bb_core SW LC) (fb_core SW LC)).
Qed.
