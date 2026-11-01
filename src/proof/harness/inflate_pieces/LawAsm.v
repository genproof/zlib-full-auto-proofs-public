(* The laws rj_any_input, api_counters and api_untouched_output: the assembly of harness_safe of each program
   from the shared bodies (inflate.c through SpecWLib.specw_lib_stmt and LibStmt5's inflate_lib5_stmt; zutil,
   libc, adler32, crc32, inftrees; the helpers of laws_common.h and, for rj_any_input and api_untouched_output,
   of laws_session.h), the three mains (Mains.v), the theory (Theory.v and Progress.v with StepW.stepf2_mwf3W) and
   the globals (Globals.v).

   inflate.c's functions get, in each program's context, the allocator-generic specifications of the port at
   zlib's default allocator (SpecWLib.zc_alloc) for inflate, inflate_fast, updatewindow, inflateStateCheck and
   inflateSetDictionary, and Spec5's for inflateInit2_ and the reset functions; main's callee specifications
   (SpecW.inflate_specW, inflateSetDictionary_specW) and the reset functions' (Spec5.inflateStateCheck_spec)
   are moved to them by the bridge (specw_bridge_stmt).  The recipe is the bit writer laws' (BWLawAsm.v). *)
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
Require Import Zlib.proof.harness.inflate_pieces.LawCS.
Require Import Zlib.proof.harness.inflate_pieces.Globals.
Require Import Zlib.proof.harness.inflate_pieces.Mains.
Require Import Zlib.proof.harness.inflate_pieces.Facts.
Require Import Zlib.proof.harness.inflate_pieces.Progress.
Require Import Zlib.proof.harness.laws_session.Spec.
Module LS := Zlib.proof.harness.laws_session.Spec.
Require Zlib.proof.inflate.StepW.
Require Zlib.proof.harness.inflate_pieces.Theory.
Require Zlib.proof.harness.inflate_pieces.Progress.
Require Zlib.contracts.rj_any_input.
Require Zlib.contracts.api_counters.
Require Zlib.contracts.api_untouched_output.
Require Zlib.harness.rj_any_input.code.
Require Zlib.harness.api_counters.code.
Require Zlib.harness.api_untouched_output.code.

(* inflate_table's body (the inftrees proof, from its segments) *)
Lemma pc_body_inflate_table : Zlib.proof.inftrees.spec.body_inflate_table_stmt.
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

(* the specifications of inflate.c's functions the three programs link: the port's at zlib's default
   allocator for inflate, inflate_fast, updatewindow, inflateStateCheck and inflateSetDictionary, Spec5's for
   inflateInit2_ and the reset functions *)
Definition G_inflate : funspecs :=
  [inflateInit2__spec; inflateReset2_spec; inflateReset_spec; inflateResetKeep_spec;
   @inflateStateCheck_uspec globals zc_alloc; @inflate_uspec globals zc_alloc;
   @inflate_fast_uspec globals zc_alloc; @updatewindow_uspec globals zc_alloc;
   @inflateSetDictionary_uspec globals zc_alloc;
   inflate_fixed_spec; Zlib.proof.inftrees.spec.inflate_table_spec;
   Zlib.proof.adler32.Spec.adler32_spec; Zlib.proof.adler32.Spec.adler32_z_spec;
   Zlib.proof.crc32.Spec.crc32_spec; Zlib.proof.crc32.Spec.crc32_z_spec;
   zcalloc_i; zcfree_i; memcpy_i; memset_i].

(* ctx_sub with, besides the environment's transports, the bridge's funspec_subs *)
(* (QuickProof.Assembly.free_spec'_sub has a single premise, which env_spec_sub's free case does not expect) *)
Ltac pc_spec_sub BR :=
  first [ env_spec_sub
        | apply free_spec'_sub; apply preserved_by_computation; vm_compute; reflexivity
        | apply (proj1 BR) | apply (proj1 (proj2 BR)) | apply (proj2 (proj2 BR)) ].

Ltac pc_ctx_sub BR :=
  let i := fresh "i" in let phi := fresh "phi" in let E := fresh "E" in
  intros i phi E; simpl in E;
  repeat (if_tac in E; [ inv E; eexists; split; [ reflexivity | pc_spec_sub BR ] | ]);
  try discriminate.

Ltac pc_entry B BR :=
  lazymatch type of B with
  | @semax_body _ _ ?cs1 ?f ?spec =>
    apply Forall_cons;
    [ eapply (entry_moved _ _ cs1 _ _ _ _ (fst spec) (snd spec) f B);
      [ reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
      | find_ids_V | vm_compute; reflexivity | vm_compute; reflexivity | pc_ctx_sub BR ]
    | ]
  end.

(* inflate_table's context lists inftrees' inflate_fixed_spec (precondition False): the entry by
   NDsubsume_subsume *)
Ltac pc_entry_table B :=
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

Definition G_any : funspecs :=
  [(Zlib.harness.rj_any_input.code._main, QPmain_spec_ext' Any.p tt main_post_TT);
   upto_spec; clip_spec; any_bytes_spec; copy_of_spec; offer_spec; new_stream_spec;
   LS.inflate_window_ok_spec; LS.position_of_spec; LS.unmoved_spec] ++ G_inflate ++
  [(_quickproof_malloc, @malloc_spec' Any.CS); (_quickproof_free, @free_spec' Any.CS);
   nondet_size_spec; @nondet_bytes_spec Any.CS; nondet_u8_spec; nondet_u32_spec; gp_assert_spec; gp_assume_spec].

Definition G_cnt : funspecs :=
  [(Zlib.harness.api_counters.code._main, QPmain_spec_ext' Cnt.p tt main_post_TT);
   upto_spec; clip_spec; any_bytes_spec; copy_of_spec; offer_spec; new_stream_spec] ++ G_inflate ++
  [(_quickproof_malloc, @malloc_spec' Cnt.CS); (_quickproof_free, @free_spec' Cnt.CS);
   nondet_size_spec; @nondet_bytes_spec Cnt.CS; nondet_u8_spec; nondet_u32_spec; gp_assert_spec].

Definition G_unt : funspecs :=
  [(Zlib.harness.api_untouched_output.code._main, QPmain_spec_ext' Unt.p tt main_post_TT);
   upto_spec; clip_spec; any_bytes_spec; copy_of_spec; bytes_eq_spec; offer_spec; new_stream_spec;
   LS.inflate_window_ok_spec; LS.position_of_spec; LS.accounted_spec; LS.unmoved_spec] ++
  G_inflate ++
  [(_quickproof_malloc, @malloc_spec' Unt.CS); (_quickproof_free, @free_spec' Unt.CS);
   nondet_size_spec; @nondet_bytes_spec Unt.CS; nondet_u8_spec; nondet_u32_spec; gp_assert_spec; gp_assume_spec].

(* the facts of the theory, from the step invariant *)
Lemma pc_facts4 : exists P, pieces_facts P /\ pieces_progress P.
Proof.
  exact (Zlib.proof.harness.inflate_pieces.Progress.pieces_theory4 Zlib.proof.inflate.StepW.stepf2_mwf3W).
Qed.

(* the entries of inflate.c's, inftrees.c's, adler32.c's, crc32.c's and zutil.c's bodies *)
Ltac pc_lib_entries ZL BR :=
  let B_init2 := fresh "B_init2" in let B_resetkeep := fresh "B_resetkeep" in
  let B_reset := fresh "B_reset" in let B_reset2 := fresh "B_reset2" in let B_fixed := fresh "B_fixed" in
  let U_inflate := fresh "U_inflate" in let U_fast := fresh "U_fast" in let U_upd := fresh "U_upd" in
  let U_check := fresh "U_check" in let U_setdict := fresh "U_setdict" in let B_table := fresh "B_table" in
  let Hinit := fresh "Hinit" in let Hreset := fresh "Hreset" in let Hfixed := fresh "Hfixed" in
  destruct Zlib.proof.inflate_api.LibProof5.inflate_lib5_proof
    as (Hinit & Hreset & _ & _ & _ & _ & _ & _ & Hfixed & _);
  destruct Hreset as [_ Hreset];
  destruct (Hinit NullExtension.Espec) as [B_init2 _];
  destruct (Hreset NullExtension.Espec) as (B_resetkeep & B_reset & B_reset2 & _);
  pose proof (Hfixed NullExtension.Espec) as B_fixed;
  destruct (ZL NullExtension.Espec) as (U_inflate & U_fast & U_upd & U_check & U_setdict & _);
  pose proof (pc_body_inflate_table NullExtension.Espec) as B_table;
  pc_entry B_init2 BR;
  pc_entry B_reset2 BR;
  pc_entry B_reset BR;
  pc_entry B_resetkeep BR;
  pc_entry U_check BR;
  pc_entry U_inflate BR;
  pc_entry U_fast BR;
  pc_entry U_upd BR;
  pc_entry U_setdict BR;
  pc_entry B_fixed BR;
  pc_entry_table B_table;
  pc_entry Zlib.proof.adler32.Body_adler32.body_adler32 BR;
  pc_entry Zlib.proof.adler32.Body_adler32_z.body_adler32_z BR;
  pc_entry Zlib.proof.crc32.Body_crc32.body_crc32 BR;
  pc_entry Zlib.proof.crc32.Body_crc32_z.body_crc32_z BR;
  pc_entry (@Zlib.proof.zutil.Spec.body_zcalloc Zlib.units.Inflate.CS) BR;
  pc_entry (@Zlib.proof.zutil.Spec.body_zcfree Zlib.units.Inflate.CS) BR;
  pc_entry (@Zlib.proof.zutil.Libc.body_memcpy Zlib.units.Inflate.CS) BR;
  pc_entry (@Zlib.proof.zutil.Libc.body_memset Zlib.units.Inflate.CS) BR.

Lemma any_core : specw_lib_stmt -> laws_common_ok -> laws_session_ok ->
  harness_safe Zlib.contracts.rj_any_input.whole_prog.
Proof.
  intros [ZL BR] (B_upto & B_clip & B_any & B_copy & _ & B_offer & B_new) (_ & S_window & S_pos & S_unmoved & _).
  destruct pc_facts4 as (P & PF & PG).
  pose proof (proj1 (pieces_mains P PF PG)) as B_main.
  harness_safe_by_specs Any.CS G_any main_post_TT.
  - reflexivity.
  - pc_entry (semax_body_main_core _ _ Any.p _ _ R_any (proj1 pieces_globals) B_main eq_refl) BR.
    pc_entry B_upto BR.
    pc_entry B_clip BR.
    pc_entry B_any BR.
    pc_entry B_copy BR.
    pc_entry B_offer BR.
    pc_entry B_new BR.
    pc_entry S_window BR.
    pc_entry S_pos BR.
    pc_entry S_unmoved BR.
    pc_lib_entries ZL BR.
    entry_external (@external_ok_malloc Any.CS).
    entry_external (@external_ok_free Any.CS).
    entry_external (@external_ok_size Any.CS).
    entry_external (@external_ok_bytes Any.CS).
    entry_external (@external_ok_u8 Any.CS).
    entry_external (@external_ok_u32 Any.CS).
    entry_external (@external_ok_assert Any.CS).
    entry_external (@external_ok_assume Any.CS).
    apply Forall_nil.
Qed.

Lemma cnt_core : specw_lib_stmt -> laws_common_ok -> harness_safe Zlib.contracts.api_counters.whole_prog.
Proof.
  intros [ZL BR] (B_upto & B_clip & B_any & B_copy & _ & B_offer & B_new).
  destruct pc_facts4 as (P & PF & PG).
  pose proof (proj1 (proj2 (pieces_mains P PF PG))) as B_main.
  harness_safe_by_specs Cnt.CS G_cnt main_post_TT.
  - reflexivity.
  - pc_entry (semax_body_main_core _ _ Cnt.p _ _ R_cnt (proj1 (proj2 pieces_globals)) B_main eq_refl) BR.
    pc_entry B_upto BR.
    pc_entry B_clip BR.
    pc_entry B_any BR.
    pc_entry B_copy BR.
    pc_entry B_offer BR.
    pc_entry B_new BR.
    pc_lib_entries ZL BR.
    entry_external (@external_ok_malloc Cnt.CS).
    entry_external (@external_ok_free Cnt.CS).
    entry_external (@external_ok_size Cnt.CS).
    entry_external (@external_ok_bytes Cnt.CS).
    entry_external (@external_ok_u8 Cnt.CS).
    entry_external (@external_ok_u32 Cnt.CS).
    entry_external (@external_ok_assert Cnt.CS).
    apply Forall_nil.
Qed.

Lemma unt_core : specw_lib_stmt -> laws_common_ok -> laws_session_ok ->
  harness_safe Zlib.contracts.api_untouched_output.whole_prog.
Proof.
  intros [ZL BR] (B_upto & B_clip & B_any & B_copy & B_eq & B_offer & B_new)
    (_ & S_window & S_pos & S_unmoved & S_acc & _).
  destruct pc_facts4 as (P & PF & PG).
  pose proof (proj2 (proj2 (pieces_mains P PF PG))) as B_main.
  harness_safe_by_specs Unt.CS G_unt main_post_TT.
  - reflexivity.
  - pc_entry (semax_body_main_core _ _ Unt.p _ _ R_unt (proj2 (proj2 pieces_globals)) B_main eq_refl) BR.
    pc_entry B_upto BR.
    pc_entry B_clip BR.
    pc_entry B_any BR.
    pc_entry B_copy BR.
    pc_entry B_eq BR.
    pc_entry B_offer BR.
    pc_entry B_new BR.
    pc_entry S_window BR.
    pc_entry S_pos BR.
    pc_entry S_acc BR.
    pc_entry S_unmoved BR.
    pc_lib_entries ZL BR.
    entry_external (@external_ok_malloc Unt.CS).
    entry_external (@external_ok_free Unt.CS).
    entry_external (@external_ok_size Unt.CS).
    entry_external (@external_ok_bytes Unt.CS).
    entry_external (@external_ok_u8 Unt.CS).
    entry_external (@external_ok_u32 Unt.CS).
    entry_external (@external_ok_assert Unt.CS).
    entry_external (@external_ok_assume Unt.CS).
    apply Forall_nil.
Qed.

Lemma inflate_pieces_core : specw_lib_stmt -> laws_common_ok -> laws_session_ok ->
  harness_safe Zlib.contracts.rj_any_input.whole_prog /\
  harness_safe Zlib.contracts.api_counters.whole_prog /\
  harness_safe Zlib.contracts.api_untouched_output.whole_prog.
Proof.
  intros SW LC LS. exact (conj (any_core SW LC LS) (conj (cnt_core SW LC) (unt_core SW LC LS))).
Qed.
