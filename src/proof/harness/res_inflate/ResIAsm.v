(* Laws res_free_inflate and res_memory_inflate: harness_safe of each program from main's body (ResISpecs's
   main_free_stmt / main_memory_stmt), the program's globals (ResIGlobals.v) and the shared bodies:
   laws_common.h's helpers (laws_common_ok), laws_session.h's inflate_window_ok for res_memory_inflate
   (laws_session_ok), the counting allocator (counted_ok), inflate.c's functions against
   their uspecs for the counting allocators (USpec.za_inflate_ulib_stmt Ac, with the uspecs in the law's
   context; main's zsig specifications are subspecifications of them, ResISpecs.inflateInit2__sub etc., from
   USpec.za_uspec_sub_stmt Ac), and the bodies that do not depend on the allocator (inflate_fixed, inflate_table,
   adler32, crc32, memcpy, memset: the existing proofs).  Every other function of the programs gets a vacuous
   specification. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.za.inflate_api.USpec.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.counted.Spec.
Require Zlib.proof.harness.laws_session.Spec.
Require Import Zlib.proof.harness.res_inflate.ResICS Zlib.proof.harness.res_inflate.ResISpecs
               Zlib.proof.harness.res_inflate.ResIGlobals.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Zlib.proof.inflate.Callees.
Require Zlib.proof.adler32.Spec Zlib.proof.adler32.Body_adler32 Zlib.proof.adler32.Body_adler32_z.
Require Zlib.proof.crc32.Spec Zlib.proof.crc32.Body_crc32 Zlib.proof.crc32.Body_crc32_z.
Require Zlib.proof.zutil.Libc.
Require Zlib.proof.inftrees.spec Zlib.proof.inftrees.verif_inflate_table Zlib.proof.inftrees.part_loop_facts
        Zlib.proof.inftrees.part_seg_counts Zlib.proof.inftrees.part_seg_max0 Zlib.proof.inftrees.part_seg_check
        Zlib.proof.inftrees.part_seg_sort Zlib.proof.inftrees.part_seg_init Zlib.proof.inftrees.part_seg_loop
        Zlib.proof.inftrees.part_seg_fin.
Require Zlib.contracts.res_free_inflate Zlib.contracts.res_memory_inflate.
Require Zlib.harness.res_free_inflate.code Zlib.harness.res_memory_inflate.code.

(* inflate_table's body (the inftrees proof, from its segments) *)
Lemma ri_body_inflate_table : Zlib.proof.inftrees.spec.body_inflate_table_stmt.
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

(* inflate_fixed's body (it only sets the four table fields of the state) *)
Lemma ri_body_inflate_fixed {Espec: OracleKind} :
  @semax_body Zlib.proof.inftrees.spec.Vprog [] Zlib.units.Inflate.CS Zlib.inftrees.code.f_inflate_fixed
    Zlib.proof.inflate.Callees.inflate_fixed_spec.
Proof.
  clear Espec. start_function.
  forward. forward. forward. forward. entailer!.
Qed.

(* The specifications of each law, but main's: every function main reaches.  inflate.c's functions have
   their uspecs at the counting allocators.  res_memory_inflate's program has laws_session.h's
   inflate_window_ok, laws_common.h's upto and clip and the environment's nondet_u8, nondet_size and gp_assume;
   res_free_inflate's does not (its main uses none of them,
   and the C compiler drops the unused static helpers). *)
Definition G_lib_memory : funspecs :=
  [(* the harness *)
   Zlib.proof.harness.laws_session.Spec.inflate_window_ok_spec;
   upto_spec; clip_spec; any_bytes_spec; offer_spec; counted_stream_spec; count_alloc_spec; count_free_spec;
   (* inflate.c, for every counting allocator *)
   inflateInit2__uspec Ac; inflate_uspec Ac; inflateEnd_uspec Ac; inflateReset2_uspec Ac; inflateReset_uspec Ac;
   inflateResetKeep_uspec Ac; inflateStateCheck_uspec Ac; updatewindow_uspec Ac; inflate_fast_uspec Ac;
   (* the functions inflate() calls that do not depend on the allocator *)
   Zlib.proof.inflate.Callees.inflate_fixed_spec; Zlib.proof.inftrees.spec.inflate_table_spec;
   Zlib.proof.adler32.Spec.adler32_spec; Zlib.proof.adler32.Spec.adler32_z_spec;
   Zlib.proof.crc32.Spec.crc32_spec; Zlib.proof.crc32.Spec.crc32_z_spec;
   memcpy_i; memset_i;
   (* the environment *)
   (_quickproof_malloc, @malloc_spec' CSi); (_quickproof_free, @free_spec' CSi);
   nondet_u8_spec; nondet_u32_spec; nondet_size_spec; @nondet_bytes_spec CSi; gp_assert_spec; gp_assume_spec].

Definition G_lib_free : funspecs :=
  [(* the harness *)
   any_bytes_spec; offer_spec; counted_stream_spec; count_alloc_spec; count_free_spec;
   (* inflate.c, for every counting allocator *)
   inflateInit2__uspec Ac; inflate_uspec Ac; inflateEnd_uspec Ac; inflateReset2_uspec Ac; inflateReset_uspec Ac;
   inflateResetKeep_uspec Ac; inflateStateCheck_uspec Ac; updatewindow_uspec Ac; inflate_fast_uspec Ac;
   (* the functions inflate() calls that do not depend on the allocator *)
   Zlib.proof.inflate.Callees.inflate_fixed_spec; Zlib.proof.inftrees.spec.inflate_table_spec;
   Zlib.proof.adler32.Spec.adler32_spec; Zlib.proof.adler32.Spec.adler32_z_spec;
   Zlib.proof.crc32.Spec.crc32_spec; Zlib.proof.crc32.Spec.crc32_z_spec;
   memcpy_i; memset_i;
   (* the environment *)
   (_quickproof_malloc, @malloc_spec' CSi); (_quickproof_free, @free_spec' CSi);
   nondet_u32_spec; @nondet_bytes_spec CSi; gp_assert_spec].

(* The variables of a body's context are the program's, by ONE computation (find_ids_V computes the
   program's variables once per variable). *)
Lemma ri_find_ids_b (V W : varspecs) :
  forallb (fun x => match initial_world.find_id (fst x) W with Some t => eqb_type t (snd x) | None => false end) V = true ->
  Forall (fun x => initial_world.find_id (fst x) W = Some (snd x)) V.
Proof.
  intros H. rewrite forallb_forall in H. rewrite Forall_forall. intros x IN. specialize (H x IN).
  destruct (initial_world.find_id (fst x) W) as [t|]; [ | discriminate]. apply eqb_type_spec in H. subst; reflexivity.
Qed.

(* a context entry: the same specification, an environment specification at other compspecs, or (main's
   calls of inflate.c) a zsig that the uspec refines ([HS]: za_uspec_sub_stmt Ac) *)
Ltac ri_spec_sub HS :=
  lazymatch goal with
  | |- funspec_sub (@malloc_spec' ?c1) (@malloc_spec' ?c2) =>
    first [ constr_eq c1 c2; apply funspec_sub_refl
          | apply malloc_spec'_sub;
            try (apply cspecs_sub_by_computation; vm_compute; reflexivity);
            try (apply preserved_by_computation; vm_compute; reflexivity) ]
  | |- funspec_sub (@free_spec' ?c1) (@free_spec' ?c2) =>
    first [ constr_eq c1 c2; apply funspec_sub_refl
          | apply free_spec'_sub;
            try (apply cspecs_sub_by_computation; vm_compute; reflexivity);
            try (apply preserved_by_computation; vm_compute; reflexivity) ]
  | |- _ =>
    first [ apply funspec_sub_refl
          | exact (inflateInit2__sub HS) | exact (inflate_sub HS) | exact (inflateEnd_sub HS)
          | apply nondet_bytes_spec_cs ]
  end.

Ltac ri_ctx_sub HS :=
  let i := fresh "i" in let phi := fresh "phi" in let E := fresh "E" in
  intros i phi E; simpl in E;
  repeat (if_tac in E; [ inv E; eexists; split; [ reflexivity | ri_spec_sub HS ] | ]);
  try discriminate.

Ltac ri_entry B HS :=
  lazymatch type of B with
  | @semax_body _ _ ?cs1 ?f ?spec =>
    apply Forall_cons;
    [ eapply (entry_moved _ _ cs1 _ _ _ _ (fst spec) (snd spec) f B);
      [ reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
      | apply ri_find_ids_b; vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
      | ri_ctx_sub HS ]
    | ]
  end.

(* inflate_table's context lists inftrees' inflate_fixed_spec (precondition False, never called): the entry
   by NDsubsume_subsume *)
Ltac ri_entry_table B :=
  apply Forall_cons;
  [ eapply (entry_moved _ _ Zlib.units.Inftrees.CS _ _ _ _ _ _ _ B);
    [ reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
    | apply ri_find_ids_b; vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | ]
  | ];
  [ intros i phi E; simpl in E;
    if_tac in E; [ inv E; eexists; split; [ reflexivity | apply funspec_sub_refl ] | ];
    if_tac in E; [ | discriminate ];
    inv E; eexists; split; [ reflexivity | ];
    apply NDsubsume_subsume; [ split; reflexivity | split; [ split; reflexivity | ] ];
      intros x [ge args]; simpl; unfold PROPx; simpl; normalize
  | ].

(* The entries of inflate.c's functions and inflate()'s other callees (the middle of either list), from the bodies of inflate.c (HU) and the existing proofs. *)
Ltac ri_entries_inflate HU HS :=
  destruct (HU NullExtension.Espec)
    as (U_inflate & U_fast & U_upd & U_check & _ & U_init2 & U_resetkeep & U_reset & U_reset2 & U_end);
  pose proof (@ri_body_inflate_fixed NullExtension.Espec) as B_fixed;
  pose proof (ri_body_inflate_table NullExtension.Espec) as B_table;
  ri_entry U_init2 HS;
  ri_entry U_inflate HS;
  ri_entry U_end HS;
  ri_entry U_reset2 HS;
  ri_entry U_reset HS;
  ri_entry U_resetkeep HS;
  ri_entry U_check HS;
  ri_entry U_upd HS;
  ri_entry U_fast HS;
  ri_entry B_fixed HS;
  ri_entry_table B_table;
  ri_entry Zlib.proof.adler32.Body_adler32.body_adler32 HS;
  ri_entry Zlib.proof.adler32.Body_adler32_z.body_adler32_z HS;
  ri_entry Zlib.proof.crc32.Body_crc32.body_crc32 HS;
  ri_entry Zlib.proof.crc32.Body_crc32_z.body_crc32_z HS;
  ri_entry (@Zlib.proof.zutil.Libc.body_memcpy Zlib.units.Inflate.CS) HS;
  ri_entry (@Zlib.proof.zutil.Libc.body_memset Zlib.units.Inflate.CS) HS.

(* After harness_safe_by_specs: main's entry from [M], then every entry of G_lib_memory. *)
Ltac ri_entries_memory M HL HLS HC HU HS :=
  destruct HL as (L_upto & L_clip & L_any_bytes & _ & _ & L_offer & _);
  destruct HLS as (_ & S_window & _);
  destruct HC as (C_alloc & C_free & C_stream);
  ri_entry M HS;
  ri_entry S_window HS;
  ri_entry L_upto HS;
  ri_entry L_clip HS;
  ri_entry L_any_bytes HS;
  ri_entry L_offer HS;
  ri_entry C_stream HS;
  ri_entry C_alloc HS;
  ri_entry C_free HS;
  ri_entries_inflate HU HS;
  entry_external (@external_ok_malloc CSi);
  entry_external (@external_ok_free CSi);
  entry_external (@external_ok_u8 CSi);
  entry_external (@external_ok_u32 CSi);
  entry_external (@external_ok_size CSi);
  entry_external (@external_ok_bytes CSi);
  entry_external (@external_ok_assert CSi);
  entry_external (@external_ok_assume CSi);
  apply Forall_nil.

(* the same for G_lib_free *)
Ltac ri_entries_free M HL HC HU HS :=
  destruct HL as (_ & _ & L_any_bytes & _ & _ & L_offer & _);
  destruct HC as (C_alloc & C_free & C_stream);
  ri_entry M HS;
  ri_entry L_any_bytes HS;
  ri_entry L_offer HS;
  ri_entry C_stream HS;
  ri_entry C_alloc HS;
  ri_entry C_free HS;
  ri_entries_inflate HU HS;
  entry_external (@external_ok_malloc CSi);
  entry_external (@external_ok_free CSi);
  entry_external (@external_ok_u32 CSi);
  entry_external (@external_ok_bytes CSi);
  entry_external (@external_ok_assert CSi);
  apply Forall_nil.

Definition G_free : funspecs :=
  (Zlib.harness.res_free_inflate.code._main,
   QPmain_spec_ext' Zlib.contracts.res_free_inflate.whole_prog tt main_post_TT) :: G_lib_free.

Definition G_memory : funspecs :=
  (Zlib.harness.res_memory_inflate.code._main,
   QPmain_spec_ext' Zlib.contracts.res_memory_inflate.whole_prog tt main_post_TT) :: G_lib_memory.

Lemma res_free_inflate_asm :
  laws_common_ok -> counted_ok -> za_inflate_ulib_stmt Ac -> za_uspec_sub_stmt Ac -> main_free_stmt ->
  harness_safe Zlib.contracts.res_free_inflate.whole_prog.
Proof.
  intros HL HC HU HS HM. red in HM.
  pose proof (semax_body_main_core _ _ Zlib.contracts.res_free_inflate.whole_prog _ _
    (Ri Zlib.harness.res_free_inflate.code.___stringlit_res_free_inflate_1) globals_free HM eq_refl) as M.
  harness_safe_by_specs CSi G_free main_post_TT.
  - reflexivity.
  - ri_entries_free M HL HC HU HS.
Qed.

Lemma res_memory_inflate_asm :
  laws_common_ok -> Zlib.proof.harness.laws_session.Spec.laws_session_ok -> counted_ok ->
  za_inflate_ulib_stmt Ac -> za_uspec_sub_stmt Ac -> main_memory_stmt ->
  harness_safe Zlib.contracts.res_memory_inflate.whole_prog.
Proof.
  intros HL HLS HC HU HS HM. red in HM.
  pose proof (semax_body_main_core _ _ Zlib.contracts.res_memory_inflate.whole_prog _ _
    (Ri Zlib.harness.res_memory_inflate.code.___stringlit_res_memory_inflate_1) globals_memory HM eq_refl) as M.
  harness_safe_by_specs CSi G_memory main_post_TT.
  - reflexivity.
  - ri_entries_memory M HL HLS HC HU HS.
Qed.

Lemma res_inflate_asm :
  laws_common_ok -> Zlib.proof.harness.laws_session.Spec.laws_session_ok -> counted_ok ->
  za_inflate_ulib_stmt Ac -> za_uspec_sub_stmt Ac -> main_free_stmt -> main_memory_stmt ->
  harness_safe Zlib.contracts.res_free_inflate.whole_prog /\ harness_safe Zlib.contracts.res_memory_inflate.whole_prog.
Proof.
  intros HL HLS HC HU HS HMf HMm. split.
  - exact (res_free_inflate_asm HL HC HU HS HMf).
  - exact (res_memory_inflate_asm HL HLS HC HU HS HMm).
Qed.
