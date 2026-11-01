(* Law api_reset: the context of the assembly (ARLawAsm.v) of harness_safe from the shared bodies (inflate.c through SpecWLib.specw_lib_stmt
   and LibStmt5's inflate_lib5_stmt; zutil, libc, adler32, crc32, inftrees; the helpers of laws_common.h), main
   (ARMain.ar_main), the globals (ARGlobals.ar_globals) and the theory (ARTheory.ar_theory).  As inflate_pieces'
   LawAsm.v, with inflateReset and inflateResetKeep at their allocator-generic specifications of the za port
   (USpec.v) at zlib's default allocator: main's view of inflateReset (ARSpec.inflateReset_specA) and Spec5's
   inflateReset_spec, which inflateReset2's body calls, are moved to it by ARSpec.ar_bridge_stmt. *)
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
Require Import Zlib.proof.harness.api_reset.ARMainDefs.
Require Zlib.contracts.api_reset.
Require Zlib.harness.api_reset.code.

(* inflate_table's body (the inftrees proof, from its segments) *)
Lemma ar_body_inflate_table : Zlib.proof.inftrees.spec.body_inflate_table_stmt.
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

(* the specifications of inflate.c's functions the program's reached part calls *)
Definition G_inflate : funspecs :=
  [inflateInit2__spec; inflateReset2_spec; @inflateReset_uspec globals zc_alloc;
   @inflateResetKeep_uspec globals zc_alloc;
   @inflateStateCheck_uspec globals zc_alloc; @inflate_uspec globals zc_alloc;
   @inflate_fast_uspec globals zc_alloc; @updatewindow_uspec globals zc_alloc;
   inflate_fixed_spec; Zlib.proof.inftrees.spec.inflate_table_spec;
   Zlib.proof.adler32.Spec.adler32_spec; Zlib.proof.adler32.Spec.adler32_z_spec;
   Zlib.proof.crc32.Spec.crc32_spec; Zlib.proof.crc32.Spec.crc32_z_spec;
   zcalloc_i; zcfree_i; memcpy_i; memset_i].

Definition G : funspecs :=
  [(Zlib.harness.api_reset.code._main, QPmain_spec_ext' p tt main_post_TT);
   upto_spec; clip_spec; any_bytes_spec; copy_of_spec; bytes_eq_spec; offer_spec; new_stream_spec] ++ G_inflate ++
  [(_quickproof_malloc, @malloc_spec' CS); (_quickproof_free, @free_spec' CS);
   nondet_size_spec; @nondet_bytes_spec CS; nondet_u8_spec; nondet_u32_spec; gp_assert_spec].

(* ctx_sub with, besides the environment's transports, the bridges' funspec_subs *)
Ltac ar_spec_sub BR AB :=
  first [ env_spec_sub
        | apply (proj1 BR) | apply (proj1 (proj2 BR)) | apply (proj2 (proj2 BR))
        | apply (proj1 AB) | apply (proj2 AB) ].

Ltac ar_ctx_sub BR AB :=
  let i := fresh "i" in let phi := fresh "phi" in let E := fresh "E" in
  intros i phi E; simpl in E;
  repeat (if_tac in E; [ inv E; eexists; split; [ reflexivity | ar_spec_sub BR AB ] | ]);
  try discriminate.

Ltac ar_entry B BR AB :=
  lazymatch type of B with
  | @semax_body _ _ ?cs1 ?f ?spec =>
    apply Forall_cons;
    [ eapply (entry_moved _ _ cs1 _ _ _ _ (fst spec) (snd spec) f B);
      [ reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
      | find_ids_V | vm_compute; reflexivity | vm_compute; reflexivity | ar_ctx_sub BR AB ]
    | ]
  end.

(* inflate_table's context lists inftrees' inflate_fixed_spec (precondition False): the entry by
   NDsubsume_subsume *)
Ltac ar_entry_table B :=
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

