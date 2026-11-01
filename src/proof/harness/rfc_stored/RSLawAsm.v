(* Law rfc_stored: the assembly of harness_safe from the shared bodies (inflate.c through
   SpecWLib.specw_lib_stmt and LibStmt5's inflate_lib5_proof; zutil, libc, adler32, crc32, inftrees; laws_common.h's
   helpers in laws_common_ok), main (RSMain.v) and the theory (RSTheory.v, from the decode theory's
   Decode7Step.decode7a_stmt), as rj_bad_header/RBHLawAsm.v.

   inflate.c's functions get the allocator-generic specifications of the port at zlib's default allocator
   (SpecWLib.zc_alloc) for inflate, inflate_fast, updatewindow and inflateStateCheck, and Spec5's for
   inflateInit2_ and the reset functions; main's inflate_specW and the reset functions' inflateStateCheck_spec
   are moved to them by the bridge (specw_bridge_stmt). *)
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
Require Zlib.proof.inftrees.spec.
Require Zlib.proof.harness.inflate_check.IKLawAsm.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.rfc1951.Decode7Step.
Require Import Zlib.proof.harness.rfc_stored.RSLawCS Zlib.proof.harness.rfc_stored.RSGlobals.
Require Import Zlib.proof.harness.rfc_stored.RSFacts Zlib.proof.harness.rfc_stored.RSTheory.
Require Import Zlib.proof.harness.rfc_stored.RSMain.
Require Import Zlib.harness.rfc_stored.code.

(* the specifications of the functions the law reaches *)
Definition G : funspecs :=
  [(_main, QPmain_spec_ext' p tt main_post_TT);
   upto_spec; clip_spec; any_bytes_spec; copy_of_spec; bytes_eq_spec; offer_spec; new_stream_spec;
   inflateInit2__spec; inflateReset2_spec; inflateReset_spec; inflateResetKeep_spec;
   @inflateStateCheck_uspec globals zc_alloc; @inflate_uspec globals zc_alloc;
   @inflate_fast_uspec globals zc_alloc; @updatewindow_uspec globals zc_alloc;
   inflate_fixed_spec; Zlib.proof.inftrees.spec.inflate_table_spec;
   Zlib.proof.adler32.Spec.adler32_spec; Zlib.proof.adler32.Spec.adler32_z_spec;
   Zlib.proof.crc32.Spec.crc32_spec; Zlib.proof.crc32.Spec.crc32_z_spec;
   zcalloc_i; zcfree_i; memcpy_i; memset_i;
   (_quickproof_malloc, malloc_spec'); (_quickproof_free, free_spec');
   nondet_size_spec; nondet_u32_spec; nondet_bytes_spec; gp_assert_spec; gp_assume_spec].

(* ctx_sub with, besides the environment's transports, the bridge's funspec_subs *)
Ltac rs_spec_sub BR :=
  first [ env_spec_sub
        | apply (proj1 BR) | apply (proj1 (proj2 BR)) | apply (proj2 (proj2 BR)) ].

Ltac rs_ctx_sub BR :=
  let i := fresh "i" in let phi := fresh "phi" in let E := fresh "E" in
  intros i phi E; simpl in E;
  repeat (if_tac in E; [ inv E; eexists; split; [ reflexivity | rs_spec_sub BR ] | ]);
  try discriminate.

Ltac rs_entry B BR :=
  lazymatch type of B with
  | @semax_body _ _ ?cs1 ?f ?spec =>
    apply Forall_cons;
    [ eapply (entry_moved _ _ cs1 _ _ _ _ (fst spec) (snd spec) f B);
      [ reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
      | find_ids_V | vm_compute; reflexivity | vm_compute; reflexivity | rs_ctx_sub BR ]
    | ]
  end.

Lemma rs_core : specw_lib_stmt -> decode7a_stmt -> laws_common_ok -> harness_safe p.
Proof.
  intros [ZL BR] D (B_upto & B_clip & B_any & B_copy & B_eq & B_offer & B_new).
  destruct (rs_theory D) as [P HP].
  pose proof (body_main P HP) as Hmain.
  destruct Zlib.proof.inflate_api.LibProof5.inflate_lib5_proof
    as (Hinit & Hreset & _ & _ & _ & _ & _ & _ & Hfixed & _).
  destruct Hreset as [_ Hreset].
  destruct (Hinit NullExtension.Espec) as [B_init2 _].
  destruct (Hreset NullExtension.Espec) as (B_resetkeep & B_reset & B_reset2 & _).
  pose proof (Hfixed NullExtension.Espec) as B_fixed.
  destruct (ZL NullExtension.Espec) as (U_inflate & U_fast & U_upd & U_check & _).
  pose proof (Zlib.proof.harness.inflate_check.IKLawAsm.body_inflate_table NullExtension.Espec) as B_table.
  harness_safe_by_specs CS G main_post_TT.
  - reflexivity.
  - rs_entry (semax_body_main_core _ _ p _ _ R globals_ok Hmain eq_refl) BR.
    rs_entry B_upto BR.
    rs_entry B_clip BR.
    Zlib.proof.harness.inflate_check.IKLawAsm.entry_shared' B_any.
    Zlib.proof.harness.inflate_check.IKLawAsm.entry_shared' B_copy.
    rs_entry B_eq BR.
    rs_entry B_offer BR.
    rs_entry B_new BR.
    rs_entry B_init2 BR.
    rs_entry B_reset2 BR.
    rs_entry B_reset BR.
    rs_entry B_resetkeep BR.
    rs_entry U_check BR.
    rs_entry U_inflate BR.
    rs_entry U_fast BR.
    rs_entry U_upd BR.
    rs_entry B_fixed BR.
    (* inflate_table's context has inftrees' PROP-False inflate_fixed_spec (never called): G's real one is a
       subspecification of it *)
    apply Forall_cons;
    [ eapply (entry_moved _ _ Zlib.units.Inftrees.CS _ _ _ _ _ _ _ B_table);
      [ reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
      | find_ids_V | vm_compute; reflexivity | vm_compute; reflexivity | ] | ].
    { intros i phi E; simpl in E.
      if_tac in E; [ inv E; eexists; split; [ reflexivity | apply funspec_sub_refl ] | ].
      if_tac in E; [ | discriminate ].
      inv E. eexists; split; [ reflexivity | ].
      apply NDsubsume_subsume; [ split; reflexivity | split; [ split; reflexivity | ] ];
        intros x [ge args]; simpl; unfold PROPx; simpl; normalize. }
    rs_entry Zlib.proof.adler32.Body_adler32.body_adler32 BR.
    rs_entry Zlib.proof.adler32.Body_adler32_z.body_adler32_z BR.
    rs_entry Zlib.proof.crc32.Body_crc32.body_crc32 BR.
    rs_entry Zlib.proof.crc32.Body_crc32_z.body_crc32_z BR.
    rs_entry (@Zlib.proof.zutil.Spec.body_zcalloc Zlib.units.Inflate.CS) BR.
    rs_entry (@Zlib.proof.zutil.Spec.body_zcfree Zlib.units.Inflate.CS) BR.
    rs_entry (@Zlib.proof.zutil.Libc.body_memcpy Zlib.units.Inflate.CS) BR.
    rs_entry (@Zlib.proof.zutil.Libc.body_memset Zlib.units.Inflate.CS) BR.
    entry_external (@external_ok_malloc CS).
    entry_external (@external_ok_free CS).
    entry_external (@external_ok_size CS).
    entry_external (@external_ok_u32 CS).
    entry_external (@external_ok_bytes CS).
    entry_external (@external_ok_assert CS).
    entry_external (@external_ok_assume CS).
    apply Forall_nil.
Qed.
