(* Law rj_inflate_params: the assembly of harness_safe from the shared bodies (inflateInit2_ and the reset functions
   it calls: the inflate area's LibProof5.inflate_lib5_proof; zutil's allocator and memset; laws_common.h's
   new_stream and offer, from the hypothesis laws_common_ok), main (RIPMain.body_main) and the globals
   (RIPGlobals.globals_ok).  Every other function of the program gets a vacuous specification (it is not reached). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.LibStmt5.
Require Zlib.proof.inflate_api.LibProof5.
Require Zlib.proof.zutil.Spec Zlib.proof.zutil.Libc.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rj_inflate_params.RIPLawCS Zlib.proof.harness.rj_inflate_params.RIPGlobals
               Zlib.proof.harness.rj_inflate_params.RIPMain.
Require Import Zlib.harness.rj_inflate_params.code.

Definition G : funspecs :=
  [(_main, QPmain_spec_ext' p tt main_post_TT);
   inflateInit2__spec; inflateReset2_spec; inflateReset_spec; inflateResetKeep_spec; inflateStateCheck_spec;
   zcalloc_i; zcfree_i; memset_i; new_stream_spec; offer_spec;
   (_quickproof_malloc, malloc_spec'); (_quickproof_free, free_spec');
   nondet_u32_spec; gp_assert_spec].

Lemma rip_law : laws_common_ok -> harness_safe p.
Proof.
  intros (_ & _ & _ & _ & _ & B_offer & B_new_stream).
  destruct Zlib.proof.inflate_api.LibProof5.inflate_lib5_proof
    as (Hinit & Hreset & _ & _ & _ & _ & _ & _ & _ & Hcheck).
  destruct Hreset as [_ Hreset].
  destruct (Hinit NullExtension.Espec) as [B_init2 _].
  destruct (Hreset NullExtension.Espec) as (B_resetkeep & B_reset & B_reset2 & _).
  pose proof (Hcheck NullExtension.Espec) as B_check.
  harness_safe_by_specs CS G main_post_TT.
  - reflexivity.
  - entry_shared (semax_body_main_core _ _ p _ _ R globals_ok body_main eq_refl).
    entry_shared B_init2.
    entry_shared B_reset2.
    entry_shared B_reset.
    entry_shared B_resetkeep.
    entry_shared B_check.
    entry_shared (@Zlib.proof.zutil.Spec.body_zcalloc Zlib.units.Inflate.CS).
    entry_shared (@Zlib.proof.zutil.Spec.body_zcfree Zlib.units.Inflate.CS).
    entry_shared (@Zlib.proof.zutil.Libc.body_memset Zlib.units.Inflate.CS).
    entry_shared B_new_stream.
    entry_shared B_offer.
    entry_external (@external_ok_malloc CS).
    entry_external (@external_ok_free CS).
    entry_external (@external_ok_u32 CS).
    entry_external (@external_ok_assert CS).
    apply Forall_nil.
Qed.
