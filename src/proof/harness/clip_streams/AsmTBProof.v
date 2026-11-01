(* Law rfc_trailing_bytes: the assembly of its program from the shared specifications, as Asm.v for the other
   three clip laws (the same G_lib and environment, with gp_assume as for rj_bad_checksum; main against
   main_core_spec R_tb), and laws_session.h's deflate_params_ok (its body proved once, laws_session/Spec.v's
   laws_session_ok).  AsmTB.v states the law's assembly lemma and takes its proof from here. *)
Require Import QuickProof.Contract.
Require Zlib.proof.harness.laws_common.Spec Zlib.proof.harness.clip_streams.CS
        Zlib.proof.harness.clip_streams.MainDefs Zlib.proof.harness.clip_streams.Globals
        Zlib.proof.inflate_api.SpecWLib Zlib.proof.harness.clip_streams.GlobalsOk
        Zlib.proof.harness.clip_streams.Asm.
Require Zlib.proof.harness.laws_session.Spec Zlib.proof.harness.clip_streams.TBDefs.
Import Zlib.proof.harness.laws_common.Spec Zlib.proof.harness.clip_streams.CS
       Zlib.proof.harness.clip_streams.MainDefs.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Import Zlib.proof.harness.clip_streams.Globals.
Require Zlib.harness.rfc_trailing_bytes.code.
Require Import Zlib.proof.deflate.MainCoreCfg.
Import Zlib.proof.harness.clip_streams.GlobalsOk Zlib.proof.harness.clip_streams.Asm.
#[local] Existing Instance Zlib.proof.harness.clip_streams.CS.CS.

(* The specifications of rfc_trailing_bytes's program: its main, the laws_common.h helpers it calls (the same
   as rj_truncated's), laws_session.h's deflate_params_ok, the library functions and the environment of Asm.v
   with gp_assume. *)
Definition G_tb : funspecs :=
  [(Zlib.harness.rfc_trailing_bytes.code._main, QPmain_spec_ext' p_tb tt main_post_TT);
   upto_spec; clip_spec; any_bytes_spec; offer_spec; new_stream_spec;
   Zlib.proof.harness.laws_session.Spec.deflate_params_ok_spec] ++ G_lib ++ G_env ++ [gp_assume_spec].

Lemma clip_asm_tb_proof : laws_common_ok -> Zlib.proof.harness.laws_session.Spec.laws_session_ok ->
  Zlib.proof.inflate_api.SpecWLib.specw_lib_stmt ->
  semax_body (QPvarspecs p_tb) Zlib.proof.harness.clip_streams.TBDefs.Gmain_tb4
    Zlib.harness.rfc_trailing_bytes.code.f_main
    (Zlib.harness.rfc_trailing_bytes.code._main, main_core_spec R_tb) ->
  harness_safe p_tb.
Proof.
  intros (B_upto & B_clip & B_any & _ & _ & B_offer & B_new) (B_dpo & _) [ZL BR] BM.
  pose proof clip_trees_bodies as TB. pose proof clip_deflate_bodies9 as DB.
  assert (BM' : semax_body (QPvarspecs p_tb) Zlib.proof.harness.clip_streams.TBDefs.Gmain_tb4
                  Zlib.harness.rfc_trailing_bytes.code.f_main
                  (Zlib.harness.rfc_trailing_bytes.code._main, QPmain_spec_ext' p_tb tt main_post_TT)).
  { eapply (semax_body_main_core_cfg _ _ p_tb Zlib.proof.deflate.GlobalsFixed.cfg_funs _ _ R_tb).
    - exact (proj2 (proj2 (proj2 clip_globals))).
    - exact BM.
    - vm_compute; reflexivity. }
  harness_safe_by_specs CS G_tb main_post_TT.
  - reflexivity.
  - clip_entry BM' BR.
    clip_entry B_upto BR. clip_entry B_clip BR. clip_entry B_any BR.
    clip_entry B_offer BR. clip_entry B_new BR. clip_entry B_dpo BR.
    clip_trees_entries BR TB.
    clip_deflate_entries1 BR DB.
    clip_deflate_entries2 BR DB.
    clip_inflate_entries BR ZL.
    clip_env_entries.
    entry_external (@external_ok_assume CS).
    apply Forall_nil.
Qed.
