(* Law rt_partial: the assembly of its program from the shared specifications, as Asm.v does for rj_truncated and
   rj_bad_checksum (the same library specifications G_lib, environment G_env and tactics), with main against
   main_core_spec R_rp in the context RPDefs.Gmain_rpc: since round 3 main calls copy_of, whose body comes from
   laws_common_ok. *)
Require Import QuickProof.Contract.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.clip_streams.CS Zlib.proof.harness.clip_streams.DFacts
               Zlib.proof.harness.clip_streams.IFacts Zlib.proof.harness.clip_streams.RPDefs.
Require Zlib.proof.inflate_api.SpecWLib.

Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib Zlib.proof.deflate.MainCoreCfg.
Require Import Zlib.proof.deflate.DSpec Zlib.proof.deflate.DSpec9 Zlib.proof.deflate.Obligations9.
Require Zlib.proof.deflate.GlobalsFixed.
Require Import Zlib.proof.harness.clip_streams.Globals Zlib.proof.harness.clip_streams.GlobalsOk.
Require Import Zlib.proof.harness.clip_streams.Asm.
Require Zlib.harness.rt_partial.code.
#[local] Existing Instance Zlib.proof.harness.clip_streams.CS.CS.

Module SWL := Zlib.proof.inflate_api.SpecWLib.

Definition G_rpc : funspecs :=
  [(Zlib.harness.rt_partial.code._main, QPmain_spec_ext' p_rp tt main_post_TT);
   upto_spec; clip_spec; any_bytes_spec; copy_of_spec; bytes_eq_spec; offer_spec; new_stream_spec]
  ++ G_lib ++ G_env.

Lemma clip_asm_rpc : laws_common_ok -> SWL.specw_lib_stmt ->
  semax_body (QPvarspecs p_rp) Gmain_rpc Zlib.harness.rt_partial.code.f_main
    (Zlib.harness.rt_partial.code._main, main_core_spec R_rp) ->
  harness_safe p_rp.
Proof.
  intros (B_upto & B_clip & B_any & B_copy & B_eq & B_offer & B_new) [ZL BR] BM.
  pose proof clip_trees_bodies as TB. pose proof clip_deflate_bodies9 as DB.
  assert (BM' : semax_body (QPvarspecs p_rp) Gmain_rpc Zlib.harness.rt_partial.code.f_main
                  (Zlib.harness.rt_partial.code._main, QPmain_spec_ext' p_rp tt main_post_TT)).
  { eapply (semax_body_main_core_cfg _ _ p_rp Zlib.proof.deflate.GlobalsFixed.cfg_funs _ _ R_rp).
    - exact (proj1 clip_globals).
    - exact BM.
    - vm_compute; reflexivity. }
  harness_safe_by_specs CS G_rpc main_post_TT.
  - reflexivity.
  - clip_entry BM' BR.
    clip_entry B_upto BR. clip_entry B_clip BR. clip_entry B_any BR. clip_entry B_copy BR. clip_entry B_eq BR.
    clip_entry B_offer BR. clip_entry B_new BR.
    clip_trees_entries BR TB.
    clip_deflate_entries1 BR DB.
    clip_deflate_entries2 BR DB.
    clip_inflate_entries BR ZL.
    clip_env_entries.
    apply Forall_nil.
Qed.
