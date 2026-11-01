(* The law api_dict_id, its assembly (DWAsmG.v): the entries of main (its body against main_core_spec, moved
   to harness_safe's main specification with the globals DWCS.dw_globals), of the laws_common.h helpers and
   of trees.c and the first piece of deflate.c, by clip_streams/Asm.v's entry tactics (main's by DWAsmKit's). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.EnvBodies.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.deflate.Obligations9.
Require Zlib.proof.inflate_api.SpecWLib.
Require Import Zlib.proof.harness.dictionary_w.DWCS.
Require Import Zlib.proof.harness.dictionary_w.DWAsmG.
Require Import Zlib.proof.harness.clip_streams.CS.
Require Import Zlib.proof.harness.clip_streams.Asm.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.MainCoreCfg.
Require Zlib.proof.deflate.GlobalsFixed.
Require Import Zlib.proof.harness.dictionary_w.DWMainDefs.
Require Zlib.harness.api_dict_id.code.
Require Import Zlib.proof.harness.dictionary_w.DWAsmKit.
#[local] Existing Instance Zlib.proof.harness.clip_streams.CS.CS.

Lemma dai_entries_main : laws_common_ok -> SWL.specw_lib_stmt ->
  semax_body (QPvarspecs p_dai) Gmain_dai Zlib.harness.api_dict_id.code.f_main
    (Zlib.harness.api_dict_id.code._main, main_core_spec R_dai) ->
  entries_dai G_dai_main.
Proof.
  intros (B_upto & B_clip & B_any & B_copy & _ & B_offer & B_new) [_ BR] BM.
  assert (BM' : semax_body (QPvarspecs p_dai) Gmain_dai Zlib.harness.api_dict_id.code.f_main
                  (Zlib.harness.api_dict_id.code._main, QPmain_spec_ext' p_dai tt main_post_TT)).
  { eapply (semax_body_main_core_cfg _ _ p_dai Zlib.proof.deflate.GlobalsFixed.cfg_funs _ _ R_dai).
    - exact (proj2 dw_globals).
    - exact BM.
    - vm_compute; reflexivity. }
  unfold entries_dai, G_dai_main.
  dw_entry BM' BR.
  clip_entry B_upto BR. clip_entry B_clip BR. clip_entry B_any BR. clip_entry B_copy BR.
  clip_entry B_offer BR. clip_entry B_new BR.
  apply Forall_nil.
Qed.

Lemma dai_entries_trees : SWL.specw_lib_stmt -> entries_dai (G_trees ++ G_defl1).
Proof.
  intros [_ BR]. pose proof clip_trees_bodies as TB. pose proof clip_deflate_bodies9 as DB.
  unfold entries_dai, G_trees, G_defl1; cbn [app].
  clip_trees_entries BR TB.
  clip_deflate_entries1 BR DB.
  apply Forall_nil.
Qed.
