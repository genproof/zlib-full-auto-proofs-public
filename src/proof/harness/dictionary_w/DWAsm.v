(* The laws rt_dictionary and api_dict_id: the assembly of each program from the shared specifications
   (QuickProof.Assembly.harness_safe_by_specs with clip_streams' CS.CS), as clip_streams/Asm.v: main against
   main_core_spec R_x (DWMainDefs.v, for the invariants the theory gives), the laws_common.h helpers
   (laws_common_ok), deflate.c and trees.c (their proved bodies), inflate.c (SpecWLib.specw_lib_stmt: the
   port's bodies, inflateSetDictionary's among them, and the bridge to SpecW's specifications; Spec5's
   inflateInit2_ and reset functions), adler32 / crc32 / zutil, the environment; the globals (DWCS.dw_globals).
   The contexts are in DWAsmG.v; the entries of each program are proved in four pieces (DWAsmDrt1-4.v,
   DWAsmDai1-4.v, with DWAsmKit.v's entry tactic for the bodies that call zcalloc / zcfree), each file well
   under the compile-time budget. *)
Require Import QuickProof.Contract.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.dictionary_w.DWCS.
Require Import Zlib.proof.harness.dictionary_w.DWFacts.
Require Import Zlib.proof.harness.dictionary_w.DWIFacts.
Require Import Zlib.proof.harness.dictionary_w.DWMainDefs.
Require Zlib.proof.inflate_api.SpecWLib.

Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.harness.dictionary_w.DWIFacts.
Require Import Zlib.proof.harness.dictionary_w.DWMainDefs.
Require Import Zlib.proof.harness.clip_streams.CS.
Require Import Zlib.proof.harness.clip_streams.Asm.
Require Import Zlib.proof.harness.dictionary_w.DWAsmG.
Require Import Zlib.proof.harness.dictionary_w.DWAsmDrt1.
Require Import Zlib.proof.harness.dictionary_w.DWAsmDrt2.
Require Import Zlib.proof.harness.dictionary_w.DWAsmDrt3.
Require Import Zlib.proof.harness.dictionary_w.DWAsmDrt4.
Require Import Zlib.proof.harness.dictionary_w.DWAsmDai1.
Require Import Zlib.proof.harness.dictionary_w.DWAsmDai2.
Require Import Zlib.proof.harness.dictionary_w.DWAsmDai3.
Require Import Zlib.proof.harness.dictionary_w.DWAsmDai4.
Require Zlib.harness.rt_dictionary.code.
Require Zlib.harness.api_dict_id.code.
#[local] Existing Instance Zlib.proof.harness.clip_streams.CS.CS.

(* Each program: harness_safe_by_specs with its context (DWAsmG.v), whose entries are the pieces proved in
   DWAsmDrt1-4.v / DWAsmDai1-4.v. *)
Lemma dw_asm_drt : laws_common_ok -> Zlib.proof.inflate_api.SpecWLib.specw_lib_stmt ->
  semax_body (QPvarspecs p_drt) Gmain_drt Zlib.harness.rt_dictionary.code.f_main
    (Zlib.harness.rt_dictionary.code._main, main_core_spec R_drt) ->
  harness_safe p_drt.
Proof.
  intros L SW BM.
  pose proof (drt_entries_main L SW BM) as E1. pose proof (drt_entries_trees SW) as E2.
  pose proof (drt_entries_defl2 SW) as E3. pose proof (drt_entries_defl3 SW) as E4.
  pose proof (drt_entries_infl SW) as E5.
  harness_safe_by_specs CS G_drt main_post_TT.
  - reflexivity.
  - match goal with |- Forall ?P _ =>
      change (Forall P (G_drt_main ++ (G_trees ++ G_defl1) ++ G_defl2 ++ G_defl3 ++
                        (G_infl ++ G_setdict ++ G_env))) end.
    apply Forall_app; split; [exact E1 | ]. apply Forall_app; split; [exact E2 | ].
    apply Forall_app; split; [exact E3 | ]. apply Forall_app; split; [exact E4 | exact E5].
Qed.

Lemma dw_asm_dai : laws_common_ok -> Zlib.proof.inflate_api.SpecWLib.specw_lib_stmt ->
  semax_body (QPvarspecs p_dai) Gmain_dai Zlib.harness.api_dict_id.code.f_main
    (Zlib.harness.api_dict_id.code._main, main_core_spec R_dai) ->
  harness_safe p_dai.
Proof.
  intros L SW BM.
  pose proof (dai_entries_main L SW BM) as E1. pose proof (dai_entries_trees SW) as E2.
  pose proof (dai_entries_defl2 SW) as E3. pose proof (dai_entries_defl3 SW) as E4.
  pose proof (dai_entries_infl SW) as E5.
  harness_safe_by_specs CS G_dai main_post_TT.
  - reflexivity.
  - match goal with |- Forall ?P _ =>
      change (Forall P (G_dai_main ++ (G_trees ++ G_defl1) ++ G_defl2 ++ G_defl3 ++ (G_infl ++ G_env))) end.
    apply Forall_app; split; [exact E1 | ]. apply Forall_app; split; [exact E2 | ].
    apply Forall_app; split; [exact E3 | ]. apply Forall_app; split; [exact E4 | exact E5].
Qed.

Lemma dict_asm : laws_common_ok -> Zlib.proof.inflate_api.SpecWLib.specw_lib_stmt ->
  main_drt_stmt -> main_dai_stmt -> dict_dfacts_stmt -> dict_ifacts_stmt ->
  harness_safe p_drt /\ harness_safe p_dai.
Proof.
  intros L SW MRT MAI [J0 [J1 [J DF]]] [Q [P IF]].
  exact (conj (dw_asm_drt L SW (MRT J0 J1 J Q P DF IF)) (dw_asm_dai L SW (MAI J0 J1 J Q P DF IF))).
Qed.
