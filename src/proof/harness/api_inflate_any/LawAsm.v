(* Law api_inflate_any: the assembly of harness_safe of the program from the shared bodies (inflate.c through
   SpecWLib.specw_lib_stmt and LibStmt5's inflate_lib5_stmt; zutil, libc, adler32, crc32, inftrees; the helpers
   of laws_common.h and laws_session.h), the main (Main.v), the theory (inflate_pieces' Progress.v with
   StepW.stepf2_mwf3W) and the globals (Globals.v); the recipe and tactics of inflate_pieces/LawAsm.v
   (api_untouched_output's assembly, with counted's body), its G_inflate and tactics. *)
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
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.laws_session.Spec.
Require Import Zlib.proof.harness.inflate_pieces.Facts.
Require Import Zlib.proof.harness.inflate_pieces.Progress.
Require Import Zlib.proof.harness.inflate_pieces.LawAsm.
Require Zlib.proof.inflate.StepW.
Require Import Zlib.proof.harness.api_inflate_any.LawCS.
Require Import Zlib.proof.harness.api_inflate_any.Globals.
Require Import Zlib.proof.harness.api_inflate_any.Main.
Require Zlib.contracts.api_inflate_any.
Require Zlib.harness.api_inflate_any.code.
Module LS := Zlib.proof.harness.laws_session.Spec.

Definition G_aia : funspecs :=
  [(Zlib.harness.api_inflate_any.code._main, QPmain_spec_ext' Aia.p tt main_post_TT);
   upto_spec; clip_spec; any_bytes_spec; copy_of_spec; bytes_eq_spec; offer_spec; new_stream_spec;
   LS.inflate_window_ok_spec; LS.position_of_spec; LS.accounted_spec; LS.counted_spec] ++
  G_inflate ++
  [(_quickproof_malloc, @malloc_spec' Aia.CS); (_quickproof_free, @free_spec' Aia.CS);
   nondet_size_spec; @nondet_bytes_spec Aia.CS; nondet_u8_spec; nondet_u32_spec; gp_assert_spec; gp_assume_spec].

Lemma aia_core : specw_lib_stmt -> laws_common_ok -> laws_session_ok ->
  harness_safe Zlib.contracts.api_inflate_any.whole_prog.
Proof.
  intros [ZL BR] (B_upto & B_clip & B_any & B_copy & B_eq & B_offer & B_new)
    (_ & S_window & S_pos & _ & S_acc & S_cnt).
  destruct (pieces_theory4 Zlib.proof.inflate.StepW.stepf2_mwf3W) as (P & PF & PG).
  pose proof (body_aia P PF PG) as B_main.
  harness_safe_by_specs Aia.CS G_aia main_post_TT.
  - reflexivity.
  - pc_entry (semax_body_main_core _ _ Aia.p _ _ R_aia aia_globals B_main eq_refl) BR.
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
    pc_entry S_cnt BR.
    pc_lib_entries ZL BR.
    entry_external (@external_ok_malloc Aia.CS).
    entry_external (@external_ok_free Aia.CS).
    entry_external (@external_ok_size Aia.CS).
    entry_external (@external_ok_bytes Aia.CS).
    entry_external (@external_ok_u8 Aia.CS).
    entry_external (@external_ok_u32 Aia.CS).
    entry_external (@external_ok_assert Aia.CS).
    entry_external (@external_ok_assume Aia.CS).
    apply Forall_nil.
Qed.
