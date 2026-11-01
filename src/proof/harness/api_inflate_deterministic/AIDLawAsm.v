(* Law api_inflate_deterministic: the assembly of harness_safe from the shared bodies (inflate.c through
   SpecWLib.specw_lib_stmt and the bodies of inflateInit2_, inflateReset2 and inflate_fixed; zutil, libc,
   adler32, crc32, inftrees; the helpers of laws_common.h; laws_session.h's inflate_window_ok), main (any proof of AIDMainDefs.aid_main_stmt), the
   globals and the theory (AIDTheory.aid_theory). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import Zlib.proof.inflate_api.SpecWLib.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.proof.harness.laws_session.Spec.
Require Import Zlib.proof.harness.api_inflate_deterministic.AIDMainDefs.
Require Zlib.contracts.api_inflate_deterministic.
Require Import QuickProof.Env.
Require Import QuickProof.EnvBodies.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Zlib.proof.inflate_api.Body5_init.
Require Zlib.proof.inflate_api.Body5_reset.
Require Zlib.proof.inflate.BodySmall.
Require Zlib.proof.adler32.Body_adler32.
Require Zlib.proof.adler32.Body_adler32_z.
Require Zlib.proof.crc32.Body_crc32.
Require Zlib.proof.crc32.Body_crc32_z.
Require Zlib.proof.zutil.Spec.
Require Zlib.proof.zutil.Libc.
Require Zlib.proof.harness.api_reset.ARLawG.
Require Import Zlib.proof.harness.api_inflate_deterministic.AIDLawG.
Require Import Zlib.proof.harness.api_inflate_deterministic.AIDLawMain.

Lemma aid_core : aid_main_stmt -> specw_lib_stmt -> laws_common_ok ->
  Zlib.proof.harness.laws_session.Spec.laws_session_ok ->
  harness_safe Zlib.contracts.api_inflate_deterministic.whole_prog.
Proof.
  intros M [ZL BR] (B_upto & B_clip & B_any & B_copy & B_eq & B_offer & B_new) (_ & B_window & _).
  (* the bodies of inflateInit2_, inflateReset2 and inflate_fixed (Spec5's specifications) *)
  destruct (Zlib.proof.inflate_api.Body5_init.api5_init NullExtension.Espec) as [B_init2 _].
  destruct (proj2 Zlib.proof.inflate_api.Body5_reset.api5_reset NullExtension.Espec) as (_ & _ & B_reset2 & _).
  pose proof (@Zlib.proof.inflate.BodySmall.body_inflate_fixed NullExtension.Espec) as B_fixed.
  destruct (ZL NullExtension.Espec) as (U_inflate & U_fast & U_upd & U_check & _ & _ & U_resetkeep & U_reset & _).
  pose proof (Zlib.proof.harness.api_reset.ARLawG.ar_body_inflate_table NullExtension.Espec) as B_table.
  harness_safe_by_specs CS G main_post_TT.
  - reflexivity.
  - apply Forall_cons; [exact (aid_main_entry M BR) |].
    aid_entry B_upto BR.
    aid_entry B_clip BR.
    aid_entry B_any BR.
    aid_entry B_copy BR.
    aid_entry B_eq BR.
    aid_entry B_offer BR.
    aid_entry B_new BR.
    aid_entry B_window BR.
    aid_entry B_init2 BR.
    aid_entry B_reset2 BR.
    aid_entry U_reset BR.
    aid_entry U_resetkeep BR.
    aid_entry U_check BR.
    aid_entry U_inflate BR.
    aid_entry U_fast BR.
    aid_entry U_upd BR.
    aid_entry B_fixed BR.
    Zlib.proof.harness.api_reset.ARLawG.ar_entry_table B_table.
    aid_entry Zlib.proof.adler32.Body_adler32.body_adler32 BR.
    aid_entry Zlib.proof.adler32.Body_adler32_z.body_adler32_z BR.
    aid_entry Zlib.proof.crc32.Body_crc32.body_crc32 BR.
    aid_entry Zlib.proof.crc32.Body_crc32_z.body_crc32_z BR.
    aid_entry (@Zlib.proof.zutil.Spec.body_zcalloc Zlib.units.Inflate.CS) BR.
    aid_entry (@Zlib.proof.zutil.Spec.body_zcfree Zlib.units.Inflate.CS) BR.
    aid_entry (@Zlib.proof.zutil.Libc.body_memcpy Zlib.units.Inflate.CS) BR.
    aid_entry (@Zlib.proof.zutil.Libc.body_memset Zlib.units.Inflate.CS) BR.
    entry_external (@external_ok_malloc CS).
    entry_external (@external_ok_free CS).
    entry_external (@external_ok_size CS).
    entry_external (@external_ok_bytes CS).
    entry_external (@external_ok_u8 CS).
    entry_external (@external_ok_u32 CS).
    entry_external (@external_ok_assert CS).
    entry_external (@external_ok_assume CS).
    apply Forall_nil.
Qed.
