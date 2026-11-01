(* Law api_reset: the assembly of harness_safe from the shared bodies (inflate.c through SpecWLib.specw_lib_stmt
   and the bodies of inflateInit2_, inflateReset2 and inflate_fixed; zutil, libc, adler32, crc32, inftrees; the helpers of laws_common.h), main
   (ARMain.ar_main), the globals (ARGlobals.ar_globals) and the theory (ARTheory.ar_theory).  As inflate_pieces'
   LawAsm.v, with inflateReset and inflateResetKeep at their allocator-generic specifications of the za port
   (USpec.v) at zlib's default allocator: main's view of inflateReset (ARSpec.inflateReset_specA) and Spec5's
   inflateReset_spec, which inflateReset2's body calls, are moved to it by ARSpec.ar_bridge_stmt. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.LibStmt5.
Require Zlib.proof.inflate_api.Body5_init.
Require Zlib.proof.inflate_api.Body5_reset.
Require Zlib.proof.inflate.BodySmall.
Require Import Zlib.proof.inflate_api.SpecWLib.
Require Zlib.proof.adler32.Body_adler32 Zlib.proof.adler32.Body_adler32_z.
Require Zlib.proof.crc32.Body_crc32 Zlib.proof.crc32.Body_crc32_z.
Require Zlib.proof.zutil.Spec Zlib.proof.zutil.Libc.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.api_reset.ARMainDefs.
Require Import Zlib.proof.harness.api_reset.ARLawG.
Require Import Zlib.proof.harness.api_reset.ARLawMain.
Require Zlib.contracts.api_reset.

Lemma ar_core : specw_lib_stmt -> ar_bridge_stmt -> laws_common_ok ->
  harness_safe Zlib.contracts.api_reset.whole_prog.
Proof.
  intros [ZL BR] AB (B_upto & B_clip & B_any & B_copy & B_eq & B_offer & B_new).
  (* the bodies of inflateInit2_, inflateReset2 and inflate_fixed (Spec5's specifications) *)
  destruct (Zlib.proof.inflate_api.Body5_init.api5_init NullExtension.Espec) as [B_init2 _].
  destruct (proj2 Zlib.proof.inflate_api.Body5_reset.api5_reset NullExtension.Espec) as (_ & _ & B_reset2 & _).
  pose proof (@Zlib.proof.inflate.BodySmall.body_inflate_fixed NullExtension.Espec) as B_fixed.
  destruct (ZL NullExtension.Espec) as (U_inflate & U_fast & U_upd & U_check & _ & _ & U_resetkeep & U_reset & _).
  pose proof (ar_body_inflate_table NullExtension.Espec) as B_table.
  harness_safe_by_specs CS G main_post_TT.
  - reflexivity.
  - apply Forall_cons; [exact (ar_main_entry BR AB) |].
    ar_entry B_upto BR AB.
    ar_entry B_clip BR AB.
    ar_entry B_any BR AB.
    ar_entry B_copy BR AB.
    ar_entry B_eq BR AB.
    ar_entry B_offer BR AB.
    ar_entry B_new BR AB.
    ar_entry B_init2 BR AB.
    ar_entry B_reset2 BR AB.
    ar_entry U_reset BR AB.
    ar_entry U_resetkeep BR AB.
    ar_entry U_check BR AB.
    ar_entry U_inflate BR AB.
    ar_entry U_fast BR AB.
    ar_entry U_upd BR AB.
    ar_entry B_fixed BR AB.
    ar_entry_table B_table.
    ar_entry Zlib.proof.adler32.Body_adler32.body_adler32 BR AB.
    ar_entry Zlib.proof.adler32.Body_adler32_z.body_adler32_z BR AB.
    ar_entry Zlib.proof.crc32.Body_crc32.body_crc32 BR AB.
    ar_entry Zlib.proof.crc32.Body_crc32_z.body_crc32_z BR AB.
    ar_entry (@Zlib.proof.zutil.Spec.body_zcalloc Zlib.units.Inflate.CS) BR AB.
    ar_entry (@Zlib.proof.zutil.Spec.body_zcfree Zlib.units.Inflate.CS) BR AB.
    ar_entry (@Zlib.proof.zutil.Libc.body_memcpy Zlib.units.Inflate.CS) BR AB.
    ar_entry (@Zlib.proof.zutil.Libc.body_memset Zlib.units.Inflate.CS) BR AB.
    entry_external (@external_ok_malloc CS).
    entry_external (@external_ok_free CS).
    entry_external (@external_ok_size CS).
    entry_external (@external_ok_bytes CS).
    entry_external (@external_ok_u8 CS).
    entry_external (@external_ok_u32 CS).
    entry_external (@external_ok_assert CS).
    apply Forall_nil.
Qed.
