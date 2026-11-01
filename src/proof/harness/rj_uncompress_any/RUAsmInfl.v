(* Law rj_uncompress_any: the entries of RUAsmKit.G_infl and RUAsmKit.G_env, as rt_roundtrip's
   (rt_roundtrip/WAsmInfl.v): inflate.c's inflateInit_, inflateInit2_, the resets, inflateEnd and inflate_fixed
   from their parts of LibStmt5.inflate_lib5_stmt (WAsmInfl.infl5_bodies_stmt), inflate() from
   SpecWSelf.body_inflate_ws_stmt, inflateStateCheck, inflate_fast and updatewindow from the allocator-generic
   port at zlib's default allocator (SpecWLib.specw_lib_stmt); inftrees.c, adler32.c, crc32.c, zutil.c, libc.c
   from their proved bodies; the environment from QuickProof.EnvBodies. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.EnvBodies.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.inflate_api.LibStmt5.
Require Zlib.proof.inflate_api.SpecWLib.
Require Zlib.proof.inflate_api.SpecWSelf.
Require Zlib.proof.adler32.Body_adler32.
Require Zlib.proof.adler32.Body_adler32_z.
Require Zlib.proof.crc32.Body_crc32.
Require Zlib.proof.crc32.Body_crc32_z.
Require Zlib.proof.zutil.Spec.
Require Zlib.proof.zutil.Libc.
Require Zlib.proof.roundtrip.RTRSLaw.
Require Zlib.proof.harness.clip_streams.Asm.
Require Zlib.proof.harness.rt_roundtrip.WAsmKit.
Require Zlib.proof.harness.rt_roundtrip.WAsmInfl.
Require Import Zlib.proof.harness.rj_uncompress_any.RUCS.
Require Import Zlib.proof.harness.rj_uncompress_any.RUAsmKit.

Local Notation CSU := Zlib.proof.harness.rj_uncompress_any.RUCS.CS.
#[local] Existing Instance CSU.

Lemma ru_entries_infl :
  Zlib.proof.harness.rt_roundtrip.WAsmInfl.infl5_bodies_stmt -> Zlib.proof.inflate_api.SpecWLib.specw_lib_stmt ->
  Zlib.proof.inflate_api.SpecWSelf.body_inflate_ws_stmt ->
  ru_entries G_infl.
Proof.
  intros LI [ZL BR] BIS.
  destruct LI as (Hinit & Hreset & Hfixed).
  destruct Hreset as [_ Hreset].
  destruct (Hinit NullExtension.Espec) as [B_init2 B_init].
  destruct (Hreset NullExtension.Espec) as (B_resetkeep & B_reset & B_reset2 & B_end).
  pose proof (Hfixed NullExtension.Espec) as B_fixed.
  pose proof (BIS NullExtension.Espec) as B_inflate.
  destruct (ZL NullExtension.Espec) as (_ & U_fast & U_upd & U_check & _).
  pose proof (Zlib.proof.roundtrip.RTRSLaw.body_inflate_table NullExtension.Espec) as B_table.
  unfold ru_entries, G_infl.
  Zlib.proof.harness.rt_roundtrip.WAsmKit.w_entry B_init BR.
  Zlib.proof.harness.rt_roundtrip.WAsmKit.w_entry B_init2 BR.
  Zlib.proof.harness.rt_roundtrip.WAsmKit.w_entry B_reset2 BR.
  Zlib.proof.harness.rt_roundtrip.WAsmKit.w_entry B_reset BR.
  Zlib.proof.harness.rt_roundtrip.WAsmKit.w_entry B_resetkeep BR.
  Zlib.proof.harness.rt_roundtrip.WAsmKit.w_entry B_end BR.
  Zlib.proof.harness.rt_roundtrip.WAsmKit.w_entry U_check BR.
  Zlib.proof.harness.rt_roundtrip.WAsmKit.w_entry B_inflate BR.
  Zlib.proof.harness.rt_roundtrip.WAsmKit.w_entry U_fast BR.
  Zlib.proof.harness.rt_roundtrip.WAsmKit.w_entry U_upd BR.
  Zlib.proof.harness.rt_roundtrip.WAsmKit.w_entry B_fixed BR.
  Zlib.proof.harness.clip_streams.Asm.clip_entry_table B_table.
  Zlib.proof.harness.rt_roundtrip.WAsmKit.w_entry Zlib.proof.adler32.Body_adler32.body_adler32 BR.
  Zlib.proof.harness.rt_roundtrip.WAsmKit.w_entry Zlib.proof.adler32.Body_adler32_z.body_adler32_z BR.
  Zlib.proof.harness.rt_roundtrip.WAsmKit.w_entry Zlib.proof.crc32.Body_crc32.body_crc32 BR.
  Zlib.proof.harness.rt_roundtrip.WAsmKit.w_entry Zlib.proof.crc32.Body_crc32_z.body_crc32_z BR.
  Zlib.proof.harness.rt_roundtrip.WAsmKit.w_entry (@Zlib.proof.zutil.Spec.body_zcalloc CSU) BR.
  Zlib.proof.harness.rt_roundtrip.WAsmKit.w_entry (@Zlib.proof.zutil.Spec.body_zcfree CSU) BR.
  Zlib.proof.harness.rt_roundtrip.WAsmKit.w_entry (@Zlib.proof.zutil.Libc.body_memcpy CSU) BR.
  Zlib.proof.harness.rt_roundtrip.WAsmKit.w_entry (@Zlib.proof.zutil.Libc.body_memset CSU) BR.
  apply Forall_nil.
Qed.

Lemma ru_entries_env : ru_entries G_env.
Proof.
  unfold ru_entries, G_env.
  entry_external (@external_ok_malloc CSU).
  entry_external (@external_ok_free CSU).
  entry_external (@external_ok_size CSU).
  entry_external (@external_ok_bytes CSU).
  entry_external (@external_ok_assert CSU).
  apply Forall_nil.
Qed.
