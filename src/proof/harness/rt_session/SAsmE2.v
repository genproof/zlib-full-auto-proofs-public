(* Law rt_session: the entries of inflate.c, inffast.c, inftrees.c, adler32.c, crc32.c, zutil.c and libc.c in
   the assembly's context (SAsmG.G_infl).  inflateInit2_ and the reset functions: Spec5's bodies (taken one by
   one); inflateStateCheck and inflateSetDictionary: the port's bodies at zlib's allocator (SpecWLibProof);
   inflate, inflate_fast and updatewindow: the intersections of SAsmI; inflateGetHeader: RTH8GetHdr's body. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Assembly.
Require Zlib.proof.inflate_api.SpecWLib Zlib.proof.inflate_api.SpecWLibProof.
Require Zlib.proof.inflate_api.Body5_init.
Require Zlib.proof.inflate_api.Body5_reset.
Require Zlib.proof.inflate.BodySmall.
Require Zlib.proof.roundtrip.RTH8GetHdr.
Require Zlib.proof.roundtrip.RTRSLaw.
Require Zlib.proof.adler32.Body_adler32.
Require Zlib.proof.adler32.Body_adler32_z.
Require Zlib.proof.crc32.Body_crc32.
Require Zlib.proof.crc32.Body_crc32_z.
Require Zlib.proof.zutil.Spec.
Require Zlib.proof.zutil.Libc.
Require Import Zlib.proof.harness.rt_session.SCS.
Require Import Zlib.proof.harness.rt_session.SAsmI.
Require Import Zlib.proof.harness.rt_session.SAsmG.
#[local] Existing Instance Zlib.proof.harness.rt_session.SCS.CS.

Lemma ses_entries_infl : entries G_infl.
Proof.
  pose proof (@Zlib.proof.inflate_api.Body5_init.body_inflateInit2_ NullExtension.Espec) as B_init2.
  pose proof (@Zlib.proof.inflate_api.Body5_reset.body_inflateResetKeep NullExtension.Espec) as B_resetkeep.
  pose proof (@Zlib.proof.inflate_api.Body5_reset.body_inflateReset NullExtension.Espec) as B_reset.
  pose proof (@Zlib.proof.inflate_api.Body5_reset.body_inflateReset2 NullExtension.Espec) as B_reset2.
  destruct Zlib.proof.inflate_api.SpecWLibProof.specw_lib as [ZL _].
  destruct (ZL NullExtension.Espec) as (_ & _ & _ & U_check & U_setdict & _).
  pose proof (@body_inflate_ses NullExtension.Espec) as B_inflate.
  pose proof (@body_fast_ses NullExtension.Espec) as B_fast.
  pose proof (@body_upd_ses NullExtension.Espec) as B_upd.
  pose proof (Zlib.proof.roundtrip.RTH8GetHdr.rth8_gethdr NullExtension.Espec) as B_gethdr.
  pose proof (@Zlib.proof.inflate.BodySmall.body_inflate_fixed NullExtension.Espec) as B_fixed.
  pose proof (Zlib.proof.roundtrip.RTRSLaw.body_inflate_table NullExtension.Espec) as B_table.
  unfold entries, G_infl.
  ses_entry B_init2. ses_entry B_reset2. ses_entry B_reset. ses_entry B_resetkeep.
  ses_entry U_check. ses_entry B_inflate. ses_entry B_fast. ses_entry B_upd. ses_entry U_setdict.
  ses_entry B_gethdr. ses_entry B_fixed.
  ses_entry_table B_table.
  ses_entry Zlib.proof.adler32.Body_adler32.body_adler32.
  ses_entry Zlib.proof.adler32.Body_adler32_z.body_adler32_z.
  ses_entry Zlib.proof.crc32.Body_crc32.body_crc32.
  ses_entry Zlib.proof.crc32.Body_crc32_z.body_crc32_z.
  ses_entry (@Zlib.proof.zutil.Spec.body_zcalloc CS).
  ses_entry (@Zlib.proof.zutil.Spec.body_zcfree CS).
  ses_entry (@Zlib.proof.zutil.Libc.body_memcpy CS).
  ses_entry (@Zlib.proof.zutil.Libc.body_memset CS).
  apply Forall_nil.
Qed.
