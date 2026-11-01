(* Law rt_roundtrip (data of any length): the entries of WAsmKit.G_infl and WAsmKit.G_env.  inflate.c:
   inflateInit_, inflateInit2_, the resets and inflateEnd, and inflate_fixed, from their parts of
   LibStmt5.inflate_lib5_stmt (against Spec5: [infl5_bodies_stmt], only the functions the law reaches),
   inflate() from SpecWSelf.body_inflate_ws_stmt, inflateStateCheck, inflate_fast and updatewindow from the
   allocator-generic port at zlib's default allocator (SpecWLib.specw_lib_stmt, whose bridge gives Spec5's
   inflateStateCheck_spec to the Spec5 bodies); inftrees.c, adler32.c, crc32.c, zutil.c, libc.c from their
   proved bodies; the environment from QuickProof.EnvBodies. *)
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
Require Import Zlib.proof.harness.rt_roundtrip.WCS.
Require Import Zlib.proof.harness.rt_roundtrip.WAsmKit.

Local Notation CSW := Zlib.proof.harness.rt_roundtrip.WCS.CS.
#[local] Existing Instance CSW.

(* the bodies of inflate.c against Spec5 that the law reaches: inflateInit_ / inflateInit2_, the resets and
   inflateEnd, inflate_fixed *)
Definition infl5_bodies_stmt : Prop :=
  api_init_stmt /\ api_reset_stmt /\
  (forall {Espec: OracleKind},
     @semax_body Zlib.proof.inftrees.spec.Vprog [] Zlib.units.Inflate.CS Zlib.inftrees.code.f_inflate_fixed
       Zlib.proof.inflate.Callees.inflate_fixed_spec).

Lemma w_entries_infl :
  infl5_bodies_stmt -> Zlib.proof.inflate_api.SpecWLib.specw_lib_stmt ->
  Zlib.proof.inflate_api.SpecWSelf.body_inflate_ws_stmt ->
  w_entries G_infl.
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
  unfold w_entries, G_infl.
  w_entry B_init BR. w_entry B_init2 BR. w_entry B_reset2 BR. w_entry B_reset BR. w_entry B_resetkeep BR.
  w_entry B_end BR.
  w_entry U_check BR. w_entry B_inflate BR. w_entry U_fast BR. w_entry U_upd BR. w_entry B_fixed BR.
  Zlib.proof.harness.clip_streams.Asm.clip_entry_table B_table.
  w_entry Zlib.proof.adler32.Body_adler32.body_adler32 BR.
  w_entry Zlib.proof.adler32.Body_adler32_z.body_adler32_z BR.
  w_entry Zlib.proof.crc32.Body_crc32.body_crc32 BR.
  w_entry Zlib.proof.crc32.Body_crc32_z.body_crc32_z BR.
  w_entry (@Zlib.proof.zutil.Spec.body_zcalloc CSW) BR.
  w_entry (@Zlib.proof.zutil.Spec.body_zcfree CSW) BR.
  w_entry (@Zlib.proof.zutil.Libc.body_memcpy CSW) BR.
  w_entry (@Zlib.proof.zutil.Libc.body_memset CSW) BR.
  apply Forall_nil.
Qed.

Lemma w_entries_env : w_entries G_env.
Proof.
  unfold w_entries, G_env.
  entry_external (@external_ok_malloc CSW).
  entry_external (@external_ok_free CSW).
  entry_external (@external_ok_size CSW).
  entry_external (@external_ok_bytes CSW).
  entry_external (@external_ok_assert CSW).
  apply Forall_nil.
Qed.
