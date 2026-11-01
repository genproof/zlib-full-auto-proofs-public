(* The law rt_dictionary, its assembly (DWAsmG.v): the entries of inflate.c (the port's bodies at zlib's
   default allocator and Spec5's inflateInit2_ and reset functions), inffast.c, inftrees.c, adler32.c,
   crc32.c, zutil.c / libc.c, of inflateSetDictionary (the port's body at zlib's default allocator, which the bridge
   of SpecWLib.specw_lib_stmt moves to main's SpecW.inflateSetDictionary_specW) and of the environment. *)
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
Require Import Zlib.proof.harness.dictionary_w.DWAsmKit.
#[local] Existing Instance Zlib.proof.harness.clip_streams.CS.CS.

Lemma drt_entries_infl : SWL.specw_lib_stmt -> entries_drt (G_infl ++ G_setdict ++ G_env).
Proof.
  intros [ZL BR].
  unfold entries_drt, G_infl, G_setdict, G_env; cbn [app].
  dw_inflate_entries BR ZL.
  destruct (ZL NullExtension.Espec) as (_ & _ & _ & _ & U_setdict & _).
  dw_entry U_setdict BR.
  clip_env_entries.
  apply Forall_nil.
Qed.
