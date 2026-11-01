(* Law rt_gzip_header on the round-2 harness: the entries of deflateEnd (DSpec), inflateInit2_, inflateReset2
   (Spec5) and updatewindow (Callees3), their bodies moved into the law's program and its specifications G of
   G2AsmKit.v.  A file of its own for the time they take; used by G2Asm.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.deflate.Obligations.
Require Zlib.proof.deflate.Body_api.
Require Zlib.proof.inflate.Callees3 Zlib.proof.inflate.BodyUw5.
Require Zlib.proof.inflate_api.Spec5 Zlib.proof.inflate_api.Body5_init Zlib.proof.inflate_api.Body5_reset.
Require Import Zlib.proof.harness.rt_gzip_header.CS.
Require Import Zlib.proof.harness.rt_gzip_header.G2AsmKit.
Require Import Zlib.harness.rt_gzip_header.code.
#[local] Existing Instance Zlib.proof.harness.rt_gzip_header.CS.CS.

Lemma rtg2_entries2 (fast g1 g2 g3 g4 g5 g6 g7 g8 : funspec) :
  Forall (entry_of_prog (@HonestEspec CS) CS p
            (G fast g1 g2 g3 g4 g5 g6 g7 g8 ++ vacuous_internals p (G fast g1 g2 g3 g4 g5 g6 g7 g8)))
    [deflateEnd_spec; Zlib.proof.inflate_api.Spec5.inflateInit2__spec;
     Zlib.proof.inflate_api.Spec5.inflateReset2_spec; Zlib.proof.inflate.Callees3.updatewindow_spec3].
Proof.
  destruct Zlib.proof.deflate.Body_api.deflate_api_bodies as (_ & _ & _ & _ & _ & _ & _ & _ & D22 & _).
  unfold ob_deflateEnd in D22.
  destruct (Zlib.proof.inflate_api.Body5_init.api5_init NullExtension.Espec) as [B_init2 _].
  destruct Zlib.proof.inflate_api.Body5_reset.api5_reset as [_ Hreset].
  destruct (Hreset NullExtension.Espec) as (_ & _ & B_reset2 & _).
  pose proof (@Zlib.proof.inflate.BodyUw5.body_updatewindow5 NullExtension.Espec) as B_upd.
  entry_fast D22. entry_fast B_init2. entry_fast B_reset2. entry_fast B_upd.
  apply Forall_nil.
Qed.
