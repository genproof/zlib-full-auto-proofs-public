(* Law rt_gzip_header on the round-2 harness: the entry of deflateInit2_ (its body under deflate.c's compspecs,
   with DSpec9's specification, moved into the law's program and its specifications G of G2AsmKit.v).  A file of
   its own for the time it takes; used by G2Asm.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.deflate.Obligations9.
Require Zlib.proof.deflate.Body_api9.
Require Import Zlib.proof.harness.rt_gzip_header.CS.
Require Import Zlib.proof.harness.rt_gzip_header.G2AsmKit.
Require Import Zlib.harness.rt_gzip_header.code.
#[local] Existing Instance Zlib.proof.harness.rt_gzip_header.CS.CS.

Lemma rtg2_entry_init2 (fast g1 g2 g3 g4 g5 g6 g7 g8 : funspec) :
  entry_of_prog (@HonestEspec CS) CS p
    (G fast g1 g2 g3 g4 g5 g6 g7 g8 ++ vacuous_internals p (G fast g1 g2 g3 g4 g5 g6 g7 g8))
    deflateInit2__spec_v9.
Proof.
  destruct Zlib.proof.deflate.Body_api9.deflate_api_bodies9 as (_ & _ & D23).
  unfold ob_deflateInit2_9 in D23.
  apply (Forall_inv (l := [])).
  entry_fast D23. apply Forall_nil.
Qed.
