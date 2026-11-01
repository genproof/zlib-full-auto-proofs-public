(* Law rfc_trailing_bytes, main: the deflate half of main's body (statements 0-20 of TBKit.v: the inputs,
   the gp_assume of the parameters, deflateInit2 and its checks, deflateBound_z and malloc, the deflate loop, compressed_len), ending at TBKit.tb_DH. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.harness.clip_streams.CS Zlib.proof.harness.clip_streams.Globals.
Require Import Zlib.proof.harness.clip_streams.DFacts Zlib.proof.harness.clip_streams.IFacts.
Require Import Zlib.proof.harness.clip_streams.TBFacts Zlib.proof.harness.clip_streams.MainDefs.
Require Import Zlib.proof.harness.clip_streams.TBKit.
Require Import Zlib.proof.harness.clip_streams.TBDKit.
Require Import Zlib.proof.harness.clip_streams.TBDSegIn.
Require Import Zlib.proof.harness.clip_streams.TBDSegInit.
Require Import Zlib.proof.harness.clip_streams.TBDSegBnd.
Require Import Zlib.proof.harness.clip_streams.TBDSegLoop.
Require Import Zlib.proof.harness.clip_streams.TBDSegEnd.
Require Import Zlib.harness.rfc_trailing_bytes.code.
#[local] Existing Instance CS.CS.

(* the segments of TBDSeg*.v (rt_partial's deflate half for this program), chained through their CPS statements
   as in MainRP.v *)
Lemma tb_deflate : tb_deflate_stmt.
Proof.
  intros Espec J0 J gv vc vd DF K.
  rewrite <- tbd_seg1_eq.
  change (tb_A0 gv vc vd) with (tbd_A0 gv vc vd).
  apply (tbd_seg_inputs _ gv vc vd).
  intros n D dp op level wbits mem strategy.
  apply (tbd_seg_init _ J0 J); auto. intros s tin tout adler msg msgv.
  apply (tbd_seg_bound _ J0 J); auto. intros b cp.
  apply (tbd_seg_loop _ J0 J); auto.
  apply tbd_seg_end. intros O.
  rewrite tbd_seg22_eq. unfold tbd_DH. apply K.
Qed.
