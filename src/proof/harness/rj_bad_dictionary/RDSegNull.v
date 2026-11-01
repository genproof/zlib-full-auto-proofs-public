(* Law rj_bad_dictionary, main (RDMain.v), statement 8: if (stream == NULL || out == NULL || dict == NULL)
   return 0 *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.proof.adler32.Spec.
Require Import Zlib.proof.harness.rj_bad_dictionary.RDLawCS.
Require Import Zlib.proof.harness.rj_bad_dictionary.RDGlobals.
Require Import Zlib.proof.harness.rj_bad_dictionary.RDFacts.
Require Import Zlib.proof.harness.rj_bad_dictionary.RDKit.
Require Import Zlib.harness.rj_bad_dictionary.code.
Local Open Scope Z_scope.

Lemma seg_null_ok : seg_null_stmt.
Proof.
  intros Espec gv v_strm t1 t2 room dlen streamp src outp dictp dict K.
  unfold rd_seg8, rd_A8, POST_B, POST_rd, t_zsl. abbreviate_semax.
  Intros. rename H3 into H6', H2 into H5', H1 into H4', H0 into H3'.
  destruct H as (H & H0 & H1 & H2). rename H3' into H3, H4' into H4, H5' into H5, H6' into H6.
  destruct (eq_dec streamp nullval) as [Es|Ns].
  { subst streamp.
    ifpost _t'8 Int.one. { forward. entailer!. } { rbd_nob. }
    ifpost _t'9 Int.one. { forward. entailer!. } { rbd_nob. }
    forward_if False. { ret0. } { rbd_nob. } }
  Intros.
  destruct (eq_dec outp nullval) as [Eo|No].
  { subst outp.
    ifpost _t'8 Int.one. { rbd_nob. } { forward. entailer!. }
    ifpost _t'9 Int.one. { forward. entailer!. } { rbd_nob. }
    forward_if False. { ret0. } { rbd_nob. } }
  Intros.
  destruct (eq_dec dictp nullval) as [Ed|Nd].
  { subst dictp.
    ifpost _t'8 Int.zero. { rbd_nob. } { forward. entailer!. rbd_cmp. }
    ifpost _t'9 Int.one. { rbd_nob. } { forward. entailer!. }
    forward_if False. { ret0. } { rbd_nob. } }
  Intros.
  ifpost _t'8 Int.zero. { rbd_nob. } { forward. entailer!. rbd_cmp. }
  ifpost _t'9 Int.zero. { rbd_nob. } { forward. entailer!. rbd_cmp. }
  forward_if True. { rbd_nob. } { forward. entailer!. }
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
  eapply semax_pre; [ | apply K].
  unfold rd_A9, rd_in. entailer!.
Qed.
