(* Law rt_gzip_header on the round-2 harness: main's body (G2MainDefs.body_main2_stmt).  The body is, up to the
   association of its sequences, the seven segments of G2MainKit.v, each proved in its own file (G2MainSeg1.v ..
   G2MainSeg7.v) from the assertion before it to the one after it; the model facts of the deflate loop (G2DFacts)
   and of the inflate loop (G2IFacts) go to the segments that call zlib. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.rt_gzip_header.G2MainDefs.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.harness.rt_gzip_header.CS.
Require Import Zlib.proof.harness.rt_gzip_header.G2MainKit.
Require Import Zlib.proof.harness.rt_gzip_header.G2MainSeg1.
Require Import Zlib.proof.harness.rt_gzip_header.G2MainSeg2.
Require Import Zlib.proof.harness.rt_gzip_header.G2MainSeg3.
Require Import Zlib.proof.harness.rt_gzip_header.G2MainSeg4.
Require Import Zlib.proof.harness.rt_gzip_header.G2MainSeg5.
Require Import Zlib.proof.harness.rt_gzip_header.G2MainSeg6.
Require Import Zlib.proof.harness.rt_gzip_header.G2MainSeg7.
Require Import Zlib.harness.rt_gzip_header.code.
#[local] Existing Instance Zlib.proof.harness.rt_gzip_header.CS.CS.

Lemma body_main2 : body_main2_stmt.
Proof.
  intros J0 J P DF IF.
  start_function.
  make_func_ptr Zlib.inflate.code._zcalloc. make_func_ptr Zlib.inflate.code._zcfree.
  gather_SEP (func_ptr' _ (gv Zlib.inflate.code._zcalloc)) (func_ptr' _ (gv Zlib.inflate.code._zcfree)).
  fold (Zlib.proof.inflate.Callees.zfuncs gv).
  match goal with |- semax _ _ (Ssequence _ ?r) _ =>
    apply (semax_unfold_Ssequence
      (Ssequence seg1 (Ssequence seg2 (Ssequence seg3 (Ssequence seg4 (Ssequence seg5 (Ssequence seg6
        (Ssequence seg7 r))))))))
  end.
  { reflexivity. }
  eapply semax_seq.
  { eapply semax_pre; [| apply (g2seg1_ok _ gv v_head v_got v_compressor v_decompressor v_room)].
    unfold PRE0, lv_locals, ifz. entailer!. }
  Intros g. eapply semax_seq; [apply (g2seg2_ok _ J0 J); assumption |].
  Intros st. eapply semax_seq; [apply (g2seg3_ok _ J0 J); assumption |].
  Intros st' hx Hr b cbp. eapply semax_seq; [apply (g2seg4_ok _ J0 J); assumption |].
  Intros O. eapply semax_seq; [apply g2seg5_ok |].
  Intros z sp. eapply semax_seq; [apply (g2seg6_ok _ P); assumption |].
  Intros L1 Fr. eapply semax_seq; [apply g2seg7_ok |].
  (* the last segment ends by a return: nothing falls through *)
  eapply semax_pre; [| apply semax_ff]. intros rho. unfold bind_ret. simpl. normalize.
Qed.
