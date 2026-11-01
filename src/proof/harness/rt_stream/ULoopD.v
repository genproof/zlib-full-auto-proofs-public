(* Law rt_stream (harness/rt_stream.c, data of any length), main's body: the deflate loop (statement 21) from its
   invariant DI to DE, the state after deflate() returned Z_STREAM_END (UMainKit.loopD_stmt).  The loop body is cut
   in ULoopDKit.v; its pieces are proved in ULoopDDraw (read and the draws), ULoopDPrep (avail_in, avail_out),
   ULoopDPosOf (position_of), ULoopDCall (the deflate() call), ULoopDAssert (the Z_BUF_ERROR / unmoved assert) and
   ULoopDTest (the out-of-room test). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.harness.rt_stream.LawCS.
Require Import Zlib.proof.harness.rt_stream.UMainStmt.
Require Import Zlib.proof.harness.rt_stream.UDFacts.
Require Import Zlib.proof.harness.rt_stream.UIFacts.
Require Import Zlib.proof.harness.rt_stream.UMainKit.
Require Import Zlib.proof.harness.rt_stream.ULoopDKit.
Require Zlib.proof.harness.rt_stream.ULoopDDraw.
Require Zlib.proof.harness.rt_stream.ULoopDPrep.
Require Zlib.proof.harness.rt_stream.ULoopDPosOf.
Require Zlib.proof.harness.rt_stream.ULoopDCall.
Require Zlib.proof.harness.rt_stream.ULoopDAssert.
Require Zlib.proof.harness.rt_stream.ULoopDTest.
Require Import Zlib.harness.rt_stream.code.
#[local] Existing Instance LawCS.CS.
Local Open Scope logic.

(* position_of, the call, the assert and the test, from DC *)
Lemma calltest_d {Espec : OracleKind} J gv vc vd va u l2 :
  urts_dfacts J -> semax Delta_m (DC gv vc vd va J u l2) callTestD (loopD_post J gv vc vd va u).
Proof.
  intros JF.
  rewrite callTestD_eq.
  eapply semax_seq with (Q := DP gv vc vd va J u l2).
  { eapply semax_post; [ | | | | exact (ULoopDPosOf.pos_d Espec J gv vc vd va u l2) ].
    - simpl RA_normal. apply ENTAIL_refl.
    - simpl RA_break. apply andp_left2; intro rho; cbv beta; normalize.
    - simpl RA_continue. apply andp_left2; intro rho; cbv beta; normalize.
    - intros. simpl RA_return. apply ENTAIL_refl. }
  eapply semax_seq
    with (Q := EX code : Z, EX l' : dls,
               DA gv vc vd va J u (dl_off l2) (dl_flush l2) code l' (cpos (dl_c l2))).
  { eapply semax_post; [ | | | | exact (ULoopDCall.call_d Espec J gv vc vd va u l2 JF) ].
    - simpl RA_normal. apply ENTAIL_refl.
    - simpl RA_break. apply andp_left2; intro rho; cbv beta; normalize.
    - simpl RA_continue. apply andp_left2; intro rho; cbv beta; normalize.
    - intros. simpl RA_return. apply ENTAIL_refl. }
  apply extract_exists_pre; intro code.
  apply extract_exists_pre; intro l.
  eapply semax_seq with (Q := DK gv vc vd va J u (dl_off l2) (dl_flush l2) code l).
  { eapply semax_post;
      [ | | | | exact (ULoopDAssert.assert_d Espec J gv vc vd va u (dl_off l2) (dl_flush l2) code l
                         (cpos (dl_c l2))) ].
    - simpl RA_normal. apply ENTAIL_refl.
    - simpl RA_break. apply andp_left2; intro rho; cbv beta; normalize.
    - simpl RA_continue. apply andp_left2; intro rho; cbv beta; normalize.
    - intros. simpl RA_return. apply ENTAIL_refl. }
  apply ULoopDTest.test_d.
Qed.

Lemma uloop_d : loopD_stmt.
Proof.
  intros Espec J gv vc vd va u JF.
  unfold loopD, Delta_m; simplify_func_tycontext.
  forward_loop (EX l : dls, DI gv vc vd va J u l)
    continue: (EX code : Z, EX l : dls, DK gv vc vd va J u (dl_off l) (dl_flush l) code l)
    break: (EX O : list Z, EX c : cst, DE gv vc vd va u O c).
  { apply ENTAIL_refl. }
  3: { unfold overridePost. simpl RA_normal. apply ENTAIL_refl. }
  2: { Intros code l. unfold DK. Intros. forward_if.
       - forward. Exists l. unfold DI, su_locals, lv_locals. simpl app.
         assert (dl_ok J u l).
         { match goal with Hk : if ?b then _ else _ |- _ => destruct b eqn:E; [ | exact Hk] end.
           apply Z.eqb_eq in E. exfalso. match goal with Hc : code <> 1 |- _ => apply Hc end.
           rewrite E. reflexivity. }
         entailer!.
       - forward. subst code. change (1 =? DState.Z_STREAM_END) with true in *.
         Exists (dl_O l) (dl_c l). unfold DE, su_locals, lv_locals. simpl app. entailer!. }
  (* the body: read and the draws, then avail_in and avail_out, then position_of, the call, the assert and the
     out-of-room test *)
  Intros l.
  apply (ULoopDDraw.draw_d Espec J gv vc vd va u l). intros l1.
  apply (ULoopDPrep.prep_d Espec J gv vc vd va u l1). intros l2.
  apply (calltest_d J gv vc vd va u l2 JF).
Qed.
