(* Law rt_stream_trailing (harness/rt_stream_trailing.c): main's deflate loop (statement 21), from its invariant DI_t to DE_t: deflate() returned Z_STREAM_END; every call accounted (gp_assert(accounted(&compressor, &at))).
   The loop body is cut in TLoopDKit.v; its pieces are proved in TLoopDDraw (read and the draws), TLoopDPrep
   (avail_in, avail_out), TLoopDPosOf (position_of), TLoopDCall (the deflate() call), TLoopDAcc (the accounted
   assert), TLoopDAssert (the Z_BUF_ERROR / unmoved assert) and TLoopDTest (the out-of-room test). *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.rt_stream_trailing.TMainKit.
Require Import VST.floyd.library.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.harness.rt_stream.LawCS.
Require Import Zlib.proof.harness.rt_stream.UDFacts.
Require Import Zlib.proof.harness.rt_stream.UMainKit.
Require Import Zlib.proof.harness.rt_stream_trailing.TMainStmt.
Require Import Zlib.proof.harness.rt_stream_trailing.TLoopDKit.
Require Zlib.proof.harness.rt_stream_trailing.TLoopDDraw.
Require Zlib.proof.harness.rt_stream_trailing.TLoopDPrep.
Require Zlib.proof.harness.rt_stream_trailing.TLoopDPosOf.
Require Zlib.proof.harness.rt_stream_trailing.TLoopDCall.
Require Zlib.proof.harness.rt_stream_trailing.TLoopDAcc.
Require Zlib.proof.harness.rt_stream_trailing.TLoopDAssert.
Require Zlib.proof.harness.rt_stream_trailing.TLoopDTest.
Require Import Zlib.harness.rt_stream_trailing.code.
#[local] Existing Instance LawCS.CS.
Local Open Scope logic.

(* position_of, the call, the two asserts and the test, from DC_t *)
Lemma calltest_d_t {Espec : OracleKind} J gv vc vd va u l2 :
  urts_dfacts J -> semax Delta_t (DC_t gv vc vd va J u l2) callTestD_t (loopD_post_t J gv vc vd va u).
Proof.
  intros JF.
  rewrite callTestD_t_eq.
  eapply semax_seq with (Q := DP_t gv vc vd va J u l2).
  { eapply semax_post; [ | | | | exact (TLoopDPosOf.tpos_d Espec J gv vc vd va u l2) ].
    - simpl RA_normal. apply ENTAIL_refl.
    - simpl RA_break. apply andp_left2; intro rho; cbv beta; normalize.
    - simpl RA_continue. apply andp_left2; intro rho; cbv beta; normalize.
    - intros. simpl RA_return. apply ENTAIL_refl. }
  eapply semax_seq
    with (Q := EX code : Z, EX l' : dls,
               DA_t gv vc vd va J u (dl_off l2) (dl_flush l2) code l' (cpos (dl_c l2))).
  { eapply semax_post; [ | | | | exact (TLoopDCall.tcall_d Espec J gv vc vd va u l2 JF) ].
    - simpl RA_normal. apply ENTAIL_refl.
    - simpl RA_break. apply andp_left2; intro rho; cbv beta; normalize.
    - simpl RA_continue. apply andp_left2; intro rho; cbv beta; normalize.
    - intros. simpl RA_return. apply ENTAIL_refl. }
  apply extract_exists_pre; intro code.
  apply extract_exists_pre; intro l.
  eapply semax_seq with (Q := DA_t gv vc vd va J u (dl_off l2) (dl_flush l2) code l (cpos (dl_c l2))).
  { eapply semax_post;
      [ | | | | exact (TLoopDAcc.tacc_d Espec J gv vc vd va u (dl_off l2) (dl_flush l2) code l
                         (cpos (dl_c l2))) ].
    - simpl RA_normal. apply ENTAIL_refl.
    - simpl RA_break. apply andp_left2; intro rho; cbv beta; normalize.
    - simpl RA_continue. apply andp_left2; intro rho; cbv beta; normalize.
    - intros. simpl RA_return. apply ENTAIL_refl. }
  eapply semax_seq with (Q := DK_t gv vc vd va J u (dl_off l2) (dl_flush l2) code l).
  { eapply semax_post;
      [ | | | | exact (TLoopDAssert.tassert_d Espec J gv vc vd va u (dl_off l2) (dl_flush l2) code l
                         (cpos (dl_c l2))) ].
    - simpl RA_normal. apply ENTAIL_refl.
    - simpl RA_break. apply andp_left2; intro rho; cbv beta; normalize.
    - simpl RA_continue. apply andp_left2; intro rho; cbv beta; normalize.
    - intros. simpl RA_return. apply ENTAIL_refl. }
  apply TLoopDTest.ttest_d.
Qed.

Lemma tloop_d : loopD_t_stmt.
Proof.
  intros Espec J gv vc vd va u JF.
  unfold loopD_t, Delta_t; simplify_func_tycontext.
  forward_loop (EX l : dls, DI_t gv vc vd va J u l)
    continue: (EX code : Z, EX l : dls, DK_t gv vc vd va J u (dl_off l) (dl_flush l) code l)
    break: (EX O : list Z, EX c : cst, DE_t gv vc vd va u O c).
  { apply ENTAIL_refl. }
  3: { unfold overridePost. simpl RA_normal. apply ENTAIL_refl. }
  2: { Intros code l. unfold DK_t. Intros. forward_if.
       - forward. Exists l. unfold DI_t, su_locals, lv_locals. simpl app.
         assert (dl_ok J u l).
         { match goal with Hk : if ?b then _ else _ |- _ => destruct b eqn:E; [ | exact Hk] end.
           apply Z.eqb_eq in E. exfalso. match goal with Hc : code <> 1 |- _ => apply Hc end.
           rewrite E. reflexivity. }
         entailer!.
       - forward. subst code. change (1 =? DState.Z_STREAM_END) with true in *.
         Exists (dl_O l) (dl_c l). unfold DE_t, su_locals, lv_locals. simpl app. entailer!. }
  (* the body: read and the draws, then avail_in and avail_out, then position_of, the call, the asserts and the
     out-of-room test *)
  Intros l.
  apply (TLoopDDraw.tdraw_d Espec J gv vc vd va u l). intros l1.
  apply (TLoopDPrep.tprep_d Espec J gv vc vd va u l1). intros l2.
  apply (calltest_d_t J gv vc vd va u l2 JF).
Qed.
