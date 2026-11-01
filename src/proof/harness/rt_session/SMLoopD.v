(* Law rt_session (harness/rt_session.c): main's deflate loop (statement 57) (SMKit.v, [loopD_stmt]), from its
   invariant DI to DE: deflate() returned Z_STREAM_END, O is a finished stream of the data with the session's
   dictionary and header, every call accounted (gp_assert(accounted(&compressor, &at))), and head is given back.
   The loop body is cut in SMLDKit.v; its pieces are proved in SMLDDraw (read and the draws), SMLDPrep (avail_in,
   avail_out), SMLDPosOf (position_of), SMLDCall (the deflate() call), SMLDAcc (the accounted assert), SMLDAssert
   (the Z_BUF_ERROR / unmoved assert) and SMLDTest (the out-of-room test). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.harness.rt_session.SCS.
Require Import Zlib.proof.harness.rt_session.SDFacts.
Require Import Zlib.proof.harness.rt_session.SMainStmt.
Require Import Zlib.proof.harness.rt_session.SMKit.
Require Import Zlib.proof.harness.rt_session.SMLDLib.
Require Import Zlib.proof.harness.rt_session.SMLDKit.
Require Zlib.proof.harness.rt_session.SMLDDraw.
Require Zlib.proof.harness.rt_session.SMLDPrep.
Require Zlib.proof.harness.rt_session.SMLDPosOf.
Require Zlib.proof.harness.rt_session.SMLDCall.
Require Zlib.proof.harness.rt_session.SMLDAcc.
Require Zlib.proof.harness.rt_session.SMLDAssert.
Require Zlib.proof.harness.rt_session.SMLDTest.
Require Import Zlib.harness.rt_session.code.
#[local] Existing Instance SCS.CS.
Local Open Scope logic.

(* position_of, the call, the two asserts and the test, from DC_s *)
Lemma calltest_d_s {Espec : OracleKind} J gv vh vg vc va vd u hx Hr l2 :
  ses_dfacts J ->
  semax Delta_s (DC_s gv vh vg vc va vd J u l2 hx Hr) callTestD_s (loopD_post_s J gv vh vg vc va vd u hx Hr).
Proof.
  intros JF.
  rewrite callTestD_s_eq.
  eapply semax_seq with (Q := DP_s gv vh vg vc va vd J u l2 hx Hr).
  { eapply semax_post; [ | | | | exact (SMLDPosOf.spos_d Espec J gv vh vg vc va vd u hx Hr l2) ].
    - simpl RA_normal. apply ENTAIL_refl.
    - simpl RA_break. apply andp_left2; intro rho; cbv beta; normalize.
    - simpl RA_continue. apply andp_left2; intro rho; cbv beta; normalize.
    - intros. simpl RA_return. apply ENTAIL_refl. }
  eapply semax_seq
    with (Q := EX code : Z, EX l' : dls,
               DA_s gv vh vg vc va vd J u (dl_off l2) (dl_flush l2) code l' (cpos_s (dl_c l2)) hx Hr).
  { eapply semax_post; [ | | | | exact (SMLDCall.scall_d Espec J gv vh vg vc va vd u hx Hr l2 JF) ].
    - simpl RA_normal. apply ENTAIL_refl.
    - simpl RA_break. apply andp_left2; intro rho; cbv beta; normalize.
    - simpl RA_continue. apply andp_left2; intro rho; cbv beta; normalize.
    - intros. simpl RA_return. apply ENTAIL_refl. }
  apply extract_exists_pre; intro code.
  apply extract_exists_pre; intro l.
  eapply semax_seq
    with (Q := DA_s gv vh vg vc va vd J u (dl_off l2) (dl_flush l2) code l (cpos_s (dl_c l2)) hx Hr).
  { eapply semax_post;
      [ | | | | exact (SMLDAcc.sacc_d Espec J gv vh vg vc va vd u (dl_off l2) (dl_flush l2) code l
                         (cpos_s (dl_c l2)) hx Hr) ].
    - simpl RA_normal. apply ENTAIL_refl.
    - simpl RA_break. apply andp_left2; intro rho; cbv beta; normalize.
    - simpl RA_continue. apply andp_left2; intro rho; cbv beta; normalize.
    - intros. simpl RA_return. apply ENTAIL_refl. }
  eapply semax_seq with (Q := DK_s gv vh vg vc va vd J u (dl_off l2) (dl_flush l2) code l hx Hr).
  { eapply semax_post;
      [ | | | | exact (SMLDAssert.sassert_d Espec J gv vh vg vc va vd u (dl_off l2) (dl_flush l2) code l
                         (cpos_s (dl_c l2)) hx Hr) ].
    - simpl RA_normal. apply ENTAIL_refl.
    - simpl RA_break. apply andp_left2; intro rho; cbv beta; normalize.
    - simpl RA_continue. apply andp_left2; intro rho; cbv beta; normalize.
    - intros. simpl RA_return. apply ENTAIL_refl. }
  apply SMLDTest.stest_d.
Qed.

Lemma sm_loopD : loopD_stmt.
Proof.
  intros Espec J gv vh vg vc va vd u hx Hr JF.
  unfold loopD, Delta_s; simplify_func_tycontext.
  forward_loop (EX l : dls, DI gv vh vg vc va vd J u l hx Hr)
    continue: (EX code : Z, EX l : dls, DK_s gv vh vg vc va vd J u (dl_off l) (dl_flush l) code l hx Hr)
    break: (EX O : list Z, EX c : cst, DE gv vh vg vc va vd u O c).
  { apply ENTAIL_refl. }
  3: { unfold overridePost. simpl RA_normal. apply ENTAIL_refl. }
  2: { Intros code l. unfold DK_s. Intros. forward_if.
       - forward. Exists l. unfold DI, lvs, lv_locals. simpl app.
         assert (dl_ok J u l).
         { match goal with Hk : if ?b then _ else _ |- _ => destruct b eqn:E; [ | exact Hk] end.
           apply Z.eqb_eq in E. exfalso. match goal with Hc : code <> 1 |- _ => apply Hc end.
           rewrite E. reflexivity. }
         entailer!.
       - forward. subst code. change (1 =? DState.Z_STREAM_END) with true in *.
         Exists (dl_O l) (dl_c l). unfold DE, lvs, lv_locals. simpl app.
         (* head is given back: the header part of the state and the rest close into hobj *)
         match goal with H : hclose _ _ _ _ _ |- _ => rename H into HC end.
         sep_apply (HC (cs_s (dl_c l)) eq_refl).
         entailer!. }
  (* the body: read and the draws, then avail_in and avail_out, then position_of, the call, the asserts and the
     out-of-room test *)
  Intros l.
  apply (SMLDDraw.sdraw_d Espec J gv vh vg vc va vd u hx Hr l). intros l1.
  apply (SMLDPrep.sprep_d Espec J gv vh vg vc va vd u hx Hr l1). intros l2.
  apply (calltest_d_s J gv vh vg vc va vd u hx Hr l2 JF).
Qed.
