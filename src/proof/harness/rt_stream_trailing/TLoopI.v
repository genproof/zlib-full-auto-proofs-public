(* Law rt_stream_trailing (harness/rt_stream_trailing.c): main's inflate loop (statement 34) on the input object (the stream, then any bytes), from its invariant II_t to IE_t: inflate() returned Z_STREAM_END having read exactly the stream; every call accounted. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.rt_stream_trailing.TMainKit.
Require Import VST.floyd.library.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.harness.rt_stream.LawCS.
Require Import Zlib.proof.harness.rt_stream.UDFacts.
Require Import Zlib.proof.harness.rt_stream.UIFacts.
Require Import Zlib.proof.harness.rt_stream.UMainKit.
Require Import Zlib.proof.harness.rt_stream.ULoopIPos.
Require Import Zlib.proof.harness.rt_stream_trailing.TIFacts.
Require Import Zlib.proof.harness.rt_stream_trailing.TMainStmt.
Require Import Zlib.proof.harness.rt_stream_trailing.TLoopIKit.
Require Import Zlib.proof.harness.rt_stream_trailing.TLoopIOfferIn.
Require Import Zlib.proof.harness.rt_stream_trailing.TLoopIOfferOut.
Require Import Zlib.proof.harness.rt_stream_trailing.TLoopICall.
Require Import Zlib.proof.harness.rt_stream_trailing.TLoopITests.
Require Import Zlib.harness.rt_stream_trailing.code.
#[local] Existing Instance LawCS.CS.
Local Open Scope logic.

(* The loop's body is proved in parts (TLoopIKit cuts it): the two offers of avail_in and avail_out
   (TLoopIOfferIn, TLoopIOfferOut: each a clip() of an upto() draw, at most 2^32 - 1), position_of and the
   inflate() call with its Z_MEM_ERROR test (TLoopICall), the tests of the documented codes, of accounted and of a
   call offered neither input nor output space (TLoopITests).  The loop runs from the invariant II_t; after the
   body, IC_t holds at the test; the break leaves with IE_t: at Z_STREAM_END next_in is input + |O|. *)
Lemma tloop_i : loopI_t_stmt.
Proof.
  intros Espec P gv vc vd va u O c src ip PF.
  rewrite loopI_t_parts.
  forward_loop (EX l : ils, II_t gv vc vd va P u O c src ip l)
    continue: (IC_t gv vc vd va P u O c src ip)
    break: (EX z : zfields, EX L : live, IE_t gv vc vd va u O c src ip z L).
  { apply ENTAIL_refl. }
  3: { unfold overridePost. simpl RA_normal. apply ENTAIL_refl. }
  2: { unfold incrI_t, IC_t, ICe_t. Intros r l.
       forward_if.
       - forward. Exists l. unfold II_t, su_locals, lv_locals. simpl app. entailer!.
       - assert (r = Z_STREAM_END).
         { match goal with H: r = Z_OK \/ _ |- _ => destruct H as [E|[E|E]] end; subst r; auto;
           match goal with H: Int.repr _ = Int.repr _ |- _ => discriminate H end. }
         match goal with H: r = Z_STREAM_END -> _ |- _ => destruct (H ltac:(assumption)) as (Eo & Ep) end.
         forward. Exists (il_z l) (il_L l). unfold IE_t.
         destruct l as [pos out L z]. unfold il_ok_t in *. cbn [il_pos il_out il_L il_z] in *.
         repeat match goal with H: _ /\ _ |- _ => destruct H end.
         subst pos out.
         unfold su_locals, lv_locals. simpl app. entailer!. }
  Intros l. unfold II_t. Intros.
  destruct l as [pos out L z]. cbn [il_pos il_out il_L il_z].
  eapply semax_seq'; [apply (offer_in_t_ok P gv vc vd va u O c src ip pos out L z); auto | ].
  Intros take. unfold OI_t at 1. Intros.
  eapply semax_seq'; [apply (offer_out_t_ok P gv vc vd va u O c src ip pos out L z take); auto | ].
  Intros room. unfold OI_t at 1. Intros.
  eapply semax_seq'; [apply (pos_t_ok gv vc vd va u O c src ip pos out L z take room); auto; lia | ].
  apply (proj2 (seq_assoc _ _ _ _ _ _)).
  eapply semax_seq; [apply (call_mem_t_ok P gv vc vd va u O c src ip pos out L z take room); auto | ].
  Intros r l'. apply tests_t_ok.
Qed.
