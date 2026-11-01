(* Law rt_stream (harness/rt_stream.c, data of any length), main's body: the inflate loop (statement 30) from its invariant II to IE, the state after inflate() returned Z_STREAM_END (UMainKit.loopI_stmt). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.harness.rt_stream.LawCS.
Require Import Zlib.proof.harness.rt_stream.UMainStmt.
Require Import Zlib.proof.harness.rt_stream.UDFacts.
Require Import Zlib.proof.harness.rt_stream.UIFacts.
Require Import Zlib.proof.harness.rt_stream.UMainKit.
Require Import Zlib.harness.rt_stream.code.
Require Import Zlib.proof.harness.rt_stream.ULoopIPos.
Require Import Zlib.proof.harness.rt_stream.ULoopIKit.
Require Import Zlib.proof.harness.rt_stream.ULoopIOfferIn.
Require Import Zlib.proof.harness.rt_stream.ULoopIOfferOut.
Require Import Zlib.proof.harness.rt_stream.ULoopICall.
Require Import Zlib.proof.harness.rt_stream.ULoopITests.
#[local] Existing Instance LawCS.CS.
Local Open Scope logic.

(* The loop's body is proved in parts (ULoopIKit cuts it): the two offers of avail_in and avail_out
   (ULoopIOfferIn, ULoopIOfferOut: each a clip() of an upto() draw, at most 2^32 - 1), position_of and the
   inflate() call with its Z_MEM_ERROR test (ULoopICall), the test of the documented codes and the test of a call
   offered neither input nor output space (ULoopITests).  The loop runs from the invariant II; after the body, IC
   holds at the test; the break leaves with IE. *)
Lemma uloop_i : loopI_stmt.
Proof.
  intros Espec P gv vc vd va u O c PF.
  rewrite loopI_parts.
  forward_loop (EX l : ils, II gv vc vd va P u O c l)
    continue: (ULoopIKit.IC gv vc vd va P u O c)
    break: (EX z : zfields, EX L : live, IE gv vc vd va u O c z L).
  { apply ENTAIL_refl. }
  3: { unfold overridePost. simpl RA_normal. apply ENTAIL_refl. }
  2: { unfold incrI, ULoopIKit.IC, ICe. Intros r l.
       forward_if.
       - forward. Exists l. unfold II, su_locals, lv_locals. simpl app. entailer!.
       - assert (r = Z_STREAM_END).
         { match goal with H: r = Z_OK \/ _ |- _ => destruct H as [E|[E|E]] end; subst r; auto;
           match goal with H: Int.repr _ = Int.repr _ |- _ => discriminate H end. }
         match goal with H: r = Z_STREAM_END -> _ |- _ => destruct (H ltac:(assumption)) as (Eo & Ep) end.
         forward. Exists (il_z l) (il_L l). unfold IE.
         destruct l as [pos out L z]. unfold il_ok in *. cbn [il_pos il_out il_L il_z] in *.
         repeat match goal with H: _ /\ _ |- _ => destruct H end.
         unfold su_locals, lv_locals. simpl app. entailer!. }
  Intros l. unfold II. Intros.
  destruct l as [pos out L z]. cbn [il_pos il_out il_L il_z].
  eapply semax_seq'; [apply (offer_in_ok P gv vc vd va u O c pos out L z); auto | ].
  Intros take. unfold OI at 1. Intros.
  eapply semax_seq'; [apply (offer_out_ok P gv vc vd va u O c pos out L z take); auto | ].
  Intros room. unfold OI at 1. Intros.
  eapply semax_seq'; [apply (pos_ok gv vc vd va u O c pos out L z take room); auto; lia | ].
  apply (proj2 (seq_assoc _ _ _ _ _ _)).
  eapply semax_seq; [apply (call_mem_ok P gv vc vd va u O c pos out L z take room); auto | ].
  Intros r l'. apply tests_ok.
Qed.
