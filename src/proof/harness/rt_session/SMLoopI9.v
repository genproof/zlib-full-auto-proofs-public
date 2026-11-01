(* Law rt_session (harness/rt_session.c): main's inflate loop (statement 73) with a header, in the context of RTH9Spec's inflate() (SMKit.v, [loopI_9_stmt]). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.SpecW.
Require Zlib.proof.roundtrip.RTH8Spec.
Require Zlib.proof.roundtrip.RTH9Spec.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.proof.harness.laws_session.Facts.
Require Import Zlib.proof.harness.rt_session.SCS.
Require Import Zlib.proof.harness.rt_session.SDFacts.
Require Import Zlib.proof.harness.rt_session.SIFacts.
Require Import Zlib.proof.harness.rt_session.SMainStmt.
Require Import Zlib.proof.harness.rt_session.SMKit.
Require Import Zlib.proof.harness.rt_stream.ULoopIPos.
Require Zlib.proof.harness.rt_stream.ULoopIKit.
Require Import Zlib.proof.harness.rt_session.SLI9Kit.
Require Import Zlib.proof.harness.rt_session.SLI9Offer.
Require Import Zlib.proof.harness.rt_session.SLI9OfferOut.
Require Import Zlib.proof.harness.rt_session.SLI9Call.
Require Import Zlib.proof.harness.rt_session.SLI9Tests.
Require Import Zlib.harness.rt_session.code.
#[local] Existing Instance SCS.CS.
Local Open Scope logic.
Module R8 := Zlib.proof.roundtrip.RTH8Spec.
Module R9 := Zlib.proof.roundtrip.RTH9Spec.
Module UK := Zlib.proof.harness.rt_stream.ULoopIKit.


(* The loop's body is proved in parts (SLI9Kit cuts it): the two offers of avail_in and avail_out
   (SLI9Offer, SLI9OfferOut: each a clip() of an upto() draw, at most 2^32 - 1), position_of and the inflate()
   call with its Z_MEM_ERROR test (SLI9Call), the tests of the documented codes, of accounted, of a call offered
   neither input nor output space and the Z_NEED_DICT branch (SLI9Tests).  The loop runs from the invariant II_9;
   after the body, IC9 holds at the test; the break leaves with IE_9: at Z_STREAM_END next_in is input + |O|, the
   output is the data, and got, out of the header modes with done = 1, is RTH8Spec.head_mem8. *)
Lemma sm_loopI_9 : loopI_9_stmt.
Proof.
  intros Espec P PN gv vh vg vc va vd u O c src ip PF.
  rewrite loopI9_parts.
  forward_loop (EX l : ils, II_9 gv vh vg vc va vd P u O c src ip l)
    continue: (IC9 gv vh vg vc va vd P u O c src ip)
    break: (EX z : zfields, EX L : live, IE_9 gv vh vg vc va vd u O c src ip z L).
  { apply ENTAIL_refl. }
  3: { unfold overridePost. simpl RA_normal. apply ENTAIL_refl. }
  2: { unfold IC9, ICe9. Intros r l.
       unfold incrI9. forward_if.
       - (* not Z_STREAM_END: back to the invariant *)
         assert (Hne : r <> Z_STREAM_END) by (intro E; subst r; apply H10; reflexivity).
         specialize (H7 Hne).
         forward. Exists l. unfold II_9, i9_locals, lvs, lv_locals. simpl app. entailer!.
       - (* Z_STREAM_END: the loop's exit *)
         assert (Hend : r = Z_STREAM_END).
         { destruct H6 as [E|[E|E]]; subst r; auto; exfalso; unfold Z_OK, Z_BUF_ERROR in H10;
           apply repr_inj_signed in H10; rep_lia. }
         destruct (H8 Hend) as (Eo & Ep & Ea & Hh).
         pose proof Hh as (Hih & Hm & Hd & _).
         destruct H4 as (_ & _ & Eni & Eno).
         rewrite Ep in Eni. rewrite Eo in Eno.
         forward. Exists (il_z l) (il_L l). unfold IE_9, i9_locals, lvs, lv_locals. simpl app.
         sep_apply (head_exit9 (il_L l) Hih Hm Hd).
         rewrite (head_no_dict u H0), Ea, Eo. entailer!. }
  Intros l. unfold II_9. Intros.
  destruct l as [pos out asked L z]. cbn [il_pos il_out il_asked il_L il_z] in *.
  match goal with H : il_ok _ _ _ _ _ _ |- _ => rename H into IL end.
  eapply semax_seq'; [apply (offer_in9_ok P gv vh vg vc va vd u O c src ip pos out asked L z); auto | ].
  Intros take. unfold OI9 at 1. Intros.
  eapply semax_seq'; [apply (offer_out9_ok P gv vh vg vc va vd u O c src ip pos out asked L z take); auto | ].
  Intros room. unfold OI9 at 1. Intros.
  eapply semax_seq'; [apply (pos9_ok gv vh vg vc va vd u O c src ip pos out asked L z take room); auto; lia | ].
  apply (proj2 (seq_assoc _ _ _ _ _ _)).
  eapply semax_seq; [apply (call_mem9_ok P PN gv vh vg vc va vd u O c src ip pos out asked L z take room); auto | ].
  Intros r l'. apply tests9_ok.
Qed.
