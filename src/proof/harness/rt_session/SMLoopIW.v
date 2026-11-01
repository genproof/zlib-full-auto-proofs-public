(* Law rt_session (harness/rt_session.c): main's inflate loop (statement 73) without a header, in the context of SpecW's inflate() (SMKit.v, [loopI_W_stmt]). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rt_stream.ULoopIPos.
Require Import Zlib.proof.harness.rt_session.SCS.
Require Import Zlib.proof.harness.rt_session.SIFacts.
Require Import Zlib.proof.harness.rt_session.SMainStmt.
Require Import Zlib.proof.harness.rt_session.SMKit.
Require Import Zlib.proof.harness.rt_session.SMIWKit.
Require Import Zlib.proof.harness.rt_session.SMIWOffer.
Require Import Zlib.proof.harness.rt_session.SMIWCall.
Require Import Zlib.proof.harness.rt_session.SMIWTests.
Require Import Zlib.proof.harness.rt_session.SMIWDict.
Require Import Zlib.harness.rt_session.code.
#[local] Existing Instance SCS.CS.
Local Open Scope logic.

(* The loop's body is proved in parts (SMIWKit cuts it): the two offers of avail_in and avail_out (SMIWOffer:
   each a clip() of an upto() draw, at most 2^32 - 1), position_of and the inflate() call with its Z_MEM_ERROR test
   (SMIWCall), the tests of the documented codes, of accounted and of a call offered neither input nor output space
   (SMIWTests), and the Z_NEED_DICT branch (SMIWDict: inflateSetDictionary, asked = 1).  The loop runs from the
   invariant II_W; after the body, IC_w holds at the test (Z_OK, Z_BUF_ERROR: the invariant P again); the break
   leaves with IE_W: at Z_STREAM_END next_in is input + |O|, the data is produced, and asked is set exactly for a
   zlib stream with a dictionary. *)
Lemma sm_loopI_W : loopI_W_stmt.
Proof.
  intros Espec P PN gv vh vg vc va vd u O c src ip PF.
  rewrite loopI_w_parts.
  forward_loop (EX l : ils, II_W gv vh vg vc va vd P u O c src ip l)
    continue: (IC_w gv vh vg vc va vd P PN u O c src ip)
    break: (IEx_w gv vh vg vc va vd u O c src ip).
  { apply ENTAIL_refl. }
  3: { unfold overridePost, IEx_w. simpl RA_normal. apply ENTAIL_refl. }
  2: { unfold IC_w, ICe_w. Intros r l. unfold iw_locals, iw_props, iw_rest, incrI_w, c_locals, d_locals, lvs, lv_locals. simpl app. Intros.
       match goal with H : cfacts _ _ _ _ _ _ _ _ |- _ => destruct H as (Hgeo & Hok & _ & Hend) end.
       forward_if.
       - (* Z_OK or Z_BUF_ERROR: the invariant again *)
         assert (Hr : r = Z_OK \/ r = Z_BUF_ERROR).
         { match goal with H : r = Z_OK \/ _ |- _ => destruct H as [E|[E|E]] end; auto.
           subst r. exfalso. match goal with H : Int.repr _ <> Int.repr _ |- _ => apply H; reflexivity end. }
         destruct (Hok Hr) as (HP & Hsw). destruct Hgeo as (Hpos & Hrest & Eni & Eno).
         forward. Exists l. unfold II_W, il_ok, c_locals, d_locals, lvs, lv_locals. simpl app. entailer!.
       - (* Z_STREAM_END: the loop's exit *)
         assert (Er : r = Z_STREAM_END).
         { match goal with H : r = Z_OK \/ _ |- _ => destruct H as [E|[E|E]] end; auto; subst r;
           match goal with H : Int.repr _ = Int.repr _ |- _ => discriminate H end. }
         destruct (Hend Er) as (Eout & Epos & Hask).
         destruct Hgeo as (Hpos & Hrest & Eni & Eno).
         match goal with H : su_ok u |- _ => rewrite (asked_end u (il_asked l) H Hask) end.
         forward. unfold IEx_w. Exists (il_z l) (il_L l). unfold IE_W, c_locals, d_locals, lvs, lv_locals. simpl app.
         rewrite Eout in *. rewrite Epos in *.
         entailer!. }
  Intros l. unfold II_W. Intros.
  destruct l as [pos out asked L z]. cbn [il_pos il_out il_asked il_L il_z].
  apply (proj2 (seq_assoc _ _ _ _ _ _)).
  eapply semax_seq'; [apply (offers_w_ok P gv vh vg vc va vd u O c src ip pos out asked L z); auto | ].
  Intros take room. unfold OI_w at 1. Intros.
  apply (proj2 (seq_assoc _ _ _ _ _ _)).
  apply (proj2 (seq_assoc _ _ _ _ _ _)).
  eapply semax_seq; [apply (call_w_ok P PN gv vh vg vc va vd u O c src ip pos out asked L z take room); auto | ].
  Intros r l'.
  apply (proj2 (seq_assoc _ _ _ _ _ _)).
  apply (proj2 (seq_assoc _ _ _ _ _ _)).
  eapply semax_seq'; [apply tests_w_ok | ].
  apply dict_w_ok; auto.
Qed.
