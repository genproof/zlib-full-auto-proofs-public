(* RT-I: copy of rfc1951/DecCallWkeep.v over the generalized definitions RTIGDefs.v. *)
(* Part of dec_call: one pass of the switch (Model2.stepf2) keeps the window fields (only inf_leave's
   updatewindow and inflateSetDictionary write them; HEAD sets wbits only when it is 0). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.roundtrip.RTIGDefs.
Require Zlib.proof.inflate_api.StepInv5Kit.
Require Zlib.proof.roundtrip.RTIGDecCallWkeepKit.
Import ListNotations.
Local Open Scope Z_scope.

Definition dcwk_rel (m m': mst) : Prop :=
  i_wsize (m_s m') = i_wsize (m_s m) /\ i_whave (m_s m') = i_whave (m_s m) /\
  i_wnext (m_s m') = i_wnext (m_s m) /\ i_wdata (m_s m') = i_wdata (m_s m) /\
  i_win (m_s m') = i_win (m_s m) /\ i_wbits (m_s m') = i_wbits (m_s m).

Lemma dcwk_keep : forall flush m, i_wbits (m_s m) <> 0 ->
  match stepf2 flush lenfix_list distfix_list m with
  | IBrk m' => dcwk_rel m m'
  | IRet _ m' => dcwk_rel m m'
  end.
Proof.
  intros flush m Hw.
  pose proof (RTIGDecCallWkeepKit.stepf2_wkrel flush lenfix_list distfix_list m) as K.
  assert (W: match stepf2 flush lenfix_list distfix_list m with
             | IBrk m' => i_win (m_s m') = i_win (m_s m) /\ i_wbits (m_s m') = i_wbits (m_s m)
             | IRet _ m' => i_win (m_s m') = i_win (m_s m) /\ i_wbits (m_s m') = i_wbits (m_s m)
             end).
  { destruct (Z.eq_dec (m_mode m) HEAD) as [Hh|Hh].
    - replace (stepf2 flush lenfix_list distfix_list m) with (c_HEAD2 m)
        by (unfold stepf2, step2; rewrite Hh; reflexivity).
      unfold c_HEAD2.
      destruct (i_wrap (m_s m) =? 0); [cbn; auto|].
      rewrite <- (StepInv5Kit.needbits_s 16 m) in Hw |- *.
      revert Hw; generalize (needbits 16 m); intros m1 Hw1.
      assert (Hz: (i_wbits (m_s m1) =? 0) = false) by (apply Z.eqb_neq; exact Hw1).
      repeat match goal with |- context [if ?c then _ else _] => let E := fresh "E" in destruct c eqn:E end;
        cbn; rewrite ?Hz; auto.
    - pose proof (StepInv5Kit.stepf2_wgood flush lenfix_list distfix_list m Hh) as G.
      destruct (stepf2 flush lenfix_list distfix_list m); destruct G as (G1 & G2 & _); auto. }
  destruct (stepf2 flush lenfix_list distfix_list m);
    unfold dcwk_rel, RTIGDecCallWkeepKit.wkrel, RTIGDecCallWkeepKit.wf5 in *; intuition.
Qed.
