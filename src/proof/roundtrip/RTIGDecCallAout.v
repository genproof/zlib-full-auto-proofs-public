(* RT-I: copy of rfc1951/DecCallAout.v over the generalized definitions RTIGDefs.v. *)
(* Part of dec_call: one pass of the switch (Model2.stepf2) keeps m_aout (avail_out at the call's
   start).  Proof idea: as src/proof/inflate/StepHd5.v (stepf2_hrel) with the relation m_aout m' = m_aout m. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.roundtrip.RTIGDefs.
Require Zlib.proof.inflate_api.StepInv5Kit.
Import ListNotations.
Local Open Scope Z_scope.

Lemma dca_aout : forall flush m,
  match stepf2 flush lenfix_list distfix_list m with
  | IBrk m' => m_aout m' = m_aout m
  | IRet _ m' => m_aout m' = m_aout m
  end.
Proof.
  intros flush m.
  destruct (Z.eq_dec (m_mode m) HEAD) as [Hh|Hh].
  - replace (stepf2 flush lenfix_list distfix_list m) with (c_HEAD2 m)
      by (unfold stepf2, step2; rewrite Hh; reflexivity).
    unfold c_HEAD2.
    destruct (i_wrap (m_s m) =? 0); [reflexivity|].
    rewrite <- (StepInv5Kit.needbits_aout 16 m).
    generalize (needbits 16 m); intros m1.
    repeat match goal with |- context [if ?c then _ else _] => destruct c end; reflexivity.
  - pose proof (StepInv5Kit.stepf2_wgood flush lenfix_list distfix_list m Hh) as G.
    destruct (stepf2 flush lenfix_list distfix_list m); apply G.
Qed.
