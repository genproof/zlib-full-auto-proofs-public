(* Law inflate_reset, theory: a one-stream fact of one pass of the switch (Model2.stepf2), used by IRRun.v next
   to the two-stream simulation: `out` stays between `left` and avail_out on entry, and HEAD has no output
   (Body5StepInv.v's out_inv; proved as Body5StepInv.v c_HEAD_inv5 / stepf_inv5 with StepInv5Kit.v). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.inflate_reset.IRDefs.
Require Import Zlib.proof.inflate_api.StepInv5Kit.
Import ListNotations.
Local Open Scope Z_scope.

Definition irp_out (m: mst) : Prop :=
  m_out m <= m_aout m /\ m_left m <= m_out m /\ (m_mode m = HEAD -> m_ow m = []).

(* HEAD: nothing is written, and the pass leaves HEAD or keeps the output empty *)
Lemma irp_c_HEAD m : m_mode m = HEAD -> irp_out m ->
  match c_HEAD2 m with IBrk m' => irp_out m' | IRet _ _ => True end.
Proof.
  intros Hm (O1 & O2 & O3).
  unfold c_HEAD2. hsplit; unfold irp_out; hcbn; autorewrite with wi; auto.
  all: assert (Hw: m_ow m = []) by auto; unfold m_left, m_mode in *; autorewrite with wi in *;
       rewrite ?Hw in *; rewrite ?Zlength_nil in *.
  all: repeat match goal with |- context [if ?c then _ else _] => let E := fresh "F" in destruct c eqn:E end.
  all: wmodes.
  all: split; [lia | split; [lia | auto]].
Qed.

Lemma irps_out (flush: Z) (m: mst) :
  mwf3 m -> m_leave m = 0 -> irp_out m ->
  match stepf2 flush lenfix_list distfix_list m with IBrk m' => irp_out m' | IRet _ _ => True end.
Proof.
  intros Hmwf Hlv Hout.
  destruct (Z.eq_dec (m_mode m) HEAD) as [Hh|Hh].
  - replace (stepf2 flush lenfix_list distfix_list m) with (c_HEAD2 m)
      by (unfold stepf2, step2; rewrite Hh; reflexivity).
    apply irp_c_HEAD; auto.
  - pose proof (stepf2_wgood flush lenfix_list distfix_list m Hh) as G.
    destruct (stepf2 flush lenfix_list distfix_list m) as [m'|r m']; [|exact I].
    unfold wgood, wrel in G; destruct G as (G1 & G2 & G3 & G4 & G5 & G6).
    unfold irp_out, m_left, m_mode in *. destruct Hout as (O1 & O2 & O3).
    split; [lia|]. split; [lia|]. intros; contradiction.
Qed.
