(* The abstract invariant awf holds after inflateInit2 with the four windows of the law and is kept by every abstract step; the shape of a step (the bit position and the output only grow). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.api_split_invariant.SIDefs.
Require Import Zlib.proof.harness.api_split_invariant.SIAwfKit Zlib.proof.harness.api_split_invariant.SIAwfStep.
Import ListNotations.
Local Open Scope Z_scope.

Lemma si_awf : tabrep_stmt -> awf_stmt.
Proof.
  intros TR. split; [|split].
  - intros w src Hw B. apply (ax_w _ _ (a0_awfx w src Hw B)).
  - intros src a n w a' W E.
    pose proof (awfx_go TR src a (awfx_of_awf _ _ W)) as G. rewrite E in G.
    destruct G as [G _]. apply (ax_w _ _ G).
  - intros src a W. unfold astep_shape.
    pose proof (awfx_go TR src a (awfx_of_awf _ _ W)) as G.
    destruct (astep lenfix_list distfix_list src a) as [n w a'|r]; [|exact I].
    destruct G as (_ & G1 & G2 & G3). split; [exact G1|]. split; [exact G2|].
    destruct G3 as [G3 | (Hw & b & G3)]; [left; exact G3 | right; split; [exact Hw | exists b; exact G3]].
Qed.
