(* The simulation of the decode modes (LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT; LEN's fast path by fast_sim_stmt). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.api_split_invariant.SIDefs.
Require Import Zlib.proof.harness.api_split_invariant.SISimDecKit.
Require Import Zlib.proof.harness.api_split_invariant.SISimDecMatch.
Require Import Zlib.proof.harness.api_split_invariant.SISimDecLen.
Require Import Zlib.proof.harness.api_split_invariant.SISimDecDist.
Require Import Zlib.proof.harness.api_split_invariant.SISimDecExt.
Import ListNotations.
Local Open Scope Z_scope.

(* LEN_: the free step to LEN, then LEN's pass *)
Lemma sd_len_ : kit_stmt -> awf_stmt -> sim_ok (fun md => md = LEN) -> sim_ok (fun md => md = LEN_).
Proof.
  intros KIT AW HL. apply sim_ok_dgoal. intros flush src P0 O0 m a Rl Aw L Hm.
  rewrite stepf2_LEN_ by exact Hm. unfold c_LEN_.
  set (m1 := set_mode m LEN).
  assert (Ha: a_mode a = LEN_) by (rewrite <- (rl_mode _ _ _ _ _ Rl); exact Hm).
  assert (NB: m_mode m <> BAD) by (rewrite Hm; discriminate).
  set (a1 := AS (set_i_mode (a_s a) LEN) (a_q a) (a_O a)).
  assert (S: astep lenfix_list distfix_list src a = AGo (a_q a) false a1)
    by (rewrite astep_LEN_ by exact Ha; reflexivity).
  assert (Aw1: awf src a1) by (eapply awf_go; eauto).
  assert (Rl1: rel src P0 O0 m1 a1).
  { eapply rel_dec_next with (m := m) (a := a); try exact Rl; cbn; try reflexivity.
    - rewrite Hm. unfold decode_mode; auto.
    - apply bitbuf_ext with m; try reflexivity. exact (rl_bb _ _ _ _ _ Rl).
    - pose proof (rl_aout _ _ _ _ _ Rl). lia.
    - unfold decode_mode; auto.
    - rewrite (rl_q _ _ _ _ _ Rl NB). reflexivity.
    - exact (rl_O _ _ _ _ _ Rl).
    - apply seq_mode; [exact (rl_s _ _ _ _ _ Rl NB)| | |]; intros P; exfalso; dmd.
    - unfold win_eq; cbn; auto.
    - exact (rl_head _ _ _ _ _ Rl). }
  eapply dgoal_go; [exact S| |].
  - rewrite (rl_q _ _ _ _ _ Rl NB). apply (mq_le src), (rl_bb _ _ _ _ _ Rl).
  - rewrite <- (stepf2_LEN flush lenfix_list distfix_list m1) by reflexivity.
    eapply dcont; [exact HL|exact Rl1|exact Aw1|exact L|reflexivity|reflexivity|reflexivity].
Qed.

Lemma si_dec : dec_sim_stmt.
Proof.
  intros KIT AW FS.
  pose proof (sd_match KIT AW) as MA.
  pose proof (sd_distext KIT AW MA) as DX.
  pose proof (sd_dist KIT AW DX) as DI.
  pose proof (sd_lenext KIT AW DI) as LX.
  pose proof (sd_len KIT AW FS LX) as LN.
  pose proof (sd_len_ KIT AW LN) as L_.
  pose proof (sd_lit KIT AW) as LT.
  intros flush src P0 O0 m a Rl Aw L Hm.
  unfold decode_mode in Hm.
  destruct Hm as [E|[E|[E|[E|[E|[E|E]]]]]];
    [apply L_|apply LN|apply LX|apply DI|apply DX|apply MA|apply LT]; auto.
Qed.
