(* RT-D part STORED: the first-phase loop (statement: RTDStoredKit.v). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDStoredKit.
Require Import Zlib.proof.roundtrip.RTDStoredLoopStep.
Import ListNotations.
Local Open Scope Z_scope.

(* The kernel must never compute the loop fuel. *)
Local Strategy opaque [loop loop2].

Theorem rtds_loop_ok : stored_block_fspec -> fpend_fspec2 -> floop_stmt.
Proof.
  intros sbf fpf s z flush s1 z1 last p HW Ho Hq Hlev Hz Ha Hf Hao Hp Hal E.
  pose proof HW as (_ & _ & Hwp & _ & _ & _ & Hl0 & _).
  destruct (Hl0 Hlev) as [Hla Hbs].
  destruct Hwp as (_ & _ & _ & Hbs1 & _).
  assert (I0 : linv s z flush (s, z)).
  { exists [], 0, []. split; [reflexivity|]. split; [lia|]. split; [exact Ho|]. split; [exact Hq|].
    split; [apply pb_grow_refl|]. split; [apply zstep_refl; auto|]. split; [constructor|].
    destruct Hz as (_ & (Hz1 & _)). split; [exact Hz1|]. split; [cbn; lia|]. split; [lia|].
    split; [reflexivity|]. split; constructor. }
  assert (F0 : finv s z p (s, z)).
  { exists 0, [], []. split; [apply zstep_refl; auto|]. split; [constructor|].
    split; [rewrite Z.add_0_r, !sublist_nil; reflexivity|].
    destruct Hq as (Hq1 & Hq2 & _).
    assert (Pend0 : pend s = []) by (unfold pend; rewrite Hq1, Hq2, Z.add_0_r; apply sublist_nil).
    rewrite Pend0. split; [cbn; rewrite app_nil_r; reflexivity|]. cbn. rewrite Z.add_0_r. exact Hal. }
  apply loop_runs in E.
  assert (G : forall a b, runs (ds_body flush (ds_min_block s)) a b ->
                linv s z flush a -> finv s z p a -> ffin s z p b).
  { intros a b R. induction R as [a r Hb | a a' r Hb R IH]; intros L F.
    - destruct (fds_step sbf fpf s z flush p HW Hlev Hz Ha Hf Hao Hp a L F) as (r' & E' & H').
      rewrite Hb in E'. inversion E'; subst. exact H'.
    - destruct (fds_step sbf fpf s z flush p HW Hlev Hz Ha Hf Hao Hp a L F) as (r' & E' & H').
      rewrite Hb in E'. inversion E'; subst. destruct H' as [L' F']. exact (IH L' F'). }
  exact (G _ _ E I0 F0).
Qed.
