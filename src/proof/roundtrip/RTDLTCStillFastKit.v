(** * Core part of the deflate law theory: cf_still, part fast -- helper lemmas.
    - [fast_run_zall]: deflate_fast runs from any [W] state with a sane stream ([zall], not [zin_ok]: the
      stream after a fill_window may have total_in above 2^40), consuming input by a zstep
      (fast_from_parts of RTDLTCFastGlue.v, replayed).
    - c_flush_pending / c_flush_block_only / c_flush_block / c_deflate_tail keep strstart. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDLTCStill.
Require Import Zlib.proof.roundtrip.RTDLTCFastGlue Zlib.proof.roundtrip.RTDLTCFastRefill Zlib.proof.roundtrip.RTDLTCFastSearch Zlib.proof.roundtrip.RTDLTCFastLit2 Zlib.proof.roundtrip.RTDLTCFastMatch2 Zlib.proof.roundtrip.RTDLTCFastInsLoop Zlib.proof.roundtrip.RTDLTCFastFbw Zlib.proof.roundtrip.RTDLTCFastBflush Zlib.proof.roundtrip.RTDLTCFastTail.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

Lemma fast_run_zall : fill_spec -> ins_spec -> lm_spec -> tally_spec2 -> fbo_spec ->
  forall s z flush,
    W s -> outok s -> quiet s -> zall z -> adler_ok (d_wrap s) (z_adler z) -> fn_of s = 1 -> 0 <= flush <= 5 ->
    exists s' z' bs k x, c_deflate_fast s z flush = Some (s', z', bs) /\ zstep (d_wrap s) z z' k x.
Proof.
  intros Hfi Hin Hlm Hta Hfb s z flush HW Ho Hq Hz Ha Hfn Hfl.
  pose proof (refill_ok Hfi) as Hre. pose proof (search_ok Hin Hlm) as Hse.
  pose proof (lit_ok2 Hta) as Hli. pose proof (match_ok2 Hta (insloop_ok Hin)) as Hma.
  pose proof (bflush_ok (fbw_ok Hfb)) as Hbf. pose proof (tail_ok (fbw_ok Hfb)) as Hta'.
  destruct (loop_ok Hre Hse Hli Hma Hbf s z flush HW Ho Hq Hz Ha Hfn Hfl) as (r & Er & Hr).
  unfold c_deflate_fast. rewrite Er. cbn [bind].
  destruct r as [[s1 z1] [bs|]]; cbv beta iota delta [loop_res] in Hr.
  - destruct Hr as (evs & Hc & _). destruct Hc as (_ & _ & _ & _ & (k & x & Hk & _) & _).
    exists s1, z1, bs, k, x. split; [reflexivity|exact Hk].
  - destruct Hr as (evs & HFI & Hla & Hai & Hnf & Hss).
    destruct (FI_parts _ _ _ _ _ _ HFI Hfn) as (HW1 & Ho1 & Hq1 & Hz1 & Ha1 & Hfn1).
    destruct (Hta' s1 z1 flush HW1 Ho1 Hq1 Hz1 Ha1 Hfn1 Hfl Hnf Hla Hai Hss)
      as (s' & z' & bs & evs2 & Et & Hc & _).
    assert (Hc2 := crel_trans s z flush s1 z1 evs s' z' evs2 Hz Ha (FI_crel _ _ _ _ _ _ HFI) Hc).
    destruct Hc2 as (_ & _ & _ & _ & (k & x & Hk & _) & _).
    exists s', z', bs, k, x. split; [exact Et|exact Hk].
Qed.

(** ** strstart is kept by the flushes *)
Lemma flush_pending_strstart s z s' z' :
  c_flush_pending s z = Some (s', z') -> d_strstart s' = d_strstart s.
Proof.
  unfold c_flush_pending. intros H.
  destruct (c_tr_flush_bits (d_out s)) as [o|]; cbn [bind] in H; [|discriminate].
  destruct (_ =? 0); [inversion H; reflexivity|].
  destruct (mb_read _ _ _) as [b|]; cbn [bind] in H; [|discriminate].
  destruct (out_put _ _) as [z2|]; cbn [bind] in H; [|discriminate].
  destruct (_ =? 0); inversion H; reflexivity.
Qed.

Lemma flush_block_only_strstart s z last s' z' :
  c_flush_block_only s z last = Some (s', z') -> d_strstart s' = d_strstart s.
Proof.
  unfold c_flush_block_only. intros H.
  destruct (in_long _); cbn [guard bind] in H; [|discriminate].
  destruct (if d_block_start s >=? 0 then _ else _) as [buf|]; cbn [bind] in H; [|discriminate].
  destruct (c_tr_flush_block _ _ _ _) as [[t kd]|]; cbn [bind] in H; [|discriminate].
  apply flush_pending_strstart in H. rewrite H. reflexivity.
Qed.

Lemma flush_block_strstart s z last s' z' r :
  c_flush_block s z last = Some (s', z', r) -> d_strstart s' = d_strstart s.
Proof.
  unfold c_flush_block. intros H.
  destruct (c_flush_block_only s z last) as [[s1 z1]|] eqn:E; cbn [bind] in H; [|discriminate].
  apply flush_block_only_strstart in E.
  destruct (_ && _); inversion H; subst; exact E.
Qed.

Lemma deflate_tail_strstart s z flush s' z' bs :
  c_deflate_tail s z flush = Some (s', z', bs) -> d_strstart s' = d_strstart s.
Proof.
  unfold c_deflate_tail. intros H.
  destruct (flush =? Z_FINISH).
  - destruct (c_flush_block s z 1) as [[[s1 z1] r]|] eqn:E; cbn [bind] in H; [|discriminate].
    apply flush_block_strstart in E. destruct r; inversion H; subst; exact E.
  - destruct (negb _).
    + destruct (c_flush_block s z 0) as [[[s1 z1] r]|] eqn:E; cbn [bind] in H; [|discriminate].
      apply flush_block_strstart in E. destruct r; inversion H; subst; exact E.
    + inversion H; reflexivity.
Qed.

(** ** A loop whose first iteration exits *)
Lemma loop2_exit {A B : Type} (body : A -> option (A + B)) d a b :
  body a = Some (inr b) -> loop2 d body a = Some (inr b).
Proof.
  intros H. induction d as [|d IH]; cbn [loop2]; [exact H|]. rewrite IH. reflexivity.
Qed.

Lemma loop_exit {A B : Type} (body : A -> option (A + B)) d a b :
  body a = Some (inr b) -> loop d body a = Some b.
Proof. intros H. unfold loop. rewrite (loop2_exit body d a b H). reflexivity. Qed.

(** ** The first iteration of deflate_fast's loop *)
Lemma fast_exit_some s z flush s1 z1 s' z' bs :
  df_body flush (s, z) = Some (inr (s1, z1, Some need_more)) ->
  c_deflate_fast s z flush = Some (s', z', bs) -> s' = s1.
Proof.
  intros Eb H.
  assert (E : c_deflate_fast s z flush = Some (s1, z1, need_more)).
  { unfold c_deflate_fast. rewrite (loop_exit (df_body flush) FUEL (s, z) _ Eb). reflexivity. }
  rewrite E in H. inversion H. reflexivity.
Qed.

Lemma fast_exit_none s z flush s1 z1 s' z' bs :
  df_body flush (s, z) = Some (inr (s1, z1, None)) ->
  c_deflate_fast s z flush = Some (s', z', bs) -> d_strstart s' = d_strstart s1.
Proof.
  intros Eb H.
  assert (E : c_deflate_fast s z flush = c_deflate_tail (set_insert_end s1) z1 flush).
  { unfold c_deflate_fast. rewrite (loop_exit (df_body flush) FUEL (s, z) _ Eb). reflexivity. }
  rewrite E in H. apply deflate_tail_strstart in H. rewrite H. reflexivity.
Qed.

Lemma fast_restart s z flush s1 z1 :
  df_body flush (s, z) = df_body flush (s1, z1) -> c_deflate_fast s z flush = c_deflate_fast s1 z1 flush.
Proof.
  intros Eb. unfold c_deflate_fast. rewrite (loop_body_eq (df_body flush) FUEL (s, z) (s1, z1) Eb).
  reflexivity.
Qed.

Lemma fast_body_fill s z flush s1 z1 :
  need_min_lookahead s = true -> c_fill_window s z = Some (s1, z1) ->
  df_body flush (s, z) =
    if need_min_lookahead s1 && (flush =? Z_NO_FLUSH) then Some (inr (s1, z1, Some need_more))
    else if d_lookahead s1 =? 0 then Some (inr (s1, z1, None))
    else df_step s1 z1.
Proof.
  intros Hn Hf. unfold df_body, c_refill. rewrite Hn, Hf. cbn [bind].
  destruct (need_min_lookahead s1 && (flush =? Z_NO_FLUSH)); [reflexivity|].
  destruct (d_lookahead s1 =? 0); reflexivity.
Qed.

Lemma fast_body_nofill s z flush :
  need_min_lookahead s = false -> df_body flush (s, z) = df_step s z.
Proof. intros Hn. unfold df_body, c_refill. rewrite Hn. reflexivity. Qed.
