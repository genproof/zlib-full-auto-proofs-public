(** * Core part of the deflate law theory: cf_still, part rle -- helper lemmas.
    - [rle_run_zall]: deflate_rle runs from any [W] state with a sane stream ([zall], not [zin_ok]: the
      stream after a fill_window may have total_in above 2^40), consuming input by a zstep
      (rle_from_parts of RTDLTCRleGlue.v, replayed).
    - c_flush_pending / c_flush_block_only / c_flush_block / c_deflate_tail keep strstart. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDLTCStill.
Require Import Zlib.proof.roundtrip.RTDLTCRleGlue Zlib.proof.roundtrip.RTDLTCRleRefill Zlib.proof.roundtrip.RTDLTCRleScan Zlib.proof.roundtrip.RTDLTCRleLit Zlib.proof.roundtrip.RTDLTCRleDist Zlib.proof.roundtrip.RTDLTCRleFbw Zlib.proof.roundtrip.RTDLTCRleBflush Zlib.proof.roundtrip.RTDLTCRleTail.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

Lemma rle_run_zall : fill_spec -> tally_spec2 -> fbo_spec ->
  forall s z flush,
    W s -> outok s -> quiet s -> zall z -> adler_ok (d_wrap s) (z_adler z) -> fn_of s = 4 -> 0 <= flush <= 5 ->
    exists s' z' bs k x, c_deflate_rle s z flush = Some (s', z', bs) /\ zstep (d_wrap s) z z' k x.
Proof.
  intros Hfill Htal Hfbo s z flush HW Ho Hq Hz Ha Hfn Hfl.
  pose proof (rfbw_ok Hfbo) as Hfbw.
  destruct (rloop_ok (rrefill_ok Hfill) rscan_ok (rlit_ok Htal) (rdist_ok Htal) (rbflush_ok Hfbw)
    s z flush HW Ho Hq Hz Ha Hfn Hfl) as ([[s1 z1] o] & E & H).
  unfold c_deflate_rle. rewrite E. cbn [bind].
  destruct o as [bs|].
  - destruct H as (evs & Hc & _). destruct Hc as (_ & _ & _ & _ & (k & x & Hk & _) & _).
    exists s1, z1, bs, k, x. split; [reflexivity|exact Hk].
  - destruct H as (evs & HFI & Hl & Hai & Hf & Hss).
    destruct (rFI_parts _ _ _ _ _ _ HFI Hfn) as (HW1 & Ho1 & Hq1 & Hz1 & Ha1 & Hfn1).
    destruct (rtail_ok Hfbw s1 z1 flush HW1 Ho1 Hq1 Hz1 Ha1 Hfn1 Hfl Hf Hl Hai Hss)
      as (s2 & z2 & bs & evs2 & E2 & Hc2 & _).
    assert (Hc := rg_crel_trans s z flush s1 z1 evs s2 z2 evs2 Hz Ha (rFI_crel _ _ _ _ _ _ HFI) Hc2).
    destruct Hc as (_ & _ & _ & _ & (k & x & Hk & _) & _).
    exists s2, z2, bs, k, x. split; [exact E2|exact Hk].
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

(** ** The first iteration of deflate_rle's loop *)
Lemma rle_body_fill s z flush s1 z1 :
  need_rle s = true -> c_fill_window s z = Some (s1, z1) ->
  rle_body flush (s, z) =
    if need_rle s1 && (flush =? Z_NO_FLUSH) then Some (inr (s1, z1, Some need_more))
    else if d_lookahead s1 =? 0 then Some (inr (s1, z1, None))
    else rle_step s1 z1.
Proof.
  intros Hn Hf. unfold rle_body, c_refill. rewrite Hn, Hf. cbn [bind].
  destruct (need_rle s1 && (flush =? Z_NO_FLUSH)); [reflexivity|].
  destruct (d_lookahead s1 =? 0); reflexivity.
Qed.


(** The kernel must never compute [loop FUEL] (2^40 iterations): Qed hangs otherwise. *)
Local Strategy opaque [loop loop2].

Lemma rle_exit_some s z flush s1 z1 s' z' bs :
  rle_body flush (s, z) = Some (inr (s1, z1, Some need_more)) ->
  c_deflate_rle s z flush = Some (s', z', bs) -> s' = s1.
Proof.
  intros Eb H.
  assert (E : c_deflate_rle s z flush = Some (s1, z1, need_more)).
  { unfold c_deflate_rle. rewrite (loop_exit (rle_body flush) FUEL (s, z) _ Eb). reflexivity. }
  rewrite E in H. inversion H. reflexivity.
Qed.

Lemma rle_exit_none s z flush s1 z1 s' z' bs :
  rle_body flush (s, z) = Some (inr (s1, z1, None)) ->
  c_deflate_rle s z flush = Some (s', z', bs) -> d_strstart s' = d_strstart s1.
Proof.
  intros Eb H.
  assert (E : c_deflate_rle s z flush = c_deflate_tail (set_d_insert s1 0) z1 flush).
  { unfold c_deflate_rle. rewrite (loop_exit (rle_body flush) FUEL (s, z) _ Eb). reflexivity. }
  rewrite E in H. apply deflate_tail_strstart in H. rewrite H. reflexivity.
Qed.

Lemma rle_k0 s z flush s1 z1 s' z' bs :
  need_rle s = true -> c_fill_window s z = Some (s1, z1) -> need_rle s1 = true -> d_lookahead s1 = 0 ->
  c_deflate_rle s z flush = Some (s', z', bs) -> d_strstart s' = d_strstart s1.
Proof.
  intros Hn Hf Hn1 Hl H.
  pose proof (rle_body_fill s z flush s1 z1 Hn Hf) as Eb. rewrite Hn1, Hl in Eb.
  destruct (flush =? Z_NO_FLUSH).
  - rewrite (rle_exit_some s z flush s1 z1 s' z' bs Eb H). reflexivity.
  - exact (rle_exit_none s z flush s1 z1 s' z' bs Eb H).
Qed.

Lemma rle_restart s z flush s1 z1 :
  need_rle s = true -> c_fill_window s z = Some (s1, z1) -> d_lookahead s1 <> 0 ->
  (need_rle s1 = true -> c_fill_window s1 z1 = Some (s1, z1)) ->
  c_deflate_rle s z flush = c_deflate_rle s1 z1 flush.
Proof.
  intros Hn Hf Hl Hid.
  assert (Eb : rle_body flush (s, z) = rle_body flush (s1, z1)).
  { rewrite (rle_body_fill s z flush s1 z1 Hn Hf).
    destruct (need_rle s1) eqn:Hn1.
    - rewrite (rle_body_fill s1 z1 flush s1 z1 Hn1 (Hid eq_refl)), Hn1. reflexivity.
    - unfold rle_body, c_refill. rewrite Hn1. cbn [andb].
      destruct (Z.eqb_spec (d_lookahead s1) 0) as [E|_]; [contradiction|]. reflexivity. }
  unfold c_deflate_rle. rewrite (loop_body_eq (rle_body flush) FUEL (s, z) (s1, z1) Eb). reflexivity.
Qed.
