(* deflate() from FINISH_STATE with input left (RTK7Defs.Stuck7): the entry stage returns at once (Z_BUF_ERROR,
   or Z_OK when flushing the pending bytes fills the output) and the trailer stage leaves FINISH_STATE and the
   input alone; neither changes w_bits. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTK7DMid.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(* flush_pending, put_byte and putShortMSB only touch the output *)
Lemma sk_flush_pending : forall s z s' z', c_flush_pending s z = Some (s', z') ->
  d_w_bits s' = d_w_bits s /\ d_status s' = d_status s /\ z_avail_in z' = z_avail_in z.
Proof.
  intros s z s' z' H. unfold c_flush_pending, bind in H.
  destruct (c_tr_flush_bits (d_out s)) as [o|]; [|discriminate].
  destruct (_ =? 0).
  { injection H as <- <-. destruct s; repeat split. }
  destruct (mb_read _ _ _) as [b|]; [|discriminate].
  unfold out_put in H. destruct (_ <=? _); [|discriminate].
  destruct (_ =? 0); injection H as <- <-; destruct s, z; repeat split.
Qed.

Lemma sk_dput_byte : forall s c s', c_dput_byte s c = Some s' ->
  d_w_bits s' = d_w_bits s /\ d_status s' = d_status s.
Proof.
  intros s c s' H. unfold c_dput_byte, bind in H.
  destruct (c_put_byte (d_out s) c); [|discriminate]. injection H as <-. destruct s; split; reflexivity.
Qed.

Lemma sk_dput_bytes : forall l s s', c_dput_bytes s l = Some s' ->
  d_w_bits s' = d_w_bits s /\ d_status s' = d_status s.
Proof.
  induction l as [|c l IH]; intros s s' H; cbn in H.
  - injection H as <-. split; reflexivity.
  - unfold bind in H. destruct (c_dput_byte s c) as [s1|] eqn:E; [|discriminate].
    destruct (sk_dput_byte _ _ _ E) as [A B]. destruct (IH _ _ H) as [C D]. split; congruence.
Qed.

Lemma sk_putShortMSB : forall s b s', c_putShortMSB s b = Some s' ->
  d_w_bits s' = d_w_bits s /\ d_status s' = d_status s.
Proof.
  intros s b s' H. unfold c_putShortMSB, bind in H.
  destruct (c_dput_byte s (Z.shiftr b 8)) as [s1|] eqn:E; [|discriminate].
  destruct (sk_dput_byte _ _ _ E) as [A B]. destruct (sk_dput_byte _ _ _ H) as [C D]. split; congruence.
Qed.

Lemma stuck_entry : forall s z s1 z1 o,
  d_status s = FINISH_STATE -> 0 < z_avail_in z ->
  c_deflate_entry s z Z_FINISH = Some (s1, z1, o) ->
  o <> None /\ d_w_bits s1 = d_w_bits s /\ d_status s1 = FINISH_STATE /\ z_avail_in z1 = z_avail_in z.
Proof.
  intros s z s1 z1 o Hs Ha H. unfold c_deflate_entry in H.
  rewrite Hs in H. cbn [Z.eqb Pos.eqb FINISH_STATE Z_FINISH negb andb] in H.
  destruct (z_avail_out z =? 0).
  { injection H as <- <- <-. split; [discriminate|]. destruct z; cbn. auto. }
  unfold then_stage, bind in H.
  destruct (negb (d_pending (set_d_last_flush s Z_FINISH) =? 0)).
  - destruct (c_flush_pending (set_d_last_flush s Z_FINISH) z) as [[s2 z2]|] eqn:E; [|discriminate].
    destruct (sk_flush_pending _ _ _ _ E) as (A & B & C).
    cbn in A, B. rewrite Hs in B.
    destruct (z_avail_out z2 =? 0).
    + injection H as <- <- <-. split; [discriminate|]. destruct s2; cbn in *. auto.
    + rewrite B in H. cbn in H. replace (z_avail_in z2 =? 0) with false in H by (symmetry; apply Z.eqb_neq; lia).
      cbn in H. injection H as <- <- <-. split; [discriminate|]. destruct z2; cbn in *. auto.
  - replace (z_avail_in z =? 0) with false in H by (symmetry; apply Z.eqb_neq; lia).
    cbn in H. rewrite Hs in H.
    replace (z_avail_in z =? 0) with false in H by (symmetry; apply Z.eqb_neq; lia).
    cbn in H. injection H as <- <- <-. split; [discriminate|]. destruct s, z; cbn in *. auto.
Qed.

Lemma stuck_trailer : forall s z flush s4 z4 c,
  d_status s = FINISH_STATE ->
  c_deflate_trailer s z flush = Some (s4, z4, c) ->
  d_w_bits s4 = d_w_bits s /\ d_status s4 = FINISH_STATE /\ z_avail_in z4 = z_avail_in z.
Proof.
  intros s z flush s4 z4 c Hs H. unfold c_deflate_trailer, bind in H.
  destruct (negb (flush =? Z_FINISH)); [injection H as <- <- <-; auto|].
  destruct (d_wrap s <=? 0); [injection H as <- <- <-; auto|].
  match type of H with context [match ?X with Some _ => _ | None => None end] =>
    destruct X as [s1|] eqn:E1; [|discriminate] end.
  assert (P1 : d_w_bits s1 = d_w_bits s /\ d_status s1 = d_status s).
  { destruct (d_wrap s =? 2).
    - exact (sk_dput_bytes _ _ _ E1).
    - destruct (c_putShortMSB s _) as [s0|] eqn:E0; [|discriminate].
      destruct (sk_putShortMSB _ _ _ E0) as [A B]. destruct (sk_putShortMSB _ _ _ E1) as [C D]. split; congruence. }
  destruct (c_flush_pending s1 z) as [[s2 z2]|] eqn:E2; [|discriminate].
  destruct (sk_flush_pending _ _ _ _ E2) as (A & B & C).
  injection H as <- <- <-.
  destruct P1 as [P1 P2].
  assert (Ew : forall x, d_w_bits (set_d_wrap s2 x) = d_w_bits s2 /\ d_status (set_d_wrap s2 x) = d_status s2)
    by (intros; destruct s2; split; reflexivity).
  destruct (d_wrap s2 >? 0); [destruct (Ew (- d_wrap s2)) as [Ew1 Ew2]; rewrite Ew1, Ew2|]; repeat split; congruence.
Qed.
