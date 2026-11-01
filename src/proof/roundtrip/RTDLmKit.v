(* RT-D part LM, kit: the hash facts (UPDATE_HASH forgets what came three bytes before; equal hashes
   and two equal bytes give the third), checked accesses, the loop invariant rule. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDSpecs.
Require Export Zlib.proof.roundtrip.RTDLTCLmKit.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** Checked accesses that succeeded *)
Lemma mb_rd_some b i v : mb_rd b i = Some v -> v = Znth i (mb_val b).
Proof. unfold mb_rd. destruct (_ && _); intros H; inversion H; reflexivity. Qed.

Lemma rd_some l i v : rd l i = Some v -> 0 <= i < Zlength l /\ v = Znth i l.
Proof.
  unfold rd, in_range. destruct ((0 <=? i) && (i <? Zlength l)) eqn:E; intros H; [|discriminate].
  inversion H. apply andb_true_iff in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  split; [lia|reflexivity].
Qed.

Lemma wr_some l i v l' : wr l i v = Some l' -> 0 <= i < Zlength l /\ l' = upd_Znth i l v.
Proof.
  unfold wr, in_range. destruct ((0 <=? i) && (i <? Zlength l)) eqn:E; intros H; [|discriminate].
  inversion H. apply andb_true_iff in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  split; [lia|reflexivity].
Qed.

(** ** A loop invariant *)
Lemma loop_inv {A B : Type} (body : A -> option (A + B)) (P : A -> Prop) (Q : B -> Prop) :
  (forall a a', P a -> body a = Some (inl a') -> P a') ->
  (forall a r, P a -> body a = Some (inr r) -> Q r) ->
  forall d a r, P a -> loop d body a = Some r -> Q r.
Proof.
  intros H1 H2 d a r Ha E. apply loop_runs in E. induction E as [a r E|a a' r E _ IH].
  - eapply H2; eauto.
  - apply IH. eapply H1; eauto.
Qed.

(** ** UPDATE_HASH bit by bit *)
Section Hash.
Variable s : dstate.
Hypothesis Hprm : prm s.

Lemma uh_bits h c i : 0 <= i ->
  Z.testbit (update_hash s h c) i =
  (i <? d_hash_bits s) && xorb (Z.testbit h (i - d_hash_shift s)) (Z.testbit c i).
Proof.
  intros Hi. destruct (prm_h s Hprm) as (Hhs & Hhm & Hhb & Hsh).
  unfold update_hash. rewrite Hhm.
  replace (2 ^ d_hash_bits s - 1) with (Z.ones (d_hash_bits s)) by (rewrite Z.ones_equiv; lia).
  rewrite u32_id.
  2:{ rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound (Z.lxor (u32 (Z.shiftl h (d_hash_shift s))) c)
        (2 ^ d_hash_bits s) ltac:(apply Z.pow_pos_nonneg; lia)).
      assert (2 ^ d_hash_bits s <= 2 ^ 16) by (apply Z.pow_le_mono_r; lia). lia. }
  rewrite Z.land_spec, Z.lxor_spec, Z.testbit_ones_nonneg by lia.
  destruct (Z.ltb_spec i (d_hash_bits s)) as [Hlt|Hge]; [|rewrite andb_false_r; reflexivity].
  rewrite andb_true_r; cbn [andb]. f_equal.
  unfold u32. change 4294967296 with (2 ^ 32). rewrite Z.mod_pow2_bits_low by lia.
  destruct (Z.leb_spec (d_hash_shift s) i).
  - rewrite Z.shiftl_spec by lia. reflexivity.
  - rewrite Z.shiftl_spec by lia. rewrite !Z.testbit_neg_r by lia. reflexivity.
Qed.

Lemma hb_le_3sh : d_hash_bits s <= 3 * d_hash_shift s.
Proof.
  destruct Hprm as (_ & _ & _ & Hb & _ & _ & Hsh & _). rewrite Hsh.
  pose proof (Z.div_mod (d_hash_bits s + 2) 3 ltac:(lia)). pose proof (Z.mod_pos_bound (d_hash_bits s + 2) 3 ltac:(lia)).
  lia.
Qed.

(** three UPDATE_HASHes forget the initial value *)
Lemma uh3 h0 a b c :
  update_hash s (update_hash s (update_hash s h0 a) b) c = update_hash s (update_hash s a b) c.
Proof.
  pose proof hb_le_3sh as H3. destruct (prm_h s Hprm) as (_ & _ & Hhb & Hsh).
  apply Z.bits_inj'. intros i Hi.
  rewrite (uh_bits (update_hash s (update_hash s h0 a) b) c i), (uh_bits (update_hash s a b) c i) by lia.
  destruct (Z.ltb_spec i (d_hash_bits s)) as [Hlt|Hge]; [|reflexivity]. cbn [andb]. f_equal.
  destruct (Z.leb_spec 0 (i - d_hash_shift s)) as [H1|H1]; [|rewrite !Z.testbit_neg_r by lia; reflexivity].
  rewrite (uh_bits (update_hash s h0 a) b), (uh_bits a b) by lia. f_equal. f_equal.
  destruct (Z.leb_spec 0 (i - d_hash_shift s - d_hash_shift s)) as [H2|H2];
    [|rewrite !Z.testbit_neg_r by lia; reflexivity].
  rewrite (uh_bits h0 a) by lia. rewrite (Z.testbit_neg_r h0) by lia.
  replace (i - d_hash_shift s - d_hash_shift s <? d_hash_bits s) with true by (symmetry; apply Z.ltb_lt; lia).
  reflexivity.
Qed.

(** equal hashes, two equal leading bytes: the third bytes are equal (deflate.c, longest_match) *)
Lemma uh_third a b c c' : 0 <= c < 256 -> 0 <= c' < 256 ->
  update_hash s (update_hash s a b) c = update_hash s (update_hash s a b) c' -> c = c'.
Proof.
  intros Hc Hc' E. destruct Hprm as (_ & _ & _ & Hb & _).
  apply Z.bits_inj'. intros i Hi.
  destruct (Z.ltb_spec i 8) as [Hlt|Hge].
  - assert (Ei := f_equal (fun x => Z.testbit x i) E). cbn beta in Ei.
    rewrite (uh_bits (update_hash s a b) c i), (uh_bits (update_hash s a b) c' i) in Ei by lia.
    replace (i <? d_hash_bits s) with true in Ei by (symmetry; apply Z.ltb_lt; lia). cbn [andb] in Ei.
    destruct (Z.testbit (update_hash s a b) (i - d_hash_shift s)), (Z.testbit c i), (Z.testbit c' i);
      cbn in Ei; congruence.
  - rewrite <- (Z.mod_small c (2 ^ 8)) by lia. rewrite <- (Z.mod_small c' (2 ^ 8)) by lia.
    rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
End Hash.
