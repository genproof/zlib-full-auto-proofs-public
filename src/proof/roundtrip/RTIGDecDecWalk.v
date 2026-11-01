(* RT-I: copy of rfc1951/DecDecWalk.v over the generalized definitions RTIGDefs.v. *)
(* Part of DecDec.group_dec: the table walk on the valid bits of the bit buffer.  Statement: DecDecDefs.v. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.roundtrip.RTIGDecDecDefs.
Import ListNotations.
Local Open Scope Z_scope.

Lemma dw_lor_disj : forall a b l, 0 <= l -> 0 <= a < 2 ^ l ->
  Z.lor a (Z.shiftl b l) = a + b * 2 ^ l.
Proof.
  intros a b l Hl Ha.
  rewrite <- Z.shiftl_mul_pow2 by lia.
  rewrite <- Z.add_lor_land.
  assert (Z.land a (Z.shiftl b l) = 0) as ->; [|lia].
  apply Z.bits_inj'; intros n Hn. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.ltb_spec n l).
  - rewrite (Z.shiftl_spec_low b l n) by lia. apply andb_false_r.
  - rewrite <- (Z.mod_small a (2 ^ l)) by lia.
    rewrite Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma dw_bval_app : forall A B, bval (A ++ B) = bval A + 2 ^ Zlength A * bval B.
Proof.
  induction A as [|x A IH]; intros B; simpl.
  - rewrite ?Zlength_nil; simpl; lia.
  - rewrite IH, Zlength_cons, Z.pow_succ_r by (pose proof (Zlength_nonneg A); lia). lia.
Qed.

Lemma dw_bval_range : forall A, 0 <= bval A < 2 ^ Zlength A.
Proof.
  induction A as [|x A IH]; simpl.
  - rewrite ?Zlength_nil; simpl; lia.
  - rewrite Zlength_cons, Z.pow_succ_r by (pose proof (Zlength_nonneg A); lia).
    destruct x; simpl; lia.
Qed.

Lemma dw_bval_zeros : forall n, bval (repeat false n) = 0.
Proof. induction n; simpl; auto. rewrite IHn. reflexivity. Qed.

Lemma dw_rl : forall k i r c, 0 <= r -> 0 <= i ->
  ref.reverse_loop k i r c =
  r * 2 ^ Z.of_nat k + bval (rev (map (fun j => Z.testbit c (Z.of_nat j)) (seq (Z.to_nat i) k))).
Proof.
  induction k as [|k IH]; intros i r c Hr Hi.
  - simpl. lia.
  - cbn [ref.reverse_loop seq map rev].
    assert (Hb: Z.lor (Z.shiftl r 1) (Z.land (Z.shiftr c i) 1) = 2 * r + Z.b2z (Z.testbit c i)).
    { assert (Hl: Z.land (Z.shiftr c i) 1 = Z.shiftr c i mod 2).
      { change 1 with (Z.ones 1) at 1. rewrite Z.land_ones by lia. reflexivity. }
      rewrite Z.lor_comm, dw_lor_disj, Hl.
      - rewrite Zmod_odd, <- Z.testbit_odd. destruct (Z.testbit c i); simpl; lia.
      - lia.
      - rewrite Hl. pose proof (Z.mod_pos_bound (Z.shiftr c i) 2). simpl. lia. }
    rewrite Hb, IH by (try destruct (Z.testbit c i); simpl; lia).
    replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
    rewrite dw_bval_app, Zlength_rev, Zlength_map, Zlength_correct, length_seq.
    rewrite Z2Nat.id by lia. cbn [bval]. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    destruct (Z.testbit c i); simpl Z.b2z; lia.
Qed.

Lemma dw_bval_msb : forall c n, 0 <= n -> bval (bits_msb c n) = ref.reverse_bits c n.
Proof.
  intros c n Hn. unfold bits_msb, bits_le, ref.reverse_bits.
  rewrite dw_rl by lia. simpl. lia.
Qed.

Lemma dw_len_send : forall lens s, 0 <= Znth s lens -> Zlength (send_sym lens s) = Znth s lens.
Proof.
  intros lens s H. unfold send_sym, bits_msb, bits_le.
  rewrite Zlength_rev, Zlength_map, Zlength_correct, length_seq. lia.
Qed.

Lemma dw_used_len : forall lens s, lens_ok lens -> used lens s -> 1 <= Znth s lens <= MAXLEN.
Proof.
  intros lens s Hok [Hs Hn]. pose proof (Forall_Znth _ lens s Hs Hok). simpl in H. lia.
Qed.

Lemma dw_tdec_app : forall s t root type lens sy R,
  tdec s t root type lens -> lens_ok lens -> used lens sy ->
  exists op val,
    twalk s t root (bval (send_sym lens sy ++ R)) = Some (op, val, Znth sy lens) /\
    ref.means_symbol type sy op val = true.
Proof.
  intros s t root type lens sy R [_ Htd] Hok Hu.
  pose proof (dw_used_len lens sy Hok Hu) as Hl. destruct Hu as [Hs Hn].
  rewrite dw_bval_app, dw_len_send by lia.
  pose proof (dw_bval_range (send_sym lens sy)) as Hr. rewrite dw_len_send in Hr by lia.
  unfold send_sym in *. rewrite dw_bval_msb in * by lia.
  rewrite Z.mul_comm, <- dw_lor_disj by lia.
  apply Htd; auto. apply dw_bval_range.
Qed.

Lemma dw_filter_pos : forall (f: Z -> bool) l x, In x l -> f x = true -> 1 <= Zlength (filter f l).
Proof.
  intros f l x Hi Hf. assert (In x (filter f l)) by (apply filter_In; auto).
  destruct (filter f l); [contradiction|]. rewrite Zlength_cons. pose proof (Zlength_nonneg l0). lia.
Qed.

Lemma dw_two : forall (l: list Z) a b, 0 <= a < b -> b < Zlength l -> Znth a l <> 0 -> Znth b l <> 0 ->
  2 <= Zlength (filter (fun x => negb (x =? 0)) l).
Proof.
  intros l a b Hab Hb Ha Hbn.
  assert (Hsp: l = sublist 0 b l ++ sublist b (Zlength l) l)
    by (rewrite sublist_rejoin, sublist_same by lia; reflexivity).
  rewrite Hsp at 1. rewrite filter_app, Zlength_app.
  assert (1 <= Zlength (filter (fun x => negb (x =? 0)) (sublist 0 b l))).
  { apply dw_filter_pos with (Znth a l).
    - replace (Znth a l) with (Znth a (sublist 0 b l)) by (rewrite Znth_sublist by lia; f_equal; lia).
      apply Znth_In. rewrite Zlength_sublist by lia. lia.
    - destruct (Z.eqb_spec (Znth a l) 0); [contradiction|reflexivity]. }
  assert (1 <= Zlength (filter (fun x => negb (x =? 0)) (sublist b (Zlength l) l))).
  { apply dw_filter_pos with (Znth b l).
    - replace (Znth b l) with (Znth 0 (sublist b (Zlength l) l)) by (rewrite Znth_sublist by lia; f_equal; lia).
      apply Znth_In. rewrite Zlength_sublist by lia. lia.
    - destruct (Z.eqb_spec (Znth b l) 0); [contradiction|reflexivity]. }
  lia.
Qed.

Lemma dw_single_unique : forall lens a b, single lens -> used lens a -> used lens b -> a = b.
Proof.
  intros lens a b [Hn _] [Ha Hna] [Hb Hnb]. unfold nused in Hn.
  destruct (Z.lt_trichotomy a b) as [H|[H|H]]; auto.
  - pose proof (dw_two lens a b ltac:(lia) ltac:(lia) Hna Hnb). lia.
  - pose proof (dw_two lens b a ltac:(lia) ltac:(lia) Hnb Hna). lia.
Qed.

Lemma dw_all_false : forall (V R: list bool) n, V ++ R = repeat false n -> Forall (eq false) V.
Proof.
  intros V R n H. apply Forall_forall. intros x Hx.
  assert (In x (repeat false n)) by (rewrite <- H; apply in_or_app; auto).
  apply repeat_spec in H0. auto.
Qed.

Lemma walk_ok : canon_stmt -> walk_stmt.
Proof.
  intros canon s t root type lens sy V R Htd Hok Hcs Hu Hcomp.
  destruct (canon lens Hok Hcs) as [Hpf Hcov].
  pose proof (dw_used_len lens sy Hok Hu) as Hl. unfold MAXLEN in Hl.
  assert (Hcase: (exists R', V = send_sym lens sy ++ R') \/
                 (Zlength V < Znth sy lens /\ V ++ R = send_sym lens sy)).
  { destruct Hcomp as [H|H]; [|left; eauto].
    destruct R as [|b R].
    - left. exists []. rewrite <- H, !app_nil_r. reflexivity.
    - right. split; auto. apply (f_equal (@Zlength bool)) in H.
      rewrite Zlength_app, Zlength_cons, dw_len_send in H by lia.
      pose proof (Zlength_nonneg R). lia. }
  destruct Hcase as [[R' ->]|[HV HVR]].
  - destruct (dw_tdec_app s t root type lens sy R' Htd Hok Hu) as (op & val & Hw & Hm).
    exists op, val, (Znth sy lens). split; auto.
    rewrite Zlength_app, dw_len_send by lia. pose proof (Zlength_nonneg R').
    split; [split; intros; lia|]. auto.
  - set (W := V ++ zeros (MAXLEN - Zlength V)).
    assert (HWl: Zlength W = MAXLEN).
    { unfold W, zeros, MAXLEN. rewrite Zlength_app, (Zlength_correct (repeat _ _)), repeat_length.
      pose proof (Zlength_nonneg V). lia. }
    assert (HWc: complete lens \/ W = zeros MAXLEN).
    { destruct Hcs as [Hc|Hsg]; [left; auto|right].
      destruct (Hcov (zeros MAXLEN)) as (s0 & R0 & Hu0 & H0).
      { unfold zeros, MAXLEN. rewrite Zlength_correct, repeat_length. reflexivity. }
      { right; reflexivity. }
      pose proof (dw_single_unique lens s0 sy Hsg Hu0 Hu); subst s0.
      rewrite <- HVR, <- app_assoc in H0.
      pose proof (dw_all_false V (R ++ R0) (Z.to_nat MAXLEN) (eq_sym H0)) as HF.
      assert (HFW: Forall (eq false) W).
      { unfold W. apply Forall_app. split; auto. unfold zeros.
        apply Forall_forall. intros x Hx. apply repeat_spec in Hx. auto. }
      apply Forall_eq_repeat in HFW. rewrite HFW. unfold zeros. f_equal.
      rewrite Zlength_correct in HWl. lia. }
    destruct (Hcov W HWl HWc) as (s' & R' & Hu' & HW).
    pose proof (dw_used_len lens s' Hok Hu') as Hl'. unfold MAXLEN in Hl'.
    destruct (dw_tdec_app s t root type lens s' R' Htd Hok Hu') as (op & val & Hw & Hm).
    assert (HbW: bval W = bval V).
    { unfold W, zeros. rewrite dw_bval_app, dw_bval_zeros. lia. }
    rewrite <- HW, HbW in Hw.
    exists op, val, (Znth s' lens). split; auto.
    assert (Hgt: Zlength V < Znth s' lens).
    { destruct (Z.lt_ge_cases (Zlength V) (Znth s' lens)) as [?|Hle]; auto. exfalso.
      assert (HC': send_sym lens s' = sublist 0 (Znth s' lens) V).
      { assert (sublist 0 (Znth s' lens) W = sublist 0 (Znth s' lens) (send_sym lens s' ++ R'))
          by (rewrite HW; reflexivity).
        unfold W in H. rewrite !sublist0_app1 in H by (rewrite ?dw_len_send; lia).
        rewrite (sublist_same 0 _ (send_sym lens s')) in H by (rewrite ?dw_len_send; lia). auto. }
      assert (send_sym lens s' ++ (sublist (Znth s' lens) (Zlength V) V ++ R) = send_sym lens sy).
      { rewrite HC', app_assoc, sublist_rejoin, sublist_same by lia. auto. }
      pose proof (Hpf sy s' _ Hu Hu' H); subst s'. lia. }
    split; [split; intros; lia|]. intros; lia.
Qed.
