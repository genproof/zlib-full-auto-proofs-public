(* Part of DecDec.group_dec: canonical codes: prefix-free, covering.  Statement: DecDecDefs.v. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.rfc1951.DecDecDefs.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* Bit values                                                                                     *)

Lemma cn_bval_app : forall A B, bval (A ++ B) = bval A + 2 ^ Zlength A * bval B.
Proof.
  induction A as [|a A IH]; intros B; simpl.
  - lia.
  - rewrite IH, Zlength_cons, Z.pow_succ_r by (pose proof (Zlength_nonneg A); lia). lia.
Qed.

Lemma cn_bval_range : forall A, 0 <= bval A < 2 ^ Zlength A.
Proof.
  induction A as [|a A IH]; simpl.
  - lia.
  - rewrite Zlength_cons, Z.pow_succ_r by (pose proof (Zlength_nonneg A); lia).
    destruct a; simpl; lia.
Qed.

Lemma cn_bits_le_S : forall c n, 0 <= c -> bits_le c (Z.of_nat (S n)) = Z.testbit c 0 :: bits_le (c / 2) (Z.of_nat n).
Proof.
  intros c n Hc. unfold bits_le. rewrite !Nat2Z.id. cbn [seq map]. f_equal.
  rewrite <- seq_shift, map_map. apply map_ext. intros i.
  rewrite <- Z.div2_div, Z.div2_spec, Z.shiftr_spec by lia. f_equal. lia.
Qed.

Lemma cn_bval_bits_le : forall n c, 0 <= c -> bval (bits_le c (Z.of_nat n)) = c mod 2 ^ Z.of_nat n.
Proof.
  induction n as [|n IH]; intros c Hc.
  - change (2 ^ Z.of_nat 0) with 1. rewrite Z.mod_1_r. reflexivity.
  - rewrite cn_bits_le_S by lia. cbn [bval]. rewrite IH by (apply Z.div_pos; lia).
    rewrite Z.bit0_mod, Nat2Z.inj_succ, Z.pow_succ_r by lia.
    rewrite Z.rem_mul_r by (try apply Z.pow_pos_nonneg; lia). lia.
Qed.

Lemma cn_bits_le_bval : forall A, bits_le (bval A) (Zlength A) = A.
Proof.
  induction A as [|a A IH]; [reflexivity|].
  rewrite Zlength_correct in *. cbn [length].
  rewrite cn_bits_le_S by (pose proof (cn_bval_range A); cbn [bval]; destruct a; cbn [Z.b2z]; lia).
  cbn [bval]. f_equal.
  - destruct a.
    + replace (Z.b2z true + 2 * bval A) with (2 * bval A + 1) by (cbn [Z.b2z]; lia). apply Z.testbit_odd_0.
    + replace (Z.b2z false + 2 * bval A) with (2 * bval A) by (cbn [Z.b2z]; lia). apply Z.testbit_even_0.
  - replace ((Z.b2z a + 2 * bval A) / 2) with (bval A); [exact IH|].
    rewrite Z.add_comm, Z.mul_comm, Z.div_add_l by lia. destruct a; cbn [Z.b2z]; [change (1/2) with 0 | change (0/2) with 0]; lia.
Qed.

Lemma cn_bits_msb_len : forall c n, 0 <= n -> Zlength (bits_msb c n) = n.
Proof.
  intros. unfold bits_msb, bits_le. rewrite Zlength_rev, Zlength_map, Zlength_correct, seq_length. lia.
Qed.

Lemma cn_bval_msb : forall c n, 0 <= c -> 0 <= n -> bval (rev (bits_msb c n)) = c mod 2 ^ n.
Proof.
  intros. unfold bits_msb. rewrite rev_involutive. rewrite <- (Z2Nat.id n) at 1 by lia.
  rewrite cn_bval_bits_le by lia. rewrite Z2Nat.id by lia. reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Filters on sublists                                                                            *)

Lemma cn_filter_split : forall (f: Z -> bool) (l: list Z) a s b, 0 <= a <= s -> s < b <= Zlength l ->
  Zlength (filter f (sublist a b l)) =
  Zlength (filter f (sublist a s l)) + (if f (Znth s l) then 1 else 0) + Zlength (filter f (sublist (s + 1) b l)).
Proof.
  intros. rewrite <- (sublist_rejoin a s b) by lia. rewrite (sublist_next s b) by lia.
  rewrite filter_app, Zlength_app. cbn [filter]. destruct (f (Znth s l)); rewrite ?Zlength_cons; lia.
Qed.

Lemma cn_filter_exists : forall l v r, 0 <= r < Zlength (filter (fun x => x =? v) l) ->
  exists s, 0 <= s < Zlength l /\ Znth s l = v /\ Zlength (filter (fun x => x =? v) (sublist 0 s l)) = r.
Proof.
  induction l as [|x l IH]; intros v r Hr.
  - simpl in Hr. rewrite Zlength_nil in Hr. lia.
  - cbn [filter] in Hr. destruct (Z.eqb_spec x v) as [E|E].
    + rewrite Zlength_cons in Hr. destruct (Z.eq_dec r 0) as [->|Hr0].
      * exists 0. rewrite Zlength_cons, Znth_0_cons, sublist_nil. pose proof (Zlength_nonneg l). split; [lia|split; [exact E|reflexivity]].
      * destruct (IH v (r - 1) ltac:(lia)) as (s & Hs & Hv & Hc). exists (s + 1).
        rewrite Zlength_cons, Znth_pos_cons, sublist_0_cons by lia. replace (s + 1 - 1) with s by lia.
        cbn [filter]. rewrite E, Z.eqb_refl, Zlength_cons. lia.
    + destruct (IH v r Hr) as (s & Hs & Hv & Hc). exists (s + 1).
      rewrite Zlength_cons, Znth_pos_cons, sublist_0_cons by lia. replace (s + 1 - 1) with s by lia.
      cbn [filter]. destruct (Z.eqb_spec x v); [contradiction|]. lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Levels: cS n = sum over l < n of count_of l * 2^(15 - l)                                       *)

Fixpoint cS (lens: list Z) (n: nat) : Z :=
  match n with O => 0 | S m => cS lens m + count_of lens (Z.of_nat m) * 2 ^ (MAXLEN - Z.of_nat m) end.

Lemma cn_count_nonneg : forall lens l, 0 <= count_of lens l.
Proof. intros. unfold count_of. destruct (l =? 0); [lia | apply Zlength_nonneg]. Qed.

Lemma cn_cS_mono : forall lens m n, (m <= n)%nat -> cS lens m <= cS lens n.
Proof.
  intros lens m n H. induction H; [lia|]. cbn [cS].
  pose proof (cn_count_nonneg lens (Z.of_nat m0)). pose proof (Z.pow_nonneg 2 (MAXLEN - Z.of_nat m0) ltac:(lia)). nia.
Qed.

Lemma cn_nc : forall lens l, (l <= 15)%nat -> next_code_n lens l * 2 ^ (MAXLEN - Z.of_nat l) = cS lens l.
Proof.
  intros lens l. induction l as [|l IH]; intros Hl; [reflexivity|].
  cbn [next_code_n cS]. rewrite <- IH by lia. unfold MAXLEN in *.
  replace (15 - Z.of_nat l) with (Z.succ (15 - Z.of_nat (S l))) by lia.
  rewrite Z.pow_succ_r by lia. lia.
Qed.

Lemma cn_nc_nonneg : forall lens l, 0 <= next_code_n lens l.
Proof. induction l; cbn [next_code_n]; [lia|]. pose proof (cn_count_nonneg lens (Z.of_nat l)). lia. Qed.

Lemma cn_count_cons : forall x r l, count_of (x :: r) l = count_of r l + (if (l =? 0) then 0 else if x =? l then 1 else 0).
Proof.
  intros. unfold count_of. destruct (l =? 0); [lia|]. cbn [filter]. destruct (x =? l); rewrite ?Zlength_cons; lia.
Qed.

Lemma cn_cS_cons : forall x r n, 0 <= x -> cS (x :: r) n =
  cS r n + (if (x =? 0) || (Z.of_nat n <=? x) then 0 else 2 ^ (MAXLEN - x)).
Proof.
  intros x r n Hx. induction n as [|n IH].
  - cbn [cS]. destruct (x =? 0); simpl; [lia|]. destruct (Z.leb_spec 0 x); lia.
  - cbn [cS]. rewrite IH, cn_count_cons.
    destruct (Z.eqb_spec x 0) as [E0|E0]; cbn [orb].
    + subst x. destruct (Z.eqb_spec (Z.of_nat n) 0); [lia|]. destruct (Z.eqb_spec 0 (Z.of_nat n)); [lia|]. lia.
    + destruct (Z.eqb_spec (Z.of_nat n) 0) as [En|En].
      * rewrite En. destruct (Z.eqb_spec x 0); [contradiction|].
        destruct (Z.leb_spec 0 x), (Z.leb_spec (Z.of_nat (S n)) x); lia.
      * destruct (Z.eqb_spec x (Z.of_nat n)) as [Ex|Ex].
        -- rewrite <- Ex. destruct (Z.leb_spec x x); [|lia]. destruct (Z.leb_spec (Z.of_nat (S n)) x); lia.
        -- destruct (Z.leb_spec (Z.of_nat n) x), (Z.leb_spec (Z.of_nat (S n)) x); lia.
Qed.

Lemma cn_kraft : forall lens, lens_ok lens -> kraft_sum lens = cS lens 16.
Proof.
  induction lens as [|x r IH]; intros Hok.
  - reflexivity.
  - inversion Hok; subst. unfold kraft_sum in *. cbn [fold_right]. rewrite IH by assumption.
    rewrite cn_cS_cons by lia. destruct (x =? 0); cbn [orb]; [lia|].
    destruct (Z.leb_spec (Z.of_nat 16) x); unfold MAXLEN in *; lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The intervals [code s * 2^(15 - l), + 2^(15 - l)) of the used symbols                          *)

Definition cn_rank (lens: list Z) (s: Z) : Z := Zlength (filter (fun x => x =? Znth s lens) (sublist 0 s lens)).

Lemma cn_len : forall lens s, lens_ok lens -> used lens s -> 1 <= Znth s lens <= MAXLEN.
Proof.
  intros lens s Hok [Hs Hn]. pose proof (Forall_Znth _ _ s Hs Hok) as H. cbv beta in H. unfold MAXLEN in *. lia.
Qed.

Lemma cn_lo : forall lens s, lens_ok lens -> used lens s ->
  code lens s * 2 ^ (MAXLEN - Znth s lens) = cS lens (Z.to_nat (Znth s lens)) + cn_rank lens s * 2 ^ (MAXLEN - Znth s lens).
Proof.
  intros lens s Hok Hu. pose proof (cn_len lens s Hok Hu) as Hl. unfold code, cn_rank.
  rewrite <- cn_nc by (unfold MAXLEN in *; lia). rewrite Z2Nat.id by lia. lia.
Qed.

Lemma cn_step : forall lens l, 0 <= l ->
  cS lens (S (Z.to_nat l)) = cS lens (Z.to_nat l) + count_of lens l * 2 ^ (MAXLEN - l).
Proof. intros. cbn [cS]. rewrite Z2Nat.id by lia. reflexivity. Qed.

Lemma cn_rank_lt : forall lens s, used lens s -> cn_rank lens s + 1 <= count_of lens (Znth s lens).
Proof.
  intros lens s [Hs Hn]. unfold count_of, cn_rank. destruct (Z.eqb_spec (Znth s lens) 0); [contradiction|].
  rewrite <- (sublist_same 0 (Zlength lens) lens) at 2 by reflexivity.
  rewrite (cn_filter_split _ lens 0 s (Zlength lens)) by lia. rewrite Z.eqb_refl.
  pose proof (Zlength_nonneg (filter (fun x => x =? Znth s lens) (sublist (s + 1) (Zlength lens) lens))). lia.
Qed.

Lemma cn_rank_mono : forall lens s t, used lens s -> used lens t -> s < t -> Znth s lens = Znth t lens ->
  cn_rank lens s + 1 <= cn_rank lens t.
Proof.
  intros lens s t [Hs _] [Ht _] Hst E. unfold cn_rank. rewrite <- E.
  rewrite (cn_filter_split _ lens 0 s t) by lia. rewrite Z.eqb_refl.
  pose proof (Zlength_nonneg (filter (fun x => x =? Znth s lens) (sublist (s + 1) t lens))). lia.
Qed.

(* the end of s's interval is at most the start of the next level *)
Lemma cn_hi : forall lens s, lens_ok lens -> used lens s ->
  code lens s * 2 ^ (MAXLEN - Znth s lens) + 2 ^ (MAXLEN - Znth s lens) <= cS lens (S (Z.to_nat (Znth s lens))).
Proof.
  intros lens s Hok Hu. pose proof (cn_len lens s Hok Hu). rewrite cn_lo, cn_step by (auto; lia).
  pose proof (cn_rank_lt lens s Hu). pose proof (Z.pow_nonneg 2 (MAXLEN - Znth s lens) ltac:(lia)). nia.
Qed.

Lemma cn_lo_ge : forall lens s, lens_ok lens -> used lens s ->
  cS lens (Z.to_nat (Znth s lens)) <= code lens s * 2 ^ (MAXLEN - Znth s lens).
Proof.
  intros lens s Hok Hu. rewrite cn_lo by auto. pose proof (cn_len lens s Hok Hu).
  assert (0 <= cn_rank lens s) by apply Zlength_nonneg.
  pose proof (Z.pow_nonneg 2 (MAXLEN - Znth s lens) ltac:(lia)). nia.
Qed.

Lemma cn_disj : forall lens s t x, lens_ok lens -> used lens s -> used lens t ->
  code lens s * 2 ^ (MAXLEN - Znth s lens) <= x < code lens s * 2 ^ (MAXLEN - Znth s lens) + 2 ^ (MAXLEN - Znth s lens) ->
  code lens t * 2 ^ (MAXLEN - Znth t lens) <= x < code lens t * 2 ^ (MAXLEN - Znth t lens) + 2 ^ (MAXLEN - Znth t lens) ->
  s = t.
Proof.
  intros lens s t x Hok Hs Ht Ix Iy.
  pose proof (cn_len lens s Hok Hs). pose proof (cn_len lens t Hok Ht).
  pose proof (cn_hi lens s Hok Hs). pose proof (cn_hi lens t Hok Ht).
  pose proof (cn_lo_ge lens s Hok Hs). pose proof (cn_lo_ge lens t Hok Ht).
  destruct (Z.lt_trichotomy (Znth s lens) (Znth t lens)) as [L|[L|L]].
  - pose proof (cn_cS_mono lens (S (Z.to_nat (Znth s lens))) (Z.to_nat (Znth t lens)) ltac:(lia)). lia.
  - rewrite !cn_lo in Ix, Iy by auto. rewrite <- L in Iy.
    set (w := 2 ^ (MAXLEN - Znth s lens)) in *. assert (0 < w) by (apply Z.pow_pos_nonneg; lia).
    set (c := cS lens (Z.to_nat (Znth s lens))) in *.
    assert (cn_rank lens s = cn_rank lens t) as Er.
    { destruct (Z.lt_trichotomy (cn_rank lens s) (cn_rank lens t)) as [R|[R|R]]; [nia| exact R | nia]. }
    destruct (Z.lt_trichotomy s t) as [St|[St|St]]; [|exact St|].
    + pose proof (cn_rank_mono lens s t Hs Ht St L). lia.
    + pose proof (cn_rank_mono lens t s Ht Hs St ltac:(lia)). lia.
  - pose proof (cn_cS_mono lens (S (Z.to_nat (Znth t lens))) (Z.to_nat (Znth s lens)) ltac:(lia)). lia.
Qed.

Lemma cn_code_lt : forall lens s, lens_ok lens -> kraft_sum lens <= 2 ^ MAXLEN -> used lens s ->
  0 <= code lens s < 2 ^ Znth s lens.
Proof.
  intros lens s Hok Hk Hu. pose proof (cn_len lens s Hok Hu). pose proof (cn_hi lens s Hok Hu).
  pose proof (cn_cS_mono lens (S (Z.to_nat (Znth s lens))) 16 ltac:(unfold MAXLEN in *; lia)) as Hm.
  rewrite <- cn_kraft in Hm by auto.
  assert (0 <= code lens s).
  { unfold code. pose proof (cn_nc_nonneg lens (Z.to_nat (Znth s lens))). pose proof (Zlength_nonneg (filter (fun x => x =? Znth s lens) (sublist 0 s lens))). lia. }
  split; auto.
  assert (2 ^ MAXLEN = 2 ^ Znth s lens * 2 ^ (MAXLEN - Znth s lens)) as E.
  { rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  assert (0 < 2 ^ (MAXLEN - Znth s lens)) by (apply Z.pow_pos_nonneg; lia).
  nia.
Qed.

Lemma cn_find_level : forall lens v n, 0 <= v < cS lens n ->
  exists l, (l < n)%nat /\ cS lens l <= v < cS lens (S l).
Proof.
  intros lens v n. induction n as [|n IH]; intros Hv.
  - cbn [cS] in Hv. lia.
  - destruct (Z.lt_ge_cases v (cS lens n)).
    + destruct (IH ltac:(lia)) as (l & ? & ?). exists l. split; [lia|auto].
    + exists n. split; [lia|]. lia.
Qed.

Lemma cn_cover : forall lens v, lens_ok lens -> 0 <= v < kraft_sum lens ->
  exists s, used lens s /\
    code lens s * 2 ^ (MAXLEN - Znth s lens) <= v < code lens s * 2 ^ (MAXLEN - Znth s lens) + 2 ^ (MAXLEN - Znth s lens).
Proof.
  intros lens v Hok Hv. rewrite cn_kraft in Hv by auto.
  destruct (cn_find_level lens v 16 Hv) as (l & Hl & Hlv).
  assert (l <> O) as Hl0 by (intros ->; cbn [cS] in Hlv; unfold count_of in Hlv; simpl in Hlv; lia).
  cbn [cS] in Hlv. set (w := 2 ^ (MAXLEN - Z.of_nat l)) in *.
  assert (0 < w) by (apply Z.pow_pos_nonneg; unfold MAXLEN; lia).
  set (r := (v - cS lens l) / w).
  assert (w * r <= v - cS lens l < w * (r + 1)) as Hr.
  { split; [apply Z.mul_div_le; lia|]. unfold r. rewrite Z.mul_add_distr_l, Z.mul_1_r.
    pose proof (Z.mod_pos_bound (v - cS lens l) w H). rewrite (Z_div_mod_eq_full (v - cS lens l) w) at 1. lia. }
  assert (0 <= r) by (apply Z.div_pos; lia).
  assert (r < count_of lens (Z.of_nat l)) by nia.
  unfold count_of in H1. destruct (Z.eqb_spec (Z.of_nat l) 0); [lia|].
  destruct (cn_filter_exists lens (Z.of_nat l) r ltac:(lia)) as (s & Hs & Hsl & Hsr).
  assert (used lens s) as Hu by (split; [lia | rewrite Hsl; lia]).
  exists s. split; auto. rewrite cn_lo by auto. unfold cn_rank. rewrite Hsl, Hsr, Nat2Z.id. fold w. lia.
Qed.

Lemma canon_ok : canon_stmt.
Proof.
  intros lens Hok Hcs.
  assert (Hk : 0 < kraft_sum lens <= 2 ^ MAXLEN)
    by (destruct Hcs as [H|[_ H]]; rewrite H; unfold MAXLEN; cbn; lia).
  split.
  - intros s s' R Hs Hs' E.
    pose proof (cn_len lens s Hok Hs). pose proof (cn_len lens s' Hok Hs').
    pose proof (cn_code_lt lens s Hok ltac:(lia) Hs). pose proof (cn_code_lt lens s' Hok ltac:(lia) Hs').
    assert (Hlen : Znth s' lens + Zlength R = Znth s lens).
    { apply (f_equal (@Zlength bool)) in E. unfold send_sym in E.
      rewrite Zlength_app, !cn_bits_msb_len in E by lia. exact E. }
    assert (Hv : bval (rev R) + 2 ^ Zlength R * code lens s' = code lens s).
    { apply (f_equal (fun L => bval (rev L))) in E. unfold send_sym in E.
      rewrite rev_app_distr, cn_bval_app, Zlength_rev, !cn_bval_msb, !Z.mod_small in E by lia. exact E. }
    pose proof (cn_bval_range (rev R)) as HR. rewrite Zlength_rev in HR.
    assert (Ew : 2 ^ (MAXLEN - Znth s' lens) = 2 ^ Zlength R * 2 ^ (MAXLEN - Znth s lens)).
    { rewrite <- Z.pow_add_r by (pose proof (Zlength_nonneg R); lia). f_equal. lia. }
    assert (0 < 2 ^ (MAXLEN - Znth s lens)) by (apply Z.pow_pos_nonneg; lia).
    apply (cn_disj lens s' s (code lens s * 2 ^ (MAXLEN - Znth s lens)) Hok Hs' Hs); [|lia].
    rewrite Ew, <- Hv. nia.
  - intros W HW Hc.
    assert (Hv : 0 <= bval (rev W) < kraft_sum lens).
    { destruct Hc as [Hc| ->].
      + pose proof (cn_bval_range (rev W)). rewrite Zlength_rev, HW in H. rewrite Hc. exact H.
      + split; [reflexivity|]. change (bval (rev (zeros MAXLEN))) with 0. lia. }
    destruct (cn_cover lens (bval (rev W)) Hok Hv) as (s & Hs & Iv).
    pose proof (cn_len lens s Hok Hs). pose proof (cn_code_lt lens s Hok ltac:(lia) Hs).
    pose (A := sublist 0 (Znth s lens) W). pose (B := sublist (Znth s lens) MAXLEN W).
    assert (HAB : A ++ B = W).
    { unfold A, B. rewrite sublist_rejoin by lia. apply sublist_same; auto. }
    assert (HA : Zlength A = Znth s lens) by (unfold A; rewrite Zlength_sublist by lia; lia).
    assert (HB : Zlength B = MAXLEN - Znth s lens) by (unfold B; rewrite Zlength_sublist by lia; lia).
    assert (Ev : bval (rev W) = bval (rev B) + 2 ^ (MAXLEN - Znth s lens) * bval (rev A)).
    { rewrite <- HAB at 1. rewrite rev_app_distr, cn_bval_app, Zlength_rev, HB. reflexivity. }
    pose proof (cn_bval_range (rev B)) as RB. rewrite Zlength_rev, HB in RB.
    assert (0 < 2 ^ (MAXLEN - Znth s lens)) by (apply Z.pow_pos_nonneg; lia).
    assert (Ea : bval (rev A) = code lens s).
    { pose proof (cn_bval_range (rev A)).
      destruct (Z.lt_trichotomy (bval (rev A)) (code lens s)) as [L|[L|L]]; [nia|exact L|nia]. }
    exists s, B. split; auto. rewrite <- HAB. f_equal.
    unfold send_sym, bits_msb. rewrite <- (rev_involutive A). f_equal.
    rewrite <- (cn_bits_le_bval (rev A)), Zlength_rev, HA, Ea. reflexivity.
Qed.
