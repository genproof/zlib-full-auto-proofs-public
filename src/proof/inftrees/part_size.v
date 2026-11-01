(* Part: size_stmt of fact_result.v (two_level_size = 2^root + sumf). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.inftrees.facts.
Require Import Zlib.proof.inftrees.fact_result.
From Coq Require Import Permutation.
Import ListNotations.
Local Open Scope Z_scope.

(* Sums written as fold_left over a list. *)
Lemma size_fold_add : forall (h: Z -> Z) l a,
  fold_left (fun t p => t + h p) l a = a + fold_right (fun p t => h p + t) 0 l.
Proof.
  intros h l. induction l as [|x l IH]; intros a; cbn [fold_left fold_right]; [lia|].
  rewrite IH. lia.
Qed.

Lemma size_fold_ext : forall (f g: Z -> Z -> Z) l a,
  (forall t p, In p l -> f t p = g t p) -> fold_left f l a = fold_left g l a.
Proof.
  intros f g l. induction l as [|x l IH]; intros a H; cbn [fold_left]; auto.
  rewrite H by (left; auto). apply IH. intros; apply H; right; auto.
Qed.

Lemma size_perm_sum : forall (h: Z -> Z) l l', Permutation l l' ->
  fold_right (fun p t => h p + t) 0 l = fold_right (fun p t => h p + t) 0 l'.
Proof.
  intros h l l' HP. induction HP; cbn [fold_right]; lia.
Qed.

Lemma size_NoDup_zseq : forall n start, NoDup (zseq start n).
Proof.
  induction n; intros; cbn [zseq]; constructor; auto.
  rewrite In_zseq. lia.
Qed.

Lemma size_length_zseq : forall n start, length (zseq start n) = n.
Proof. induction n; intros; cbn [zseq length]; auto. Qed.


(* Summing over the reversed indices is summing over the indices. *)
Lemma size_rev_sum (Hbits : bits_stmt) : forall (F: Z -> Z) r, 0 <= r ->
  fold_right (fun p t => F (reverse_bits p r) + t) 0 (zseq 0 (Z.to_nat (2 ^ r))) =
  fold_right (fun p t => F p + t) 0 (zseq 0 (Z.to_nat (2 ^ r))).
Proof.
  intros F r Hr. destruct Hbits as (B1 & B2 & B3 & B4 & B5).
  assert (E: forall l, fold_right (fun p t => F (reverse_bits p r) + t) 0 l =
                       fold_right (fun p t => F p + t) 0 (map (fun p => reverse_bits p r) l)).
  { induction l; cbn [fold_right map]; congruence. }
  rewrite E. symmetry. apply size_perm_sum.
  apply NoDup_Permutation_bis.
  - apply size_NoDup_zseq.
  - rewrite length_map. lia.
  - intros q Hq. apply In_zseq in Hq. apply in_map_iff.
    exists (reverse_bits q r). split.
    + apply B3; lia.
    + apply In_zseq. specialize (B1 q r Hr). lia.
Qed.

Lemma size_key (Hsorted : sorted_stmt) (Hrfc : rfc_stmt) (Hbits : bits_stmt) : forall lens root, Forall (fun l => 0 <= l <= MAXBITS) lens ->
  kraft lens <= 2 ^ MAXBITS -> 0 <= root <= MAXBITS ->
  forall i p, 0 <= i < Zlength (sl lens) -> 0 <= p < 2 ^ root ->
  root < Znth i (sl lens) ->
  (Z.land (reverse_bits (rfc_code lens (Znth i (sorted_syms lens))) (Znth i (sl lens)))
          (Z.shiftl 1 root - 1) = p <->
   kpre (sl lens) i / 2 ^ (MAXBITS - root) = reverse_bits p root).
Proof.
  intros lens root Hl Hk Hr i p Hi Hp Hlt.
  destruct Hbits as (B1 & B2 & B3 & B4 & B5).
  destruct (Hsorted lens Hl) as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9).
  pose proof (Hrfc lens Hl i Hi) as R.
  set (ls := sl lens) in *. set (l := Znth i ls) in *.
  set (c := rfc_code lens (Znth i (sorted_syms lens))) in *.
  assert (Hlr: 1 <= l <= MAXBITS).
  { eapply Forall_forall in S2; [exact S2|]. apply Znth_In; lia. }
  unfold MAXBITS in *.
  assert (Hpos: 0 < 2 ^ (15 - l)) by (apply Z.pow_pos_nonneg; lia).
  pose proof (ksum_nonneg (sublist 0 i ls)) as Hkn. fold (kpre ls i) in Hkn.
  assert (Hc: 0 <= c) by nia.
  pose proof (kpre_next_le ls i Hi) as Hnx. unfold MAXBITS in Hnx.
  assert (Hq: kpre ls i / 2 ^ (15 - root) = c / 2 ^ (l - root)).
  { rewrite <- R. replace (2 ^ (15 - root)) with (2 ^ (15 - l) * 2 ^ (l - root))
      by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    rewrite <- Z.div_div by (try lia; apply Z.pow_pos_nonneg; lia).
    rewrite Z.div_mul by lia. reflexivity. }
  assert (Hqr: 0 <= kpre ls i / 2 ^ (15 - root) < 2 ^ root).
  { split; [apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia]|].
    apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia|].
    rewrite <- Z.pow_add_r by lia. replace (15 - root + root) with 15 by lia. lia. }
  rewrite pow2_shiftl by lia.
  rewrite B2 by lia. rewrite <- Hq.
  split; intros H.
  - subst p. rewrite B3 by lia. reflexivity.
  - rewrite H. apply B3; lia.
Qed.

Lemma size_grp (Hsorted : sorted_stmt) (Hrfc : rfc_stmt) (Hbits : bits_stmt) : forall lens root, Forall (fun l => 0 <= l <= MAXBITS) lens ->
  kraft lens <= 2 ^ MAXBITS -> 0 <= root <= MAXBITS ->
  forall p, 0 <= p < 2 ^ root ->
  grp lens root p = gmax (sl lens) root (reverse_bits p root).
Proof.
  intros lens root Hl Hk Hr p Hp.
  destruct (Hsorted lens Hl) as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9).
  set (cond := fun s => (root <? Znth s lens) &&
     (Z.land (reverse_bits (rfc_code lens s) (Znth s lens)) (Z.shiftl 1 root - 1) =? p)).
  assert (Hg: grp lens root p =
    fold_left (fun g s => if cond s then Z.max g (Znth s lens) else g) (zseq 0 (length lens)) 0).
  { unfold grp. apply size_fold_ext. intros t s _. unfold cond.
    destruct (_ && _); auto. destruct (t <? Znth s lens) eqn:E;
      [apply Z.ltb_lt in E | apply Z.ltb_ge in E]; lia. }
  destruct (fold_max_props cond (fun s => Znth s lens) (zseq 0 (length lens)) 0) as [G1 [G2 G3]].
  rewrite <- Hg in G1, G2, G3.
  destruct (gmax_props (sl lens) root (reverse_bits p root)) as [M1 [M2 M3]].
  assert (HlenW: Zlength (sl lens) = Zlength (sorted_syms lens)) by (unfold sl; apply Zlength_map).
  assert (HZ: forall i, 0 <= i < Zlength (sl lens) ->
            Znth i (sl lens) = Znth (Znth i (sorted_syms lens)) lens).
  { intros. unfold sl. rewrite Znth_map by lia. reflexivity. }
  apply Z.le_antisymm.
  - destruct G3 as [G3|[s [Hs [Hc G3]]]]; [lia|].
    rewrite G3. unfold cond in Hc. rewrite andb_true_iff, Z.ltb_lt, Z.eqb_eq in Hc.
    apply In_zseq in Hs. rewrite <- Zlength_correct in Hs.
    assert (Hin: In s (sorted_syms lens)) by (apply S4; lia).
    apply In_Znth in Hin. destruct Hin as [i [Hi Hsi]].
    rewrite <- HlenW in Hi. subst s. rewrite <- HZ in * by lia.
    apply M2; [lia | lia|].
    apply (size_key Hsorted Hrfc Hbits lens root Hl Hk Hr i p Hi Hp); tauto.
  - destruct M3 as [M3|[i [Hi [Hlt [Hq M3]]]]]; [lia|].
    rewrite M3. rewrite HZ by lia. apply G2.
    + apply In_zseq. rewrite <- Zlength_correct.
      eapply Forall_forall in S1; [exact S1|]. apply Znth_In; lia.
    + unfold cond. rewrite andb_true_iff, Z.ltb_lt, Z.eqb_eq. rewrite <- HZ by lia.
      split; auto. apply (size_key Hsorted Hrfc Hbits lens root Hl Hk Hr i p Hi Hp); auto.
Qed.

Lemma size_ok2_proof (Hsorted : sorted_stmt) (Hrfc : rfc_stmt) (Hbits : bits_stmt) : size_stmt.
Proof.
  intros lens root Hl Hk Hr.
  unfold two_level_size. rewrite Z.shiftl_1_l.
  rewrite (size_fold_ext _ (fun t p => t + fq (sl lens) root (reverse_bits p root))).
  2: { intros t p Hp. apply In_zseq in Hp.
       rewrite (size_grp Hsorted Hrfc Hbits) by (auto; lia). unfold fq.
       destruct (gmax (sl lens) root (reverse_bits p root) =? 0); [lia|].
       rewrite Z.shiftl_1_l. reflexivity. }
  rewrite size_fold_add. unfold sumf. rewrite size_fold_add.
  rewrite (size_rev_sum Hbits (fq (sl lens) root)) by lia. lia.
Qed.


Lemma size_ok2 : sorted_stmt -> rfc_stmt -> bits_stmt -> size_stmt.
Proof.
  exact size_ok2_proof.
Qed.
