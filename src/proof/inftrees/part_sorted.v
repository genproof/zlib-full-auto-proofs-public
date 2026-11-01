(* Part: sorted_stmt of fact_result.v (the sorted symbols work[] and their lengths). *)
From Coq Require Import ZArith List Lia Bool Sorted.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.inftrees.facts.
Require Import Zlib.proof.inftrees.fact_result.
Import ListNotations.
Local Open Scope Z_scope.

(* Members and size of syms_of_len. *)
Lemma sorted_in_syms_aux : forall L a l s,
  In s (map fst (filter (fun p => snd p =? l) (combine (zseq a (length L)) L))) <->
  a <= s < a + Zlength L /\ Znth (s - a) L = l.
Proof.
  induction L as [|x L IH]; intros a l s; simpl.
  - rewrite Zlength_nil. split; [tauto | lia].
  - rewrite Zlength_cons. pose proof (Zlength_nonneg L) as HL0. destruct (x =? l) eqn:E; simpl; rewrite IH.
    + apply Z.eqb_eq in E. split.
      * intros [H|[H1 H2]].
        -- subst. rewrite Z.sub_diag, Znth_0_cons. split; [lia | auto].
        -- rewrite Znth_pos_cons by lia. replace (s - a - 1) with (s - (a + 1)) by lia. split; [lia | auto].
      * intros [H1 H2]. destruct (Z.eq_dec s a); [left; auto | right].
        rewrite Znth_pos_cons in H2 by lia. replace (s - a - 1) with (s - (a + 1)) in H2 by lia.
        split; [lia | auto].
    + apply Z.eqb_neq in E. split.
      * intros [H1 H2]. rewrite Znth_pos_cons by lia. replace (s - a - 1) with (s - (a + 1)) by lia.
        split; [lia | auto].
      * intros [H1 H2]. destruct (Z.eq_dec s a).
        -- subst s. rewrite Z.sub_diag, Znth_0_cons in H2. contradiction.
        -- rewrite Znth_pos_cons in H2 by lia. replace (s - a - 1) with (s - (a + 1)) in H2 by lia.
           split; [lia | auto].
Qed.

Lemma sorted_len_syms_aux : forall L a l,
  Zlength (map fst (filter (fun p => snd p =? l) (combine (zseq a (length L)) L))) = count_len L l.
Proof.
  induction L as [|x L IH]; intros; simpl; [reflexivity|].
  rewrite count_len_cons, (Z.eqb_sym l x).
  destruct (x =? l); cbn [filter map fst snd]; rewrite ?Zlength_cons, IH; lia.
Qed.

(* Concatenated runs of equal lengths. *)
Definition sorted_rl (c: Z -> nat) (start: Z) (n: nat) : list Z :=
  flat_map (fun l => repeat l (c l)) (zseq start n).

Lemma sorted_rl_S : forall c start n,
  sorted_rl c start (S n) = repeat start (c start) ++ sorted_rl c (start + 1) n.
Proof. reflexivity. Qed.

Lemma sorted_rl_in : forall c n start x, In x (sorted_rl c start n) -> start <= x < start + Z.of_nat n.
Proof.
  intros c n start x H. unfold sorted_rl in H. apply in_flat_map in H. destruct H as [l [Hl Hx]].
  apply repeat_spec in Hx. subst. apply In_zseq in Hl. lia.
Qed.

Lemma sorted_SS_app : forall a b, StronglySorted Z.le a -> StronglySorted Z.le b ->
  (forall x y, In x a -> In y b -> x <= y) -> StronglySorted Z.le (a ++ b).
Proof.
  induction a as [|h a IH]; intros b Ha Hb H; simpl; auto.
  inversion Ha; subst. constructor.
  - apply IH; auto. intros; apply H; simpl; auto.
  - apply Forall_app; split; auto. apply Forall_forall; intros; apply H; simpl; auto.
Qed.

Lemma sorted_SS_repeat : forall x n, StronglySorted Z.le (repeat x n).
Proof.
  induction n; simpl; constructor; auto.
  apply Forall_forall; intros y Hy. apply repeat_spec in Hy. lia.
Qed.

Lemma sorted_rl_sorted : forall c n start, StronglySorted Z.le (sorted_rl c start n).
Proof.
  induction n; intros start; [constructor|]. rewrite sorted_rl_S.
  apply sorted_SS_app; auto using sorted_SS_repeat.
  intros x y Hx Hy. apply repeat_spec in Hx. apply sorted_rl_in in Hy. lia.
Qed.

Lemma sorted_SS_Znth : forall l, StronglySorted Z.le l ->
  forall a b, 0 <= a -> a <= b < Zlength l -> Znth a l <= Znth b l.
Proof.
  induction l as [|h l IH]; intros HS a b Ha Hb; [rewrite Zlength_nil in Hb; lia|].
  inversion HS; subst. rewrite Zlength_cons in Hb.
  destruct (Z.eq_dec a 0).
  - subst. rewrite Znth_0_cons. destruct (Z.eq_dec b 0); [subst; rewrite Znth_0_cons; lia|].
    rewrite Znth_pos_cons by lia. rewrite Forall_forall in H2. apply H2. apply Znth_In; lia.
  - rewrite !Znth_pos_cons by lia. apply IH; auto; lia.
Qed.

Lemma sorted_count_repeat : forall x n l, count_len (repeat x n) l = if l =? x then Z.of_nat n else 0.
Proof.
  induction n; intros; simpl.
  - destruct (l =? x); reflexivity.
  - rewrite count_len_cons, IHn. destruct (l =? x); lia.
Qed.

Lemma sorted_rl_count : forall c n start l,
  count_len (sorted_rl c start n) l =
  if (start <=? l) && (l <? start + Z.of_nat n) then Z.of_nat (c l) else 0.
Proof.
  induction n; intros start l.
  - unfold sorted_rl. cbn [zseq flat_map]. rewrite count_len_nil.
    destruct (start <=? l) eqn:E1, (l <? start + Z.of_nat 0) eqn:E2; simpl; auto.
    apply Z.ltb_lt in E2. lia.
  - rewrite sorted_rl_S, count_len_app, sorted_count_repeat, IHn. rewrite Nat2Z.inj_succ.
    bdestr; simpl; subst; lia.
Qed.

Lemma sorted_ksum_repeat : forall x n, ksum (repeat x n) = Z.of_nat n * 2 ^ (MAXBITS - x).
Proof.
  induction n; [reflexivity|]. cbn [repeat]. unfold ksum in *; cbn [fold_right]. rewrite IHn, Nat2Z.inj_succ. ring.
Qed.

Lemma sorted_rl_ksum : forall c n start, start + Z.of_nat n = 16 ->
  ksum (sorted_rl c start n) = wsum (fun l => Z.of_nat (c l)) n start.
Proof.
  induction n; intros start H; [reflexivity|].
  rewrite sorted_rl_S, ksum_app, sorted_ksum_repeat, IHn by lia. cbn [wsum].
  replace (MAXBITS - start) with (Z.of_nat n) by (unfold MAXBITS; lia). reflexivity.
Qed.

Lemma sorted_map_flat_map : forall (f: Z -> Z) (g: Z -> list Z) xs,
  map f (flat_map g xs) = flat_map (fun x => map f (g x)) xs.
Proof. induction xs; simpl; auto. rewrite map_app, IHxs. reflexivity. Qed.

Lemma sorted_map_const : forall (f: Z -> Z) c xs, Forall (fun s => f s = c) xs -> map f xs = repeat c (length xs).
Proof. induction xs; intros H; simpl; auto. inversion H; subst. rewrite IHxs; auto. Qed.

(* The facts about sorted_syms. *)
Definition sorted_cnt (lens: list Z) (l: Z) : nat := length (syms_of_len lens l).

Lemma sorted_cnt_eq : forall lens l, Z.of_nat (sorted_cnt lens l) = count_len lens l.
Proof. intros. unfold sorted_cnt, syms_of_len. rewrite <- Zlength_correct. apply sorted_len_syms_aux. Qed.

Lemma sorted_in_syms : forall lens l s, In s (syms_of_len lens l) <-> 0 <= s < Zlength lens /\ Znth s lens = l.
Proof.
  intros. unfold syms_of_len. rewrite sorted_in_syms_aux. rewrite Z.sub_0_r. split; intros [? ?]; split; auto; lia.
Qed.

Lemma sorted_sl_eq : forall lens, sl lens = sorted_rl (sorted_cnt lens) 1 15.
Proof.
  intros. unfold sl, sorted_syms, sorted_rl. rewrite sorted_map_flat_map.
  apply flat_map_ext. intros l. apply sorted_map_const.
  apply Forall_forall. intros s Hs. apply sorted_in_syms in Hs. tauto.
Qed.

Lemma sorted_in_sorted : forall lens s,
  In s (sorted_syms lens) <-> 0 <= s < Zlength lens /\ 1 <= Znth s lens <= 15.
Proof.
  intros. unfold sorted_syms. rewrite in_flat_map. split.
  - intros [l [Hl Hs]]. apply In_zseq in Hl. apply sorted_in_syms in Hs. simpl in Hl. lia.
  - intros [H1 H2]. exists (Znth s lens). split.
    + apply In_zseq. simpl. lia.
    + apply sorted_in_syms. auto.
Qed.

Lemma sorted_in_sl : forall lens, Forall (fun l => 0 <= l <= MAXBITS) lens ->
  forall x, In x (sl lens) <-> In x lens /\ 1 <= x.
Proof.
  intros lens HF x. unfold sl. rewrite in_map_iff. rewrite Forall_forall in HF. split.
  - intros [s [Hx Hs]]. apply sorted_in_sorted in Hs. subst. split; [apply Znth_In|]; lia.
  - intros [Hx H1]. apply In_Znth in Hx. destruct Hx as [s [Hs Hx]]. exists s. split; auto.
    apply sorted_in_sorted. subst. split; auto. split; auto.
    specialize (HF (Znth s lens) (Znth_In _ _ Hs)). unfold MAXBITS in HF. lia.
Qed.

Lemma sorted_maxlen_ge : forall lens x, In x lens -> x <= maxlen lens.
Proof.
  induction lens as [|h t IH]; intros x H; [contradiction|]. unfold maxlen; simpl. fold (maxlen t).
  destruct H; [subst; lia | specialize (IH x H); lia].
Qed.

Lemma sorted_maxlen_in : forall lens, maxlen lens = 0 \/ In (maxlen lens) lens.
Proof.
  induction lens as [|h t IH]; [left; reflexivity|]. unfold maxlen; simpl. fold (maxlen t).
  destruct (Z.max_spec h (maxlen t)) as [[H1 H2]|[H1 H2]]; rewrite H2.
  - destruct IH; [left; auto | right; right; auto].
  - right; left; auto.
Qed.

Lemma sorted_maxlen_nonneg : forall lens, 0 <= maxlen lens.
Proof. induction lens; unfold maxlen in *; simpl; lia. Qed.

Lemma sorted_minlen_le : forall lens x, In x lens -> x <> 0 -> minlen lens <= x.
Proof.
  induction lens as [|h t IH]; intros x H Hx; [contradiction|]. unfold minlen; simpl. fold (minlen t).
  destruct H.
  - subst. destruct (x =? 0) eqn:E; [apply Z.eqb_eq in E; contradiction|]. lia.
  - specialize (IH x H Hx). destruct (h =? 0); lia.
Qed.

Lemma sorted_minlen_in : forall lens, minlen lens = 16 \/ In (minlen lens) lens.
Proof.
  induction lens as [|h t IH]; [left; reflexivity|]. unfold minlen; simpl. fold (minlen t).
  destruct (h =? 0).
  - destruct IH; [left; auto | right; right; auto].
  - destruct (Z.min_spec h (minlen t)) as [[H1 H2]|[H1 H2]]; rewrite H2.
    + right; left; auto.
    + destruct IH; [left; auto | right; right; auto].
Qed.

Lemma sorted_ok2 : sorted_stmt.
Proof.
  intros lens HF.
  assert (HF' := HF). rewrite Forall_forall in HF'.
  assert (Hsl_ok : forall x, In x (sl lens) <-> In x lens /\ 1 <= x) by (apply sorted_in_sl; auto).
  assert (HSS : forall a b, 0 <= a -> a <= b < Zlength (sl lens) -> Znth a (sl lens) <= Znth b (sl lens)).
  { rewrite sorted_sl_eq. apply sorted_SS_Znth. apply sorted_rl_sorted. }
  assert (Hnil : sl lens = [] <-> maxlen lens = 0).
  { split.
    - intros H. destruct (sorted_maxlen_in lens) as [|Hin]; auto.
      pose proof (sorted_maxlen_nonneg lens).
      destruct (Z.eq_dec (maxlen lens) 0); auto. exfalso.
      assert (In (maxlen lens) (sl lens)) by (apply Hsl_ok; split; auto; lia).
      rewrite H in H1. contradiction.
    - intros H. destruct (sl lens) as [|x r] eqn:E; auto. exfalso.
      assert (In x (x :: r)) by (left; auto).
      apply Hsl_ok in H0. destruct H0. apply sorted_maxlen_ge in H0. lia. }
  split; [|split; [|split; [exact HSS|split; [|split; [|split; [|split; [|split; [exact Hnil|]]]]]]]].
  - apply Forall_forall. intros s Hs. apply sorted_in_sorted in Hs. lia.
  - rewrite sorted_sl_eq. apply Forall_forall. intros x Hx. apply sorted_rl_in in Hx. simpl in Hx.
    unfold MAXBITS; lia.
  - intros s Hs Hn. apply sorted_in_sorted. split; auto.
    specialize (HF' (Znth s lens) (Znth_In _ _ Hs)). unfold MAXBITS in HF'. lia.
  - intros l Hl. rewrite Znth_counts by (unfold MAXBITS in Hl; lia).
    rewrite sorted_sl_eq, sorted_rl_count. unfold MAXBITS in Hl.
    destruct (1 <=? l) eqn:E1; [|apply Z.leb_gt in E1; lia].
    destruct (l <? 1 + Z.of_nat 15) eqn:E2; [|apply Z.ltb_ge in E2; simpl in E2; lia].
    simpl. symmetry. apply sorted_cnt_eq.
  - unfold counts. rewrite Zlength_map, Zlength_zseq. reflexivity.
  - rewrite sorted_sl_eq, sorted_rl_ksum by reflexivity. rewrite kraft_wsum by auto.
    apply wsum_ext. intros l _. apply sorted_cnt_eq.
  - intros Hne. assert (Hmx : maxlen lens <> 0) by (intro H; apply Hne, Hnil, H).
    assert (Hlen : 1 <= Zlength (sl lens)).
    { destruct (sl lens) as [|x r]; [contradiction|]. rewrite Zlength_cons. pose proof (Zlength_nonneg r); lia. }
    destruct (minlen_range lens HF) as [R1 R2].
    split.
    + assert (H0 : In (Znth 0 (sl lens)) (sl lens)) by (apply Znth_In; lia).
      apply Hsl_ok in H0. destruct H0 as [H0 H0'].
      pose proof (sorted_minlen_le lens _ H0 ltac:(lia)).
      destruct (sorted_minlen_in lens) as [Hm|Hm]; [apply R2 in Hm; contradiction|].
      assert (Hm' : In (minlen lens) (sl lens)) by (apply Hsl_ok; split; auto; lia).
      apply In_Znth in Hm'. destruct Hm' as [k [Hk Hk']].
      specialize (HSS 0 k ltac:(lia) ltac:(lia)). lia.
    + assert (H0 : In (Znth (Zlength (sl lens) - 1) (sl lens)) (sl lens)) by (apply Znth_In; lia).
      apply Hsl_ok in H0. destruct H0 as [H0 H0'].
      pose proof (sorted_maxlen_ge lens _ H0).
      destruct (sorted_maxlen_in lens) as [Hm|Hm]; [contradiction|].
      pose proof (sorted_maxlen_nonneg lens).
      assert (Hm' : In (maxlen lens) (sl lens)) by (apply Hsl_ok; split; auto; lia).
      apply In_Znth in Hm'. destruct Hm' as [k [Hk Hk']].
      specialize (HSS k (Zlength (sl lens) - 1) ltac:(lia) ltac:(lia)). lia.
Qed.
