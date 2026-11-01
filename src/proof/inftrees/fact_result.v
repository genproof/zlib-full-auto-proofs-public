(* Proof of fact_result (facts.v), shared part: a pure fact about the model of inflate_table (model.v)
   against the reference model of harness/common.h (ref.v).  The other parts and the assembly
   (fact_result_ok) are in part_*.v. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.inftrees.facts.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* Abstract view of a code: the lengths in the order of work[] (sorted), the Kraft prefix sums,
   the root prefix of each code, the longest code under each root prefix.                         *)

(* The lengths of the sorted symbols: ls_i = lens[work[i]]. *)
Definition sl (lens: list Z) : list Z := map (fun s => Znth s lens) (sorted_syms lens).

(* Kraft sum of a list of lengths 1..15, in units of 2^-15. *)
Definition ksum (ls: list Z) : Z := fold_right (fun l a => 2 ^ (MAXBITS - l) + a) 0 ls.

(* K_i: the Kraft sum of the first i sorted lengths = the canonical code of symbol i, left-aligned
   on 15 bits. *)
Definition kpre (ls: list Z) (i: Z) : Z := ksum (sublist 0 i ls).

(* The longest length > root among the sorted positions whose root prefix K_i / 2^(15-root) is q
   (0 when none). *)
Definition gmax (ls: list Z) (root q: Z) : Z :=
  fold_left (fun g i => let l := Znth i ls in
               if (root <? l) && (kpre ls i / 2 ^ (MAXBITS - root) =? q) then Z.max g l else g)
            (zseq 0 (length ls)) 0.

(* The size of the sub-table under root prefix q (0 when none), and the sum over q < n. *)
Definition fq (ls: list Z) (root q: Z) : Z :=
  let g := gmax ls root q in if g =? 0 then 0 else 2 ^ (g - root).
Definition sumf (ls: list Z) (root: Z) (n: nat) : Z :=
  fold_left (fun t q => t + fq ls root q) (zseq 0 n) 0.

(* ---------------------------------------------------------------------------------------------- *)
(* The parts of the proof.  Each `*_stmt` is a Prop proved by its own lemma: classify_ok below, the
   others in part_<part>.v (sorted_ok2, rfc_ok2, bits_ok2, subbits_ok2, size_ok2), which Require this
   file; part_result.v assembles fact_result_ok.  A part that needs another one takes it as a hypothesis. *)

(* Classification: max/min against ref.v's longest/shortest, and the `left` loop is the Kraft test. *)
Definition classify_stmt : Prop :=
  forall lens, Forall (fun l => 0 <= l <= MAXBITS) lens ->
  maxlen lens = longest lens /\
  (maxlen lens <> 0 -> minlen lens = shortest lens) /\
  match left_final (counts lens) with
  | None => 2 ^ MAXBITS < kraft lens
  | Some lft => lft = 2 ^ MAXBITS - kraft lens
  end.

(* The sorted symbols work[] and their lengths. *)
Definition sorted_stmt : Prop :=
  forall lens, Forall (fun l => 0 <= l <= MAXBITS) lens ->
  Forall (fun s => 0 <= s < Zlength lens) (sorted_syms lens) /\
  Forall (fun l => 1 <= l <= MAXBITS) (sl lens) /\
  (forall a b, 0 <= a -> a <= b < Zlength (sl lens) -> Znth a (sl lens) <= Znth b (sl lens)) /\
  (forall s, 0 <= s < Zlength lens -> Znth s lens <> 0 -> In s (sorted_syms lens)) /\
  (forall l, 1 <= l <= MAXBITS -> Znth l (counts lens) = count_len (sl lens) l) /\
  Zlength (counts lens) = 16 /\
  ksum (sl lens) = kraft lens /\
  (sl lens = [] <-> maxlen lens = 0) /\
  (sl lens <> [] -> Znth 0 (sl lens) = minlen lens /\
                    Znth (Zlength (sl lens) - 1) (sl lens) = maxlen lens).

(* The canonical code (RFC 1951 3.2.2) of the i-th sorted symbol, left-aligned on 15 bits, is the
   Kraft sum of the lengths before it. *)
Definition rfc_stmt : Prop :=
  forall lens, Forall (fun l => 0 <= l <= MAXBITS) lens ->
  forall i, 0 <= i < Zlength (sl lens) ->
  rfc_code lens (Znth i (sorted_syms lens)) * 2 ^ (MAXBITS - Znth i (sl lens)) = kpre (sl lens) i.

(* Bit reversal (ref.v) and the backwards increment of inftrees.c (model.v). *)
Definition bits_stmt : Prop :=
  (forall c n, 0 <= n -> 0 <= reverse_bits c n < 2 ^ n) /\
  (forall c n r, 0 <= c -> 0 <= r <= n ->
     Z.land (reverse_bits c n) (2 ^ r - 1) = reverse_bits (c / 2 ^ (n - r)) r) /\
  (forall c r, 0 <= r -> 0 <= c < 2 ^ r -> reverse_bits (reverse_bits c r) r = c) /\
  (forall c n d, 0 <= c -> 0 <= n -> 0 <= d -> reverse_bits (c * 2 ^ d) (n + d) = reverse_bits c n) /\
  (forall c n, 1 <= n <= MAXBITS -> 0 <= c < 2 ^ n ->
     next_huff (reverse_bits c n) n = reverse_bits ((c + 1) mod 2 ^ n) n).

(* The look-ahead of inftrees.c (`curr` of a new sub-table, model.v sub_bits) on the remaining
   counts is the longest length under the root prefix of a group start, minus root
   (complete code). *)
Definition subbits_stmt : Prop :=
  forall ls root i cnt,
  Forall (fun l => 1 <= l <= MAXBITS) ls ->
  (forall a b, 0 <= a -> a <= b < Zlength ls -> Znth a ls <= Znth b ls) ->
  ksum ls = 2 ^ MAXBITS ->
  0 <= root <= MAXBITS -> 0 <= i < Zlength ls -> root < Znth i ls ->
  kpre ls i mod 2 ^ (MAXBITS - root) = 0 ->
  Zlength cnt = 16 ->
  (forall l, 1 <= l <= MAXBITS -> Znth l cnt = count_len (sublist i (Zlength ls) ls) l) ->
  sub_bits (Znth i ls) root (Znth (Zlength ls - 1) ls) cnt
    = gmax ls root (kpre ls i / 2 ^ (MAXBITS - root)) - root.

(* ref.v's two_level_size is 2^root plus the sub-table sizes per root prefix. *)
Definition size_stmt : Prop :=
  forall lens root, Forall (fun l => 0 <= l <= MAXBITS) lens ->
  kraft lens <= 2 ^ MAXBITS -> 0 <= root <= MAXBITS ->
  two_level_size lens root = 2 ^ root + sumf (sl lens) root (Z.to_nat (2 ^ root)).

(* ---------------------------------------------------------------------------------------------- *)
(* classify_stmt.                                                                                  *)

Lemma longest_fold : forall lens a, 0 <= a ->
  fold_left (fun m l => if m <? l then l else m) lens a = Z.max a (fold_right Z.max 0 lens).
Proof.
  induction lens as [|x xs IH]; intros a Ha; simpl.
  - lia.
  - rewrite IH.
    + assert (0 <= fold_right Z.max 0 xs) by (clear; induction xs; simpl; lia).
      destruct (a <? x) eqn:E; [apply Z.ltb_lt in E | apply Z.ltb_ge in E]; lia.
    + destruct (a <? x) eqn:E; [apply Z.ltb_lt in E|]; lia.
Qed.

Lemma maxlen_longest : forall lens, maxlen lens = longest lens.
Proof.
  intros. unfold longest, maxlen. rewrite longest_fold by lia.
  assert (0 <= fold_right Z.max 0 lens) by (clear; induction lens; simpl; lia). lia.
Qed.

Lemma minlen_range : forall lens, Forall (fun l => 0 <= l <= MAXBITS) lens ->
  1 <= minlen lens <= 16 /\ (minlen lens = 16 <-> maxlen lens = 0).
Proof.
  induction lens as [|x xs IH]; intros H; simpl; [unfold MAXBITS; lia|].
  inversion H; subst. destruct (IH H3) as [IH1 IH2].
  fold (minlen xs) (maxlen xs). unfold MAXBITS in *.
  destruct (x =? 0) eqn:E; [apply Z.eqb_eq in E | apply Z.eqb_neq in E]; split; try lia.
  assert (0 <= maxlen xs) by (clear; induction xs; simpl; lia). lia.
Qed.

Lemma shortest_fold : forall lens m, Forall (fun l => 0 <= l <= MAXBITS) lens -> 0 <= m <= MAXBITS ->
  fold_left (fun m l => if negb (l =? 0) && ((m =? 0) || (l <? m)) then l else m) lens m =
  if m =? 0 then (if minlen lens =? 16 then 0 else minlen lens) else Z.min m (minlen lens).
Proof.
  induction lens as [|x xs IH]; intros m H Hm; simpl.
  - destruct (m =? 0) eqn:E; [apply Z.eqb_eq in E; simpl; lia|]. unfold MAXBITS in *; simpl; lia.
  - inversion H; subst. destruct (minlen_range xs H3) as [R1 R2].
    fold (minlen xs).
    unfold MAXBITS in *.
    destruct (x =? 0) eqn:Ex; [apply Z.eqb_eq in Ex | apply Z.eqb_neq in Ex]; simpl.
    + rewrite IH by (auto; lia). reflexivity.
    + destruct (m =? 0) eqn:Em; [apply Z.eqb_eq in Em | apply Z.eqb_neq in Em]; simpl.
      * rewrite IH by (auto; lia).
        destruct (x =? 0) eqn:E2; [lia|].
        destruct (minlen xs =? 16) eqn:E3; [apply Z.eqb_eq in E3 | apply Z.eqb_neq in E3];
        destruct (Z.min x (minlen xs) =? 16) eqn:E4; [apply Z.eqb_eq in E4 | apply Z.eqb_neq in E4 | apply Z.eqb_eq in E4 | apply Z.eqb_neq in E4]; lia.
      * destruct (x <? m) eqn:E5; [apply Z.ltb_lt in E5 | apply Z.ltb_ge in E5];
        rewrite IH by (auto; lia);
        destruct (x =? 0) eqn:E2; try lia;
        destruct (m =? 0) eqn:E6; try (apply Z.eqb_eq in E6; lia); lia.
Qed.

Lemma minlen_shortest : forall lens, Forall (fun l => 0 <= l <= MAXBITS) lens ->
  maxlen lens <> 0 -> minlen lens = shortest lens.
Proof.
  intros. unfold shortest. rewrite shortest_fold by (auto; unfold MAXBITS; lia). simpl.
  destruct (minlen_range lens H) as [R1 R2].
  destruct (minlen lens =? 16) eqn:E; [apply Z.eqb_eq in E|]; lia.
Qed.

(* Weighted sum of f over len .. len+k-1: sum_j f (len+j) * 2^(k-1-j). *)
Fixpoint wsum (f: Z -> Z) (k: nat) (len: Z) : Z :=
  match k with O => 0 | S k' => f len * 2 ^ Z.of_nat k' + wsum f k' (len + 1) end.

Lemma left_loop_wsum : forall k len left cnt, 0 <= left ->
  (forall l, len <= l < len + Z.of_nat k -> 0 <= Znth l cnt) ->
  let F := left * 2 ^ Z.of_nat k - wsum (fun l => Znth l cnt) k len in
  left_loop k len left cnt = if F <? 0 then None else Some F.
Proof.
  induction k as [|k IH]; intros len left cnt Hl Hc F; subst F.
  - simpl. destruct (left * 1 - 0 <? 0) eqn:E; [apply Z.ltb_lt in E; lia|]. f_equal; lia.
  - cbn [left_loop wsum].
    assert (Hw: forall k len, (forall l, len <= l < len + Z.of_nat k -> 0 <= Znth l cnt) ->
                0 <= wsum (fun l => Znth l cnt) k len).
    { clear. induction k; intros; simpl; [lia|].
      assert (0 <= Znth len cnt) by (apply H; lia).
      assert (0 <= wsum (fun l => Znth l cnt) k (len + 1)) by (apply IHk; intros; apply H; lia).
      nia. }
    assert (Hp: 2 ^ Z.of_nat (S k) = 2 * 2 ^ Z.of_nat k).
    { rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia. }
    rewrite Hp.
    destruct (2 * left - Znth len cnt <? 0) eqn:E.
    + apply Z.ltb_lt in E.
      assert (0 <= wsum (fun l => Znth l cnt) k (len + 1)) by (apply Hw; intros; apply Hc; lia).
      assert (0 < 2 ^ Z.of_nat k) by lia.
      destruct (left * (2 * 2 ^ Z.of_nat k) - (Znth len cnt * 2 ^ Z.of_nat k + wsum (fun l => Znth l cnt) k (len + 1)) <? 0) eqn:E2;
        [reflexivity | apply Z.ltb_ge in E2; nia].
    + apply Z.ltb_ge in E. rewrite IH by (auto; intros; apply Hc; lia).
      replace (left * (2 * 2 ^ Z.of_nat k) - (Znth len cnt * 2 ^ Z.of_nat k + wsum (fun l => Znth l cnt) k (len + 1)))
        with ((2 * left - Znth len cnt) * 2 ^ Z.of_nat k - wsum (fun l => Znth l cnt) k (len + 1)) by ring.
      reflexivity.
Qed.

Lemma wsum_ext : forall f g k len, (forall l, len <= l < len + Z.of_nat k -> f l = g l) ->
  wsum f k len = wsum g k len.
Proof.
  induction k; intros; simpl; auto.
  rewrite H by lia. rewrite (IHk (len + 1)); auto. intros; apply H; lia.
Qed.

Lemma wsum_plus : forall f g k len, wsum (fun l => f l + g l) k len = wsum f k len + wsum g k len.
Proof. induction k; intros; simpl; auto. rewrite IHk. ring. Qed.

Ltac bdestr :=
  repeat match goal with
  | |- context [?a =? ?b] => let E := fresh "E" in destruct (a =? b) eqn:E;
       [apply Z.eqb_eq in E | apply Z.eqb_neq in E]
  | |- context [?a <=? ?b] => let E := fresh "E" in destruct (a <=? b) eqn:E;
       [apply Z.leb_le in E | apply Z.leb_gt in E]
  | |- context [?a <? ?b] => let E := fresh "E" in destruct (a <? b) eqn:E;
       [apply Z.ltb_lt in E | apply Z.ltb_ge in E]
  end.

Lemma wsum_ind : forall x k len, wsum (fun l => if l =? x then 1 else 0) k len =
  if (len <=? x) && (x <? len + Z.of_nat k) then 2 ^ (len + Z.of_nat k - 1 - x) else 0.
Proof.
  induction k; intros.
  - cbn [wsum]. simpl Z.of_nat. bdestr; simpl; lia.
  - cbn [wsum]. rewrite IHk. rewrite Nat2Z.inj_succ.
    bdestr; cbn [andb]; subst; try lia;
      rewrite ?Z.mul_1_l, ?Z.mul_0_l, ?Z.add_0_r, ?Z.add_0_l; f_equal; lia.
Qed.

Lemma count_len_cons : forall x xs l, count_len (x :: xs) l = (if l =? x then 1 else 0) + count_len xs l.
Proof.
  intros. unfold count_len. simpl. destruct (l =? x); rewrite ?Zlength_cons; lia.
Qed.

Lemma kraft_fold : forall lens a, Forall (fun l => 0 <= l <= MAXBITS) lens ->
  fold_left (fun k l => if l =? 0 then k else k + Z.shiftl 1 (MAXBITS - l)) lens a =
  a + fold_right (fun l k => (if l =? 0 then 0 else 2 ^ (MAXBITS - l)) + k) 0 lens.
Proof.
  induction lens as [|x xs IH]; intros a H; cbn [fold_left fold_right]; [lia|].
  inversion H; subst. rewrite IH by auto. destruct (x =? 0); [lia|].
  rewrite Z.shiftl_1_l. lia.
Qed.

Lemma kraft_wsum : forall lens, Forall (fun l => 0 <= l <= MAXBITS) lens ->
  kraft lens = wsum (count_len lens) 15 1.
Proof.
  intros. unfold kraft. rewrite kraft_fold by auto. rewrite Z.add_0_l.
  induction lens as [|x xs IH]; cbn [fold_right].
  - reflexivity.
  - inversion H; subst. rewrite IH by auto.
    rewrite (wsum_ext (count_len (x :: xs)) (fun l => (if l =? x then 1 else 0) + count_len xs l))
      by (intros; apply count_len_cons).
    rewrite wsum_plus, wsum_ind. unfold MAXBITS in *. simpl Z.of_nat.
    bdestr; cbn [andb]; subst; try lia.
    do 2 f_equal; try lia.
Qed.

Lemma Znth_zseq : forall n start i, 0 <= i < Z.of_nat n -> Znth i (zseq start n) = start + i.
Proof.
  induction n; intros; simpl in *; [lia|].
  destruct (Z.eq_dec i 0).
  - subst. rewrite Znth_0_cons. lia.
  - rewrite Znth_pos_cons by lia. rewrite IHn by lia. lia.
Qed.

Lemma Zlength_zseq : forall n start, Zlength (zseq start n) = Z.of_nat n.
Proof. induction n; intros; simpl; [reflexivity|]. rewrite Zlength_cons, IHn. lia. Qed.

Lemma Znth_counts : forall lens l, 0 <= l < 16 -> Znth l (counts lens) = count_len lens l.
Proof.
  intros. unfold counts. rewrite Znth_map by (rewrite Zlength_zseq; simpl; lia).
  rewrite Znth_zseq by (simpl; lia). f_equal; lia.
Qed.

Lemma classify_proof : classify_stmt.
Proof.
  intros lens H. split; [apply maxlen_longest|]. split; [apply minlen_shortest; auto|].
  unfold left_final.
  rewrite left_loop_wsum.
  2: lia.
  2: { intros. rewrite Znth_counts by (simpl in *; lia). unfold count_len. apply Zlength_nonneg. }
  rewrite (wsum_ext _ (count_len lens)) by (intros; apply Znth_counts; simpl in *; lia).
  rewrite <- kraft_wsum by auto. simpl Z.of_nat. unfold MAXBITS.
  destruct (1 * 2 ^ 15 - kraft lens <? 0) eqn:E; [apply Z.ltb_lt in E | apply Z.ltb_ge in E]; lia.
Qed.

Lemma classify_ok : classify_stmt.
Proof.
  exact classify_proof.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Kraft prefixes, root prefixes and gmax.                                                        *)

Lemma ksum_app : forall a b, ksum (a ++ b) = ksum a + ksum b.
Proof.
  intros a b; induction a as [|x a IH]; unfold ksum in *; cbn [fold_right app]; [lia|].
  rewrite IH; lia.
Qed.

Lemma ksum_nonneg : forall ls, 0 <= ksum ls.
Proof.
  induction ls; unfold ksum in *; cbn [fold_right]; [lia|].
  assert (0 <= 2 ^ (MAXBITS - a)) by (apply Z.pow_nonneg; lia). lia.
Qed.

Lemma kpre_0 : forall ls, kpre ls 0 = 0.
Proof. intros. unfold kpre. rewrite sublist_nil'. reflexivity. lia. Qed.

Lemma kpre_S : forall ls i, 0 <= i < Zlength ls ->
  kpre ls (i + 1) = kpre ls i + 2 ^ (MAXBITS - Znth i ls).
Proof.
  intros. unfold kpre. rewrite (sublist_split 0 i (i + 1)) by lia.
  rewrite ksum_app, sublist_len_1 by lia.
  replace (ksum [Znth i ls]) with (2 ^ (MAXBITS - Znth i ls)) by (unfold ksum; cbn [fold_right]; lia).
  reflexivity.
Qed.

Lemma kpre_full : forall ls, kpre ls (Zlength ls) = ksum ls.
Proof. intros. unfold kpre. rewrite sublist_same by lia. reflexivity. Qed.

Lemma kpre_split : forall ls i j, 0 <= i <= j -> j <= Zlength ls ->
  kpre ls j = kpre ls i + ksum (sublist i j ls).
Proof.
  intros. unfold kpre. rewrite (sublist_split 0 i j) by lia. apply ksum_app.
Qed.

Lemma kpre_mono : forall ls i j, 0 <= i <= j -> j <= Zlength ls -> kpre ls i <= kpre ls j.
Proof. intros. rewrite (kpre_split ls i j) by lia. pose proof (ksum_nonneg (sublist i j ls)). lia. Qed.

Lemma kpre_next_le : forall ls i, 0 <= i < Zlength ls ->
  kpre ls i + 2 ^ (MAXBITS - Znth i ls) <= ksum ls.
Proof.
  intros. rewrite <- kpre_S by lia. rewrite <- kpre_full. apply kpre_mono; lia.
Qed.

(* sums of powers 2^(15 - l) with l <= d are multiples of 2^(15 - d) *)
Lemma ksum_div : forall ls d, d <= MAXBITS -> Forall (fun l => l <= d) ls ->
  ksum ls mod 2 ^ (MAXBITS - d) = 0.
Proof.
  induction ls as [|x xs IH]; intros d Hd H; unfold ksum in *; cbn [fold_right].
  - apply Z.mod_0_l. apply Z.pow_nonzero; lia.
  - inversion H; subst.
    replace (2 ^ (MAXBITS - x)) with (2 ^ (d - x) * 2 ^ (MAXBITS - d))
      by (rewrite <- Z.pow_add_r by (unfold MAXBITS in *; lia); f_equal; lia).
    rewrite Z.add_mod by (apply Z.pow_nonzero; lia).
    rewrite Z.mod_mul by (apply Z.pow_nonzero; lia).
    rewrite IH by auto. reflexivity.
Qed.

Section Sorted.
Variable ls : list Z.
Hypothesis Hrange : Forall (fun l => 1 <= l <= MAXBITS) ls.
Hypothesis Hsorted : forall a b, 0 <= a -> a <= b < Zlength ls -> Znth a ls <= Znth b ls.

Lemma ls_range : forall i, 0 <= i < Zlength ls -> 1 <= Znth i ls <= MAXBITS.
Proof. intros. eapply Forall_forall in Hrange; [exact Hrange|]. apply Znth_In; lia. Qed.

Lemma kpre_div : forall i d, 0 <= i <= Zlength ls -> d <= MAXBITS ->
  (forall j, 0 <= j < i -> Znth j ls <= d) -> kpre ls i mod 2 ^ (MAXBITS - d) = 0.
Proof.
  intros. unfold kpre. apply ksum_div; auto.
  apply Forall_forall. intros x Hx. apply In_Znth in Hx. destruct Hx as [j [Hj Hx]].
  rewrite Zlength_sublist in Hj by lia. rewrite Znth_sublist in Hx by lia. subst. apply H1. lia.
Qed.

Lemma kpre_div_self : forall i, 0 <= i < Zlength ls -> kpre ls i mod 2 ^ (MAXBITS - Znth i ls) = 0.
Proof.
  intros. apply kpre_div; try lia. pose proof (ls_range i H); lia.
  intros. apply Hsorted; lia.
Qed.

End Sorted.

Lemma fold_max_props : forall (c: Z -> bool) (v: Z -> Z) xs a,
  let F := fold_left (fun g i => if c i then Z.max g (v i) else g) xs a in
  a <= F /\ (forall i, In i xs -> c i = true -> v i <= F) /\
  (F = a \/ exists i, In i xs /\ c i = true /\ F = v i).
Proof.
  intros c v xs. induction xs as [|x xs IH]; intros a F; subst F; cbn [fold_left].
  - split; [lia|]. split; [intros; contradiction|]. auto.
  - destruct (c x) eqn:Ec.
    + destruct (IH (Z.max a (v x))) as [H1 [H2 H3]]. split; [lia|]. split.
      * intros i [Hi|Hi] Hc; [subst; lia|]. apply H2; auto.
      * destruct H3 as [H3|[i [Hi [Hc H3]]]].
        -- rewrite H3. destruct (Z.max_spec a (v x)) as [[_ ->]|[_ ->]]; [right; exists x; simpl; auto|left; auto].
        -- right. exists i. simpl; auto.
    + destruct (IH a) as [H1 [H2 H3]]. split; [lia|]. split.
      * intros i [Hi|Hi] Hc; [subst; congruence|]. apply H2; auto.
      * destruct H3 as [H3|[i [Hi [Hc H3]]]]; auto. right. exists i. simpl; auto.
Qed.

Lemma In_zseq : forall n start i, In i (zseq start n) <-> start <= i < start + Z.of_nat n.
Proof.
  induction n; intros; cbn [zseq In]; [lia|]. rewrite IHn. lia.
Qed.

Lemma zseq_S : forall n start, zseq start (S n) = zseq start n ++ [start + Z.of_nat n].
Proof.
  induction n; intros; [cbn; f_equal; lia|].
  change (zseq start (S (S n))) with (start :: zseq (start + 1) (S n)).
  rewrite IHn. cbn [zseq app]. do 3 f_equal. lia.
Qed.

Definition grp_cond (ls: list Z) (root q j: Z) : bool :=
  (root <? Znth j ls) && (kpre ls j / 2 ^ (MAXBITS - root) =? q).

Lemma gmax_props : forall ls root q,
  0 <= gmax ls root q /\
  (forall j, 0 <= j < Zlength ls -> root < Znth j ls -> kpre ls j / 2 ^ (MAXBITS - root) = q ->
     Znth j ls <= gmax ls root q) /\
  (gmax ls root q = 0 \/ exists j, 0 <= j < Zlength ls /\ root < Znth j ls /\
     kpre ls j / 2 ^ (MAXBITS - root) = q /\ gmax ls root q = Znth j ls).
Proof.
  intros. unfold gmax.
  destruct (fold_max_props (grp_cond ls root q) (fun j => Znth j ls) (zseq 0 (length ls)) 0)
    as [H1 [H2 H3]].
  unfold grp_cond in *. split; [auto|]. split.
  - intros. apply H2. apply In_zseq. rewrite Zlength_correct in H. lia.
    rewrite andb_true_iff, Z.ltb_lt, Z.eqb_eq. auto.
  - destruct H3 as [H3|[j [Hj [Hc H3]]]]; [left; auto|right].
    apply In_zseq in Hj. rewrite andb_true_iff, Z.ltb_lt, Z.eqb_eq in Hc.
    exists j. rewrite Zlength_correct. split; [lia|]. tauto.
Qed.

Lemma fq_nonneg : forall ls root q, 0 <= fq ls root q.
Proof.
  intros. unfold fq. destruct (gmax ls root q =? 0); [lia|]. apply Z.pow_nonneg; lia.
Qed.

Lemma fq_nonzero : forall ls root q, fq ls root q <> 0 ->
  exists j, 0 <= j < Zlength ls /\ root < Znth j ls /\ kpre ls j / 2 ^ (MAXBITS - root) = q.
Proof.
  intros. unfold fq in H. destruct (gmax_props ls root q) as [_ [_ [H3|[j H3]]]].
  - rewrite H3 in H. simpl in H. congruence.
  - exists j. tauto.
Qed.

Definition sumq (ls: list Z) (root n: Z) : Z := sumf ls root (Z.to_nat n).

Lemma sumf_S : forall ls root n, sumf ls root (S n) = sumf ls root n + fq ls root (Z.of_nat n).
Proof.
  intros. unfold sumf. rewrite zseq_S, fold_left_app. reflexivity.
Qed.

Lemma sumq_succ : forall ls root n, 0 <= n -> sumq ls root (n + 1) = sumq ls root n + fq ls root n.
Proof.
  intros. unfold sumq. rewrite Z2Nat.inj_add by lia. rewrite Nat.add_1_r, sumf_S.
  rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma sumq_zero : forall ls root a b, 0 <= a <= b ->
  (forall q, a <= q < b -> fq ls root q = 0) -> sumq ls root b = sumq ls root a.
Proof.
  intros ls root a b Hab H.
  replace b with (a + Z.of_nat (Z.to_nat (b - a))) in * by lia.
  induction (Z.to_nat (b - a)) as [|k IH].
  - f_equal. lia.
  - rewrite Nat2Z.inj_succ, <- Z.add_1_r, Z.add_assoc, sumq_succ by lia.
    rewrite IH by (lia || (intros; apply H; lia)). rewrite H by lia. lia.
Qed.

Lemma sumq_mono : forall ls root a b, 0 <= a <= b -> sumq ls root a <= sumq ls root b.
Proof.
  intros ls root a b Hab.
  replace b with (a + Z.of_nat (Z.to_nat (b - a))) in * by lia.
  induction (Z.to_nat (b - a)) as [|k IH].
  - replace (a + Z.of_nat 0) with a by lia. lia.
  - rewrite Nat2Z.inj_succ, <- Z.add_1_r, Z.add_assoc, sumq_succ by lia.
    pose proof (fq_nonneg ls root (a + Z.of_nat k)). lia.
Qed.

Lemma sumq_nonneg : forall ls root a, 0 <= a -> 0 <= sumq ls root a.
Proof.
  intros. replace 0 with (sumq ls root 0) at 1 by reflexivity. apply sumq_mono. lia.
Qed.

(* The do/while fill writes below U. *)
Lemma rep_fill_props : forall n t base incr e U,
  (forall k, 0 <= k < Z.of_nat n -> 0 <= base + k * incr < U) -> entry_ok e -> Forall entry_ok t ->
  Zlength (rep_fill t base incr n e) = Zlength t /\
  Forall entry_ok (rep_fill t base incr n e) /\
  (forall j, U <= j -> Znth j (rep_fill t base incr n e) = Znth j t).
Proof.
  induction n; intros t base incr e U Hk He Ht; cbn [rep_fill].
  - auto.
  - assert (Hb: 0 <= base + Z.of_nat n * incr < U) by (apply Hk; lia).
    destruct (IHn (upd_Znth (base + Z.of_nat n * incr) t e) base incr e U) as [H1 [H2 H3]].
    + intros; apply Hk; lia.
    + auto.
    + apply Forall_upd_Znth; auto.
    + split; [|split; auto].
      * rewrite H1. destruct (Z_lt_dec (base + Z.of_nat n * incr) (Zlength t)).
        -- apply upd_Znth_Zlength. lia.
        -- rewrite upd_Znth_out_of_range by lia. auto.
      * intros. rewrite H3 by auto.
        destruct (Z_lt_dec (base + Z.of_nat n * incr) (Zlength t)).
        -- apply upd_Znth_diff'; lia.
        -- rewrite upd_Znth_out_of_range by lia. auto.
Qed.

Lemma Znth_Forall_def : forall {A} {d: Inhabitant A} (P: A -> Prop) l i,
  Forall P l -> P d -> P (Znth i l).
Proof.
  intros. destruct (Z_lt_dec i 0); [rewrite Znth_underflow; auto|].
  destruct (Z_lt_dec i (Zlength l)); [|rewrite Znth_overflow; auto].
  eapply Forall_forall; [exact H|]. apply Znth_In. lia.
Qed.

Lemma sym_entry_ok : forall type s bits, 0 <= s <= 65535 -> 0 <= bits <= 255 ->
  entry_ok (sym_entry type s bits).
Proof.
  intros. unfold sym_entry, entry_ok.
  destruct (s + 1 <? match_of type); [cbn; lia|].
  destruct (match_of type <=? s); [|cbn; lia]. cbn [e_op e_bits e_val].
  split; [|split; [lia|]].
  - apply (@Znth_Forall_def Z 0 (fun x => 0 <= x <= 255)); [|lia].
    unfold extra_of. destruct (type =? CODES); [constructor|].
    destruct (type =? LENS); unfold lext, dext; repeat constructor; lia.
  - apply (@Znth_Forall_def Z 0 (fun x => 0 <= x <= 65535)); [|lia].
    unfold base_of. destruct (type =? CODES); [constructor|].
    destruct (type =? LENS); unfold lbase, dbase; repeat constructor; lia.
Qed.

Lemma reverse_loop_0 : forall k i, reverse_loop k i 0 0 = 0.
Proof. induction k; intros; cbn [reverse_loop]; auto. rewrite Z.shiftr_0_l, Z.land_0_l. apply IHk. Qed.

Lemma reverse_bits_0 : forall n, reverse_bits 0 n = 0.
Proof. intros. apply reverse_loop_0. Qed.

Lemma div_succ : forall c m, 0 < m -> (c + 1) / m = c / m \/ (c + 1) mod m = 0.
Proof.
  intros. destruct (Z.eq_dec ((c + 1) mod m) 0); [right; auto|left].
  pose proof (Z.div_mod c m ltac:(lia)). pose proof (Z.mod_pos_bound c m H).
  pose proof (Z.div_mod (c + 1) m ltac:(lia)). pose proof (Z.mod_pos_bound (c + 1) m H).
  assert (c mod m + 1 < m \/ c mod m + 1 = m) as [Hl|Hl] by lia.
  - symmetry. apply Z.div_unique with (c mod m + 1); lia.
  - exfalso. apply n. symmetry. apply Z.mod_unique with (c / m + 1); lia.
Qed.

Lemma count_len_app : forall a b x, count_len (a ++ b) x = count_len a x + count_len b x.
Proof. intros. unfold count_len. rewrite filter_app, Zlength_app. reflexivity. Qed.

Lemma count_len_In : forall xs x, In x xs -> 0 < count_len xs x.
Proof.
  induction xs; intros; [contradiction|]. rewrite count_len_cons.
  destruct H; [subst; rewrite Z.eqb_refl; unfold count_len; pose proof (Zlength_nonneg (filter (Z.eqb x) xs)); lia|].
  specialize (IHxs x H). destruct (x =? a); lia.
Qed.

Lemma count_len_nz : forall xs x, count_len xs x <> 0 -> In x xs.
Proof.
  induction xs; intros; [exfalso; apply H; reflexivity|]. rewrite count_len_cons in H.
  destruct (x =? a) eqn:E; [apply Z.eqb_eq in E; subst; left; auto|right; apply IHxs; lia].
Qed.

Lemma count_len_nil : forall x, count_len [] x = 0.
Proof. reflexivity. Qed.

Lemma count_len_sublist_cons : forall ls i x, 0 <= i < Zlength ls ->
  count_len (sublist i (Zlength ls) ls) x =
  (if x =? Znth i ls then 1 else 0) + count_len (sublist (i + 1) (Zlength ls) ls) x.
Proof.
  intros. rewrite (sublist_split i (i + 1)) by lia. rewrite sublist_len_1 by lia.
  rewrite count_len_app, count_len_cons, count_len_nil. lia.
Qed.

Lemma pow2_shiftl : forall n, 0 <= n -> Z.shiftl 1 n = 2 ^ n.
Proof. intros. apply Z.shiftl_1_l. Qed.

Definition pfx (ls: list Z) (root i: Z) : Z := kpre ls i / 2 ^ (MAXBITS - root).

(* The writes of the do/while fill of one iteration lie in [next, next + 2^curr). *)
Lemma fill_bounds : forall huff len drop curr next k,
  0 <= drop <= len -> len - drop <= curr -> 0 <= huff < 2 ^ len -> 0 <= next ->
  0 <= k < Z.shiftl 1 curr / Z.shiftl 1 (len - drop) ->
  0 <= next + Z.shiftr huff drop + k * Z.shiftl 1 (len - drop) < next + 2 ^ curr.
Proof.
  intros. rewrite !pow2_shiftl in * by lia. rewrite Z.shiftr_div_pow2 by lia.
  replace (2 ^ curr) with (2 ^ (curr - (len - drop)) * 2 ^ (len - drop)) in *
    by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  rewrite Z.div_mul in H3 by (apply Z.pow_nonzero; lia).
  assert (0 < 2 ^ (len - drop)) by (apply Z.pow_pos_nonneg; lia).
  assert (huff / 2 ^ drop < 2 ^ (len - drop)).
  { apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia|].
    rewrite <- Z.pow_add_r by lia. replace (drop + (len - drop)) with len by lia. lia. }
  assert (0 <= huff / 2 ^ drop) by (apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia]).
  nia.
Qed.

Section Loop.
Variables (type: Z) (lens W ls: list Z) (root: Z) (old: list entry).
Hypothesis Hrange : Forall (fun l => 1 <= l <= MAXBITS) ls.
Hypothesis Hsorted : forall a b, 0 <= a -> a <= b < Zlength ls -> Znth a ls <= Znth b ls.
Hypothesis HN : 0 < Zlength ls.
Hypothesis HWls : forall i, 0 <= i < Zlength ls -> Znth (Znth i W) lens = Znth i ls.
Hypothesis HWr : Forall (fun s => 0 <= s <= 65535) W.
Hypothesis Hroot : Znth 0 ls <= root <= Znth (Zlength ls - 1) ls.
Hypothesis Hk : ksum ls <= 2 ^ MAXBITS.
Hypothesis Hinc : ksum ls < 2 ^ MAXBITS -> Znth (Zlength ls - 1) ls <= root.
Hypothesis Htype : 0 <= type <= 2.
Hypothesis Hcodes : type = CODES -> Znth (Zlength ls - 1) ls <= root.
Hypothesis Hcap : (type = LENS -> ENOUGH_LENS <= Zlength old) /\ (type = DISTS -> ENOUGH_DISTS <= Zlength old).
Hypothesis Hcap0 : 2 ^ root <= Zlength old.
Hypothesis Hold : Forall entry_ok old.
Hypothesis Hbits : bits_stmt.
Hypothesis Hsub : subbits_stmt.

Definition total : Z := 2 ^ root + sumq ls root (2 ^ root).

Definition inv (i: Z) (s: state) : Prop :=
  0 <= i < Zlength ls /\ s_sym s = i /\ s_len s = Znth i ls /\
  s_huff s = reverse_bits (kpre ls i / 2 ^ (MAXBITS - Znth i ls)) (Znth i ls) /\
  Zlength (s_cnt s) = 16 /\
  (forall l, 1 <= l <= MAXBITS -> Znth l (s_cnt s) = count_len (sublist i (Zlength ls) ls) l) /\
  (Znth i ls <= root -> s_drop s = 0 /\ s_curr s = root /\ s_next s = 0 /\ s_used s = 2 ^ root /\
                        s_low s = Z.ones 32) /\
  (root < Znth i ls -> s_drop s = root /\ s_low s = reverse_bits (pfx ls root i) root /\
     s_curr s = gmax ls root (pfx ls root i) - root /\
     s_next s = 2 ^ root + sumq ls root (pfx ls root i) /\ s_used s = s_next s + 2 ^ s_curr s) /\
  Zlength (s_tab s) = Zlength old /\ Forall entry_ok (s_tab s) /\
  (forall j, s_used s <= j -> Znth j (s_tab s) = Znth j old) /\ s_used s <= Zlength old.

Lemma l_range : forall i, 0 <= i < Zlength ls -> 1 <= Znth i ls <= MAXBITS.
Proof. apply ls_range; auto. Qed.

Lemma l_le_mx : forall i, 0 <= i < Zlength ls -> Znth i ls <= Znth (Zlength ls - 1) ls.
Proof. intros. apply Hsorted; lia. Qed.

Lemma root_range : 1 <= root <= MAXBITS.
Proof. pose proof (l_range 0). pose proof (l_range (Zlength ls - 1)). lia. Qed.

Lemma pfx_mono : forall i j, 0 <= i <= j -> j <= Zlength ls -> pfx ls root i <= pfx ls root j.
Proof.
  intros. unfold pfx. apply Z.div_le_mono; [pose proof root_range; apply Z.pow_pos_nonneg; unfold MAXBITS in *; lia|].
  apply kpre_mono; lia.
Qed.

Lemma pfx_range : forall i, 0 <= i < Zlength ls -> 0 <= pfx ls root i < 2 ^ root.
Proof.
  intros. pose proof root_range. pose proof (kpre_next_le ls i H).
  pose proof (l_range i H). unfold pfx.
  assert (0 < 2 ^ (MAXBITS - Znth i ls)) by (apply Z.pow_pos_nonneg; lia).
  assert (0 <= kpre ls i) by (unfold kpre; apply ksum_nonneg).
  split; [apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia]|].
  apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia|].
  rewrite <- Z.pow_add_r by lia. replace (MAXBITS - root + root) with MAXBITS by lia. lia.
Qed.


Lemma pow_split : forall a b, 0 <= a -> 0 <= b -> 2 ^ (a + b) = 2 ^ a * 2 ^ b.
Proof. intros. apply Z.pow_add_r; lia. Qed.

Lemma C_facts : forall i, 0 <= i < Zlength ls ->
  let l := Znth i ls in let C := kpre ls i / 2 ^ (MAXBITS - l) in
  0 <= C /\ kpre ls i = C * 2 ^ (MAXBITS - l) /\ kpre ls (i + 1) = (C + 1) * 2 ^ (MAXBITS - l) /\
  C + 1 <= 2 ^ l /\ (i + 1 < Zlength ls -> C + 1 < 2 ^ l).
Proof.
  intros i Hi l C. pose proof (l_range i Hi). fold l in H.
  assert (Hp: 0 < 2 ^ (MAXBITS - l)) by (apply Z.pow_pos_nonneg; lia).
  assert (Hd: kpre ls i mod 2 ^ (MAXBITS - l) = 0) by (apply kpre_div_self; auto).
  assert (HK: kpre ls i = C * 2 ^ (MAXBITS - l)).
  { pose proof (Z.div_mod (kpre ls i) (2 ^ (MAXBITS - l)) ltac:(lia)). subst C. lia. }
  assert (0 <= kpre ls i) by (unfold kpre; apply ksum_nonneg).
  assert (0 <= C) by (subst C; apply Z.div_pos; lia).
  assert (HS: kpre ls (i + 1) = (C + 1) * 2 ^ (MAXBITS - l)) by (rewrite kpre_S by lia; fold l; lia).
  assert (H2: 2 ^ MAXBITS = 2 ^ l * 2 ^ (MAXBITS - l)) by (rewrite <- pow_split by lia; f_equal; lia).
  split; [lia|]. split; [auto|]. split; [auto|]. split.
  - pose proof (kpre_next_le ls i Hi). fold l in H1. nia.
  - intros. pose proof (kpre_next_le ls (i + 1) ltac:(lia)).
    pose proof (l_range (i + 1) ltac:(lia)).
    assert (0 < 2 ^ (MAXBITS - Znth (i + 1) ls)) by (apply Z.pow_pos_nonneg; lia). nia.
Qed.

Lemma huff_next : forall i, 0 <= i -> i + 1 < Zlength ls ->
  next_huff (reverse_bits (kpre ls i / 2 ^ (MAXBITS - Znth i ls)) (Znth i ls)) (Znth i ls) =
  reverse_bits (kpre ls (i + 1) / 2 ^ (MAXBITS - Znth (i + 1) ls)) (Znth (i + 1) ls).
Proof.
  intros i Hi Hi1. destruct (C_facts i ltac:(lia)) as (HC0 & HK & HS & HC1 & HC2).
  specialize (HC2 Hi1).
  set (l := Znth i ls) in *. set (C := kpre ls i / 2 ^ (MAXBITS - l)) in *.
  pose proof (l_range i ltac:(lia)). pose proof (l_range (i + 1) ltac:(lia)).
  assert (Hll: l <= Znth (i + 1) ls) by (apply Hsorted; lia).
  set (l' := Znth (i + 1) ls) in *. fold l in H.
  destruct Hbits as (B1 & B2 & B3 & B4 & B5).
  rewrite B5 by lia. rewrite Z.mod_small by lia.
  rewrite HS.
  replace (2 ^ (MAXBITS - l)) with (2 ^ (l' - l) * 2 ^ (MAXBITS - l'))
    by (rewrite <- pow_split by lia; f_equal; lia).
  rewrite Z.mul_assoc, Z.div_mul by (apply Z.pow_nonzero; lia).
  replace l' with (l + (l' - l)) at 2 by lia. rewrite B4 by lia. reflexivity.
Qed.

Lemma huff_mask : forall i, 0 <= i < Zlength ls -> root <= Znth i ls ->
  Z.land (reverse_bits (kpre ls i / 2 ^ (MAXBITS - Znth i ls)) (Znth i ls)) (Z.shiftl 1 root - 1)
  = reverse_bits (pfx ls root i) root.
Proof.
  intros. pose proof (l_range i H). pose proof root_range.
  destruct Hbits as (B1 & B2 & B3 & B4 & B5).
  rewrite pow2_shiftl by lia. rewrite B2.
  - unfold pfx. rewrite Z.div_div by (first [apply Z.pow_nonzero | apply Z.pow_pos_nonneg]; lia).
    f_equal. f_equal. rewrite <- pow_split by lia. f_equal. lia.
  - apply Z.div_pos; [unfold kpre; apply ksum_nonneg | apply Z.pow_pos_nonneg; lia].
  - lia.
Qed.

Lemma rev_inj : forall a b r, 0 <= r -> 0 <= a < 2 ^ r -> 0 <= b < 2 ^ r ->
  reverse_bits a r = reverse_bits b r -> a = b.
Proof.
  intros. destruct Hbits as (B1 & B2 & B3 & B4 & B5).
  rewrite <- (B3 a r), <- (B3 b r) by lia. congruence.
Qed.

Lemma no_long_before : forall i j, 0 <= j <= i -> i < Zlength ls -> Znth i ls <= root -> Znth j ls <= root.
Proof. intros. pose proof (Hsorted j i). lia. Qed.

(* No long code has a root prefix strictly between pfx i (when i is long) and pfx (i+1). *)
Lemma fq_gap : forall i q, 0 <= i -> i + 1 < Zlength ls ->
  (Znth i ls <= root -> 0 <= q) -> (root < Znth i ls -> pfx ls root i < q) ->
  q < pfx ls root (i + 1) -> fq ls root q = 0.
Proof.
  intros. destruct (Z.eq_dec (fq ls root q) 0); auto. exfalso.
  destruct (fq_nonzero ls root q n) as [j (Hj & Hl & Hp)]. fold (pfx ls root j) in Hp.
  destruct (Z_le_gt_dec j i).
  - destruct (Z_le_gt_dec (Znth i ls) root).
    + pose proof (no_long_before i j). lia.
    + pose proof (pfx_mono j i). lia.
  - pose proof (pfx_mono (i + 1) j). lia.
Qed.

Lemma fq_after : forall i q, 0 <= i < Zlength ls ->
  (forall j, i < j < Zlength ls -> False) ->
  (Znth i ls <= root -> 0 <= q) -> (root < Znth i ls -> pfx ls root i < q) -> fq ls root q = 0.
Proof.
  intros. destruct (Z.eq_dec (fq ls root q) 0); auto. exfalso.
  destruct (fq_nonzero ls root q n) as [j (Hj & Hl & Hp)]. fold (pfx ls root j) in Hp.
  destruct (Z_le_gt_dec j i).
  - destruct (Z_le_gt_dec (Znth i ls) root).
    + pose proof (no_long_before i j). lia.
    + pose proof (pfx_mono j i). lia.
  - apply (H0 j). lia.
Qed.

Lemma gmax_long : forall i, 0 <= i < Zlength ls -> root < Znth i ls ->
  Znth i ls <= gmax ls root (pfx ls root i) <= MAXBITS.
Proof.
  intros. destruct (gmax_props ls root (pfx ls root i)) as (G1 & G2 & G3).
  assert (A: Znth i ls <= gmax ls root (pfx ls root i)) by (apply G2; auto).
  pose proof (l_range i H).
  destruct G3 as [G3|(j & Hj & _ & _ & G3)]; [lia|]. rewrite G3 in *. pose proof (l_range j Hj). lia.
Qed.

Lemma fq_long : forall i, 0 <= i < Zlength ls -> root < Znth i ls ->
  fq ls root (pfx ls root i) = 2 ^ (gmax ls root (pfx ls root i) - root).
Proof.
  intros. pose proof (gmax_long i H H0). pose proof root_range. unfold fq.
  destruct (gmax ls root (pfx ls root i) =? 0) eqn:E; [apply Z.eqb_eq in E; lia|]. auto.
Qed.

Lemma group_start : forall i, 0 <= i -> i + 1 < Zlength ls ->
  (Znth i ls <= root \/ (root < Znth i ls /\ pfx ls root (i + 1) <> pfx ls root i)) ->
  kpre ls (i + 1) mod 2 ^ (MAXBITS - root) = 0.
Proof.
  intros i Hi Hi1 [Hl | [Hl Hp]].
  - apply kpre_div; auto; try lia. pose proof root_range; lia.
    intros. apply (no_long_before i j); lia.
  - destruct (C_facts i ltac:(lia)) as (HC0 & HK & HS & HC1 & HC2).
    set (l := Znth i ls) in *. set (C := kpre ls i / 2 ^ (MAXBITS - l)) in *.
    pose proof (l_range i ltac:(lia)). fold l in H. pose proof root_range.
    assert (HB: 2 ^ (MAXBITS - root) = 2 ^ (l - root) * 2 ^ (MAXBITS - l))
      by (rewrite <- pow_split by lia; f_equal; lia).
    assert (0 < 2 ^ (l - root)) by (apply Z.pow_pos_nonneg; lia).
    assert (0 < 2 ^ (MAXBITS - l)) by (apply Z.pow_pos_nonneg; lia).
    unfold pfx in Hp. rewrite HS, HK, HB in *.
    rewrite !Z.div_mul_cancel_r in Hp by lia.
    rewrite Z.mul_mod_distr_r by lia.
    destruct (div_succ C (2 ^ (l - root))) as [E|E]; [lia|congruence|]. rewrite E. lia.
Qed.


Lemma upd_len : forall {A} i (l: list A) x, Zlength (upd_Znth i l x) = Zlength l.
Proof.
  intros. destruct (Z_le_gt_dec 0 i); [destruct (Z_lt_dec i (Zlength l))|].
  - apply upd_Znth_Zlength. lia.
  - rewrite upd_Znth_out_of_range by lia. auto.
  - rewrite upd_Znth_out_of_range by lia. auto.
Qed.

Lemma upd_frame : forall {A} {d: Inhabitant A} i (l: list A) x j, i < j -> Znth j (upd_Znth i l x) = Znth j l.
Proof.
  intros. destruct (Z_le_gt_dec 0 i); [destruct (Z_lt_dec i (Zlength l))|].
  - apply upd_Znth_diff'; lia.
  - rewrite upd_Znth_out_of_range by lia. auto.
  - rewrite upd_Znth_out_of_range by lia. auto.
Qed.

Lemma ones32 : Z.ones 32 = 4294967295.
Proof. reflexivity. Qed.

Lemma complete_of_long : forall j, 0 <= j < Zlength ls -> root < Znth j ls -> ksum ls = 2 ^ MAXBITS.
Proof.
  intros. pose proof (l_le_mx j H). destruct (Z_lt_le_dec (ksum ls) (2 ^ MAXBITS)); [|lia].
  specialize (Hinc l). lia.
Qed.

Lemma new_table : forall i huff cnt T U Nx D low,
  0 <= i -> i + 1 < Zlength ls -> root < Znth (i + 1) ls ->
  huff = reverse_bits (kpre ls (i + 1) / 2 ^ (MAXBITS - Znth (i + 1) ls)) (Znth (i + 1) ls) ->
  Zlength cnt = 16 ->
  (forall l, 1 <= l <= MAXBITS -> Znth l cnt = count_len (sublist (i + 1) (Zlength ls) ls) l) ->
  U = Nx -> Nx = 2 ^ root + sumq ls root (pfx ls root (i + 1)) -> D = root ->
  kpre ls (i + 1) mod 2 ^ (MAXBITS - root) = 0 ->
  Zlength T = Zlength old -> Forall entry_ok T -> (forall j, U <= j -> Znth j T = Znth j old) ->
  (exists s', (if over type (U + Z.shiftl 1 (sub_bits (Znth (i + 1) ls) D (Znth (Zlength ls - 1) ls) cnt))
     then Full (mkSt huff (i + 1) (Znth (i + 1) ls) (sub_bits (Znth (i + 1) ls) D (Znth (Zlength ls - 1) ls) cnt)
                  D low (U + Z.shiftl 1 (sub_bits (Znth (i + 1) ls) D (Znth (Zlength ls - 1) ls) cnt)) Nx cnt T)
     else Continue (mkSt huff (i + 1) (Znth (i + 1) ls) (sub_bits (Znth (i + 1) ls) D (Znth (Zlength ls - 1) ls) cnt)
                  D (Z.land huff (Z.shiftl 1 root - 1))
                  (U + Z.shiftl 1 (sub_bits (Znth (i + 1) ls) D (Znth (Zlength ls - 1) ls) cnt)) Nx cnt
                  (upd_Znth (Z.land huff (Z.shiftl 1 root - 1)) T
                     (mkE (sub_bits (Znth (i + 1) ls) D (Znth (Zlength ls - 1) ls) cnt) root Nx))))
     = Continue s' /\ inv (i + 1) s') \/
  (exists s', (if over type (U + Z.shiftl 1 (sub_bits (Znth (i + 1) ls) D (Znth (Zlength ls - 1) ls) cnt))
     then Full (mkSt huff (i + 1) (Znth (i + 1) ls) (sub_bits (Znth (i + 1) ls) D (Znth (Zlength ls - 1) ls) cnt)
                  D low (U + Z.shiftl 1 (sub_bits (Znth (i + 1) ls) D (Znth (Zlength ls - 1) ls) cnt)) Nx cnt T)
     else Continue (mkSt huff (i + 1) (Znth (i + 1) ls) (sub_bits (Znth (i + 1) ls) D (Znth (Zlength ls - 1) ls) cnt)
                  D (Z.land huff (Z.shiftl 1 root - 1))
                  (U + Z.shiftl 1 (sub_bits (Znth (i + 1) ls) D (Znth (Zlength ls - 1) ls) cnt)) Nx cnt
                  (upd_Znth (Z.land huff (Z.shiftl 1 root - 1)) T
                     (mkE (sub_bits (Znth (i + 1) ls) D (Znth (Zlength ls - 1) ls) cnt) root Nx))))
     = Full s' /\ over type (s_used s') = true /\ s_used s' <= total /\
     Zlength (s_tab s') = Zlength old /\ Forall entry_ok (s_tab s')).
Proof.
  intros i huff cnt T U Nx D low Hi Hi1 Hl1 Hhuff Hcl Hcnt HU HNx HD Hgs HTl HTok HTfr.
  subst D U.
  pose proof root_range as Hr.
  pose proof (complete_of_long (i + 1) ltac:(lia) Hl1) as Hcomp.
  assert (Hsb: sub_bits (Znth (i + 1) ls) root (Znth (Zlength ls - 1) ls) cnt
               = gmax ls root (pfx ls root (i + 1)) - root).
  { apply Hsub; auto; lia. }
  rewrite Hsb.
  pose proof (gmax_long (i + 1) ltac:(lia) Hl1) as Hg.
  pose proof (pfx_range (i + 1) ltac:(lia)) as Hp.
  set (g := gmax ls root (pfx ls root (i + 1))) in *.
  rewrite pow2_shiftl by lia.
  assert (Hmask: Z.land huff (Z.shiftl 1 root - 1) = reverse_bits (pfx ls root (i + 1)) root).
  { subst huff. apply huff_mask; lia. }
  rewrite Hmask.
  destruct Hbits as (B1 & B2 & B3 & B4 & B5).
  pose proof (B1 (pfx ls root (i + 1)) root ltac:(lia)) as Hrv.
  assert (Hsq: 0 <= sumq ls root (pfx ls root (i + 1))) by (apply sumq_nonneg; lia).
  assert (Htot: Nx + 2 ^ (g - root) <= total).
  { unfold total. subst Nx.
    pose proof (sumq_mono ls root (pfx ls root (i + 1) + 1) (2 ^ root) ltac:(lia)).
    rewrite sumq_succ in H by lia. rewrite fq_long in H by lia. fold g in H. lia. }
  destruct (over type (Nx + 2 ^ (g - root))) eqn:Eo.
  - right. eexists. split; [reflexivity|]. cbn [s_used s_tab]. auto.
  - left. eexists. split; [reflexivity|].
    assert (Hu: Nx + 2 ^ (g - root) <= Zlength old /\ Nx + 2 ^ (g - root) <= 65536).
    { unfold over in Eo. destruct Hcap as [HcL HcD]. unfold CODES, LENS, DISTS, ENOUGH_LENS, ENOUGH_DISTS in *.
      assert (type <> 0) by (intro; subst; pose proof (Hcodes eq_refl); pose proof (l_le_mx (i + 1)); lia).
      assert (type = 1 \/ type = 2) as [-> | ->] by lia; cbn in Eo;
        [destruct (852 <? Nx + 2 ^ (g - root)) eqn:E | destruct (592 <? Nx + 2 ^ (g - root)) eqn:E];
        try discriminate; apply Z.ltb_ge in E;
        [specialize (HcL eq_refl) | specialize (HcD eq_refl)]; lia. }
    assert (0 < 2 ^ (g - root)) by (apply Z.pow_pos_nonneg; lia).
    unfold inv. cbn [s_huff s_sym s_len s_curr s_drop s_low s_used s_next s_cnt s_tab].
    split; [lia|]. split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|].
    split; [intros; lia|]. split.
    + intros _. split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|]. first [reflexivity | f_equal; f_equal; lia].
    + split; [rewrite upd_len; auto|]. split.
      * apply Forall_upd_Znth; auto. unfold entry_ok; cbn [e_op e_bits e_val]. unfold MAXBITS in *.
        assert (2 ^ root <= Nx) by lia. lia.
      * split; [|lia]. intros. rewrite upd_frame by lia. apply HTfr. lia.
Qed.

Lemma step_inv : forall i s, inv i s -> i + 1 < Zlength ls ->
  (exists s', step type lens W root (Znth (Zlength ls - 1) ls) s = Continue s' /\ inv (i + 1) s') \/
  (exists s', step type lens W root (Znth (Zlength ls - 1) ls) s = Full s' /\
     over type (s_used s') = true /\ s_used s' <= total /\
     Zlength (s_tab s') = Zlength old /\ Forall entry_ok (s_tab s')).
Proof.
  intros i s Hinv Hi1.
  destruct s as [huff sym len curr drop low used next cnt tab].
  destruct Hinv as (Hi & Hsym & Hlen & Hhuff & Hcl & Hcnt & Hlow & Hhigh & Htl & Htok & Htfr & Hucap).
  cbn [s_huff s_sym s_len s_curr s_drop s_low s_used s_next s_cnt s_tab] in *.
  subst sym len huff.
  assert (HM: MAXBITS = 15) by reflexivity.
  pose proof (l_range i Hi) as Hl.
  pose proof root_range as Hr.
  assert (Hl' : Znth i ls <= Znth (i + 1) ls) by (apply Hsorted; lia).
  pose proof (l_range (i + 1) ltac:(lia)) as Hl1.
  destruct (C_facts i Hi) as (HC0 & HK & HS & HC1 & HC2). specialize (HC2 Hi1).
  pose proof (huff_next i ltac:(lia) Hi1) as Hhn.
  pose proof Hbits as Hbits'. destruct Hbits' as (B1 & B2 & B3 & B4 & B5).
  set (l := Znth i ls) in *. set (l' := Znth (i + 1) ls) in *.
  set (C := kpre ls i / 2 ^ (MAXBITS - l)) in *.
  assert (Hc: Znth l cnt - 1 = count_len (sublist (i + 1) (Zlength ls) ls) l).
  { rewrite Hcnt by lia. rewrite count_len_sublist_cons by lia. fold l. rewrite Z.eqb_refl. lia. }
  assert (Hlen' : (if Znth l cnt - 1 =? 0 then Znth (Znth (i + 1) W) lens else l) = l').
  { destruct (Znth l cnt - 1 =? 0) eqn:E.
    - apply HWls; lia.
    - apply Z.eqb_neq in E. rewrite Hc in E. apply count_len_nz in E.
      apply In_Znth in E. destruct E as [j [Hj Hj']]. rewrite Zlength_sublist in Hj by lia.
      rewrite Znth_sublist in Hj' by lia.
      assert (l' <= Znth (j + (i + 1)) ls) by (apply Hsorted; lia). lia. }
  assert (Hbrk : (Znth l cnt - 1 =? 0) && (l =? Znth (Zlength ls - 1) ls) = false).
  { destruct (l =? Znth (Zlength ls - 1) ls) eqn:E; [|apply andb_false_r].
    apply Z.eqb_eq in E. rewrite andb_true_r. apply Z.eqb_neq. rewrite Hc.
    assert (l' = l) by (pose proof (l_le_mx (i + 1)); lia).
    assert (In l' (sublist (i + 1) (Zlength ls) ls)).
    { replace l' with (Znth 0 (sublist (i + 1) (Zlength ls) ls)) by (rewrite Znth_sublist by lia; replace (0 + (i + 1)) with (i + 1) by lia; reflexivity).
      apply Znth_In. rewrite Zlength_sublist by lia. lia. }
    pose proof (count_len_In _ _ H0). rewrite H in H1. lia. }
  assert (Hcl' : Zlength (upd_Znth l cnt (Znth l cnt - 1)) = 16) by (rewrite upd_len; lia).
  assert (Hcnt' : forall l0, 1 <= l0 <= MAXBITS ->
            Znth l0 (upd_Znth l cnt (Znth l cnt - 1)) = count_len (sublist (i + 1) (Zlength ls) ls) l0).
  { intros. destruct (Z.eq_dec l0 l).
    - subst l0. rewrite upd_Znth_same by lia. auto.
    - rewrite upd_Znth_diff by lia. rewrite Hcnt by lia. rewrite count_len_sublist_cons by lia. fold l.
      destruct (l0 =? l) eqn:E; [apply Z.eqb_eq in E; lia|lia]. }
  assert (Hdc : 0 <= drop <= l /\ l - drop <= curr /\ 0 <= next /\ used = next + 2 ^ curr /\ 0 <= curr).
  { destruct (Z_le_gt_dec l root) as [L|L].
    - destruct (Hlow L) as (-> & -> & -> & -> & _). lia.
    - destruct (Hhigh ltac:(lia)) as (-> & _ & -> & -> & ->). pose proof (gmax_long i Hi ltac:(lia)).
      pose proof (pfx_range i Hi). pose proof (sumq_nonneg ls root (pfx ls root i)).
      assert (0 < 2 ^ root) by (apply Z.pow_pos_nonneg; lia). fold l in H. lia. }
  destruct Hdc as (Hd & Hdc & Hnx & Hu & Hcu).
  assert (Hhere: entry_ok (sym_entry type (Znth i W) (l - drop))).
  { apply sym_entry_ok; [|lia]. apply (@Znth_Forall_def Z 0 (fun s => 0 <= s <= 65535)); auto. lia. }
  assert (Hcnt0: 0 <= Z.shiftl 1 curr / Z.shiftl 1 (l - drop)).
  { rewrite !pow2_shiftl by lia. apply Z.div_pos; [apply Z.pow_nonneg | apply Z.pow_pos_nonneg]; lia. }
  destruct (rep_fill_props (Z.to_nat (Z.shiftl 1 curr / Z.shiftl 1 (l - drop))) tab
             (next + Z.shiftr (reverse_bits C l) drop) (Z.shiftl 1 (l - drop))
             (sym_entry type (Znth i W) (l - drop)) used) as (T1 & T2 & T3); auto.
  { intros k Hkk. rewrite Z2Nat.id in Hkk by lia. rewrite Hu.
    replace (next + Z.shiftr (reverse_bits C l) drop + k * Z.shiftl 1 (l - drop))
      with (next + Z.shiftr (reverse_bits C l) drop + k * Z.shiftl 1 (l - drop)) by reflexivity.
    apply fill_bounds; auto; try lia. apply B1. lia. }
  set (t1 := rep_fill tab (next + Z.shiftr (reverse_bits C l) drop) (Z.shiftl 1 (l - drop))
               (Z.to_nat (Z.shiftl 1 curr / Z.shiftl 1 (l - drop))) (sym_entry type (Znth i W) (l - drop))) in *.
  unfold step. cbn [s_huff s_sym s_len s_curr s_drop s_low s_used s_next s_cnt s_tab].
  fold t1. rewrite Hbrk, Hlen', Hhn.
  set (huff' := reverse_bits (kpre ls (i + 1) / 2 ^ (MAXBITS - l')) l').
  destruct (Z_le_gt_dec l' root) as [L'|L'].
  - (* no sub-table *)
    replace (root <? l') with false by (symmetry; apply Z.ltb_ge; lia). cbn [andb].
    left. eexists. split; [reflexivity|].
    destruct (Hlow ltac:(lia)) as (Ed & Ec & En & Eu & Elo).
    unfold inv. cbn [s_huff s_sym s_len s_curr s_drop s_low s_used s_next s_cnt s_tab].
    split; [lia|]. split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|].
    split; [intros; auto|]. split; [intros; lia|].
    split; [lia|]. split; [auto|]. split; [|lia]. intros. rewrite T3 by lia. apply Htfr. lia.
  - replace (root <? l') with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb].
    assert (Hmask: Z.land huff' (Z.shiftl 1 root - 1) = reverse_bits (pfx ls root (i + 1)) root)
      by (apply huff_mask; lia).
    pose proof (pfx_range (i + 1) ltac:(lia)) as Hp1.
    destruct (Z_le_gt_dec l root) as [L|L].
    + (* first sub-table *)
      destruct (Hlow L) as (Ed & Ec & En & Eu & Elo).
      rewrite Hmask, Elo.
      replace (reverse_bits (pfx ls root (i + 1)) root =? Z.ones 32) with false.
      2: { symmetry. apply Z.eqb_neq. rewrite ones32. pose proof (B1 (pfx ls root (i + 1)) root ltac:(lia)).
           assert (2 ^ root <= 2 ^ 15) by (apply Z.pow_le_mono_r; lia). lia. }
      cbn [negb]. rewrite <- Hmask.
      replace (if drop =? 0 then root else drop) with root by (rewrite Ed; reflexivity).
      apply new_table; auto; try lia.
      * rewrite Ec, En, pow2_shiftl by lia. lia.
      * rewrite En, Ec, pow2_shiftl by lia.
        rewrite (sumq_zero ls root 0 (pfx ls root (i + 1))); [change (sumq ls root 0) with 0; lia|lia|].
        intros. apply (fq_gap i q); lia.
      * apply group_start; auto; lia.
      * intros; rewrite T3 by lia; apply Htfr; lia.
    + (* inside sub-tables *)
      destruct (Hhigh ltac:(lia)) as (Ed & Elo & Ec & En & Eu).
      rewrite Hmask, Elo.
      assert (Hpm: pfx ls root i <= pfx ls root (i + 1)) by (apply pfx_mono; lia).
      pose proof (pfx_range i Hi) as Hp0.
      destruct (Z.eq_dec (pfx ls root (i + 1)) (pfx ls root i)) as [Ep|Ep].
      * rewrite Ep, Z.eqb_refl. cbn [negb].
        left. eexists. split; [reflexivity|].
        unfold inv. cbn [s_huff s_sym s_len s_curr s_drop s_low s_used s_next s_cnt s_tab].
        split; [lia|]. split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|].
        split; [intros; lia|]. split.
        -- intros _. rewrite Ep. auto.
        -- split; [lia|]. split; [auto|]. split; [|lia]. intros. rewrite T3 by lia. apply Htfr. lia.
      * replace (reverse_bits (pfx ls root (i + 1)) root =? reverse_bits (pfx ls root i) root) with false.
        2: { symmetry. apply Z.eqb_neq. intro E. apply Ep. apply (rev_inj _ _ root); auto; lia. }
        cbn [negb]. rewrite <- Hmask.
        replace (if drop =? 0 then root else drop) with root
          by (rewrite Ed; destruct (root =? 0) eqn:E; auto; apply Z.eqb_eq in E; lia).
        apply new_table; auto; try lia.
        -- rewrite pow2_shiftl by lia. lia.
        -- rewrite pow2_shiftl by lia. rewrite En, Ec.
           rewrite (sumq_zero ls root (pfx ls root i + 1) (pfx ls root (i + 1))); [|lia|].
           ++ rewrite sumq_succ by lia. rewrite fq_long by lia. lia.
           ++ intros. apply (fq_gap i q); lia.
        -- apply group_start; auto; lia.
        -- intros; rewrite T3 by lia; apply Htfr; lia.
Qed.

End Loop.
