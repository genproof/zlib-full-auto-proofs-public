(* The verified search behind ENOUGH_LENS / ENOUGH_DISTS (zlib's examples/enough.c).
   A code is followed length by length, l = 1..15, in the state (A l, K l): A l the bit patterns of
   length l not yet used by the codes shorter than l, K l the number of those codes.  A table G
   (computed by `build`, a dynamic program over the states) and its prefix maxima M are checked by
   `chk`; `dp_sound` turns a successful check into a bound on the sum of `term R l (A l)`, which
   bounds the sub-tables of the two-level table of root R (part_enough.v). *)
From Coq Require Import ZArith List Lia Bool.
From Coq Require Import FSets.FMapPositive.
Require Import Zlib.proof.inftrees.model.
Import ListNotations.
Local Open Scope Z_scope.

Definition lsum (f: Z -> Z) (xs: list Z) : Z := fold_right (fun x s => f x + s) 0 xs.

Lemma In_zseq' : forall n start i, In i (zseq start n) <-> start <= i < start + Z.of_nat n.
Proof.
  induction n; intros; cbn [zseq In]; [lia|]. rewrite IHn. lia.
Qed.

Definition tab := PositiveMap.t Z.
Definition key (l a k: Z) : positive := Z.to_pos ((l * 512 + a) * 512 + k + 1).
Definition tget (T: tab) (l a k: Z) : Z :=
  match PositiveMap.find (key l a k) T with Some v => v | None => 0 end.
Definition rng (lo hi: Z) : list Z := zseq lo (Z.to_nat (hi - lo + 1)).

Lemma rng_In : forall x lo hi, In x (rng lo hi) <-> lo <= x <= hi.
Proof. intros. unfold rng. rewrite In_zseq'. lia. Qed.

(* The weight of length l in the size of a sub-table: 2^(g - R) = sum of wgt R l for R < l <= g. *)
Definition wgt (R l: Z) : Z := if l =? R + 1 then 2 else 2 ^ (l - R - 1).
(* (2^15 - a * 2^(15 - l)) is the Kraft sum of the codes shorter than l (left-aligned on 15 bits);
   2^R minus its root prefix is the number of root entries that have codes of length >= l. *)
Definition term (R l a: Z) : Z :=
  if l <=? R then 0 else wgt R l * (2 ^ R - (2 ^ 15 - a * 2 ^ (15 - l)) / 2 ^ (15 - R)).

Definition build_G (R l N: Z) (TG TM: tab) : tab :=
  fold_left (fun TG k => fold_left (fun TG a =>
      PositiveMap.add (key l a k)
        (if l =? 15 then term R l a else term R l a + tget TM (l + 1) (k + a) (Z.min a (N - k - a))) TG)
    (rng 0 (Z.min (2 ^ l) (N - k))) TG) (rng 0 N) TG.

Definition build_M (l N: Z) (TG TM: tab) : tab :=
  fold_left (fun TM e => snd (fold_left (fun (p: Z * tab) j =>
      let v := tget TG l (2 * j) (e - j) in
      let b := if j =? 0 then v else Z.max (fst p) v in
      (b, PositiveMap.add (key l e j) b (snd p)))
    (rng 0 (Z.min e (N - e))) (0, TM))) (rng 0 N) TM.

Definition build (R N: Z) : tab * tab :=
  fold_left (fun (p: tab * tab) l =>
      let TG := build_G R l N (fst p) (snd p) in (TG, build_M l N TG (snd p)))
    (rev (rng 1 15)) (PositiveMap.empty Z, PositiveMap.empty Z).

Definition chk (R N E: Z) (TG TM: tab) : bool :=
  forallb (fun k => forallb (fun a => term R 15 a <=? tget TG 15 a k)
     (rng 0 (Z.min (2 ^ 15) (N - k)))) (rng 0 N) &&
  forallb (fun l => forallb (fun k => forallb (fun a =>
       term R l a + tget TM (l + 1) (k + a) (Z.min a (N - k - a)) <=? tget TG l a k)
     (rng 0 (Z.min (2 ^ l) (N - k)))) (rng 0 N)) (rng 1 14) &&
  forallb (fun l => forallb (fun e => forallb (fun j =>
       (tget TG l (2 * j) (e - j) <=? tget TM l e j) &&
       ((j =? 0) || (tget TM l e (j - 1) <=? tget TM l e j)))
     (rng 0 (Z.min e (N - e)))) (rng 0 N)) (rng 2 15) &&
  (2 ^ R + tget TG 1 2 0 <=? E).

Definition chkb (R N E: Z) : bool := let T := build R N in chk R N E (fst T) (snd T).

Section Sound.
Context (R N E: Z) (TG TM: tab).
Context (Hchk : chk R N E TG TM = true).

Local Notation G := (tget TG).
Local Notation M := (tget TM).

Lemma chk_parts :
  (forall k a, 0 <= k <= N -> 0 <= a <= Z.min (2 ^ 15) (N - k) -> term R 15 a <= G 15 a k) /\
  (forall l k a, 1 <= l <= 14 -> 0 <= k <= N -> 0 <= a <= Z.min (2 ^ l) (N - k) ->
     term R l a + M (l + 1) (k + a) (Z.min a (N - k - a)) <= G l a k) /\
  (forall l e j, 2 <= l <= 15 -> 0 <= e <= N -> 0 <= j <= Z.min e (N - e) ->
     G l (2 * j) (e - j) <= M l e j /\ (j = 0 \/ M l e (j - 1) <= M l e j)) /\
  2 ^ R + G 1 2 0 <= E.
Proof.
  pose proof Hchk as H. unfold chk in H. rewrite !andb_true_iff in H.
  destruct H as [[[H1 H2] H3] H4].
  rewrite forallb_forall in H1, H2, H3. split; [|split; [|split]].
  - intros k a Hk Ha. specialize (H1 k (proj2 (rng_In _ _ _) Hk)).
    rewrite forallb_forall in H1. apply Z.leb_le. apply H1. apply rng_In. lia.
  - intros l k a Hl Hk Ha. specialize (H2 l (proj2 (rng_In _ _ _) Hl)).
    rewrite forallb_forall in H2. specialize (H2 k (proj2 (rng_In _ _ _) Hk)).
    rewrite forallb_forall in H2. apply Z.leb_le. apply H2. apply rng_In. lia.
  - intros l e j Hl He Hj. specialize (H3 l (proj2 (rng_In _ _ _) Hl)).
    rewrite forallb_forall in H3. specialize (H3 e (proj2 (rng_In _ _ _) He)).
    rewrite forallb_forall in H3. specialize (H3 j (proj2 (rng_In _ _ _) Hj)).
    rewrite andb_true_iff, orb_true_iff, Z.leb_le, Z.eqb_eq, Z.leb_le in H3. tauto.
  - apply Z.leb_le. exact H4.
Qed.

Lemma M_prefix : forall l e m, 2 <= l <= 15 -> 0 <= e <= N -> 0 <= m <= Z.min e (N - e) ->
  forall j, 0 <= j <= m -> G l (2 * j) (e - j) <= M l e m.
Proof.
  destruct chk_parts as [_ [_ [HM _]]].
  intros l e m Hl He Hm. destruct Hm as [Hm0 Hm1]. revert Hm1.
  pattern m. apply natlike_ind; [| |exact Hm0].
  - intros _ j Hj. replace j with 0 by lia. apply (HM l e 0); lia.
  - intros x Hx IH Hx1 j Hj.
    destruct (Z.eq_dec j (Z.succ x)).
    + subst j. apply (HM l e (Z.succ x)); lia.
    + destruct (HM l e (Z.succ x) Hl He ltac:(lia)) as [_ [?|Hle]]; [lia|].
      replace (Z.succ x - 1) with x in Hle by lia.
      specialize (IH ltac:(lia) j ltac:(lia)). lia.
Qed.

Lemma dp_sound : forall (A K C: Z -> Z),
  (forall l, 1 <= l <= 15 -> 0 <= K l <= N /\ 0 <= A l <= Z.min (2 ^ l) (N - K l)) ->
  (forall l, 1 <= l <= 14 -> A (l + 1) = 2 * (A l - C l) /\ K (l + 1) = K l + C l /\ 0 <= C l) ->
  lsum (fun l => term R l (A l)) (zseq 1 15) <= G 1 (A 1) (K 1).
Proof.
  destruct chk_parts as [H15 [HG [_ _]]].
  intros A K C HAK HT.
  assert (D: forall d, (d <= 14)%nat ->
    lsum (fun l => term R l (A l)) (zseq (15 - Z.of_nat d) (S d))
      <= G (15 - Z.of_nat d) (A (15 - Z.of_nat d)) (K (15 - Z.of_nat d))).
  { induction d as [|d IH]; intros Hd.
    - simpl. destruct (HAK 15 ltac:(lia)). specialize (H15 (K 15) (A 15)). lia.
    - set (l := 15 - Z.of_nat (S d)).
      replace (zseq l (S (S d))) with (l :: zseq (l + 1) (S d)) by reflexivity.
      replace (l + 1) with (15 - Z.of_nat d) by (subst l; lia).
      cbn [lsum fold_right]. fold (lsum (fun l => term R l (A l)) (zseq (15 - Z.of_nat d) (S d))).
      specialize (IH ltac:(lia)).
      replace (15 - Z.of_nat d) with (l + 1) in * by (subst l; lia).
      assert (Hl: 1 <= l <= 14) by (subst l; lia).
      destruct (HAK l ltac:(lia)) as [HK HA].
      destruct (HAK (l + 1) ltac:(lia)) as [HK1 HA1].
      destruct (HT l Hl) as [EA [EK HC]].
      set (j := A l - C l) in *.
      set (e := K l + A l).
      assert (Hj: 0 <= j <= Z.min (A l) (N - K l - A l)) by lia.
      assert (HMp := M_prefix (l + 1) e (Z.min (A l) (N - K l - A l)) ltac:(lia) ltac:(subst e; lia)
                       ltac:(subst e; lia) j ltac:(lia)).
      replace (2 * j) with (A (l + 1)) in HMp by lia.
      replace (e - j) with (K (l + 1)) in HMp by (subst e; lia).
      specialize (HG l (K l) (A l) Hl ltac:(lia) ltac:(lia)).
      subst e. lia. }
  specialize (D 14%nat ltac:(lia)). simpl in D. exact D.
Qed.

End Sound.

Lemma chk_lens : chkb 9 286 852 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma chk_dists : chkb 6 30 592 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
