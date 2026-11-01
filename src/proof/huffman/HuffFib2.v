(** * The depth bound of greedy Huffman merging with frequencies >= 1: weight >= fib (depth + 2) *)

From Coq Require Import ZArith List Lia Bool Permutation.
Require Import Zlib.proof.huffman.HuffAbs.
Import ListNotations.
Local Open Scope Z_scope.

Definition fib2_inv (P : list item) : Prop :=
  exists m,
  (forall I, In I P -> forall x, In x I -> 0 <= ld x /\ 1 <= lf x) /\
  (forall I, In I P -> m <= weight I /\ 1 <= weight I) /\
  (forall I, In I P -> forall x, In x I -> fib (ld x + 2) <= weight I) /\
  (forall I, In I P -> forall x, In x I -> 1 <= ld x -> fib (ld x + 1) <= m).

Lemma fib2_inv_perm : forall P Q, Permutation P Q -> fib2_inv P -> fib2_inv Q.
Proof.
  intros P Q Hp [m [H0 [H1 [H2 H3]]]]. exists m.
  assert (Hin : forall I, In I Q -> In I P) by (intros; eapply Permutation_in; [apply Permutation_sym|]; eauto).
  split; [|split; [|split]]; intros; [apply (H0 I)|apply (H1 I)|apply (H2 I)|apply (H3 I)]; auto.
Qed.

Lemma fib_mono_step : forall d, 0 <= d -> fib d <= fib (d + 1).
Proof.
  intros d Hd. destruct (Z.eq_dec d 0) as [->|Hne]; [change (fib 0) with 0; apply fib_nonneg|].
  replace (d + 1) with ((d - 1) + 2) by lia. rewrite fib_succ_succ by lia.
  replace (d - 1 + 1) with d by lia. assert (H := fib_nonneg (d - 1)). lia.
Qed.

Lemma fib2_inv_step : forall a b rest,
  (forall J, In J (b :: rest) -> weight a <= weight J) ->
  (forall J, In J rest -> weight b <= weight J) ->
  fib2_inv (a :: b :: rest) -> fib2_inv (merge a b :: rest).
Proof.
  intros a b rest Ha Hb [m [H0 [H1 [H2 H3]]]].
  assert (Hab : weight a <= weight b) by (apply Ha; left; auto).
  assert (Wa := H1 a (in_eq _ _)). assert (Wb := H1 b (or_intror (in_eq _ _))).
  assert (Hm : forall x, In x (merge a b) -> exists y, x = deeper y /\ (In y a \/ In y b))
    by (intros; apply in_merge; auto).
  exists (weight b). split; [|split; [|split]].
  - intros I [<-|HI] x Hx.
    + destruct (Hm x Hx) as [y [-> [Hy|Hy]]]; unfold deeper, ld, lf; simpl;
        [destruct (H0 a (in_eq _ _) y Hy)|destruct (H0 b (or_intror (in_eq _ _)) y Hy)];
        unfold ld, lf in *; lia.
    + apply (H0 I); simpl; auto.
  - intros I [<-|HI].
    + rewrite weight_merge. lia.
    + split; [apply Hb; auto|]. apply (H1 I); simpl; auto.
  - intros I [<-|HI] x Hx.
    + rewrite weight_merge. destruct (Hm x Hx) as [y [-> [Hy|Hy]]]; unfold deeper; unfold ld at 1; simpl.
      * destruct (H0 a (in_eq _ _) y Hy) as [Hd Hf]. unfold ld in Hd |- *.
        replace (snd y + 1 + 2) with (snd y + 1 + 2) by lia.
        assert (E : fib (snd y + 1 + 2) = fib (snd y + 2) + fib (snd y + 1))
          by (replace (snd y + 1 + 2) with ((snd y + 1) + 2) by lia; rewrite fib_succ_succ by lia;
              replace (snd y + 1 + 1) with (snd y + 2) by lia; reflexivity).
        rewrite E. assert (E1 := H2 a (in_eq _ _) y Hy). unfold ld in E1.
        destruct (Z.eq_dec (snd y) 0) as [Hz|Hz].
        { rewrite Hz in *. change (fib (0 + 1)) with 1. lia. }
        assert (E2 := H3 a (in_eq _ _) y Hy). unfold ld in E2. specialize (E2 ltac:(lia)). lia.
      * destruct (H0 b (or_intror (in_eq _ _)) y Hy) as [Hd Hf]. unfold ld in Hd |- *.
        assert (E : fib (snd y + 1 + 2) = fib (snd y + 2) + fib (snd y + 1))
          by (replace (snd y + 1 + 2) with ((snd y + 1) + 2) by lia; rewrite fib_succ_succ by lia;
              replace (snd y + 1 + 1) with (snd y + 2) by lia; reflexivity).
        rewrite E. assert (E1 := H2 b (or_intror (in_eq _ _)) y Hy). unfold ld in E1.
        destruct (Z.eq_dec (snd y) 0) as [Hz|Hz].
        { rewrite Hz in *. change (fib (0 + 1)) with 1. lia. }
        assert (E2 := H3 b (or_intror (in_eq _ _)) y Hy). unfold ld in E2. specialize (E2 ltac:(lia)). lia.
    + apply (H2 I); simpl; auto.
  - intros I [<-|HI] x Hx Hd.
    + destruct (Hm x Hx) as [y [-> [Hy|Hy]]].
      * assert (E1 := H2 a (in_eq _ _) y Hy). unfold deeper, ld in *; simpl in Hd |- *.
        replace (snd y + 1 + 1) with (snd y + 2) by lia. lia.
      * assert (E1 := H2 b (or_intror (in_eq _ _)) y Hy). unfold deeper, ld in *; simpl in Hd |- *.
        replace (snd y + 1 + 1) with (snd y + 2) by lia. lia.
    + assert (E := H3 I (or_intror (or_intror HI)) x Hx Hd). lia.
Qed.

Theorem huff_fib2 : forall P R, huff P R -> fib2_inv P ->
  forall x, In x R -> fib (ld x + 2) <= weight R.
Proof.
  intros P R H HP x Hx.
  assert (HR := huff_ind_pool fib2_inv fib2_inv_perm fib2_inv_step P R H HP).
  destruct HR as [m [_ [_ [H2 _]]]]. apply (H2 R (in_eq _ _) x Hx).
Qed.

Lemma fib2_inv_init : forall (S : list Z) (f : Z -> Z), (forall x, In x S -> 1 <= f x) ->
  fib2_inv (map (fun x => [(x, f x, 0)]) S).
Proof.
  intros S f HS. exists 0. split; [|split; [|split]].
  - intros I HI y Hy. apply in_map_iff in HI. destruct HI as [x [<- Hx]].
    destruct Hy as [<-|[]]; unfold ld, lf; simpl. specialize (HS x Hx). lia.
  - intros I HI. apply in_map_iff in HI. destruct HI as [x [<- Hx]].
    unfold weight; simpl. unfold lf; simpl. specialize (HS x Hx). lia.
  - intros I HI y Hy. apply in_map_iff in HI. destruct HI as [x [<- Hx]].
    destruct Hy as [<-|[]]. change (fib (ld (x, f x, 0) + 2)) with 1.
    unfold weight; simpl. unfold lf; simpl. specialize (HS x Hx). lia.
  - intros I HI y Hy Hd. apply in_map_iff in HI. destruct HI as [x [<- Hx]].
    destruct Hy as [<-|[]]. unfold ld in Hd; simpl in Hd. lia.
Qed.

(** Depths stay below [D] when the total weight is below fib (D + 2). *)
Corollary huff_depth_bound : forall P R D, huff P R -> fib2_inv P -> weight R < fib (D + 2) -> 0 <= D ->
  forall x, In x R -> ld x < D.
Proof.
  intros P R D H HP HW HD x Hx. assert (E := huff_fib2 P R H HP x Hx).
  destruct (Z_lt_ge_dec (ld x) D) as [|Hge]; auto. exfalso.
  assert (Hmono : forall k, 0 <= k -> fib (D + 2) <= fib (D + 2 + k)).
  { intros k Hk. pattern k. apply natlike_ind; [rewrite Z.add_0_r; lia| |lia].
    intros j Hj IH. replace (D + 2 + Z.succ j) with (D + 2 + j + 1) by lia.
    assert (fib (D + 2 + j) <= fib (D + 2 + j + 1)) by (apply fib_mono_step; lia). lia. }
  specialize (Hmono (ld x - D) ltac:(lia)). replace (D + 2 + (ld x - D)) with (ld x + 2) in Hmono by lia. lia.
Qed.
