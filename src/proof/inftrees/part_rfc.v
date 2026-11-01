(* Part: rfc_stmt of fact_result.v (RFC 1951 canonical codes are the Kraft prefix sums). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.inftrees.facts.
Require Import Zlib.proof.inftrees.fact_result.
Import ListNotations.
Local Open Scope Z_scope.

(* The symbols of length L, with an offset: g st xs lists st + j for the j with xs_j = L. *)
Definition rfc_g (L st: Z) (xs: list Z) : list Z :=
  map fst (filter (fun p => snd p =? L) (combine (zseq st (length xs)) xs)).

Lemma rfc_g_cons : forall L st x xs,
  rfc_g L st (x :: xs) = if x =? L then st :: rfc_g L (st + 1) xs else rfc_g L (st + 1) xs.
Proof. intros. unfold rfc_g. simpl. destruct (x =? L); reflexivity. Qed.

Lemma rfc_count_cons : forall x xs L,
  count_len (x :: xs) L = (if x =? L then 1 else 0) + count_len xs L.
Proof.
  intros. unfold count_len. simpl. rewrite (Z.eqb_sym L x).
  destruct (x =? L); [rewrite Zlength_cons|]; lia.
Qed.

Lemma rfc_g_len : forall L xs st, Zlength (rfc_g L st xs) = count_len xs L.
Proof.
  induction xs as [|x xs IH]; intros st.
  - reflexivity.
  - rewrite rfc_g_cons, rfc_count_cons. destruct (x =? L).
    + rewrite Zlength_cons, IH. lia.
    + rewrite IH. lia.
Qed.

Lemma rfc_g_prop : forall L xs st k, 0 <= k < Zlength (rfc_g L st xs) ->
  let s := Znth k (rfc_g L st xs) in
  st <= s < st + Zlength xs /\ Znth (s - st) xs = L /\ count_len (sublist 0 (s - st) xs) L = k.
Proof.
  induction xs as [|x xs IH]; intros st k Hk s.
  - unfold rfc_g in Hk. simpl in Hk. rewrite Zlength_nil in Hk. lia.
  - subst s. rewrite rfc_g_cons in *. rewrite Zlength_cons.
    destruct (x =? L) eqn:E.
    + apply Z.eqb_eq in E. subst x.
      destruct (Z.eq_dec k 0) as [->|Hk0].
      * rewrite Znth_0_cons. replace (st - st) with 0 by lia.
        rewrite Znth_0_cons, sublist_nil. pose proof (Zlength_nonneg xs). split; [lia|]. split; reflexivity.
      * rewrite Znth_pos_cons by lia. rewrite Zlength_cons in Hk.
        destruct (IH (st + 1) (k - 1) ltac:(lia)) as (H1 & H2 & H3).
        set (s := Znth (k - 1) (rfc_g L (st + 1) xs)) in *.
        split; [lia|].
        rewrite Znth_pos_cons by lia. replace (s - st - 1) with (s - (st + 1)) by lia.
        split; [exact H2|].
        rewrite sublist_0_cons by lia. rewrite rfc_count_cons, Z.eqb_refl.
        replace (s - st - 1) with (s - (st + 1)) by lia. lia.
    + destruct (IH (st + 1) k Hk) as (H1 & H2 & H3).
      set (s := Znth k (rfc_g L (st + 1) xs)) in *.
      split; [lia|].
      rewrite Znth_pos_cons by lia. replace (s - st - 1) with (s - (st + 1)) by lia.
      split; [exact H2|].
      rewrite sublist_0_cons by lia. rewrite rfc_count_cons, E.
      replace (s - st - 1) with (s - (st + 1)) by lia. lia.
Qed.

Lemma rfc_syms_len : forall lens L, Zlength (syms_of_len lens L) = count_len lens L.
Proof. intros. apply (rfc_g_len L lens 0). Qed.

Lemma rfc_syms_prop : forall lens L k, 0 <= k < count_len lens L ->
  let s := Znth k (syms_of_len lens L) in
  0 <= s < Zlength lens /\ Znth s lens = L /\ count_len (sublist 0 s lens) L = k.
Proof.
  intros lens L k Hk s.
  rewrite <- rfc_syms_len in Hk.
  destruct (rfc_g_prop L lens 0 k Hk) as (H1 & H2 & H3).
  fold (syms_of_len lens L) in *. subst s. rewrite Z.sub_0_r in *. auto.
Qed.

Lemma rfc_ksum_const : forall lens L xs, Forall (fun s => Znth s lens = L) xs ->
  ksum (map (fun s => Znth s lens) xs) = Zlength xs * 2 ^ (MAXBITS - L).
Proof.
  induction xs as [|x xs IH]; intros H.
  - reflexivity.
  - inversion H; subst. unfold ksum in *. simpl map. cbn [fold_right].
    rewrite IH by assumption. rewrite Zlength_cons. lia.
Qed.

Lemma rfc_syms_forall : forall lens L,
  Forall (fun s => Znth s lens = L) (syms_of_len lens L).
Proof.
  intros. apply Forall_forall. intros x Hx. apply In_Znth in Hx as (k & Hk & <-).
  rewrite rfc_syms_len in Hk. apply (rfc_syms_prop lens L k Hk).
Qed.

Lemma rfc_zseq_S : forall n st, zseq st (S n) = zseq st n ++ [st + Z.of_nat n].
Proof.
  induction n as [|n IH]; intros st.
  - simpl. f_equal. lia.
  - change (zseq st (S (S n))) with (st :: zseq (st + 1) (S n)). rewrite IH.
    change (zseq st (S n)) with (st :: zseq (st + 1) n). simpl. do 3 f_equal. lia.
Qed.

Lemma rfc_loop_S : forall k l c lens,
  next_code_loop (S k) l c lens = Z.shiftl (next_code_loop k l c lens + bl_count lens (l + Z.of_nat k - 1)) 1.
Proof.
  induction k as [|k IH]; intros l c lens.
  - cbn [next_code_loop]. rewrite Z.add_0_r. reflexivity.
  - change (next_code_loop (S (S k)) l c lens)
      with (next_code_loop (S k) (l + 1) (Z.shiftl (c + bl_count lens (l - 1)) 1) lens).
    rewrite IH. f_equal. f_equal. f_equal. lia.
Qed.

Definition rfc_P (lens: list Z) (n: nat) : list Z := flat_map (syms_of_len lens) (zseq 1 n).

Lemma rfc_P_S : forall lens n, rfc_P lens (S n) = rfc_P lens n ++ syms_of_len lens (Z.of_nat n + 1).
Proof.
  intros. unfold rfc_P. rewrite rfc_zseq_S, flat_map_app. cbn [flat_map]. rewrite app_nil_r, Z.add_comm. reflexivity.
Qed.

Lemma rfc_nc : forall lens n, (n <= 14)%nat ->
  next_code_loop (S n) 1 0 lens * 2 ^ (MAXBITS - (Z.of_nat n + 1))
  = ksum (map (fun s => Znth s lens) (rfc_P lens n)).
Proof.
  induction n as [|n IH]; intros Hn.
  - reflexivity.
  - rewrite rfc_loop_S, Z.shiftl_mul_pow2 by lia.
    rewrite rfc_P_S, map_app, ksum_app, <- IH by lia.
    rewrite rfc_ksum_const with (L := Z.of_nat n + 1) by apply rfc_syms_forall. rewrite rfc_syms_len.
    replace (1 + Z.of_nat (S n) - 1) with (Z.of_nat n + 1) by lia.
    unfold bl_count. replace (Z.of_nat n + 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (MAXBITS - (Z.of_nat n + 1)) with (MAXBITS - (Z.of_nat (S n) + 1) + 1)
      by (unfold MAXBITS; lia).
    rewrite Z.pow_add_r by (unfold MAXBITS in *; lia). ring.
Qed.

Lemma rfc_main : forall lens n, (n <= 15)%nat ->
  forall i, 0 <= i < Zlength (rfc_P lens n) ->
  let s := Znth i (rfc_P lens n) in
  rfc_code lens s * 2 ^ (MAXBITS - Znth s lens)
  = ksum (map (fun s => Znth s lens) (sublist 0 i (rfc_P lens n))).
Proof.
  induction n as [|n IH]; intros Hn i Hi s.
  - unfold rfc_P in Hi. simpl in Hi. rewrite Zlength_nil in Hi. lia.
  - subst s. rewrite rfc_P_S in *. rewrite Zlength_app in Hi.
    destruct (Z_lt_le_dec i (Zlength (rfc_P lens n))) as [Hlt|Hge].
    + rewrite app_Znth1 by lia. rewrite sublist_app1 by lia. apply IH; lia.
    + set (L := Z.of_nat n + 1) in *.
      set (k := i - Zlength (rfc_P lens n)).
      rewrite app_Znth2 by lia. fold k.
      rewrite rfc_syms_len in Hi.
      destruct (rfc_syms_prop lens L k ltac:(lia)) as (H1 & H2 & H3).
      set (s := Znth k (syms_of_len lens L)) in *.
      rewrite sublist0_app2 by (rewrite rfc_syms_len; lia). fold k.
      rewrite map_app, ksum_app, <- rfc_nc by lia. fold L.
      rewrite rfc_ksum_const with (L := L).
      2:{ apply Forall_sublist, rfc_syms_forall. }
      rewrite Zlength_sublist by (try rewrite rfc_syms_len; unfold k; lia).
      unfold rfc_code. rewrite H2. replace (L =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite H3.
      unfold next_code. replace (Z.to_nat L) with (S n) by lia. ring.
Qed.

Lemma rfc_ok2 : rfc_stmt.
Proof.
  intros lens _ i Hi.
  unfold sl in *. rewrite Zlength_map in Hi.
  unfold kpre. rewrite sublist_map, Znth_map by lia.
  change (sorted_syms lens) with (rfc_P lens 15) in *.
  apply rfc_main; auto.
Qed.
