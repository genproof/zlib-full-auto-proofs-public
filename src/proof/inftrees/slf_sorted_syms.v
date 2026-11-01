(* Part of loop_facts: sorted_syms_ok_stmt (model_inv.v). Pure Coq. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.inftrees.model_inv.
Import ListNotations.
Local Open Scope Z_scope.

Lemma slf_in_combine_zseq : forall (l: list Z) start x y,
  In (x, y) (combine (zseq start (length l)) l) ->
  start <= x < start + Zlength l /\ Znth (x - start) l = y.
Proof.
  induction l as [|a l IH]; intros start x y H; simpl in H.
  - contradiction.
  - rewrite Zlength_cons. destruct H as [H|H].
    + inversion H; subst. split; [pose proof (Zlength_nonneg l); lia|].
      replace (x - x) with 0 by lia. apply Znth_0_cons.
    + apply IH in H. destruct H as [H1 H2]. split; [lia|].
      rewrite Znth_pos_cons by lia. rewrite <- H2. f_equal. lia.
Qed.

Lemma slf_length_combine_zseq : forall (l: list Z) start,
  length (combine (zseq start (length l)) l) = length l.
Proof.
  induction l as [|a l IH]; intros start; simpl; [reflexivity|]. rewrite IH. reflexivity.
Qed.

Lemma slf_count_nodup : forall (v: Z) ks, NoDup ks -> (length (filter (Z.eqb v) ks) <= 1)%nat.
Proof.
  intros v ks H. induction H as [|k ks Hk Hnd IH]; simpl; [lia|].
  destruct (Z.eqb_spec v k) as [->|]; simpl; [|exact IH].
  assert (filter (Z.eqb k) ks = []) as ->; [|simpl; lia].
  destruct (filter (Z.eqb k) ks) as [|z zs] eqn:E; [reflexivity|].
  exfalso. assert (In z (filter (Z.eqb k) ks)) as Hz by (rewrite E; left; reflexivity).
  apply filter_In in Hz. destruct Hz as [Hz1 Hz2]. apply Z.eqb_eq in Hz2. subst. contradiction.
Qed.

Lemma slf_flat_map_filter_len : forall (ps: list (Z*Z)) ks, NoDup ks ->
  (length (flat_map (fun k => filter (fun p => Z.eqb (snd p) k) ps) ks) <= length ps)%nat.
Proof.
  induction ps as [|p ps IH]; intros ks Hnd.
  - induction ks; simpl; [lia|]. inversion Hnd; subst. simpl. auto.
  - assert (forall ks, length (flat_map (fun k => filter (fun q => Z.eqb (snd q) k) (p :: ps)) ks) =
              (length (flat_map (fun k => filter (fun q => Z.eqb (snd q) k) ps) ks) +
               length (filter (Z.eqb (snd p)) ks))%nat) as Heq.
    { clear Hnd. intros ks0. induction ks0 as [|k ks0 IHk]; [reflexivity|].
      cbn [flat_map]. rewrite !app_length, IHk. cbn [filter].
      destruct (Z.eqb_spec (snd p) k) as [->|Hne].
      + cbn [length]. lia.
      + lia. }
    rewrite Heq. specialize (IH ks Hnd). pose proof (slf_count_nodup (snd p) ks Hnd). cbn [length]. lia.
Qed.

Lemma slf_flat_map_map_len : forall (A B C: Type) (f: B -> C) (F: A -> list B) ks,
  length (flat_map (fun k => map f (F k)) ks) = length (flat_map F ks).
Proof.
  intros. induction ks; simpl; [reflexivity|]. rewrite !app_length, map_length, IHks. reflexivity.
Qed.

Lemma slf_nodup_zseq : forall n start, NoDup (zseq start n).
Proof.
  assert (Hin: forall n start x, In x (zseq start n) -> start <= x).
  { induction n; intros start x H; simpl in H; [contradiction|].
    destruct H as [->|H]; [lia|]. apply IHn in H. lia. }
  induction n; intros start; simpl; constructor; auto.
  intros H. apply Hin in H. lia.
Qed.

Lemma slf_in_zseq : forall n start x, In x (zseq start n) -> start <= x < start + Z.of_nat n.
Proof.
  induction n; intros start x H; simpl in H; [contradiction|].
  destruct H as [->|H]; [lia|]. apply IHn in H. lia.
Qed.

Lemma slf_sorted_syms_ok : sorted_syms_ok_stmt.
Proof.
  intros lens _. split.
  - unfold sorted_syms, syms_of_len. rewrite !Zlength_correct. apply Nat2Z.inj_le.
    rewrite slf_flat_map_map_len.
    eapply Nat.le_trans; [apply slf_flat_map_filter_len, slf_nodup_zseq|].
    rewrite slf_length_combine_zseq. lia.
  - apply Forall_forall. intros x Hx. unfold sorted_syms in Hx.
    apply in_flat_map in Hx. destruct Hx as [l [Hl Hx]].
    apply slf_in_zseq in Hl. simpl in Hl.
    unfold syms_of_len in Hx. apply in_map_iff in Hx. destruct Hx as [[x' y] [Hfst Hin]].
    simpl in Hfst. subst x'. apply filter_In in Hin. destruct Hin as [Hin Hy].
    simpl in Hy. apply Z.eqb_eq in Hy. subst y.
    apply slf_in_combine_zseq in Hin. destruct Hin as [H1 H2].
    rewrite Z.sub_0_r in H2. split; [lia|]. rewrite H2. lia.
Qed.
