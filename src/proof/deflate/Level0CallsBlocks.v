(** * Level 0 over several deflate() calls: the full stored blocks written before the last call

    A deflate(Z_NO_FLUSH) call at level 0 given whole blocks of 65535 bytes (and room for them) writes them as
    non-final stored blocks of 65535 bytes.  [nblocks i d] is the first [i] such blocks of [d]; the stored
    blocks of the whole data ([Level0Defs.stored_blocks]) are those blocks followed by the stored blocks of the
    rest ([stored_blocks_split]). *)
From Coq Require Import ZArith List Lia.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.Level0Defs.
Import ListNotations.
Local Open Scope Z_scope.

(** The [i] non-final stored blocks of the bytes [a + 65535 j .. a + 65535 (j + 1)) of [d], [j < i]. *)
Fixpoint nblocks (a : Z) (i : nat) (d : list Z) : list Z :=
  match i with
  | O => []
  | S i' => nblocks a i' d ++ stored_block 0 (sublist (a + 65535 * Z.of_nat i') (a + 65535 * Z.of_nat i' + 65535) d)
  end.

Lemma nblocks_S a i d :
  nblocks a (S i) d =
  nblocks a i d ++ stored_block 0 (sublist (a + 65535 * Z.of_nat i) (a + 65535 * Z.of_nat i + 65535) d).
Proof. reflexivity. Qed.

Lemma Zlength_nblocks a i d :
  0 <= a -> a + 65535 * Z.of_nat i <= Zlength d -> Zlength (nblocks a i d) = 65540 * Z.of_nat i.
Proof.
  induction i as [|i IH]; intros H0 H; [reflexivity|].
  rewrite Nat2Z.inj_succ in H.
  rewrite nblocks_S, Zlength_app, IH, Zlength_stored_block, Zlength_sublist by lia.
  rewrite Nat2Z.inj_succ. lia.
Qed.

(** The blocks of a slice are the blocks of the data at the slice's offset. *)
Lemma nblocks_sublist a b i d :
  0 <= a -> a + 65535 * Z.of_nat i <= b <= Zlength d -> nblocks 0 i (sublist a b d) = nblocks a i d.
Proof.
  induction i as [|i IH]; intros H0 H; [reflexivity|].
  rewrite Nat2Z.inj_succ in H.
  rewrite !nblocks_S, IH by lia. f_equal. f_equal.
  rewrite sublist_sublist by lia. f_equal; lia.
Qed.

(** The first [p + k] blocks: the first [p], then the next [k]. *)
Lemma nblocks_add a p k d :
  nblocks a (p + k) d = nblocks a p d ++ nblocks (a + 65535 * Z.of_nat p) k d.
Proof.
  induction k as [|k IH].
  - rewrite Nat.add_0_r. cbn [nblocks]. rewrite app_nil_r. reflexivity.
  - rewrite Nat.add_succ_r, !nblocks_S, IH, <- app_assoc. f_equal. f_equal. f_equal.
    rewrite Nat2Z.inj_add. f_equal; lia.
Qed.

(** The stored blocks of [d]: its first [i] full blocks, then the stored blocks of the rest. *)
Lemma stored_blocks_split i d :
  (i = O \/ 65535 * Z.of_nat i < Zlength d) ->
  stored_blocks d = nblocks 0 i d ++ stored_blocks (sublist (65535 * Z.of_nat i) (Zlength d) d).
Proof.
  induction i as [|i IH]; intros H.
  - cbn [nblocks app]. rewrite Z.mul_0_r, sublist_same by lia. reflexivity.
  - rewrite Nat2Z.inj_succ in H. destruct H as [H|H]; [discriminate|].
    rewrite IH by lia. rewrite nblocks_S, <- app_assoc. f_equal.
    set (r := sublist (65535 * Z.of_nat i) (Zlength d) d).
    assert (Lr : Zlength r = Zlength d - 65535 * Z.of_nat i) by (unfold r; rewrite Zlength_sublist; lia).
    rewrite (stored_blocks_eq r). unfold MAX_STORED_LEN.
    replace (Zlength r <=? 65535) with false by (symmetry; apply Z.leb_gt; lia).
    rewrite Nat2Z.inj_succ. f_equal.
    + f_equal. unfold r. rewrite sublist_sublist by lia. f_equal; lia.
    + f_equal. unfold r. rewrite Zlength_sublist, sublist_sublist by lia. f_equal; lia.
Qed.
