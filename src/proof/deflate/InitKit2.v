(** * Kit for the body proof of deflateInit2_, part 2: the zero values of the fields of
    deflate_state as the values of the representation. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DSpec Zlib.proof.deflate.DCS.
Require Import Zlib.deflate.code.
Require Import Zlib.proof.deflate.DModel3.
Local Open Scope logic.

Lemma ct_canon_zero n : 0 <= n -> ct_canon (zero_tree n) = Zrepeat (ctv_of false false 0 0) n.
Proof.
  intros Hn. unfold ct_canon, ct_arr, zero_tree. cbn [fc dl].
  rewrite Zlength_correct, repeat_length, Nat2Z.id. unfold Zrepeat.
  generalize (Z.to_nat n) as k. intros k.
  rewrite map_map.
  transitivity (map (fun _ : nat => ctv_of false false 0 0) (seq 0 k)).
  - apply map_ext_in. intros i Hi. apply in_seq in Hi.
    rewrite !Znth_repeat' by lia. reflexivity.
  - rewrite <- (length_seq k 0) at 2. generalize (seq 0 k). intros l.
    induction l; simpl; congruence.
Qed.

Lemma pair_JMeq {A B A' B'} (a : A) (b : B) (a' : A') (b' : B') :
  JMeq a a' -> JMeq b b' -> JMeq (a, b) (a', b').
Proof. intros [x p] [x0 p0]. subst A' B'. simpl in p, p0. subst a' b'. apply JMeq_refl. Qed.

Lemma zv_ct : zero_val t_ct = ctv_of false false 0 0.
Proof.
  apply JMeq_eq. rewrite zero_val_eq. eapply JMeq_trans; [apply fold_reptype_JMeq|]. simpl. unfold ctv_of.
  match goal with |- JMeq (zero_val ?u1, zero_val ?u2) _ => rewrite (zero_val_eq u1), (zero_val_eq u2) end.
  simpl. apply pair_JMeq; (eapply JMeq_trans; [apply fold_reptype_JMeq|]); rewrite zero_val_Tint; apply JMeq_refl.
Qed.

Lemma zv_tree n : 0 <= n -> @zero_val DCS.CS (tarray t_ct n) = ct_canon (zero_tree n).
Proof. intros. rewrite ct_canon_zero by lia. rewrite zero_val_tarray, zv_ct. reflexivity. Qed.
