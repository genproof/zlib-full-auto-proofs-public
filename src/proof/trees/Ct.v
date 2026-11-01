(* ct_data arrays (trees.c's trees) in VST, refined by the model's trees (Zlib.proof.huffman.Model.tree: the fc
   and dl union members as two lists of numbers).

   VST represents a union value by the member that was written last (reptype = val + val), and a load of the
   other member gives Vundef.  Both members of ct_data's unions are unsigned shorts at offset 0, so data_at does
   not depend on the member (ct_switch, ct_arr_mode): the proofs present an array in whatever members the next
   accesses use.  [ct_arr mf md t] is the model tree t with entry i in member (mf i) of fc (false: Freq, true:
   Code) and (md i) of dl (false: Dad, true: Len). *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Rep.
Require Import Zlib.proof.huffman.Model.

#[local] Existing Instance DCS.CS.

Definition ctv_of (bf bd: bool) (f d: Z) : reptype t_ct :=
  ((if bf then inr (vi f) else inl (vi f)), (if bd then inr (vi d) else inl (vi d))).

Definition ct_arr (mf md: Z -> bool) (t: tree) : list (reptype t_ct) :=
  map (fun i => ctv_of (mf i) (md i) (Znth i (fc t)) (Znth i (dl t))) (map Z.of_nat (seq 0 (Z.to_nat (Zlength (fc t))))).

(* the canonical presentation: Freq and Dad *)
Definition ffalse (_: Z) : bool := false.
Definition ftrue (_: Z) : bool := true.

Definition tree_ok (t: tree) (n: Z) : Prop :=
  Zlength (fc t) = n /\ Zlength (dl t) = n /\
  (forall i, 0 <= i < n -> 0 <= Znth i (fc t) < 65536 /\ 0 <= Znth i (dl t) < 65536).

Lemma Zlength_ct_arr mf md t: Zlength (ct_arr mf md t) = Zlength (fc t).
Proof.
  unfold ct_arr. rewrite !Zlength_map. rewrite Zlength_correct, length_seq.
  rewrite Z2Nat.id; auto. apply Zlength_nonneg.
Qed.

Lemma Znth_seq_Z n i: 0 <= i < n -> Znth i (map Z.of_nat (seq 0 (Z.to_nat n))) = i.
Proof.
  intros. rewrite Znth_map by (rewrite Zlength_correct, length_seq; lia).
  unfold Znth. rewrite if_false by lia. rewrite seq_nth by lia. lia.
Qed.

Lemma Znth_ct_arr mf md t i: 0 <= i < Zlength (fc t) ->
  Znth i (ct_arr mf md t) = ctv_of (mf i) (md i) (Znth i (fc t)) (Znth i (dl t)).
Proof.
  intros. unfold ct_arr. rewrite Znth_map by (rewrite Zlength_map, Zlength_correct, length_seq; lia).
  rewrite Znth_seq_Z by lia. reflexivity.
Qed.

(* data_at does not depend on the union members *)
Lemma ct_data_rec_mode sh bf bd bf' bd' f d:
  data_at_rec sh t_ct (ctv_of bf bd f d) = data_at_rec sh t_ct (ctv_of bf' bd' f d).
Proof. destruct bf, bd, bf', bd'; reflexivity. Qed.

Lemma ct_value_fits_mode bf bd bf' bd' f d:
  value_fits t_ct (ctv_of bf bd f d) = value_fits t_ct (ctv_of bf' bd' f d).
Proof. destruct bf, bd, bf', bd'; reflexivity. Qed.

(* The array version, data_at sh (tarray t_ct n) (ct_arr mf md t) p =
   data_at sh (tarray t_ct n) (ct_arr mf' md' t) p, follows from ct_data_rec_mode / ct_value_fits_mode with
   array_pred_ext (VST floyd/aggregate_pred.v): CtMode.v (and its copy CtModeS.v). *)
