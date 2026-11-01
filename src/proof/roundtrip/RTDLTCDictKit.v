(** * deflateSetDictionary (part DICT of the deflate core theory): shared definitions

    - [loop_measure]: a loop whose continuing iterations decrease a measure below [2 ^ d] terminates.
    - [zframe]: the stream with its output side replaced (fill_window never touches it).
    - [inG], [heads_lt], [chains]: the hash-chain invariants of the dictionary insertions. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDLTCLib.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** Termination of [loop] by a measure *)
Lemma loop2_measure {A B : Type} (body : A -> option (A + B)) (inv : A -> Prop) (Q : B -> Prop) (m : A -> Z) :
  (forall a, inv a -> exists r, body a = Some r /\
     match r with inl a' => inv a' /\ m a' < m a | inr b => Q b end) ->
  forall d a, inv a ->
    (exists b, loop2 d body a = Some (inr b) /\ Q b) \/
    (exists a', loop2 d body a = Some (inl a') /\ inv a' /\ m a' <= m a - 2 ^ Z.of_nat d).
Proof.
  intros Hb d. induction d as [|d IH]; intros a Ha.
  - destruct (Hb a Ha) as [[a'|b] [E H]]; simpl; rewrite E.
    + right. exists a'. destruct H. split; [reflexivity|]. split; [assumption|]. simpl. lia.
    + left. eauto.
  - simpl loop2. destruct (IH a Ha) as [[b [E HQ]]|[a' [E [Ha' Hm]]]]; rewrite E.
    + left. eauto.
    + destruct (IH a' Ha') as [[b [E' HQ]]|[a'' [E' [Ha'' Hm']]]]; rewrite E'.
      * left. eauto.
      * right. exists a''. split; [reflexivity|]. split; [assumption|].
        rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia.
Qed.

Lemma loop_measure {A B : Type} (body : A -> option (A + B)) (inv : A -> Prop) (Q : B -> Prop) (m : A -> Z) d :
  (forall a, inv a -> 0 <= m a) ->
  (forall a, inv a -> exists r, body a = Some r /\
     match r with inl a' => inv a' /\ m a' < m a | inr b => Q b end) ->
  forall a, inv a -> m a < 2 ^ Z.of_nat d -> exists b, loop d body a = Some b /\ Q b.
Proof.
  intros Hm Hb a Ha Hlt. unfold loop.
  destruct (loop2_measure body inv Q m Hb d a Ha) as [[b [E HQ]]|[a' [E [Ha' Hm']]]]; rewrite E.
  - eauto.
  - specialize (Hm a' Ha'). lia.
Qed.

(** ** The stream with its output side replaced *)
Definition zframe (z : strm) (o : list Z) (ao to : Z) : strm :=
  mkST (z_in z) (z_next_in z) (z_avail_in z) (z_total_in z) o ao to (z_adler z) (z_msg z).

(** ** Hash-chain invariants of the dictionary insertions (positions below w_size, inserted: [0, n)) *)
Definition inG (n v : Z) : Prop := v = 0 \/ 0 < v < n.

(** every head entry is below [w] (the chains survive one slide_hash as NIL) *)
Definition heads_lt (w : Z) (H : list Z) : Prop :=
  forall i, 0 <= i < Zlength H -> 0 <= Znth i H < w.

(** the head entries and the prev entries of the inserted positions [1, n) are NIL or in [1, n) *)
Definition chains (n : Z) (H P : list Z) : Prop :=
  (forall i, 0 <= i < Zlength H -> inG n (Znth i H)) /\
  (forall q, 0 < q < n -> inG n (Znth q P)).
