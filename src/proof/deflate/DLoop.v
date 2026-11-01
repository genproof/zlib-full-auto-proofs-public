(** * Loops of the checked models, and checked slices

    [loop d body a]: the C loop whose one iteration is [body] ([Some (inl a')]: go on with [a']; [Some (inr r)]:
    leave the loop with [r]; [None]: the iteration is unsafe), run at most [2 ^ d] times; [None] if the iterations
    run out.  The fuel is binary ([loop2] doubles it per level), so [FUEL] can be large without anything ever
    computing a large number.  [runs body a r] is the relational reading used by the VST loop invariants:
    [loop_runs] turns a successful run into it, and [runs_inv] peels one iteration. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.trees.CBase.
Import ListNotations.
Local Open Scope Z_scope.

Fixpoint loop2 {A B : Type} (d : nat) (body : A -> option (A + B)) (a : A) : option (A + B) :=
  match d with
  | O => body a
  | S d' => match loop2 d' body a with Some (inl a') => loop2 d' body a' | r => r end
  end.

Definition loop {A B : Type} (d : nat) (body : A -> option (A + B)) (a : A) : option B :=
  match loop2 d body a with Some (inr r) => Some r | _ => None end.

(** The fuel of every loop of the deflate model: 2^40 iterations. *)
Definition FUEL : nat := 40.

Inductive runs {A B : Type} (body : A -> option (A + B)) : A -> B -> Prop :=
| runs_exit : forall a r, body a = Some (inr r) -> runs body a r
| runs_step : forall a a' r, body a = Some (inl a') -> runs body a' r -> runs body a r.

Lemma loop2_runs {A B : Type} (body : A -> option (A + B)) :
  forall d a r, loop2 d body a = Some (inr r) -> runs body a r.
Proof.
  induction d as [|d IH]; intros a r H; simpl in H.
  - apply runs_exit. exact H.
  - destruct (loop2 d body a) as [[a'|r']|] eqn:E.
    + (* first half continued with a' *)
      assert (Hr : runs body a' r) by (apply IH; exact H).
      clear H. revert a E. generalize d at 1 as d0. intros d0 a E.
      (* glue: a reaches a' (continue) in loop2 d, then a' reaches r *)
      assert (G : forall d1 x y, loop2 d1 body x = Some (inl y) -> runs body y r -> runs body x r).
      { clear. induction d1 as [|d1 IH1]; intros x y Hx Hy; simpl in Hx.
        - eapply runs_step; eauto.
        - destruct (loop2 d1 body x) as [[x'|x']|] eqn:Ex; try discriminate.
          eapply IH1; [exact Ex|]. eapply IH1; [exact Hx|exact Hy]. }
      eapply G; [exact E|exact Hr].
    + inversion H; subst. apply IH. exact E.
    + discriminate.
Qed.

Lemma loop_runs {A B : Type} (d : nat) (body : A -> option (A + B)) (a : A) (r : B) :
  loop d body a = Some r -> runs body a r.
Proof.
  unfold loop. destruct (loop2 d body a) as [[a'|r']|] eqn:E; intros H; try discriminate.
  inversion H; subst. eapply loop2_runs; eauto.
Qed.

Lemma runs_inv {A B : Type} (body : A -> option (A + B)) (a : A) (r : B) :
  runs body a r -> body a = Some (inr r) \/ exists a', body a = Some (inl a') /\ runs body a' r.
Proof. intros H; inversion H; subst; [left; auto | right; eauto]. Qed.

(** A checked slice of a fully defined array: [l[lo .. lo + n)]. *)
Definition rds (l : list Z) (lo n : Z) : option (list Z) :=
  if (0 <=? lo) && (0 <=? n) && (lo + n <=? Zlength l) then Some (sublist lo (lo + n) l) else None.

(** Signed C integers: VST requires signed arithmetic not to overflow; the model guards such operations. *)
Definition in_int (x : Z) : bool := (-2147483648 <=? x) && (x <=? 2147483647).
Definition in_long (x : Z) : bool := (-9223372036854775808 <=? x) && (x <=? 9223372036854775807).
