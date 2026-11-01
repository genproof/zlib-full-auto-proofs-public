(** * Double counting over a parent function (sums over lists of node numbers) *)

From Coq Require Import ZArith List Lia Bool Permutation.
Require Import Zlib.proof.huffman.HuffAbs.
Import ListNotations.
Local Open Scope Z_scope.

Lemma sumZ_map_add : forall {A} (f g : A -> Z) l, sumZ (map (fun x => f x + g x) l) = sumZ (map f l) + sumZ (map g l).
Proof. intros A f g l. induction l as [|a l IH]; simpl; [reflexivity|]. rewrite IH. lia. Qed.

Lemma sumZ_map_ext : forall {A} (f g : A -> Z) l, (forall x, In x l -> f x = g x) -> sumZ (map f l) = sumZ (map g l).
Proof. intros. f_equal. apply map_ext_in. auto. Qed.

Lemma sumZ_map_zero : forall {A} (l : list A), sumZ (map (fun _ => 0) l) = 0.
Proof. intros A l. induction l; simpl; auto. Qed.

Lemma sumZ_map_scal : forall {A} (c : Z) (f : A -> Z) l, sumZ (map (fun x => c * f x) l) = c * sumZ (map f l).
Proof. intros A c f l. induction l as [|a l IH]; simpl; [lia|]. rewrite IH. lia. Qed.

(** Swapping a double sum. *)
Lemma sumZ_swap : forall {A B} (f : A -> B -> Z) (l1 : list A) (l2 : list B),
  sumZ (map (fun x => sumZ (map (fun y => f x y) l2)) l1) = sumZ (map (fun y => sumZ (map (fun x => f x y) l1)) l2).
Proof.
  intros A B f l1 l2. induction l1 as [|a l1 IH]; simpl.
  - rewrite sumZ_map_zero. reflexivity.
  - rewrite IH. rewrite <- sumZ_map_add. reflexivity.
Qed.

(** The number of occurrences of [y] in a list without duplicates is 1 when [y] is in it. *)
Lemma sumZ_indicator_nodup : forall (l : list Z) y, NoDup l -> In y l ->
  sumZ (map (fun x => if x =? y then 1 else 0) l) = 1.
Proof.
  intros l y Hnd Hy. induction l as [|a l IH]; [destruct Hy|].
  inversion Hnd as [|? ? Hna Hnd']; subst. simpl. destruct Hy as [->|Hy].
  - rewrite Z.eqb_refl. rewrite (sumZ_map_ext _ (fun _ => 0)); [rewrite sumZ_map_zero; lia|].
    intros x Hx. destruct (Z.eqb_spec x y); [subst; contradiction|reflexivity].
  - destruct (Z.eqb_spec a y); [subst; contradiction|]. rewrite IH; auto.
Qed.

(** Every element of [l'] has its parent in [l] (no duplicates): the sum over [l'] regroups by parents. *)
Theorem double_count : forall (l l' : list Z) (par : Z -> Z) (phi : Z -> Z),
  NoDup l -> (forall v, In v l' -> In (par v) l) ->
  sumZ (map phi l') = sumZ (map (fun y => sumZ (map (fun v => if par v =? y then phi v else 0) l')) l).
Proof.
  intros l l' par phi Hnd Hpar.
  rewrite (sumZ_swap (fun y v => if par v =? y then phi v else 0) l l').
  apply sumZ_map_ext. intros v Hv.
  rewrite (sumZ_map_ext _ (fun y => phi v * (if y =? par v then 1 else 0))).
  - rewrite sumZ_map_scal. rewrite sumZ_indicator_nodup; auto. lia.
  - intros y Hy. destruct (Z.eqb_spec (par v) y), (Z.eqb_spec y (par v)); subst; try lia; congruence.
Qed.

(** Counting the elements of [l'] with parent [y]. *)
Definition nkids (l' : list Z) (par : Z -> Z) (y : Z) : Z := sumZ (map (fun v => if par v =? y then 1 else 0) l').

Corollary double_count_const : forall (l l' : list Z) (par : Z -> Z) (psi : Z -> Z),
  NoDup l -> (forall v, In v l' -> In (par v) l) ->
  sumZ (map (fun v => psi (par v)) l') = sumZ (map (fun y => nkids l' par y * psi y) l).
Proof.
  intros l l' par psi Hnd Hpar. rewrite (double_count l l' par (fun v => psi (par v)) Hnd Hpar).
  apply sumZ_map_ext. intros y Hy. unfold nkids. rewrite Z.mul_comm, <- sumZ_map_scal.
  apply sumZ_map_ext. intros v Hv. destruct (Z.eqb_spec (par v) y); subst; lia.
Qed.
