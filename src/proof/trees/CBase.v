(** * Checked functional models: the option monad shared by the models of trees.c and deflate.c

    A checked model function returns [None] exactly when the C code it transcribes would do something the proofs
    exclude: access an array out of its bounds, read a byte of a buffer that was never written (pending_buf and
    the window come from malloc uninitialised), run a loop past its fuel; otherwise it returns [Some r] with [r]
    what the C code computes.  The VST specification of a C function [f] is then uniform:

      PRE   the representation of the arguments, and [c_f args = Some r]
      POST  the representation of [r].

    So every proof that a call is safe is a pure Coq proof that the checked run succeeds, and the VST proofs
    follow the model statement by statement (each [let*] of the model is one access of the C code).

    Masked buffers: a byte buffer whose bytes may be undefined is a list of numbers [mb_val] together with a list
    of booleans [mb_def] (true = written); its VST contents are [vi (Znth i mb_val)] where [mb_def] is true and
    [Vundef] elsewhere ([mb_vals]). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Import ListNotations.
Local Open Scope Z_scope.

Definition bind {A B : Type} (a : option A) (f : A -> option B) : option B :=
  match a with Some x => f x | None => None end.

Declare Scope cmodel_scope.
Notation "'let*' p ':=' c1 'in' c2" := (bind c1 (fun p => c2))
  (at level 200, p pattern, c1 at level 100, c2 at level 200, right associativity) : cmodel_scope.
Open Scope cmodel_scope.

Definition guard (b : bool) : option unit := if b then Some tt else None.

Definition in_range (i n : Z) : bool := (0 <=? i) && (i <? n).

(** A checked read / write of an array of numbers. *)
Definition rd (l : list Z) (i : Z) : option Z :=
  if in_range i (Zlength l) then Some (Znth i l) else None.
Definition wr (l : list Z) (i v : Z) : option (list Z) :=
  if in_range i (Zlength l) then Some (upd_Znth i l v) else None.

(** Masked byte buffers. *)
Record mbuf := mkMB { mb_val : list Z; mb_def : list bool }.

Definition mb_ok (b : mbuf) : Prop :=
  Zlength (mb_def b) = Zlength (mb_val b) /\
  forall i, 0 <= i < Zlength (mb_val b) -> Znth i (mb_def b) = true -> 0 <= Znth i (mb_val b) < 256.

Definition mb_rd (b : mbuf) (i : Z) : option Z :=
  if in_range i (Zlength (mb_val b)) && Znth i (mb_def b) then Some (Znth i (mb_val b)) else None.
Definition mb_wr (b : mbuf) (i v : Z) : option mbuf :=
  if in_range i (Zlength (mb_val b)) then Some (mkMB (upd_Znth i (mb_val b) v) (upd_Znth i (mb_def b) true))
  else None.

(** All bytes of [b] in [lo, hi) are defined. *)
Definition mb_defined (b : mbuf) (lo hi : Z) : Prop :=
  0 <= lo /\ hi <= Zlength (mb_val b) /\ forall i, lo <= i < hi -> Znth i (mb_def b) = true.
Definition mb_definedb (b : mbuf) (lo hi : Z) : bool :=
  (0 <=? lo) && (hi <=? Zlength (mb_val b)) &&
  forallb (fun i => Znth i (mb_def b)) (map (fun k => lo + Z.of_nat k) (seq 0 (Z.to_nat (hi - lo)))).

(** Checked block read / write (memcpy into / out of a masked buffer). *)
Definition mb_read (b : mbuf) (lo len : Z) : option (list Z) :=
  if (0 <=? len) && mb_definedb b lo (lo + len) then Some (sublist lo (lo + len) (mb_val b)) else None.
Definition mb_write (b : mbuf) (lo : Z) (src : list Z) : option mbuf :=
  let hi := lo + Zlength src in
  if (0 <=? lo) && (hi <=? Zlength (mb_val b)) then
    Some (mkMB (sublist 0 lo (mb_val b) ++ src ++ sublist hi (Zlength (mb_val b)) (mb_val b))
               (sublist 0 lo (mb_def b) ++ repeat true (Z.to_nat (Zlength src)) ++
                sublist hi (Zlength (mb_def b)) (mb_def b)))
  else None.
