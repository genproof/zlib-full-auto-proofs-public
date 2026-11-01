(* Round-trip laws, part RT-CB: pure facts for compress2_z's body: deflateInit's return codes and the
   destination's contents around a deflate call. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist VST.zlist.list_solver.
Require Import Zlib.proof.deflate.LTBInit Zlib.proof.deflate.LTCInitKit.
Import ListNotations.
Local Open Scope Z_scope.

Lemma c2_init_code level a1 a2 a3 a4 a5 z os z' code :
  c_deflateInit2_ true true false level 8 15 8 0 a1 a2 a3 a4 a5 z = Some (os, z', code) ->
  code = Z_OK \/ code = Z_STREAM_ERROR \/ code = Z_MEM_ERROR.
Proof.
  intros H. rewrite bi_shape in H.
  destruct (params_ok level 8 15 8 0) eqn:P; [| injection H as _ _ <-; auto].
  destruct a1; [| injection H as _ _ <-; auto].
  destruct (a2 && a3 && a4 && a5)%bool; [| injection H as _ _ <-; auto].
  rewrite (init_eq _ _ _ _ _ _ P) in H. injection H as _ _ <-. auto.
Qed.

Lemma c2_init_none level a1 a2 a3 a4 a5 z os z' code :
  c_deflateInit2_ true true false level 8 15 8 0 a1 a2 a3 a4 a5 z = Some (os, z', code) ->
  code <> Z_OK -> os = None.
Proof.
  intros H Hc. rewrite bi_shape in H.
  destruct (params_ok level 8 15 8 0) eqn:P; [| injection H as <- _ _; auto].
  destruct a1; [| injection H as <- _ _; auto].
  destruct (a2 && a3 && a4 && a5)%bool; [| injection H as <- _ _; auto].
  rewrite (init_eq _ _ _ _ _ _ P) in H. injection H as _ _ <-. contradiction.
Qed.

Section Dest.
Context {A : Type} {d : Inhabitant A}.

Lemma dest_rest (out : list A) (dc : list A) cap :
  Zlength dc = cap -> Zlength out <= cap ->
  sublist (Zlength out) cap (out ++ sublist (Zlength out) cap dc) = sublist (Zlength out) cap dc.
Proof. intros. list_solve. Qed.

Lemma dest_pre (out : list A) (dc : list A) cap :
  Zlength dc = cap -> Zlength out <= cap ->
  sublist 0 (Zlength out) (out ++ sublist (Zlength out) cap dc) = out.
Proof. intros. list_solve. Qed.

Lemma dest_len (out : list A) (dc : list A) cap :
  Zlength dc = cap -> Zlength out <= cap ->
  Zlength (out ++ sublist (Zlength out) cap dc) = cap.
Proof. intros. list_solve. Qed.

Lemma dest_step (out zo : list A) (dc : list A) cap :
  Zlength dc = cap -> Zlength out + Zlength zo <= cap ->
  out ++ (zo ++ sublist (Zlength zo) (cap - Zlength out) (sublist (Zlength out) cap dc)) =
  (out ++ zo) ++ sublist (Zlength (out ++ zo)) cap dc.
Proof. intros. list_solve. Qed.

End Dest.
