(** * Tactics and small lemmas for the body proof of deflateInit2_. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DModel3 Zlib.proof.deflate.DSpec Zlib.proof.deflate.DCS.
Require Import Zlib.deflate.code.

Lemma ni_valid (ni p : val) :
  (@field_at DCS.CS Ews t_strm (DOT _next_in) ni p * TT)%logic |-- valid_pointer p.
Proof. apply sepcon_valid_pointer1. apply field_at_valid_ptr0; auto; reflexivity. Qed.

Lemma repr_inj_s32 x y : s32_ok x -> s32_ok y -> Int.repr x = Int.repr y -> x = y.
Proof.
  unfold s32_ok; intros Hx Hy E. apply (f_equal Int.signed) in E. rewrite !Int.signed_repr in E by rep_lia. exact E.
Qed.

Lemma ueq_s32 x y : Int.min_signed <= x <= Int.max_signed -> Int.min_signed <= y <= Int.max_signed ->
  Int.unsigned (Int.repr x) = Int.unsigned (Int.repr y) -> x = y.
Proof.
  intros Hx Hy E. apply repr_inj_s32; unfold s32_ok; auto.
  rewrite <- (Int.repr_unsigned (Int.repr x)), <- (Int.repr_unsigned (Int.repr y)), E. reflexivity.
Qed.

Ltac cmp_solve :=
  unfold s32_ok in *;
  repeat match goal with
   | H : typed_true _ _ |- _ => unfold typed_true, strict_bool_val in H
   | H : typed_false _ _ |- _ => unfold typed_false, strict_bool_val in H end;
  rewrite ?Int.signed_repr in * by rep_lia;
  unfold Int.lt, Int.eq, Val.of_bool, bool2val;
  repeat match goal with
   | H : _ = Some _ |- _ => progress unfold Val.of_bool, bool2val, Int.eq, Int.lt in H
   | H : _ = Some _ |- _ => progress rewrite ?Int.signed_repr, ?Int.unsigned_repr in H by rep_lia end;
  rewrite ?Int.signed_repr, ?Int.unsigned_repr by rep_lia;
  repeat match goal with
   | |- context [Z.ltb ?x ?y] => destruct (Z.ltb_spec x y)
   | |- context [Z.gtb ?x ?y] => destruct (Z.gtb_spec x y)
   | |- context [Z.eqb ?x ?y] => destruct (Z.eqb_spec x y)
   | |- context [zlt ?x ?y] => destruct (zlt x y)
   | |- context [zeq ?x ?y] => destruct (zeq x y)
   | H : _ = Some _ |- _ => match type of H with context [Z.ltb ?x ?y] => destruct (Z.ltb_spec x y) end
   | H : _ = Some _ |- _ => match type of H with context [Z.gtb ?x ?y] => destruct (Z.gtb_spec x y) end
   | H : _ = Some _ |- _ => match type of H with context [Z.eqb ?x ?y] => destruct (Z.eqb_spec x y) end
  end; simpl;
  repeat match goal with H : _ = Some _ |- _ => progress simpl in H end;
  repeat match goal with H : context [Int.signed (Int.repr ?x)] |- _ =>
    rewrite (Int.signed_repr x) in H by rep_lia end;
  repeat match goal with H : Int.unsigned (Int.repr ?x) = Int.unsigned (Int.repr ?y) |- _ =>
    apply ueq_s32 in H; [ | rep_lia | rep_lia] end;
  try reflexivity; try congruence; try rep_lia;
  try (match goal with H: _ = Some _ |- _ => vm_compute in H; discriminate end).

