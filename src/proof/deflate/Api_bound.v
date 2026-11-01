(** * Body proofs of deflate.c's deflateBound and compress.c's compressBound_z, compressBound. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.Obligations.
Require Import Zlib.proof.deflate.DModel3 Zlib.proof.deflate.DSpec Zlib.proof.deflate.DCS.
Require Import Zlib.deflate.code.

Lemma repr_UMAX64 : Int64.repr UMAX64 = Int64.repr (-1).
Proof. apply Int64.eqm_samerepr. exists 1. reflexivity. Qed.

Lemma u64_shr_repr (n k : Z) : 0 <= n <= Int64.max_unsigned -> 0 <= k < 64 ->
  Int64.shru (Int64.repr n) (Int64.repr k) = Int64.repr (Z.shiftr n k).
Proof.
  intros. unfold Int64.shru. rewrite !Int64.unsigned_repr by rep_lia. reflexivity.
Qed.

Ltac u64_simpl H :=
  rewrite ?Int.unsigned_repr in H by rep_lia; rewrite ?u64_shr_repr in H by lia;
  rewrite ?add64_repr in H; rewrite ?Int64.unsigned_repr_eq in H.

Lemma body_compressBound_z : ob_compressBound_z.
Proof.
  unfold ob_compressBound_z. start_function.
  forward.
  forward_if (PROP () LOCAL (temp Zlib.compress.code._t'1 (Vlong (Int64.repr (compressBound_z n)))) SEP ()).
  - forward. entailer!. u64_simpl H0. rewrite (Z.mod_small n) in H0 by rep_lia.
    unfold compressBound_z, u64. change Int64.modulus with 18446744073709551616 in H0.
    rewrite (proj2 (Z.ltb_lt _ _) H0). rewrite repr_UMAX64. reflexivity.
  - forward. entailer!. u64_simpl H0. rewrite (Z.mod_small n) in H0 by rep_lia.
    unfold compressBound_z, u64. change Int64.modulus with 18446744073709551616 in H0.
    destruct (_ <? _) eqn:E; [apply Z.ltb_lt in E; lia|]. rewrite !u64_shr_repr by rep_lia. rewrite !add64_repr. f_equal.
    change 18446744073709551616 with Int64.modulus. rewrite <- Int64.unsigned_repr_eq, Int64.repr_unsigned. reflexivity.
  - forward.
Qed.

Lemma body_compressBound : ob_compressBound.
Proof.
  unfold ob_compressBound. start_function.
  forward_call n.
  forward_if (PROP () LOCAL (temp Zlib.compress.code._t'2 (Vlong (Int64.repr (c_compressBound n)))) SEP ()).
  - contradiction.
  - forward. entailer!.
  - forward.
Qed.

Lemma body_deflateBound : ob_deflateBound.
Proof.
  unfold ob_deflateBound. start_function.
  forward_call (os, strmp, ni, ghp, hx, n, r, gv).
  forward_if (PROP () LOCAL (temp _t'2 (Vlong (Int64.repr r))) SEP (@field_at DCS.CS Ews t_strm (DOT _next_in) ni strmp; dstream 2 os strmp ghp gv; hdr_at os ghp hx)).
  - contradiction.
  - forward. entailer!.
  - forward.
Qed.
