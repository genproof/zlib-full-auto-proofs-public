(* Integer facts for the deflate proofs: the C operations of zlib's bit writer and buffer arithmetic on
   representable values, as operations on Z. *)
Require Import VST.floyd.proofauto.

Lemma zext8_repr c: Int.zero_ext 8 (Int.repr c) = Int.repr (c mod 256).
Proof.
  rewrite <- (Int.repr_unsigned (Int.zero_ext 8 (Int.repr c))).
  rewrite Int.zero_ext_mod by (cbn; lia).
  rewrite Int.unsigned_repr_eq. f_equal. change (two_p 8) with 256.
  symmetry. apply Znumtheory.Zmod_div_mod; [lia | reflexivity | exists 16777216; reflexivity].
Qed.

Lemma zext16_repr c: Int.zero_ext 16 (Int.repr c) = Int.repr (c mod 65536).
Proof.
  rewrite <- (Int.repr_unsigned (Int.zero_ext 16 (Int.repr c))).
  rewrite Int.zero_ext_mod by (cbn; lia).
  rewrite Int.unsigned_repr_eq. f_equal. change (two_p 16) with 65536.
  symmetry. apply Znumtheory.Zmod_div_mod; [lia | reflexivity | exists 65536; reflexivity].
Qed.

Lemma zext8_idem c: Int.zero_ext 8 (Int.zero_ext 8 c) = Int.zero_ext 8 c.
Proof. apply Int.zero_ext_idem. lia. Qed.

Lemma and255_repr x: Int.and (Int.repr x) (Int.repr 255) = Int.repr (x mod 256).
Proof.
  unfold Int.and. rewrite (Int.unsigned_repr 255) by rep_lia.
  change 255 with (Z.ones 8). rewrite Z.land_ones by lia.
  rewrite Int.unsigned_repr_eq. change (2 ^ 8) with 256. f_equal.
  symmetry. apply Znumtheory.Zmod_div_mod; [lia | reflexivity | exists 16777216; reflexivity].
Qed.

Lemma shru_repr x k: 0 <= x <= Int.max_unsigned -> 0 <= k < Int.zwordsize ->
  Int.shru (Int.repr x) (Int.repr k) = Int.repr (x / two_p k).
Proof.
  intros X K. rewrite Int.shru_div_two_p. rewrite !Int.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma shr_repr x k: 0 <= x <= Int.max_signed -> 0 <= k < Int.zwordsize ->
  Int.shr (Int.repr x) (Int.repr k) = Int.repr (x / two_p k).
Proof.
  intros X K. rewrite Int.shr_div_two_p. rewrite Int.signed_repr by rep_lia.
  rewrite Int.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma byte_mod_range x: 0 <= x mod 256 <= 255.
Proof. pose proof (Z.mod_pos_bound x 256). lia. Qed.

Lemma ush_mod_range x: 0 <= x mod 65536 <= 65535.
Proof. pose proof (Z.mod_pos_bound x 65536). lia. Qed.

(* tc_val of small numbers *)
Lemma tc_val_tushort_repr x: 0 <= x <= 65535 -> tc_val tushort (Vint (Int.repr x)).
Proof. intros. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. Qed.

Lemma tc_val_tuchar_repr x: 0 <= x <= 255 -> tc_val tuchar (Vint (Int.repr x)).
Proof. intros. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. Qed.

Ltac tc_small :=
  first [ apply tc_val_tushort_repr; lia | apply tc_val_tuchar_repr; lia ].

(* Int64 sums of small numbers *)
Lemma add64_repr a b: Int64.add (Int64.repr a) (Int64.repr b) = Int64.repr (a + b).
Proof. apply Int64.eqm_samerepr. unfold Int64.add. apply Int64.eqm_add; apply Int64.eqm_sym, Int64.eqm_unsigned_repr. Qed.

Lemma sub64_repr a b: Int64.sub (Int64.repr a) (Int64.repr b) = Int64.repr (a - b).
Proof. apply Int64.eqm_samerepr. unfold Int64.sub. apply Int64.eqm_sub; apply Int64.eqm_sym, Int64.eqm_unsigned_repr. Qed.

Lemma signed_repr_small a: Int.min_signed <= a <= Int.max_signed -> Int.signed (Int.repr a) = a.
Proof. apply Int.signed_repr. Qed.

Lemma sub_repr32 a b: Int.sub (Int.repr a) (Int.repr b) = Int.repr (a - b).
Proof. apply Int.eqm_samerepr. unfold Int.sub. apply Int.eqm_sub; apply Int.eqm_sym, Int.eqm_unsigned_repr. Qed.

Lemma add_repr32 a b: Int.add (Int.repr a) (Int.repr b) = Int.repr (a + b).
Proof. apply Int.eqm_samerepr. unfold Int.add. apply Int.eqm_add; apply Int.eqm_sym, Int.eqm_unsigned_repr. Qed.

Lemma and_repr32 a b: Int.and (Int.repr a) (Int.repr b) = Int.repr (Z.land a b).
Proof.
  apply Int.same_bits_eq. intros i Hi.
  rewrite Int.bits_and by auto. rewrite !Int.testbit_repr by auto.
  rewrite Z.land_spec. reflexivity.
Qed.

Lemma or_repr32 a b: Int.or (Int.repr a) (Int.repr b) = Int.repr (Z.lor a b).
Proof.
  apply Int.same_bits_eq. intros i Hi.
  rewrite Int.bits_or by auto. rewrite !Int.testbit_repr by auto.
  rewrite Z.lor_spec. reflexivity.
Qed.

(* decide the boolean comparisons of the goal by lia *)
Ltac decide_cmps :=
  repeat match goal with
  | |- context [?a <? ?b] =>
      first [ rewrite (proj2 (Z.ltb_lt a b)) by lia | rewrite (proj2 (Z.ltb_ge a b)) by lia ]
  | |- context [?a <=? ?b] =>
      first [ rewrite (proj2 (Z.leb_le a b)) by lia | rewrite (proj2 (Z.leb_gt a b)) by lia ]
  | |- context [?a =? ?b] =>
      first [ rewrite (proj2 (Z.eqb_eq a b)) by lia | rewrite (proj2 (Z.eqb_neq a b)) by lia ]
  end.

Lemma div256_ush b: 0 <= b < 65536 -> 0 <= b / 256 < 65536.
Proof. intros. split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia. Qed.

Lemma land7_mod x: Z.land x 7 = x mod 8.
Proof. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.
