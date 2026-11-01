(* The bodies of the helpers of harness/laws_session.h against their specifications (Spec.v), one lemma per
   helper, and their conjunction laws_session_bodies : laws_session_ok.  The range tests (at CS_none) go through
   C's short-circuit && and || one [if] at a time, each temporary holding [Val.of_bool] of the test so far (bfin
   closes each step by the cases of the integer comparisons).  unmoved and accounted compare pointers: the
   comparability comes from the memory [B] the caller lends (tc_test_eq_sepcon moves it out of the frame);
   counted's comparison is C's uInt difference and uLong sum (counted_eq). *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.laws_session.Spec.

Lemma prop_sepcon_TT (p : Prop) : (!!p * TT : mpred) |-- !!p.
Proof.
  eapply derives_trans; [apply sepcon_derives; [rewrite <- (andp_TT (!!p)) at 1; apply derives_refl | apply derives_refl] |].
  rewrite sepcon_andp_prop'. apply andp_left1, derives_refl.
Qed.

(* The comparability of two pointers ([==]) in a part of the memory holds in the whole memory. *)
Lemma tc_test_eq_sepcon (P Q : mpred) (x y : val) :
  P |-- denote_tc_test_eq x y -> P * Q |-- denote_tc_test_eq x y.
Proof.
  intros H. eapply derives_trans; [apply sepcon_derives; [exact H | apply TT_right] |]. clear H.
  Transparent denote_tc_test_eq.
  unfold denote_tc_test_eq; destruct x, y; simpl;
    try (rewrite FF_sepcon; apply derives_refl);
    try (normalize; apply andp_right; apply prop_right; auto; fail).
  all: (try (unfold test_eq_ptrs; destruct (sameblock _ _));
    (apply andp_right;
    [ eapply derives_trans; [apply sepcon_derives; [apply andp_left1, derives_refl | apply derives_refl] |]
    | eapply derives_trans; [apply sepcon_derives; [apply andp_left2, derives_refl | apply derives_refl] |] ]);
    first [ apply extend_weak_valid_pointer | apply extend_valid_pointer
          | apply prop_sepcon_TT ]).
  Opaque denote_tc_test_eq.
Qed.

Lemma ptr_eqb_refl (x : val) : ptr_eqb x x = true.
Proof. unfold ptr_eqb. destruct (Val.eq x x); congruence. Qed.

Lemma ptr_eqb_neq (x y : val) : x <> y -> ptr_eqb x y = false.
Proof. unfold ptr_eqb. destruct (Val.eq x y); congruence. Qed.

Lemma int_eq_repr (a b : Z) :
  0 <= a <= Int.max_unsigned -> 0 <= b <= Int.max_unsigned -> Int.eq (Int.repr a) (Int.repr b) = (a =? b).
Proof.
  intros. destruct (Z.eqb_spec a b).
  - subst. apply Int.eq_true.
  - apply Int.eq_false. intro E. apply repr_inj_unsigned in E; auto.
Qed.

Lemma int64_eq_repr (a b : Z) :
  0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned -> Int64.eq (Int64.repr a) (Int64.repr b) = (a =? b).
Proof.
  intros. destruct (Z.eqb_spec a b).
  - subst. apply Int64.eq_true.
  - apply Int64.eq_false. intro E. apply repr_inj_unsigned64 in E; auto.
Qed.

Lemma bool2val_zeq (a b : Z) : bool2val (zeq a b) = Val.of_bool (a =? b).
Proof. destruct (zeq a b), (Z.eqb_spec a b); try congruence; reflexivity. Qed.

(* the branches of an [if] on a C boolean [Val.of_bool b]: the case of [b] *)
Ltac tf_case :=
  match goal with
  | H : typed_true _ (if ?b then _ else _) |- _ => destruct b eqn:?; [clear H | cbv in H; discriminate]
  | H : typed_false _ (if ?b then _ else _) |- _ => destruct b eqn:?; [cbv in H; discriminate | clear H]
  end.

(* [ptr_eqb x y] against the C comparison's [eq_dec x y] *)
Ltac ptr_cmp_case :=
  unfold ptr_eqb;
  match goal with |- context [Val.eq ?x ?y] => destruct (Val.eq x y) end;
  match goal with |- context [@eq_dec _ ?D ?x ?y] => destruct (@eq_dec _ D x y) end;
  first [ reflexivity | exfalso; unfold offset_val in *; congruence ].

(* counted's comparison total == total' + (avail' - avail): the uInt difference modulo 2^32, the uLong sum
   modulo 2^64 *)
Lemma counted_eq (t t' a a' : Z) :
  0 <= t <= Int64.max_unsigned ->
  Int64.eq (Int64.repr t) (Int64.repr (t' + Int.unsigned (Int.repr (a' - a)))) =
  (t =? (t' + (a' - a) mod Int.modulus) mod Int64.modulus).
Proof.
  intros Ht. rewrite Int.unsigned_repr_eq.
  rewrite <- (Int64.repr_unsigned (Int64.repr (t' + _))), Int64.unsigned_repr_eq.
  apply int64_eq_repr; [ lia | ].
  pose proof (Z.mod_pos_bound (t' + (a' - a) mod Int.modulus) Int64.modulus ltac:(rep_lia)). rep_lia.
Qed.

(* closes [Val.of_bool b = <C's value>] by the cases of the integer comparisons *)
Ltac bfin :=
  unfold deflate_params_valid, inflate_window_valid, Int.lt, Int.eq in *;
  rewrite ?Int.signed_repr, ?Int.unsigned_repr in * by rep_lia;
  repeat match goal with
  | |- context [zlt ?a ?b] => destruct (zlt a b)
  | |- context [zle ?a ?b] => destruct (zle a b)
  | |- context [zeq ?a ?b] => destruct (zeq a b)
  | |- context [?a <=? ?b] => destruct (Z.leb_spec a b)
  | |- context [?a <? ?b] => destruct (Z.ltb_spec a b)
  | |- context [?a =? ?b] => destruct (Z.eqb_spec a b)
  end; simpl in *; first [reflexivity | lia | discriminate].

Ltac bstep := forward; entailer!; bfin.

(* the same where deflate_params_ok's [valid] part is already known (the case split stays small) *)
Ltac vstep :=
  forward; entailer!; unfold deflate_params_valid;
  repeat match goal with E : ?b = true |- context [?b] => rewrite E end;
  repeat match goal with E : ?b = false |- context [?b] => rewrite E end;
  bfin.

Lemma land15_range (w : Z) : 0 <= Z.land w 15 <= 15.
Proof.
  change (Z.land w 15) with (Z.land w (Z.ones 4)). rewrite Z.land_ones by lia.
  pose proof (Z.mod_pos_bound w (2 ^ 4) ltac:(lia)). simpl in *. lia.
Qed.

Lemma land15_repr (w : Z) : 0 <= w <= Int.max_unsigned -> Int.and (Int.repr w) (Int.repr 15) = Int.repr (Z.land w 15).
Proof. intros. unfold Int.and. rewrite !Int.unsigned_repr by rep_lia. reflexivity. Qed.

Section RangeTests.
#[local] Existing Instance CS_none.

Lemma body_deflate_params_ok : semax_body Vprog_ls Gprog_ls RS.f_deflate_params_ok deflate_params_ok_spec.
Proof.
  start_function.
  forward_if (temp RS._t'1 (Val.of_bool ((8 <=? wbits) && (wbits <=? 15)))); [bstep | bstep |].
  forward.
  forward_if (temp RS._t'2 (Val.of_bool ((-15 <=? wbits) && (wbits <=? -9)))); [bstep | bstep |].
  forward.
  forward_if (temp RS._t'3 (Val.of_bool ((25 <=? wbits) && (wbits <=? 31)))); [bstep | bstep |].
  forward.
  forward_if (temp RS._t'4 (Val.of_bool ((-1 <=? level) && (level <=? 9)))); [bstep | bstep |].
  forward_if (temp RS._t'5 (Val.of_bool ((-1 <=? level) && (level <=? 9) && (1 <=? mem))));
    [tf_case; bstep | tf_case; bstep |].
  forward_if (temp RS._t'6 (Val.of_bool ((-1 <=? level) && (level <=? 9) && (1 <=? mem) && (mem <=? 9))));
    [tf_case; bstep | tf_case; bstep |].
  forward_if (temp RS._t'7 (Val.of_bool ((-1 <=? level) && (level <=? 9) && (1 <=? mem) && (mem <=? 9) &&
                                         (0 <=? strategy))));
    [tf_case; bstep | tf_case; bstep |].
  forward_if (temp RS._t'8 (Val.of_bool ((-1 <=? level) && (level <=? 9) && (1 <=? mem) && (mem <=? 9) &&
                                         (0 <=? strategy) && (strategy <=? 4))));
    [tf_case; bstep | tf_case; bstep |].
  forward.
  forward_if (temp RS._t'9 (Val.of_bool (deflate_params_valid level wbits mem strategy))).
  { tf_case.
    forward_if (temp RS._t'10 (Val.of_bool ((8 <=? wbits) && (wbits <=? 15) || (-15 <=? wbits) && (wbits <=? -9))));
      [tf_case; bstep | tf_case; bstep |].
    forward_if; [tf_case; vstep | tf_case; forward; vstep]. }
  { tf_case. vstep. }
  forward.
Qed.
Lemma body_inflate_window_ok : semax_body Vprog_ls Gprog_ls AI.f_inflate_window_ok inflate_window_ok_spec.
Proof.
  start_function.
  pose proof (land15_range w) as LB.
  forward.
  forward_if (temp AI._t'1 (Val.of_bool ((-15 <=? w) && (w <=? -8)))); [bstep | bstep |].
  forward.
  forward_if (temp AI._t'2 (Val.of_bool ((0 <=? w) && (w <? 48)))); [bstep | bstep |].
  forward_if (temp AI._t'3 (Val.of_bool ((0 <=? w) && (w <? 48) && ((Z.land w 15 =? 0) || (8 <=? Z.land w 15))))).
  { tf_case.
    assert (W : 0 <= w < 48) by (apply andb_prop in Heqb; destruct Heqb as [W1 W2]; apply Z.leb_le in W1; apply Z.ltb_lt in W2; lia).
    rewrite land15_repr by rep_lia.
    forward_if; [bstep | forward; bstep]. }
  { tf_case. bstep. }
  forward.
  forward_if (temp AI._t'4 (Val.of_bool (inflate_window_valid w))); [tf_case; bstep | tf_case; bstep |].
  forward.
Qed.

End RangeTests.

Section Bodies.
#[local] Existing Instance CS_session.

Lemma body_unmoved : semax_body Vprog_ls Gprog_ls RS.f_unmoved unmoved_spec.
Proof.
  start_function.
  destruct c as [ni ai ti no ao to], a as [ni' ai' ti' no' ao' to'], r as [[[[[[[msg st] za] zf] op] dt] ad] rs].
  unfold zs_of, pos_of, pos_val, zs_val; simpl pz_next_in; simpl pz_avail_in; simpl pz_total_in; simpl pz_next_out; simpl pz_avail_out; simpl pz_total_out.
  unfold posz_ok in H, H0; cbn in H, H0.
  destruct H as (Pi & Po & Ai & Ti & Ao & To), H0 as (Pi' & Po' & Ai' & Ti' & Ao' & To').
  forward. forward.
  forward_if (temp RS._t'1 (Val.of_bool (ptr_eqb ni ni' && (ai =? ai')))).
  { rewrite (sepcon_comm _ (B && _)). apply tc_test_eq_sepcon. unfold unmoved_cmp; simpl. apply andp_left2, andp_left1, derives_refl. }
  { subst ni'. forward. forward. forward. entailer!. rewrite ptr_eqb_refl, bool2val_zeq. reflexivity. }
  { forward. entailer!. rewrite ptr_eqb_neq by auto. reflexivity. }
  forward_if (temp RS._t'2 (Val.of_bool (ptr_eqb ni ni' && (ai =? ai') && (ti =? ti')))).
  { tf_case. forward. forward. forward. entailer!. rewrite bool2val_zeq. reflexivity. }
  { tf_case. forward. entailer!. }
  forward.
  forward. forward.
  forward_if (temp RS._t'3 (Val.of_bool (ptr_eqb no no' && (ao =? ao')))).
  { rewrite (sepcon_comm _ (B && _)). apply tc_test_eq_sepcon. unfold unmoved_cmp; simpl. apply andp_left2, andp_left2, derives_refl. }
  { subst no'. forward. forward. forward. entailer!. rewrite ptr_eqb_refl, bool2val_zeq. reflexivity. }
  { forward. entailer!. rewrite ptr_eqb_neq by auto. reflexivity. }
  forward_if (temp RS._t'4 (Val.of_bool (ptr_eqb no no' && (ao =? ao') && (to =? to')))).
  { tf_case. forward. forward. forward. entailer!. rewrite bool2val_zeq. reflexivity. }
  { tf_case. forward. entailer!. }
  forward.
  forward_if (temp RS._t'5 (Val.of_bool ((ptr_eqb ni ni' && (ai =? ai') && (ti =? ti')) &&
                                          (ptr_eqb no no' && (ao =? ao') && (to =? to'))))).
  { tf_case. forward. entailer!. destruct (ptr_eqb no no' && (ao =? ao') && (to =? to'))%bool; reflexivity. }
  { tf_case. forward. entailer!. }
  forward.
  unfold zs_of, pos_of, pos_val, zs_val. cancel. apply andp_left1, derives_refl.
Qed.

Lemma body_accounted : semax_body Vprog_ls Gprog_ls AI.f_accounted accounted_spec.
Proof.
  start_function.
  destruct c as [ni ai ti no ao to], a as [ni' ai' ti' no' ao' to'], r as [[[[[[[msg st] za] zf] op] dt] ad] rs].
  unfold zs_of, pos_of, pos_val, zs_val; simpl pz_next_in; simpl pz_avail_in; simpl pz_total_in; simpl pz_next_out; simpl pz_avail_out; simpl pz_total_out.
  unfold posz_ok in H, H0; cbn in H, H0.
  destruct H as (Pi & Po & Ai & Ti & Ao & To), H0 as (Pi' & Po' & Ai' & Ti' & Ao' & To').
  cbn in H1, H2, H3, H4.
  forward. forward.
  forward_if (temp AI._t'1 (Val.of_bool ((ai <=? ai') && ptr_eqb (offset_val ai ni) (offset_val ai' ni')))).
  { forward. forward. forward. forward.
    forward.
    { destruct ni; try contradiction; destruct ni'; try contradiction. entailer!.
      rewrite (sepcon_comm _ (B && _)). apply tc_test_eq_sepcon. unfold accounted_cmp; simpl.
      apply andp_left2, andp_left1, derives_refl. }
    destruct ni; try contradiction; destruct ni'; try contradiction. entailer!.
    rewrite (proj2 (Z.leb_le ai ai')) by lia. ptr_cmp_case. }
  { forward. entailer!. rewrite (proj2 (Z.leb_gt ai ai')) by lia. reflexivity. }
  forward.
  forward. forward.
  forward_if (temp AI._t'2 (Val.of_bool ((ao <=? ao') && ptr_eqb (offset_val ao no) (offset_val ao' no')))).
  { forward. forward. forward. forward.
    forward.
    { destruct no; try contradiction; destruct no'; try contradiction. entailer!.
      rewrite (sepcon_comm _ (B && _)). apply tc_test_eq_sepcon. unfold accounted_cmp; simpl.
      apply andp_left2, andp_left2, derives_refl. }
    destruct no; try contradiction; destruct no'; try contradiction. entailer!.
    rewrite (proj2 (Z.leb_le ao ao')) by lia. ptr_cmp_case. }
  { forward. entailer!. rewrite (proj2 (Z.leb_gt ao ao')) by lia. reflexivity. }
  forward.
  forward_if (temp AI._t'3 (Val.of_bool (((ai <=? ai') && ptr_eqb (offset_val ai ni) (offset_val ai' ni')) &&
                                          ((ao <=? ao') && ptr_eqb (offset_val ao no) (offset_val ao' no'))))).
  { tf_case. forward. entailer!.
    destruct ((ao <=? ao') && ptr_eqb (offset_val ao no) (offset_val ao' no'))%bool; reflexivity. }
  { tf_case. forward. entailer!. }
  forward.
  unfold zs_of, pos_of, pos_val, zs_val. cancel. apply andp_left1, derives_refl.
Qed.

Lemma body_counted : semax_body Vprog_ls Gprog_ls AI.f_counted counted_spec.
Proof.
  start_function.
  destruct c as [ni ai ti no ao to], a as [ni' ai' ti' no' ao' to'], r as [[[[[[[msg st] za] zf] op] dt] ad] rs].
  unfold zs_of, pos_of, pos_val, zs_val; simpl pz_next_in; simpl pz_avail_in; simpl pz_total_in; simpl pz_next_out; simpl pz_avail_out; simpl pz_total_out.
  unfold posz_ok in H, H0; cbn in H, H0.
  destruct H as (Pi & Po & Ai & Ti & Ao & To), H0 as (Pi' & Po' & Ai' & Ti' & Ao' & To').
  forward. forward. forward. forward. forward.
  forward. forward. forward. forward. forward.
  forward_if (temp AI._t'1 (Val.of_bool (counted_b (mk_posz ni ai ti no ao to) (mk_posz ni' ai' ti' no' ao' to')))).
  { forward. entailer!. rewrite counted_eq in H by rep_lia. unfold counted_b; cbn [pz_total_in pz_avail_in pz_total_out pz_avail_out].
    rewrite H. unfold Int64.cmpu. rewrite counted_eq by rep_lia. destruct (to =? _); reflexivity. }
  { forward. entailer!.
    match goal with N : Int64.repr ?x <> Int64.repr ?y |- _ =>
      assert (E : Int64.eq (Int64.repr x) (Int64.repr y) = false) by (apply Int64.eq_false; exact N) end.
    rewrite counted_eq in E by rep_lia. unfold counted_b; cbn [pz_total_in pz_avail_in pz_total_out pz_avail_out].
    rewrite E. reflexivity. }
  forward.
Qed.

Lemma body_position_of : semax_body Vprog_ls Gprog_ls AI.f_position_of position_of_spec.
Proof.
  start_function.
  destruct c as [ni ai ti no ao to], r as [[[[[[[msg st] za] zf] op] dt] ad] rs].
  unfold zs_of, pos_of, pos_val, zs_val; simpl pz_next_in; simpl pz_avail_in; simpl pz_total_in; simpl pz_next_out; simpl pz_avail_out; simpl pz_total_out.
  unfold posz_ok in H; cbn in H.
  destruct H as (Pi & Po & Ai & Ti & Ao & To).
  forward. forward. forward. forward. forward. forward.
  forward. forward. forward. forward. forward. forward.
  entailer!.
Qed.

End Bodies.

Lemma laws_session_bodies : laws_session_ok.
Proof.
  split; [exact body_deflate_params_ok | ].
  split; [exact body_inflate_window_ok | ].
  split; [exact body_position_of | ].
  split; [exact body_unmoved | ].
  split; [exact body_accounted | exact body_counted].
Qed.
