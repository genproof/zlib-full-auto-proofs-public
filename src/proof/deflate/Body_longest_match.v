(** * The body of longest_match (deflate.c) against its shared specification DSpec.longest_match_spec (v2 base) *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.trees.TLemmas.
Require Import Zlib.proof.deflate.Obligations.
Require Import Zlib.deflate.code.

#[export] Existing Instance DCS.CS.

Open Scope cmodel_scope.

(** ** Integer and pointer arithmetic *)

Lemma u32_unsigned x : Int.unsigned (Int.repr x) = u32 x.
Proof. rewrite Int.unsigned_repr_eq. reflexivity. Qed.

Lemma repr_u32 x : Int.repr (u32 x) = Int.repr x.
Proof. apply Int.eqm_samerepr, Int.eqm_sym, Zbits.eqmod_mod. reflexivity. Qed.

Lemma repr_sub_u32 a b : Int.repr (a - u32 b) = Int.repr (a - b).
Proof.
  apply Int.eqm_samerepr, Int.eqm_sub; [apply Int.eqm_refl|].
  apply Int.eqm_sym, Zbits.eqmod_mod. reflexivity.
Qed.

Lemma u32_small x : 0 <= x <= Int.max_unsigned -> u32 x = x.
Proof. intros. unfold u32. apply Z.mod_small. rep_lia. Qed.

Lemma add_ptr_u (q : val) k : isptr q ->
  force_val (sem_binary_operation' Oadd (tptr tuchar) tuint q (Vint (Int.repr k))) = offset_val (u32 k) q.
Proof.
  intros Hq. destruct q; try contradiction. simpl.
  unfold sem_add_ptr_int. simpl. f_equal. f_equal.
  rewrite Ptrofs.mul_commut, Ptrofs.mul_one. unfold Ptrofs.of_intu, Ptrofs.of_int. rewrite u32_unsigned. reflexivity.
Qed.

Lemma add_ptr_u' (q : val) k : isptr q ->
  eval_binop Oadd (tptr tuchar) tuint q (Vint (Int.repr k)) = offset_val (u32 k) q.
Proof. intros Hq. unfold eval_binop. apply add_ptr_u; auto. Qed.

Lemma add_ptr_s (q : val) k : isptr q -> Int.min_signed <= k <= Int.max_signed ->
  force_val (sem_binary_operation' Oadd (tptr tuchar) tint q (Vint (Int.repr k))) = offset_val k q.
Proof.
  intros Hq Hk. destruct q; try contradiction. simpl.
  unfold sem_add_ptr_int. simpl. f_equal. f_equal.
  rewrite Ptrofs.mul_commut, Ptrofs.mul_one. unfold Ptrofs.of_ints. rewrite Int.signed_repr by lia. reflexivity.
Qed.

Lemma signed_sub1 x : 0 <= x <= Int.max_signed -> Int.signed (Int.sub (Int.repr x) (Int.repr 1)) = x - 1.
Proof.
  intros. rewrite Int.sub_signed, (Int.signed_repr x), (Int.signed_repr 1) by rep_lia.
  apply Int.signed_repr. rep_lia.
Qed.

Lemma add_ptr_s' (q : val) k i : isptr q -> Int.min_signed <= i <= Int.max_signed ->
  force_val (sem_binary_operation' Oadd (tptr tuchar) tint (offset_val k q) (Vint (Int.repr i))) = offset_val (k + i) q.
Proof.
  intros Hq Hi. rewrite add_ptr_s by (auto; destruct q; try contradiction; simpl; auto).
  rewrite offset_offset_val. reflexivity.
Qed.

Lemma ptr_diff_val (q : val) a b : isptr q ->
  force_val (sem_cast_l2i I32 Signed (force_val (sem_sub_pp tuchar (offset_val b q) (offset_val a q)))) =
  Vint (Int.repr (b - a)).
Proof.
  intros Hq. destruct q; try contradiction.
  unfold sem_sub_pp, offset_val. simpl. destruct (eq_block b0 b0); [|congruence]. simpl.
  rewrite (Ptrofs.add_commut i (Ptrofs.repr b)), (Ptrofs.add_commut i (Ptrofs.repr a)), Ptrofs.sub_shifted.
  change (Ptrofs.repr 1) with Ptrofs.one. rewrite Ptrofs.divs_one by (cbv; congruence).
  rewrite Int64.Z_mod_modulus_eq. f_equal. apply Int.eqm_samerepr.
  apply Zbits.eqmod_trans with (Ptrofs.unsigned (Ptrofs.sub (Ptrofs.repr b) (Ptrofs.repr a))).
  - apply Zbits.eqmod_divides with Int64.modulus; [apply Zbits.eqmod_sym, Zbits.eqmod_mod; reflexivity|].
    exists (2^32). reflexivity.
  - apply Zbits.eqmod_divides with Ptrofs.modulus; [| exists (2^32); reflexivity].
    unfold Ptrofs.sub. rewrite Ptrofs.unsigned_repr_eq, !Ptrofs.unsigned_repr_eq.
    apply Zbits.eqmod_trans with (b mod Ptrofs.modulus - a mod Ptrofs.modulus).
    + apply Zbits.eqmod_sym, Zbits.eqmod_mod; reflexivity.
    + apply Zbits.eqmod_sub; apply Zbits.eqmod_sym, Zbits.eqmod_mod; reflexivity.
Qed.

Lemma len_val (q : val) a b : isptr q ->
  force_val (sem_binary_operation' Osub tint tint (Vint (Int.repr 258))
    (eval_cast tlong tint (eval_binop Osub (tptr tuchar) (tptr tuchar) (offset_val b q) (offset_val a q)))) =
  Vint (Int.repr (258 - (b - a))).
Proof.
  intros Hq.
  assert (E : eval_cast tlong tint (eval_binop Osub (tptr tuchar) (tptr tuchar) (offset_val b q) (offset_val a q)) =
              Vint (Int.repr (b - a))) by (rewrite <- (ptr_diff_val q a b Hq); reflexivity).
  rewrite E. simpl. rewrite sub_repr32. reflexivity.
Qed.

Lemma sameblock_offset (q : val) a b : isptr q -> is_true (sameblock (offset_val b q) (offset_val a q)).
Proof. intros Hq. destruct q; try contradiction. simpl. destruct (peq b0 b0); [reflexivity | congruence]. Qed.

Lemma sub_ptr_s (q : val) k i : isptr q -> Int.min_signed <= i <= Int.max_signed ->
  force_val (sem_binary_operation' Osub (tptr tuchar) tint (offset_val k q) (Vint (Int.repr i))) = offset_val (k - i) q.
Proof.
  intros Hq Hi. destruct q; try contradiction. simpl.
  unfold sem_sub_pi. simpl. f_equal.
  rewrite Ptrofs.mul_commut, Ptrofs.mul_one. unfold Ptrofs.of_ints. rewrite Int.signed_repr by lia.
  rewrite Ptrofs.sub_add_opp, Ptrofs.add_assoc, Ptrofs.neg_repr, ptrofs_add_repr. reflexivity.
Qed.

(** ** The window: reads and addresses *)

Lemma mb_rd_vals w k v : mb_ok w -> mb_rd w k = Some v ->
  0 <= k < Zlength (mb_val w) /\ @Znth val Vundef k (mb_vals w) = Vint (Int.repr v) /\ 0 <= v < 256.
Proof.
  intros [Hl Hb] H. unfold mb_rd in H.
  destruct (in_range k (Zlength (mb_val w))) eqn:E1; [|discriminate].
  destruct (Znth k (mb_def w)) eqn:E2; [|discriminate]. simpl in H. inversion H; subst v.
  unfold in_range in E1. apply andb_prop in E1. destruct E1 as [E1 E3].
  apply Z.leb_le in E1. apply Z.ltb_lt in E3.
  split; [lia|]. split.
  - change (@Znth val Vundef k (mb_vals w)) with (@Znth val Inhabitant_val k (mb_vals w)).
    unfold mb_vals. rewrite Znth_pb_vals by (auto; lia). rewrite E2. reflexivity.
  - apply Hb; auto.
Qed.

Lemma win_fa q n k : field_compatible (tarray tuchar n) [] q -> 0 <= k < n ->
  offset_val k q = field_address (tarray tuchar n) [ArraySubsc k] q.
Proof.
  intros. rewrite arr_field_address by (auto; lia). simpl sizeof. f_equal. lia.
Qed.

Lemma win_fa_s q n k i j : field_compatible (tarray tuchar n) [] q -> j = k + Int.signed i -> 0 <= j < n ->
  force_val (sem_add_ptr_int tuchar Signed (offset_val k q) (Vint i)) = field_address (tarray tuchar n) [ArraySubsc j] q.
Proof.
  intros Hf -> Hj. rewrite <- win_fa by auto.
  assert (Hp : isptr q) by (destruct Hf; auto). destruct q; try contradiction. simpl.
  unfold sem_add_ptr_int. simpl. f_equal. rewrite Ptrofs.add_assoc. f_equal.
  rewrite Ptrofs.mul_commut, Ptrofs.mul_one. unfold Ptrofs.of_ints.
  apply ptrofs_add_repr.
Qed.

(** ** The model, re-read for the loop invariants *)

(** What is left of a loop run after one iteration [o] of its body. *)
Definition runs_after {A B : Type} (body : A -> option (A + B)) (o : option (A + B)) (r : B) : Prop :=
  match o with Some (inl a') => runs body a' r | Some (inr r') => r' = r | None => False end.

Lemma runs_after_of {A B : Type} (body : A -> option (A + B)) a r :
  runs body a r -> runs_after body (body a) r.
Proof. intros H. destruct (runs_inv _ _ _ H) as [E | [a' [E H']]]; rewrite E; simpl; auto. Qed.

(** The loop test of the chain loop ([next] of [lm_body]). *)
Definition lm_next (limit : Z) (a : lm_st) : option (lm_st + (Z * dstate)) :=
  let s := lm_s a in
  let* cur' := rd (d_prev s) (Z.land (lm_cur a) (d_w_mask s)) in
  if cur' >? limit then
    let chain := u32 (lm_chain a - 1) in
    if chain =? 0 then Some (inr (lm_best a, s))
    else Some (inl (mkLM cur' chain (lm_best a) (lm_end1 a) (lm_end a) s))
  else Some (inr (lm_best a, s)).

Definition lm_body' (nice limit : Z) (a : lm_st) : option (lm_st + (Z * dstate)) :=
  let s := lm_s a in
  let scan := d_strstart s in
  let strend := d_strstart s + DState.MAX_MATCH in
  let cur := lm_cur a in
  let best := lm_best a in
  let* m0 := mb_rd (d_window s) (cur + best) in
  if negb (m0 =? lm_end a) then lm_next limit a else
  let* m1 := mb_rd (d_window s) (cur + best - 1) in
  if negb (m1 =? lm_end1 a) then lm_next limit a else
  let* m2 := mb_rd (d_window s) cur in
  let* sc0 := mb_rd (d_window s) scan in
  if negb (m2 =? sc0) then lm_next limit a else
  let* m3 := mb_rd (d_window s) (cur + 1) in
  let* sc1 := mb_rd (d_window s) (scan + 1) in
  if negb (m3 =? sc1) then lm_next limit a else
  let* scan' := loop FUEL (lm_cmp_body s strend) (scan + 2, cur + 2, 0) in
  let len := DState.MAX_MATCH - (strend - scan') in
  if len >? best then
    let s := set_d_match_start s cur in
    if len >=? nice then Some (inr (len, s)) else
    let* e1 := mb_rd (d_window s) (scan + len - 1) in
    let* e := mb_rd (d_window s) (scan + len) in
    lm_next limit (mkLM cur (lm_chain a) len e1 e s)
  else lm_next limit a.

Lemma lm_body_eq nice limit a : lm_body nice limit a = lm_body' nice limit a.
Proof. reflexivity. Qed.

(** ** The inner comparison loop [do {} while ( *++scan == *++match && ... && scan < strend);] *)

Definition lm_cmp_stmt : statement :=
(Sloop
                                      Sskip
                                      (Ssequence
                                        (Ssequence
                                          (Ssequence
                                            (Ssequence
                                              (Ssequence
                                                (Ssequence
                                                  (Ssequence
                                                    (Ssequence
                                                      (Ssequence
                                                        (Ssequence
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sset _t'9
                                                                (Ecast
                                                                  (Ebinop Oadd
                                                                    (Etempvar _scan (tptr tuchar))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuchar))
                                                                  (tptr tuchar)))
                                                              (Sset _scan
                                                                (Etempvar _t'9 (tptr tuchar))))
                                                            (Sset _t'10
                                                              (Ecast
                                                                (Ebinop Oadd
                                                                  (Etempvar _match (tptr tuchar))
                                                                  (Econst_int (Int.repr 1) tint)
                                                                  (tptr tuchar))
                                                                (tptr tuchar))))
                                                          (Sset _match
                                                            (Etempvar _t'10 (tptr tuchar))))
                                                        (Ssequence
                                                          (Sset _t'50
                                                            (Ederef
                                                              (Etempvar _t'9 (tptr tuchar))
                                                              tuchar))
                                                          (Ssequence
                                                            (Sset _t'51
                                                              (Ederef
                                                                (Etempvar _t'10 (tptr tuchar))
                                                                tuchar))
                                                            (Sifthenelse 
                                                              (Ebinop Oeq
                                                                (Etempvar _t'50 tuchar)
                                                                (Etempvar _t'51 tuchar)
                                                                tint)
                                                              (Ssequence
                                                                (Ssequence
                                                                  (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'12
                                                                    (Ecast
                                                                    (Ebinop Oadd
                                                                    (Etempvar _scan (tptr tuchar))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuchar))
                                                                    (tptr tuchar)))
                                                                    (Sset _scan
                                                                    (Etempvar _t'12 (tptr tuchar))))
                                                                    (Sset _t'13
                                                                    (Ecast
                                                                    (Ebinop Oadd
                                                                    (Etempvar _match (tptr tuchar))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuchar))
                                                                    (tptr tuchar))))
                                                                  (Sset _match
                                                                    (Etempvar _t'13 (tptr tuchar))))
                                                                (Ssequence
                                                                  (Sset _t'52
                                                                    (Ederef
                                                                    (Etempvar _t'12 (tptr tuchar))
                                                                    tuchar))
                                                                  (Ssequence
                                                                    (Sset _t'53
                                                                    (Ederef
                                                                    (Etempvar _t'13 (tptr tuchar))
                                                                    tuchar))
                                                                    (Sset _t'11
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'52 tuchar)
                                                                    (Etempvar _t'53 tuchar)
                                                                    tint)
                                                                    tbool)))))
                                                              (Sset _t'11
                                                                (Econst_int (Int.repr 0) tint))))))
                                                      (Sifthenelse (Etempvar _t'11 tint)
                                                        (Ssequence
                                                          (Ssequence
                                                            (Ssequence
                                                              (Ssequence
                                                                (Sset _t'15
                                                                  (Ecast
                                                                    (Ebinop Oadd
                                                                    (Etempvar _scan (tptr tuchar))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuchar))
                                                                    (tptr tuchar)))
                                                                (Sset _scan
                                                                  (Etempvar _t'15 (tptr tuchar))))
                                                              (Sset _t'16
                                                                (Ecast
                                                                  (Ebinop Oadd
                                                                    (Etempvar _match (tptr tuchar))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuchar))
                                                                  (tptr tuchar))))
                                                            (Sset _match
                                                              (Etempvar _t'16 (tptr tuchar))))
                                                          (Ssequence
                                                            (Sset _t'48
                                                              (Ederef
                                                                (Etempvar _t'15 (tptr tuchar))
                                                                tuchar))
                                                            (Ssequence
                                                              (Sset _t'49
                                                                (Ederef
                                                                  (Etempvar _t'16 (tptr tuchar))
                                                                  tuchar))
                                                              (Sset _t'14
                                                                (Ecast
                                                                  (Ebinop Oeq
                                                                    (Etempvar _t'48 tuchar)
                                                                    (Etempvar _t'49 tuchar)
                                                                    tint)
                                                                  tbool)))))
                                                        (Sset _t'14
                                                          (Econst_int (Int.repr 0) tint))))
                                                    (Sifthenelse (Etempvar _t'14 tint)
                                                      (Ssequence
                                                        (Ssequence
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sset _t'18
                                                                (Ecast
                                                                  (Ebinop Oadd
                                                                    (Etempvar _scan (tptr tuchar))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuchar))
                                                                  (tptr tuchar)))
                                                              (Sset _scan
                                                                (Etempvar _t'18 (tptr tuchar))))
                                                            (Sset _t'19
                                                              (Ecast
                                                                (Ebinop Oadd
                                                                  (Etempvar _match (tptr tuchar))
                                                                  (Econst_int (Int.repr 1) tint)
                                                                  (tptr tuchar))
                                                                (tptr tuchar))))
                                                          (Sset _match
                                                            (Etempvar _t'19 (tptr tuchar))))
                                                        (Ssequence
                                                          (Sset _t'46
                                                            (Ederef
                                                              (Etempvar _t'18 (tptr tuchar))
                                                              tuchar))
                                                          (Ssequence
                                                            (Sset _t'47
                                                              (Ederef
                                                                (Etempvar _t'19 (tptr tuchar))
                                                                tuchar))
                                                            (Sset _t'17
                                                              (Ecast
                                                                (Ebinop Oeq
                                                                  (Etempvar _t'46 tuchar)
                                                                  (Etempvar _t'47 tuchar)
                                                                  tint)
                                                                tbool)))))
                                                      (Sset _t'17
                                                        (Econst_int (Int.repr 0) tint))))
                                                  (Sifthenelse (Etempvar _t'17 tint)
                                                    (Ssequence
                                                      (Ssequence
                                                        (Ssequence
                                                          (Ssequence
                                                            (Sset _t'21
                                                              (Ecast
                                                                (Ebinop Oadd
                                                                  (Etempvar _scan (tptr tuchar))
                                                                  (Econst_int (Int.repr 1) tint)
                                                                  (tptr tuchar))
                                                                (tptr tuchar)))
                                                            (Sset _scan
                                                              (Etempvar _t'21 (tptr tuchar))))
                                                          (Sset _t'22
                                                            (Ecast
                                                              (Ebinop Oadd
                                                                (Etempvar _match (tptr tuchar))
                                                                (Econst_int (Int.repr 1) tint)
                                                                (tptr tuchar))
                                                              (tptr tuchar))))
                                                        (Sset _match
                                                          (Etempvar _t'22 (tptr tuchar))))
                                                      (Ssequence
                                                        (Sset _t'44
                                                          (Ederef
                                                            (Etempvar _t'21 (tptr tuchar))
                                                            tuchar))
                                                        (Ssequence
                                                          (Sset _t'45
                                                            (Ederef
                                                              (Etempvar _t'22 (tptr tuchar))
                                                              tuchar))
                                                          (Sset _t'20
                                                            (Ecast
                                                              (Ebinop Oeq
                                                                (Etempvar _t'44 tuchar)
                                                                (Etempvar _t'45 tuchar)
                                                                tint) tbool)))))
                                                    (Sset _t'20
                                                      (Econst_int (Int.repr 0) tint))))
                                                (Sifthenelse (Etempvar _t'20 tint)
                                                  (Ssequence
                                                    (Ssequence
                                                      (Ssequence
                                                        (Ssequence
                                                          (Sset _t'24
                                                            (Ecast
                                                              (Ebinop Oadd
                                                                (Etempvar _scan (tptr tuchar))
                                                                (Econst_int (Int.repr 1) tint)
                                                                (tptr tuchar))
                                                              (tptr tuchar)))
                                                          (Sset _scan
                                                            (Etempvar _t'24 (tptr tuchar))))
                                                        (Sset _t'25
                                                          (Ecast
                                                            (Ebinop Oadd
                                                              (Etempvar _match (tptr tuchar))
                                                              (Econst_int (Int.repr 1) tint)
                                                              (tptr tuchar))
                                                            (tptr tuchar))))
                                                      (Sset _match
                                                        (Etempvar _t'25 (tptr tuchar))))
                                                    (Ssequence
                                                      (Sset _t'42
                                                        (Ederef
                                                          (Etempvar _t'24 (tptr tuchar))
                                                          tuchar))
                                                      (Ssequence
                                                        (Sset _t'43
                                                          (Ederef
                                                            (Etempvar _t'25 (tptr tuchar))
                                                            tuchar))
                                                        (Sset _t'23
                                                          (Ecast
                                                            (Ebinop Oeq
                                                              (Etempvar _t'42 tuchar)
                                                              (Etempvar _t'43 tuchar)
                                                              tint) tbool)))))
                                                  (Sset _t'23
                                                    (Econst_int (Int.repr 0) tint))))
                                              (Sifthenelse (Etempvar _t'23 tint)
                                                (Ssequence
                                                  (Ssequence
                                                    (Ssequence
                                                      (Ssequence
                                                        (Sset _t'27
                                                          (Ecast
                                                            (Ebinop Oadd
                                                              (Etempvar _scan (tptr tuchar))
                                                              (Econst_int (Int.repr 1) tint)
                                                              (tptr tuchar))
                                                            (tptr tuchar)))
                                                        (Sset _scan
                                                          (Etempvar _t'27 (tptr tuchar))))
                                                      (Sset _t'28
                                                        (Ecast
                                                          (Ebinop Oadd
                                                            (Etempvar _match (tptr tuchar))
                                                            (Econst_int (Int.repr 1) tint)
                                                            (tptr tuchar))
                                                          (tptr tuchar))))
                                                    (Sset _match
                                                      (Etempvar _t'28 (tptr tuchar))))
                                                  (Ssequence
                                                    (Sset _t'40
                                                      (Ederef
                                                        (Etempvar _t'27 (tptr tuchar))
                                                        tuchar))
                                                    (Ssequence
                                                      (Sset _t'41
                                                        (Ederef
                                                          (Etempvar _t'28 (tptr tuchar))
                                                          tuchar))
                                                      (Sset _t'26
                                                        (Ecast
                                                          (Ebinop Oeq
                                                            (Etempvar _t'40 tuchar)
                                                            (Etempvar _t'41 tuchar)
                                                            tint) tbool)))))
                                                (Sset _t'26
                                                  (Econst_int (Int.repr 0) tint))))
                                            (Sifthenelse (Etempvar _t'26 tint)
                                              (Ssequence
                                                (Ssequence
                                                  (Ssequence
                                                    (Ssequence
                                                      (Sset _t'30
                                                        (Ecast
                                                          (Ebinop Oadd
                                                            (Etempvar _scan (tptr tuchar))
                                                            (Econst_int (Int.repr 1) tint)
                                                            (tptr tuchar))
                                                          (tptr tuchar)))
                                                      (Sset _scan
                                                        (Etempvar _t'30 (tptr tuchar))))
                                                    (Sset _t'31
                                                      (Ecast
                                                        (Ebinop Oadd
                                                          (Etempvar _match (tptr tuchar))
                                                          (Econst_int (Int.repr 1) tint)
                                                          (tptr tuchar))
                                                        (tptr tuchar))))
                                                  (Sset _match
                                                    (Etempvar _t'31 (tptr tuchar))))
                                                (Ssequence
                                                  (Sset _t'38
                                                    (Ederef
                                                      (Etempvar _t'30 (tptr tuchar))
                                                      tuchar))
                                                  (Ssequence
                                                    (Sset _t'39
                                                      (Ederef
                                                        (Etempvar _t'31 (tptr tuchar))
                                                        tuchar))
                                                    (Sset _t'29
                                                      (Ecast
                                                        (Ebinop Oeq
                                                          (Etempvar _t'38 tuchar)
                                                          (Etempvar _t'39 tuchar)
                                                          tint) tbool)))))
                                              (Sset _t'29
                                                (Econst_int (Int.repr 0) tint))))
                                          (Sifthenelse (Etempvar _t'29 tint)
                                            (Sset _t'32
                                              (Ecast
                                                (Ebinop Olt
                                                  (Etempvar _scan (tptr tuchar))
                                                  (Etempvar _strend (tptr tuchar))
                                                  tint) tbool))
                                            (Sset _t'32
                                              (Econst_int (Int.repr 0) tint))))
                                        (Sifthenelse (Etempvar _t'32 tint)
                                          Sskip
                                          Sbreak))).

(** The model's position inside a round of 8 comparisons starting at (i, jm): after [c] equal comparisons. *)
Definition lm_after (s : dstate) (strend i jm c sf : Z) : Prop :=
  if c =? 8 then (if i + 8 <? strend then runs (lm_cmp_body s strend) (i + 8, jm + 8, 0) sf else sf = i + 8)
  else runs (lm_cmp_body s strend) (i + c, jm + c, c) sf.

Lemma cmp_step s strend i jm c c' sf : 0 <= c <= 7 -> c' = c + 1 -> lm_after s strend i jm c sf ->
  exists v1 v2, mb_rd (d_window s) (i + c') = Some v1 /\ mb_rd (d_window s) (jm + c') = Some v2 /\
    (v1 <> v2 -> sf = i + c') /\ (v1 = v2 -> lm_after s strend i jm c' sf).
Proof.
  intros Hc -> H. unfold lm_after in H.
  destruct (Z.eqb_spec c 8); [lia|].
  apply runs_inv in H. unfold lm_cmp_body in H.
  rewrite <- !Z.add_assoc in H.
  destruct (mb_rd (d_window s) (i + (c + 1))) as [v1|] eqn:E1; [|simpl in H; destruct H as [H|[? [H _]]]; discriminate].
  destruct (mb_rd (d_window s) (jm + (c + 1))) as [v2|] eqn:E2; [|simpl in H; destruct H as [H|[? [H _]]]; discriminate].
  simpl in H. exists v1, v2. split; [auto|]. split; [auto|]. split.
  - intros Hn. apply Z.eqb_neq in Hn. rewrite Hn in H. simpl in H.
    destruct H as [H|[? [H _]]]; inversion H; auto.
  - intros ->. rewrite Z.eqb_refl in H. simpl in H. unfold lm_after.
    destruct (Z.eqb_spec c 7).
    + subst c. change (7 + 1) with 8 in *. simpl. destruct (i + 8 <? strend).
      * destruct H as [H|[? [H H']]]; inversion H; subst; auto.
      * destruct H as [H|[? [H _]]]; inversion H; subst; auto.
    + destruct (Z.eqb_spec (c + 1) 8); [lia|].
      destruct H as [H|[? [H H']]]; inversion H; subst; auto.
Qed.

Lemma lm_after_0 s strend i jm sf : runs (lm_cmp_body s strend) (i, jm, 0) sf -> lm_after s strend i jm 0 sf.
Proof. unfold lm_after. simpl. rewrite !Z.add_0_r. auto. Qed.

Lemma int_eq_byte v1 v2 : 0 <= v1 < 256 -> 0 <= v2 < 256 -> Int.eq (Int.repr v1) (Int.repr v2) = (v1 =? v2).
Proof.
  intros. destruct (Z.eqb_spec v1 v2).
  - subst. apply Int.eq_true.
  - apply Int.eq_false. intros E. apply repr_inj_unsigned in E; rep_lia.
Qed.

(** [mb_rd_vals] with the inhabitant VST's loads produce. *)
Lemma mb_rd_vals' w k v : mb_ok w -> mb_rd w k = Some v ->
  0 <= k < Zlength (mb_val w) /\ @Znth val Vundef k (mb_vals w) = Vint (Int.repr v) /\ 0 <= v < 256.
Proof. apply mb_rd_vals. Qed.

(** The join point after comparison [c] of a round (temp [t] holds the && chain so far). *)
Definition lm_JP (s : dstate) (strend i jm c sf : Z) (b : bool) (sc : Z) : Prop :=
  if b then sc = i + c /\ lm_after s strend i jm c sf else sc = sf /\ i < sf <= i + c.

Definition lm_J (s : dstate) (win : val) (strend i jm c sf : Z) (t : ident) : environ -> mpred :=
  EX b : bool, EX sc : Z,
  PROP (lm_JP s strend i jm c sf b sc)
  LOCAL (temp t (Val.of_bool b); temp _scan (offset_val sc win); temp _match (offset_val (jm + (sc - i)) win);
         temp _strend (offset_val strend win))
  SEP (data_at Ews (tarray tuchar (Zlength (mb_val (d_window s)))) (mb_vals (d_window s)) win).

(** One comparison [scan++; match++; t = *scan == *match] of a round, from [lm_after .. c sf] ([Ha]) with
    [scan = win + (i + c)], [match = win + (jm + c)]; reads both bytes. *)
Ltac lm_cmp Hok s win st i jm c c' Ha :=
  let v1 := fresh "v1" in let v2 := fresh "v2" in let E1 := fresh "E1" in let E2 := fresh "E2" in
  let Hne := fresh "Hne" in let Heq := fresh "Heq" in
  let Hk1 := fresh "Hk1" in let Hz1 := fresh "Hz1" in let Hv1 := fresh "Hv1" in
  let Hk2 := fresh "Hk2" in let Hz2 := fresh "Hz2" in let Hv2 := fresh "Hv2" in let Hq := fresh "Hq" in
  destruct (cmp_step s (st + 258) i jm c c' _ ltac:(lia) eq_refl Ha) as (v1 & v2 & E1 & E2 & Hne & Heq);
  destruct (mb_rd_vals' _ _ _ Hok E1) as (Hk1 & Hz1 & Hv1);
  destruct (mb_rd_vals' _ _ _ Hok E2) as (Hk2 & Hz2 & Hv2);
  forward; forward; forward; forward;
  rewrite !add_ptr_s, !offset_offset_val by (auto; rep_lia);
  replace (i + c + 1) with (i + c') by lia;
  replace (jm + c + 1) with (jm + c') by lia;
  rewrite (win_fa win (Zlength (mb_val (d_window s))) (i + c')) by (auto; lia);
  rewrite (win_fa win (Zlength (mb_val (d_window s))) (jm + c')) by (auto; lia);
  forward; [entailer!; rewrite Hz1; apply tc_val_tuchar_repr; lia|];
  forward; [entailer!; rewrite Hz2; apply tc_val_tuchar_repr; lia|];
  rewrite Hz1, Hz2; rewrite <- !win_fa by (auto; lia);
  clear Hz1 Hz2 Hk1 Hk2 E1 E2;
  forward;
  unfold lm_J; match goal with |- context [zeq ?a ?b] => destruct (zeq a b) as [Hq|Hq] end;
  [ Exists true (i + c'); entailer!; split; [split; [reflexivity | apply Heq; auto] | f_equal; lia]
  | Exists false (i + c'); entailer!; split; [specialize (Hne Hq); unfold lm_JP; lia | f_equal; lia] ].

(** The [if (t) { comparison c' } else t' = 0] step, from the join point [lm_J .. c] to [lm_J .. c']. *)
Ltac lm_join Hok s win st sf i jm c c' t' :=
  let b := fresh "b" in let sc := fresh "sc" in let Ha := fresh "Ha" in
  unfold lm_J at 1; Intros b sc;
  forward_if (lm_J s win (st + 258) i jm c' sf t');
  [ lazymatch goal with Hb : lm_JP _ _ _ _ _ _ _ _, Hc : typed_true _ _ |- _ =>
      destruct b;
      [ destruct Hb as [-> Ha]; replace (jm + (i + c - i)) with (jm + c) by lia; lm_cmp Hok s win st i jm c c' Ha
      | exfalso; compute in Hc; discriminate ] end
  | lazymatch goal with Hb : lm_JP _ _ _ _ _ _ _ _, Hc : typed_false _ _ |- _ =>
      destruct b;
      [ exfalso; compute in Hc; discriminate
      | forward; unfold lm_J; Exists false sc; entailer!; unfold lm_JP in *; lia ] end
  | lazymatch goal with Hb : lm_JP _ _ _ _ _ _ _ _ |- _ => clear Hb end; clear b sc ].

(** [scan < strend] inside the window. *)
Lemma win_test_order sh n vs win a b : readable_share sh -> isptr win -> 0 <= a <= n -> 0 <= b <= n -> 0 < n ->
  data_at sh (tarray tuchar n) vs win |-- denote_tc_test_order (offset_val a win) (offset_val b win).
Proof.
  intros Hsh Hp Ha Hb Hn.
  rewrite isptr_denote_tc_test_order by (apply isptr_offset_val'; auto).
  unfold test_order_ptrs. destruct win; try contradiction. simpl sameblock.
  destruct (peq b0 b0); [|congruence]. simpl.
  eapply derives_trans; [apply data_at_memory_block|].
  simpl sizeof. rewrite Z.max_r, Z.mul_1_l by lia.
  apply andp_right; [apply (memory_block_weak_valid_pointer sh n (Vptr b0 i) a) |
    apply (memory_block_weak_valid_pointer sh n (Vptr b0 i) b)]; auto; apply readable_nonidentity; auto.
Qed.

Lemma win_lt_val n win a b : field_compatible (tarray tuchar n) [] win -> 0 <= a <= n -> 0 <= b <= n ->
  force_val (sem_cast tint tbool (eval_binop Olt (tptr tuchar) (tptr tuchar) (offset_val a win) (offset_val b win))) =
  Val.of_bool (a <? b).
Proof.
  intros Hf Ha Hb. destruct win; try (destruct Hf; contradiction).
  destruct Hf as (_ & _ & Hsz & _). simpl in Hsz. rewrite Z.max_r, Z.mul_1_l in Hsz by lia.
  pose proof (Ptrofs.unsigned_range i).
  unfold eval_binop. simpl. unfold sem_cmp_pp. simpl. rewrite peq_true. simpl.
  unfold Ptrofs.ltu, Ptrofs.add. rewrite (Ptrofs.unsigned_repr a), (Ptrofs.unsigned_repr b) by rep_lia.
  rewrite !Ptrofs.unsigned_repr by rep_lia.
  destruct (zlt _ _), (Z.ltb_spec a b); try lia; reflexivity.
Qed.

(** After the test [scan < strend] of a round. *)
Definition lm_KP (s : dstate) (strend i jm sf : Z) (b : bool) (sc : Z) : Prop :=
  if b then sc = i + 8 /\ i + 8 < strend /\ runs (lm_cmp_body s strend) (i + 8, jm + 8, 0) sf
  else sc = sf /\ i < sf <= i + 8.

(** From [scan = window + i], [match = window + j] (i = strstart + 2, j = cur_match + 2) to the exit value [sf]
    of the model's loop; [match] advances with [scan]. *)
Lemma lm_cmp_loop (Espec : OracleKind) (s : dstate) (win : val) (st j sf : Z) :
  mb_ok (d_window s) ->
  field_compatible (tarray tuchar (Zlength (mb_val (d_window s)))) [] win ->
  0 <= st -> st + 258 <= Zlength (mb_val (d_window s)) -> Zlength (mb_val (d_window s)) <= Int.max_unsigned ->
  0 <= j ->
  runs (lm_cmp_body s (st + 258)) (st + 2, j, 0) sf ->
  forall DS : Maps.PTree.t funspec,
  semax (with_Delta_specs DS (func_tycontext f_longest_match DSpec.Vprog Gprog_longest_match nil))
    (PROP ()
     LOCAL (temp _scan (offset_val (st + 2) win); temp _match (offset_val j win);
            temp _strend (offset_val (st + 258) win))
     SEP (data_at Ews (tarray tuchar (Zlength (mb_val (d_window s)))) (mb_vals (d_window s)) win))
    lm_cmp_stmt
    (normal_ret_assert
      (PROP (st + 3 <= sf <= st + 258)
       LOCAL (temp _scan (offset_val sf win); temp _match (offset_val (j + (sf - (st + 2))) win);
              temp _strend (offset_val (st + 258) win))
       SEP (data_at Ews (tarray tuchar (Zlength (mb_val (d_window s)))) (mb_vals (d_window s)) win))).
Proof.
  intros Hok Hfc Hst HL HLu Hj Hr DS.
  (* the shape of Delta that start_function produces *)
  pose (Delta := @abbreviate tycontext (with_Delta_specs DS (func_tycontext f_longest_match DSpec.Vprog Gprog_longest_match nil))).
  change (with_Delta_specs DS (func_tycontext f_longest_match DSpec.Vprog Gprog_longest_match nil)) with Delta.
  cbv beta iota zeta delta - [abbreviate] in Delta.
  unfold lm_cmp_stmt.
  assert_PROP (isptr win) by entailer!.
  forward_loop (EX i : Z, EX jm : Z,
    PROP (st + 2 <= i <= st + 250; (i - (st + 2)) mod 8 = 0; jm = (j + (i - (st + 2)))%Z;
          runs (lm_cmp_body s (st + 258)) (i, jm, 0) sf)
    LOCAL (temp _scan (offset_val i win); temp _match (offset_val jm win); temp _strend (offset_val (st + 258) win))
    SEP (data_at Ews (tarray tuchar (Zlength (mb_val (d_window s)))) (mb_vals (d_window s)) win))
  break: (PROP (st + 3 <= sf <= st + 258)
       LOCAL (temp _scan (offset_val sf win); temp _match (offset_val (j + (sf - (st + 2))) win);
              temp _strend (offset_val (st + 258) win))
       SEP (data_at Ews (tarray tuchar (Zlength (mb_val (d_window s)))) (mb_vals (d_window s)) win)).
  { Exists (st + 2) j. entailer!. rewrite Z.sub_diag. reflexivity. }
  Intros i jm.
  apply lm_after_0 in H3.
  destruct (cmp_step s (st+258) i jm 0 1 sf ltac:(lia) eq_refl H3) as (v1 & v2 & E1 & E2 & Hne & Heq).
  destruct (mb_rd_vals' _ _ _ Hok E1) as (Hk1 & Hz1 & Hv1).
  destruct (mb_rd_vals' _ _ _ Hok E2) as (Hk2 & Hz2 & Hv2).
  forward. forward. forward. forward.
  rewrite !add_ptr_s, !offset_offset_val by (auto; rep_lia).
  rewrite (win_fa win (Zlength (mb_val (d_window s))) (i + 1)) by (auto; lia).
  rewrite (win_fa win (Zlength (mb_val (d_window s))) (jm + 1)) by (auto; lia).
  forward; [entailer!; rewrite Hz1; apply tc_val_tuchar_repr; lia|].
  forward; [entailer!; rewrite Hz2; apply tc_val_tuchar_repr; lia|].
  rewrite Hz1, Hz2.
  rewrite <- !win_fa by (auto; lia).
  clear Hz1 Hz2 Hk1 Hk2 E1 E2.
  forward_if (lm_J s win (st + 258) i jm 2 sf _t'11).
  { specialize (Heq H4). lm_cmp Hok s win st i jm 1 2 Heq. }
  { forward. unfold lm_J. Exists false (i + 1). entailer!. split; [specialize (Hne H4); unfold lm_JP; lia | f_equal; lia]. }
  lm_join Hok s win st sf i jm 2 3 _t'14.
  lm_join Hok s win st sf i jm 3 4 _t'17.
  lm_join Hok s win st sf i jm 4 5 _t'20.
  lm_join Hok s win st sf i jm 5 6 _t'23.
  lm_join Hok s win st sf i jm 6 7 _t'26.
  lm_join Hok s win st sf i jm 7 8 _t'29.
  unfold lm_J at 1. Intros b sc.
  forward_if (EX b' : bool, EX sc' : Z,
    PROP (lm_KP s (st + 258) i jm sf b' sc')
    LOCAL (temp _t'32 (Val.of_bool b'); temp _scan (offset_val sc' win); temp _match (offset_val (jm + (sc' - i)) win);
           temp _strend (offset_val (st + 258) win))
    SEP (data_at Ews (tarray tuchar (Zlength (mb_val (d_window s)))) (mb_vals (d_window s)) win)).
  { destruct b; [|exfalso; compute in H5; discriminate].
    destruct H4 as [-> Ha].
    forward.
    { entailer!. apply win_test_order; auto; lia. }
    rewrite (win_lt_val (Zlength (mb_val (d_window s)))) by (auto; lia).
    unfold lm_after in Ha. simpl in Ha.
    destruct (Z.ltb_spec (i + 8) (st + 258)).
    - Exists true (i + 8). entailer!; unfold lm_KP; repeat split; auto; try lia; f_equal; lia.
    - Exists false (i + 8). entailer!; unfold lm_KP; repeat split; auto; try lia; f_equal; lia. }
  { destruct b; [exfalso; compute in H5; discriminate|].
    forward. Exists false sc. entailer!; unfold lm_JP, lm_KP in *; lia. }
  clear b sc H4.
  Intros b' sc'. rename H4 into Hk.
  forward_if.
  - match goal with Hc : typed_true _ _ |- _ => destruct b'; [|exfalso; compute in Hc; discriminate] end.
    destruct Hk as (-> & Hlt & Hr').
    apply Z.mod_divide in H1; [|lia]. destruct H1 as [k Hk].
    forward. Exists (i + 8) (jm + 8). entailer!.
    repeat split; try lia; try (f_equal; lia).
    replace (i + 8 - (st + 2)) with ((k + 1) * 8) by lia. apply Z_mod_mult.
  - match goal with Hc : typed_false _ _ |- _ => destruct b'; [exfalso; compute in Hc; discriminate|] end.
    unfold lm_KP in Hk. destruct Hk as [-> Hk].
    forward. entailer!; repeat split; try lia; f_equal; lia.
Qed.

Lemma set_ms_same s : set_d_match_start s (d_match_start s) = s.
Proof. destruct s; reflexivity. Qed.

Lemma set_ms_twice s a b : set_d_match_start (set_d_match_start s a) b = set_d_match_start s b.
Proof. destruct s; reflexivity. Qed.

Lemma ranges_set_ms s x : dstate_ranges s -> 0 <= x <= Int.max_unsigned -> dstate_ranges (set_d_match_start s x).
Proof.
  intros H Hx. destruct s. unfold dstate_ranges, u32_ok in *. cbn in *. tauto.
Qed.

Lemma rd_some l i v : rd l i = Some v -> 0 <= i < Zlength l /\ Znth i l = v.
Proof.
  unfold rd, in_range. intros H.
  destruct ((0 <=? i) && (i <? Zlength l))%bool eqn:E; [|discriminate].
  apply andb_prop in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  inversion H. split; [lia | reflexivity].
Qed.

Lemma zext8_byte x : 0 <= x < 256 -> Int.zero_ext 8 (Int.repr x) = Int.repr x.
Proof. intros. rewrite zext8_repr, Z.mod_small by lia. reflexivity. Qed.

Lemma u32_range x : 0 <= u32 x <= Int.max_unsigned.
Proof. unfold u32. pose proof (Z.mod_pos_bound x 4294967296 ltac:(lia)). rep_lia. Qed.

Lemma eq_repr_u32_0 x : Int.eq (Int.repr x) (Int.repr 0) = (u32 x =? 0).
Proof.
  rewrite <- repr_u32. pose proof (u32_range x).
  destruct (Z.eqb_spec (u32 x) 0) as [E|E].
  - rewrite E. apply Int.eq_true.
  - apply Int.eq_false. intros E'. apply repr_inj_unsigned in E'; rep_lia.
Qed.

Lemma eq_repr_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> Int.eq (Int.repr a) (Int.repr b) = (a =? b).
Proof.
  intros. destruct (Z.eqb_spec a b) as [E|E].
  - subst. apply Int.eq_true.
  - apply Int.eq_false. intros E'. apply repr_inj_unsigned in E'; rep_lia.
Qed.

Ltac dcmp := rewrite ?Z.geb_leb, ?Z.gtb_ltb; decide_cmps.

Ltac lm_fold_post s ms FR3 FR2 FR :=
  thaw FR3; thaw FR2; thaw FR;
  unfold dstate_at, win_at, hash_at, match_at, cfg_at;
  cbn [d_window d_window_size d_w_size d_w_bits d_w_mask d_high_water d_prev d_head d_ins_h d_hash_size
       d_hash_bits d_hash_mask d_hash_shift d_block_start d_match_length d_prev_match d_match_available d_strstart
       d_match_start d_lookahead d_prev_length d_insert d_slid d_max_chain_length d_max_lazy_match d_good_match
       d_nice_match set_d_match_start];
  match goal with |- context [stat_at (set_d_match_start s ms) ?pp] => replace (stat_at (set_d_match_start s ms) pp) with (stat_at s pp) by reflexivity end;
  replace (d_trm (set_d_match_start s ms)) with (d_trm s) by reflexivity.

Ltac zbools :=
  repeat match goal with
  | H : context [Int.unsigned (Int.repr ?v)] |- _ => rewrite (Int.unsigned_repr v) in H by rep_lia
  | H : context [Int.signed (Int.repr ?v)] |- _ => rewrite (Int.signed_repr v) in H by rep_lia
  | H : (_ >? _) = _ |- _ => rewrite Z.gtb_ltb in H
  | H : (_ >=? _) = _ |- _ => rewrite Z.geb_leb in H
  | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
  | H : (_ <? _) = false |- _ => apply Z.ltb_ge in H
  | H : (_ <=? _) = true |- _ => apply Z.leb_le in H
  | H : (_ <=? _) = false |- _ => apply Z.leb_gt in H
  | H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
  | H : (_ =? _) = false |- _ => apply Z.eqb_neq in H
  end.

Ltac dead := exfalso; zbools; try lia; try discriminate; try congruence.

(** The variables the inner loop modifies, computed once (the kernel would otherwise recompute [modifiedvars] of
    the loop for every framed local). *)
Definition lm_cmp_mods : Maps.PTree.t unit := ltac:(let x := eval vm_compute in (modifiedvars' lm_cmp_stmt idset0) in exact x).

Lemma lm_cmp_mods_eq : modifiedvars' lm_cmp_stmt idset0 = lm_cmp_mods.
Proof. vm_compute. reflexivity. Qed.

(** [lm_cmp_loop] with a frame of further locals and resources. *)
Lemma lm_cmp_loop_framed (Espec : OracleKind) (s : dstate) (win : val) (st j sf : Z) DS Q2 R2 :
  mb_ok (d_window s) ->
  field_compatible (tarray tuchar (Zlength (mb_val (d_window s)))) [] win ->
  0 <= st -> st + 258 <= Zlength (mb_val (d_window s)) -> Zlength (mb_val (d_window s)) <= Int.max_unsigned ->
  0 <= j ->
  runs (lm_cmp_body s (st + 258)) (st + 2, j, 0) sf ->
  closed_wrt_vars (fun i => isSome (Maps.PTree.get i lm_cmp_mods)) (LOCALx Q2 (SEPx R2)) ->
  semax (with_Delta_specs DS (func_tycontext f_longest_match DSpec.Vprog Gprog_longest_match nil))
    (PROPx []
     (LOCALx (temp _scan (offset_val (st + 2) win) :: temp _match (offset_val j win) ::
              temp _strend (offset_val (st + 258) win) :: Q2)
     (SEPx (data_at Ews (tarray tuchar (Zlength (mb_val (d_window s)))) (mb_vals (d_window s)) win :: R2))))
    lm_cmp_stmt
    (normal_ret_assert
      (PROPx [st + 3 <= sf <= st + 258]
       (LOCALx (temp _scan (offset_val sf win) :: temp _match (offset_val (j + (sf - (st + 2))) win) ::
                temp _strend (offset_val (st + 258) win) :: Q2)
       (SEPx (data_at Ews (tarray tuchar (Zlength (mb_val (d_window s)))) (mb_vals (d_window s)) win :: R2))))).
Proof.
  intros Hok Hfc Hst HL HLu Hj Hr Hcl0.
  assert (Hcl : closed_wrt_modvars lm_cmp_stmt (LOCALx Q2 (SEPx R2))).
  { unfold closed_wrt_modvars, modifiedvars. rewrite lm_cmp_mods_eq. exact Hcl0. }
  apply (semax_frame_PQR Q2 R2 Espec _
          [data_at Ews (tarray tuchar (Zlength (mb_val (d_window s)))) (mb_vals (d_window s)) win] []
          [temp _scan (offset_val (st + 2) win); temp _match (offset_val j win); temp _strend (offset_val (st + 258) win)]
          [st + 3 <= sf <= st + 258]
          [temp _scan (offset_val sf win); temp _match (offset_val (j + (sf - (st + 2))) win);
           temp _strend (offset_val (st + 258) win)]
          [data_at Ews (tarray tuchar (Zlength (mb_val (d_window s)))) (mb_vals (d_window s)) win]); auto.
  apply lm_cmp_loop; auto.
Qed.

Ltac beq :=
  rewrite ?eq_repr_byte by lia;
  repeat match goal with
  | |- context [zeq ?a ?b] => destruct (zeq a b); try (exfalso; lia)
  | |- context [?a =? ?b] => destruct (Z.eqb_spec a b); try (exfalso; lia)
  end; reflexivity.

(** The rest of the [||] chain once it is true: set the next temps to 1 and [continue]. *)
Ltac cont_tail a ms :=
  repeat (match goal with |- semax _ _ (Ssequence (Sifthenelse (Etempvar _ _) (Sset ?t _) _) _) _ =>
            forward_if (temp t (Vint (Int.repr 1))); [forward; entailer! | dead | ] end);
  forward_if; [forward; Exists a ms; entailer! | dead].

Ltac win_tc Hz := go_lower; apply prop_right; rewrite Hz; apply tc_val_tuchar_repr; lia.

(** [rewrite Z.eqb_refl in H; cbn [negb] in H] on a big model hypothesis makes the kernel's Qed explode; this
    lemma does the same step in a small context. *)
Lemma runs_after_eqb_refl {A B : Type} (body : A -> option (A + B)) (x : Z) (X Y : option (A + B)) (r : B) :
  runs_after body (if negb (x =? x) then X else Y) r -> runs_after body Y r.
Proof. rewrite Z.eqb_refl. exact (fun H => H). Qed.

Lemma win_set_ms s x : d_window (set_d_match_start s x) = d_window s.
Proof. reflexivity. Qed.
Lemma st_set_ms s x : d_strstart (set_d_match_start s x) = d_strstart s.
Proof. reflexivity. Qed.
Lemma cmp_set_ms s x : lm_cmp_body (set_d_match_start s x) = lm_cmp_body s.
Proof. reflexivity. Qed.
Lemma max_match_258 : DState.MAX_MATCH = 258.
Proof. reflexivity. Qed.

(** The model of the chain-loop body when the four first comparisons succeed: the inner loop's result [sc] and
    the rest.  A pure lemma (kept apart: the conversions on [loop FUEL ..] are slow for the kernel in big proofs). *)
Lemma lm_E_model (nice limit bf : Z) (sf s : dstate) (ac ach ab ae1 ae ms sc0 sc1 : Z) :
  runs (lm_body nice limit) (mkLM ac ach ab ae1 ae (set_d_match_start s ms)) (bf, sf) ->
  mb_rd (d_window s) (ac + ab) = Some ae -> mb_rd (d_window s) (ac + ab - 1) = Some ae1 ->
  mb_rd (d_window s) ac = Some sc0 -> mb_rd (d_window s) (d_strstart s) = Some sc0 ->
  mb_rd (d_window s) (ac + 1) = Some sc1 -> mb_rd (d_window s) (d_strstart s + 1) = Some sc1 ->
  exists sc, runs (lm_cmp_body s (d_strstart s + 258)) (d_strstart s + 2, ac + 2, 0) sc /\
    runs_after (lm_body nice limit) (if sc - d_strstart s >? ab then
       if sc - d_strstart s >=? nice then Some (inr (sc - d_strstart s, set_d_match_start s ac))
       else let* e1 := mb_rd (d_window s) (sc - 1) in
            let* e := mb_rd (d_window s) sc in
            lm_next limit (mkLM ac ach (sc - d_strstart s) e1 e (set_d_match_start s ac))
     else lm_next limit (mkLM ac ach ab ae1 ae (set_d_match_start s ms))) (bf, sf).
Proof.
  intros Hrun E0 E1 E2 E3 E4 E5.
  pose proof (runs_after_of _ _ _ Hrun) as Hm. clear Hrun.
  rewrite lm_body_eq in Hm. unfold lm_body' in Hm.
  cbn [lm_s lm_cur lm_chain lm_best lm_end1 lm_end] in Hm.
  rewrite win_set_ms, st_set_ms, cmp_set_ms in Hm.
  (* abstract the model's inner loop first: a conversion on Hm that exposes [bind (loop FUEL ..) _] makes the
     kernel evaluate the loop (Qed > 600 s) *)
  remember (loop FUEL (lm_cmp_body s (d_strstart s + DState.MAX_MATCH)) (d_strstart s + 2, ac + 2, 0)) as LR eqn:ELR.
  rewrite E0 in Hm. cbn [bind] in Hm. apply runs_after_eqb_refl in Hm.
  rewrite E1 in Hm. cbn [bind] in Hm. apply runs_after_eqb_refl in Hm.
  rewrite E2 in Hm. cbn [bind] in Hm. rewrite E3 in Hm. cbn [bind] in Hm. apply runs_after_eqb_refl in Hm.
  rewrite E4 in Hm. cbn [bind] in Hm. rewrite E5 in Hm. cbn [bind] in Hm. apply runs_after_eqb_refl in Hm.
  destruct LR as [sc|]; cbn [bind] in Hm; [|contradiction].
  exists sc. split; [symmetry in ELR; apply loop_runs in ELR; rewrite max_match_258 in ELR; exact ELR|].
  rewrite max_match_258 in Hm.
  replace (258 - (d_strstart s + 258 - sc)) with (sc - d_strstart s) in Hm by lia.
  replace (d_strstart s + (sc - d_strstart s) - 1) with (sc - 1) in Hm by lia.
  replace (d_strstart s + (sc - d_strstart s)) with sc in Hm by lia.
  rewrite !win_set_ms in Hm.
  rewrite set_ms_twice in Hm.
  exact Hm.
Qed.

(** The rest of the chain-loop body from the inner comparison loop on (case: the four first bytes match). *)
Definition lm_rest_stmt : statement :=
(Ssequence
                                      (Sset _len
                                        (Ebinop Osub
                                          (Econst_int (Int.repr 258) tint)
                                          (Ecast
                                            (Ebinop Osub
                                              (Etempvar _strend (tptr tuchar))
                                              (Etempvar _scan (tptr tuchar))
                                              tlong) tint) tint))
                                      (Ssequence
                                        (Sset _scan
                                          (Ebinop Osub
                                            (Etempvar _strend (tptr tuchar))
                                            (Econst_int (Int.repr 258) tint)
                                            (tptr tuchar)))
                                        (Sifthenelse (Ebinop Ogt
                                                       (Etempvar _len tint)
                                                       (Etempvar _best_len tint)
                                                       tint)
                                          (Ssequence
                                            (Sassign
                                              (Efield
                                                (Ederef
                                                  (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                  (Tstruct _internal_state noattr))
                                                _match_start tuint)
                                              (Etempvar _cur_match tuint))
                                            (Ssequence
                                              (Sset _best_len
                                                (Etempvar _len tint))
                                              (Ssequence
                                                (Sifthenelse (Ebinop Oge
                                                               (Etempvar _len tint)
                                                               (Etempvar _nice_match tint)
                                                               tint)
                                                  Sbreak
                                                  Sskip)
                                                (Ssequence
                                                  (Ssequence
                                                    (Sset _t'37
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Etempvar _scan (tptr tuchar))
                                                          (Ebinop Osub
                                                            (Etempvar _best_len tint)
                                                            (Econst_int (Int.repr 1) tint)
                                                            tint)
                                                          (tptr tuchar))
                                                        tuchar))
                                                    (Sset _scan_end1
                                                      (Ecast
                                                        (Etempvar _t'37 tuchar)
                                                        tuchar)))
                                                  (Ssequence
                                                    (Sset _t'36
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Etempvar _scan (tptr tuchar))
                                                          (Etempvar _best_len tint)
                                                          (tptr tuchar))
                                                        tuchar))
                                                    (Sset _scan_end
                                                      (Ecast
                                                        (Etempvar _t'36 tuchar)
                                                        tuchar)))))))
                                          Sskip))).

Lemma lm_tail (Espec : OracleKind) (DS : Maps.PTree.t funspec) (Fr : list mpred) (R : ret_assert)
  (s : dstate) (p : dptrs) (nice limit bf : Z) (sf : dstate) (ac ach ab ae1 ae ms sc : Z) :
  mb_ok (d_window s) ->
  field_compatible (tarray tuchar (Zlength (mb_val (d_window s)))) [] (p_window p) ->
  isptr (p_window p) ->
  d_strstart s + 258 <= Zlength (mb_val (d_window s)) ->
  Zlength (mb_val (d_window s)) <= Int.max_unsigned ->
  0 <= d_strstart s <= Int.max_unsigned ->
  0 <= ms <= Int.max_unsigned -> 0 <= ac <= Int.max_unsigned -> 0 <= ach <= Int.max_unsigned ->
  0 <= ab <= Int.max_signed -> 0 <= ae1 < 256 -> 0 <= ae < 256 ->
  Int.min_signed <= nice <= Int.max_signed -> 0 <= limit <= Int.max_unsigned ->
  runs (lm_cmp_body s (d_strstart s + 258)) (d_strstart s + 2, ac + 2, 0) sc ->
  runs_after (lm_body nice limit) (if sc - d_strstart s >? ab then
       if sc - d_strstart s >=? nice then Some (inr (sc - d_strstart s, set_d_match_start s ac))
       else let* e1 := mb_rd (d_window s) (sc - 1) in
            let* e := mb_rd (d_window s) sc in
            lm_next limit (mkLM ac ach (sc - d_strstart s) e1 e (set_d_match_start s ac))
     else lm_next limit (mkLM ac ach ab ae1 ae (set_d_match_start s ms))) (bf, sf) ->
  semax (with_Delta_specs DS (func_tycontext f_longest_match DSpec.Vprog Gprog_longest_match nil))
   (PROP ( )
    LOCAL (temp _match (offset_val (ac + 1 + 1) (p_window p));
           temp _scan (offset_val (d_strstart s + 2) (p_window p));
           temp _t'7 (Vint (Int.repr 0)); temp _t'6 (Vint (Int.repr 0));
           temp _t'5 (Vint (Int.repr 0)); temp _t'58 (Vint (Int.repr ae));
           temp _t'60 (p_window p); temp _cur_match (Vint (Int.repr ac));
           temp _chain_length (Vint (Int.repr ach));
           temp _best_len (Vint (Int.repr ab));
           temp _scan_end1 (Vint (Int.repr ae1));
           temp _scan_end (Vint (Int.repr ae));
           temp _strend (offset_val (d_strstart s + 258) (p_window p));
           temp _nice_match (Vint (Int.repr nice));
           temp _limit (Vint (Int.repr limit)); temp _prev (p_prev p);
           temp _wmask (Vint (Int.repr (d_w_mask s))); temp _s (p_s p))
    SEP (FRZL Fr; field_at Ews t_ds (DOT _window) (p_window p) (p_s p);
         data_at Ews (tarray tuchar (Zlength (mb_val (d_window s)))) (mb_vals (d_window s)) (p_window p);
         data_at Ews (tarray tushort (Zlength (d_prev s))) (map (fun z : Z => Vint (Int.repr z)) (d_prev s)) (p_prev p);
         field_at Ews t_ds (DOT _match_start) (Vint (Int.repr ms)) (p_s p);
         field_at Ews t_ds (DOT _lookahead) (Vint (Int.repr (d_lookahead s))) (p_s p)))
   (Ssequence lm_cmp_stmt lm_rest_stmt)
   (loop1_ret_assert (EX (a : lm_st) (ms : Z),
      PROP (runs_after (lm_body nice limit) (lm_next limit a) (bf, sf); lm_s a = set_d_match_start s ms;
            0 <= ms <= Int.max_unsigned; 0 <= lm_cur a <= Int.max_unsigned; 0 <= lm_chain a <= Int.max_unsigned;
            0 <= lm_best a <= Int.max_signed; 0 <= lm_end1 a < 256; 0 <= lm_end a < 256)
      LOCAL (temp _cur_match (Vint (Int.repr (lm_cur a))); temp _chain_length (Vint (Int.repr (lm_chain a)));
             temp _best_len (Vint (Int.repr (lm_best a))); temp _scan_end1 (Vint (Int.repr (lm_end1 a)));
             temp _scan_end (Vint (Int.repr (lm_end a)));
             temp _scan (offset_val (d_strstart s) (p_window p));
             temp _strend (offset_val (d_strstart s + 258) (p_window p));
             temp _nice_match (Vint (Int.repr nice)); temp _limit (Vint (Int.repr limit)); temp _prev (p_prev p);
             temp _wmask (Vint (Int.repr (d_w_mask s))); temp _s (p_s p))
      SEP (FRZL Fr; field_at Ews t_ds (DOT _window) (p_window p) (p_s p);
           data_at Ews (tarray tuchar (Zlength (mb_val (d_window s)))) (mb_vals (d_window s)) (p_window p);
           data_at Ews (tarray tushort (Zlength (d_prev s))) (map (fun z : Z => Vint (Int.repr z)) (d_prev s)) (p_prev p);
           field_at Ews t_ds (DOT _match_start) (Vint (Int.repr ms)) (p_s p);
           field_at Ews t_ds (DOT _lookahead) (Vint (Int.repr (d_lookahead s))) (p_s p)))%argsassert (overridePost (PROP (sf = set_d_match_start s (d_match_start sf); 0 <= d_match_start sf <= Int.max_unsigned;
                  0 <= bf <= Int.max_signed)
      LOCAL (temp _best_len (Vint (Int.repr bf)); temp _s (p_s p))
      SEP (FRZL Fr; field_at Ews t_ds (DOT _window) (p_window p) (p_s p);
           data_at Ews (tarray tuchar (Zlength (mb_val (d_window s)))) (mb_vals (d_window s)) (p_window p);
           data_at Ews (tarray tushort (Zlength (d_prev s))) (map (fun z : Z => Vint (Int.repr z)) (d_prev s)) (p_prev p);
           field_at Ews t_ds (DOT _match_start) (Vint (Int.repr (d_match_start sf))) (p_s p);
           field_at Ews t_ds (DOT _lookahead) (Vint (Int.repr (d_lookahead s))) (p_s p))) R)).
Proof.
  intros Hwok Hfc Hwin Ha1 HwL Hst H4 H5 H6 H7 H8 H9 Hnice Hlim EL Hm.
  destruct R as [r1 r2 r3 r4].
    replace (ac + 1 + 1) with (ac + 2) by lia.
    unfold lm_rest_stmt.
    match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx (?a :: ?b :: _ :: ?rest)))) _ _ =>
      let Q2 := remove_LOCAL2 constr:([temp _scan Vundef; temp _match Vundef; temp _strend Vundef]) Q in
      eapply semax_seq';
      [ eapply semax_pre;
        [ | apply (lm_cmp_loop_framed Espec s (p_window p) (d_strstart s) (ac + 2) sc DS Q2
                 (a :: b :: rest));
          auto; try lia; try (auto 50 with closed) ]
      | ]
    end.
    { entailer!. }
    pose (Delta := @abbreviate tycontext (with_Delta_specs DS (func_tycontext f_longest_match DSpec.Vprog Gprog_longest_match nil))).
    change (with_Delta_specs DS (func_tycontext f_longest_match DSpec.Vprog Gprog_longest_match nil)) with Delta.
    cbv beta iota zeta delta - [abbreviate] in Delta.
    abbreviate_semax. Intros.
    forward.
    { entailer!. rewrite ptr_diff_val by auto. apply andp_right; apply prop_right.
      - rewrite Int.signed_repr by rep_lia. rep_lia.
      - apply sameblock_offset; auto. }
    rewrite len_val by auto.
    forward.
    rewrite sub_ptr_s by (auto; rep_lia).
    replace (d_strstart s + 258 - 258) with (d_strstart s) by lia.
    replace (258 - (d_strstart s + 258 - sc)) with (sc - d_strstart s) by lia.
    destruct (sc - d_strstart s >? ab) eqn:Elen.
    - forward_if; [|dead].
      forward. forward.
      destruct (sc - d_strstart s >=? nice) eqn:Enice2.
      + forward_if; [|dead].
        forward. cbn in Hm. inversion Hm; subst bf sf.
        entailer!; try (cbn [d_match_start set_d_match_start]; auto).
      + forward_if; [dead|].
        destruct (mb_rd (d_window s) (sc - 1)) as [e1|] eqn:E6; cbn [bind] in Hm; [|contradiction].
        destruct (mb_rd_vals _ _ _ Hwok E6) as (Hke1 & Hze1 & Hve1).
        destruct (mb_rd (d_window s) sc) as [e|] eqn:E7; cbn [bind] in Hm; [|contradiction].
        destruct (mb_rd_vals _ _ _ Hwok E7) as (Hke & Hze & Hve).
        assert (Hfa : force_val (sem_add_ptr_int tuchar Signed (offset_val (d_strstart s) (p_window p))
            (Vint (Int.sub (Int.repr (sc - d_strstart s)) (Int.repr 1)))) =
          field_address (tarray tuchar (Zlength (mb_val (d_window s)))) [ArraySubsc (sc - 1)] (p_window p)).
        { apply win_fa_s; auto. rewrite signed_sub1 by rep_lia. lia. }
        forward; [win_tc Hze1 | rewrite Hze1]. clear Hfa.
        forward.
        assert (Hfa : force_val (sem_add_ptr_int tuchar Signed (offset_val (d_strstart s) (p_window p))
            (Vint (Int.repr (sc - d_strstart s)))) =
          field_address (tarray tuchar (Zlength (mb_val (d_window s)))) [ArraySubsc sc] (p_window p)).
        { apply win_fa_s; auto. rewrite Int.signed_repr by rep_lia. lia. }
        forward; [win_tc Hze | rewrite Hze]. clear Hfa.
        forward.
        rewrite !zext8_byte by lia.
        Exists (mkLM ac ach (sc - d_strstart s) e1 e (set_d_match_start s ac)) ac.
        entailer!. cbn [lm_best lm_end1 lm_end]. rep_lia.
    - forward_if; [dead|].
      forward.
      Exists (mkLM ac ach ab ae1 ae (set_d_match_start s ms)) ms.
      entailer!.
Qed.

(** The body of the chain loop (separate Qed). *)
Definition lm_body_stmt : statement :=
(Ssequence
                              (Ssequence
                                (Sset _t'60
                                  (Efield
                                    (Ederef
                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                      (Tstruct _internal_state noattr))
                                    _window (tptr tuchar)))
                                (Sset _match
                                  (Ebinop Oadd (Etempvar _t'60 (tptr tuchar))
                                    (Etempvar _cur_match tuint)
                                    (tptr tuchar))))
                              (Ssequence
                                (Ssequence
                                  (Ssequence
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'58
                                          (Ederef
                                            (Ebinop Oadd
                                              (Etempvar _match (tptr tuchar))
                                              (Etempvar _best_len tint)
                                              (tptr tuchar)) tuchar))
                                        (Sifthenelse (Ebinop Cop.One
                                                       (Etempvar _t'58 tuchar)
                                                       (Etempvar _scan_end tuchar)
                                                       tint)
                                          (Sset _t'5
                                            (Econst_int (Int.repr 1) tint))
                                          (Ssequence
                                            (Sset _t'59
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Etempvar _match (tptr tuchar))
                                                  (Ebinop Osub
                                                    (Etempvar _best_len tint)
                                                    (Econst_int (Int.repr 1) tint)
                                                    tint) (tptr tuchar))
                                                tuchar))
                                            (Sset _t'5
                                              (Ecast
                                                (Ebinop Cop.One
                                                  (Etempvar _t'59 tuchar)
                                                  (Etempvar _scan_end1 tuchar)
                                                  tint) tbool)))))
                                      (Sifthenelse (Etempvar _t'5 tint)
                                        (Sset _t'6
                                          (Econst_int (Int.repr 1) tint))
                                        (Ssequence
                                          (Sset _t'56
                                            (Ederef
                                              (Etempvar _match (tptr tuchar))
                                              tuchar))
                                          (Ssequence
                                            (Sset _t'57
                                              (Ederef
                                                (Etempvar _scan (tptr tuchar))
                                                tuchar))
                                            (Sset _t'6
                                              (Ecast
                                                (Ebinop Cop.One
                                                  (Etempvar _t'56 tuchar)
                                                  (Etempvar _t'57 tuchar)
                                                  tint) tbool))))))
                                    (Sifthenelse (Etempvar _t'6 tint)
                                      (Sset _t'7
                                        (Econst_int (Int.repr 1) tint))
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'8
                                            (Ecast
                                              (Ebinop Oadd
                                                (Etempvar _match (tptr tuchar))
                                                (Econst_int (Int.repr 1) tint)
                                                (tptr tuchar)) (tptr tuchar)))
                                          (Sset _match
                                            (Etempvar _t'8 (tptr tuchar))))
                                        (Ssequence
                                          (Sset _t'54
                                            (Ederef
                                              (Etempvar _t'8 (tptr tuchar))
                                              tuchar))
                                          (Ssequence
                                            (Sset _t'55
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Etempvar _scan (tptr tuchar))
                                                  (Econst_int (Int.repr 1) tint)
                                                  (tptr tuchar)) tuchar))
                                            (Sset _t'7
                                              (Ecast
                                                (Ebinop Cop.One
                                                  (Etempvar _t'54 tuchar)
                                                  (Etempvar _t'55 tuchar)
                                                  tint) tbool)))))))
                                  (Sifthenelse (Etempvar _t'7 tint)
                                    Scontinue
                                    Sskip))
                                (Ssequence
                                  (Ssequence
                                    (Sset _scan
                                      (Ebinop Oadd
                                        (Etempvar _scan (tptr tuchar))
                                        (Econst_int (Int.repr 2) tint)
                                        (tptr tuchar)))
                                    (Sset _match
                                      (Ebinop Oadd
                                        (Etempvar _match (tptr tuchar))
                                        (Econst_int (Int.repr 1) tint)
                                        (tptr tuchar))))
                                  (Ssequence
                                    (Sloop
                                      Sskip
                                      (Ssequence
                                        (Ssequence
                                          (Ssequence
                                            (Ssequence
                                              (Ssequence
                                                (Ssequence
                                                  (Ssequence
                                                    (Ssequence
                                                      (Ssequence
                                                        (Ssequence
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sset _t'9
                                                                (Ecast
                                                                  (Ebinop Oadd
                                                                    (Etempvar _scan (tptr tuchar))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuchar))
                                                                  (tptr tuchar)))
                                                              (Sset _scan
                                                                (Etempvar _t'9 (tptr tuchar))))
                                                            (Sset _t'10
                                                              (Ecast
                                                                (Ebinop Oadd
                                                                  (Etempvar _match (tptr tuchar))
                                                                  (Econst_int (Int.repr 1) tint)
                                                                  (tptr tuchar))
                                                                (tptr tuchar))))
                                                          (Sset _match
                                                            (Etempvar _t'10 (tptr tuchar))))
                                                        (Ssequence
                                                          (Sset _t'50
                                                            (Ederef
                                                              (Etempvar _t'9 (tptr tuchar))
                                                              tuchar))
                                                          (Ssequence
                                                            (Sset _t'51
                                                              (Ederef
                                                                (Etempvar _t'10 (tptr tuchar))
                                                                tuchar))
                                                            (Sifthenelse 
                                                              (Ebinop Oeq
                                                                (Etempvar _t'50 tuchar)
                                                                (Etempvar _t'51 tuchar)
                                                                tint)
                                                              (Ssequence
                                                                (Ssequence
                                                                  (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'12
                                                                    (Ecast
                                                                    (Ebinop Oadd
                                                                    (Etempvar _scan (tptr tuchar))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuchar))
                                                                    (tptr tuchar)))
                                                                    (Sset _scan
                                                                    (Etempvar _t'12 (tptr tuchar))))
                                                                    (Sset _t'13
                                                                    (Ecast
                                                                    (Ebinop Oadd
                                                                    (Etempvar _match (tptr tuchar))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuchar))
                                                                    (tptr tuchar))))
                                                                  (Sset _match
                                                                    (Etempvar _t'13 (tptr tuchar))))
                                                                (Ssequence
                                                                  (Sset _t'52
                                                                    (Ederef
                                                                    (Etempvar _t'12 (tptr tuchar))
                                                                    tuchar))
                                                                  (Ssequence
                                                                    (Sset _t'53
                                                                    (Ederef
                                                                    (Etempvar _t'13 (tptr tuchar))
                                                                    tuchar))
                                                                    (Sset _t'11
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'52 tuchar)
                                                                    (Etempvar _t'53 tuchar)
                                                                    tint)
                                                                    tbool)))))
                                                              (Sset _t'11
                                                                (Econst_int (Int.repr 0) tint))))))
                                                      (Sifthenelse (Etempvar _t'11 tint)
                                                        (Ssequence
                                                          (Ssequence
                                                            (Ssequence
                                                              (Ssequence
                                                                (Sset _t'15
                                                                  (Ecast
                                                                    (Ebinop Oadd
                                                                    (Etempvar _scan (tptr tuchar))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuchar))
                                                                    (tptr tuchar)))
                                                                (Sset _scan
                                                                  (Etempvar _t'15 (tptr tuchar))))
                                                              (Sset _t'16
                                                                (Ecast
                                                                  (Ebinop Oadd
                                                                    (Etempvar _match (tptr tuchar))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuchar))
                                                                  (tptr tuchar))))
                                                            (Sset _match
                                                              (Etempvar _t'16 (tptr tuchar))))
                                                          (Ssequence
                                                            (Sset _t'48
                                                              (Ederef
                                                                (Etempvar _t'15 (tptr tuchar))
                                                                tuchar))
                                                            (Ssequence
                                                              (Sset _t'49
                                                                (Ederef
                                                                  (Etempvar _t'16 (tptr tuchar))
                                                                  tuchar))
                                                              (Sset _t'14
                                                                (Ecast
                                                                  (Ebinop Oeq
                                                                    (Etempvar _t'48 tuchar)
                                                                    (Etempvar _t'49 tuchar)
                                                                    tint)
                                                                  tbool)))))
                                                        (Sset _t'14
                                                          (Econst_int (Int.repr 0) tint))))
                                                    (Sifthenelse (Etempvar _t'14 tint)
                                                      (Ssequence
                                                        (Ssequence
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sset _t'18
                                                                (Ecast
                                                                  (Ebinop Oadd
                                                                    (Etempvar _scan (tptr tuchar))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuchar))
                                                                  (tptr tuchar)))
                                                              (Sset _scan
                                                                (Etempvar _t'18 (tptr tuchar))))
                                                            (Sset _t'19
                                                              (Ecast
                                                                (Ebinop Oadd
                                                                  (Etempvar _match (tptr tuchar))
                                                                  (Econst_int (Int.repr 1) tint)
                                                                  (tptr tuchar))
                                                                (tptr tuchar))))
                                                          (Sset _match
                                                            (Etempvar _t'19 (tptr tuchar))))
                                                        (Ssequence
                                                          (Sset _t'46
                                                            (Ederef
                                                              (Etempvar _t'18 (tptr tuchar))
                                                              tuchar))
                                                          (Ssequence
                                                            (Sset _t'47
                                                              (Ederef
                                                                (Etempvar _t'19 (tptr tuchar))
                                                                tuchar))
                                                            (Sset _t'17
                                                              (Ecast
                                                                (Ebinop Oeq
                                                                  (Etempvar _t'46 tuchar)
                                                                  (Etempvar _t'47 tuchar)
                                                                  tint)
                                                                tbool)))))
                                                      (Sset _t'17
                                                        (Econst_int (Int.repr 0) tint))))
                                                  (Sifthenelse (Etempvar _t'17 tint)
                                                    (Ssequence
                                                      (Ssequence
                                                        (Ssequence
                                                          (Ssequence
                                                            (Sset _t'21
                                                              (Ecast
                                                                (Ebinop Oadd
                                                                  (Etempvar _scan (tptr tuchar))
                                                                  (Econst_int (Int.repr 1) tint)
                                                                  (tptr tuchar))
                                                                (tptr tuchar)))
                                                            (Sset _scan
                                                              (Etempvar _t'21 (tptr tuchar))))
                                                          (Sset _t'22
                                                            (Ecast
                                                              (Ebinop Oadd
                                                                (Etempvar _match (tptr tuchar))
                                                                (Econst_int (Int.repr 1) tint)
                                                                (tptr tuchar))
                                                              (tptr tuchar))))
                                                        (Sset _match
                                                          (Etempvar _t'22 (tptr tuchar))))
                                                      (Ssequence
                                                        (Sset _t'44
                                                          (Ederef
                                                            (Etempvar _t'21 (tptr tuchar))
                                                            tuchar))
                                                        (Ssequence
                                                          (Sset _t'45
                                                            (Ederef
                                                              (Etempvar _t'22 (tptr tuchar))
                                                              tuchar))
                                                          (Sset _t'20
                                                            (Ecast
                                                              (Ebinop Oeq
                                                                (Etempvar _t'44 tuchar)
                                                                (Etempvar _t'45 tuchar)
                                                                tint) tbool)))))
                                                    (Sset _t'20
                                                      (Econst_int (Int.repr 0) tint))))
                                                (Sifthenelse (Etempvar _t'20 tint)
                                                  (Ssequence
                                                    (Ssequence
                                                      (Ssequence
                                                        (Ssequence
                                                          (Sset _t'24
                                                            (Ecast
                                                              (Ebinop Oadd
                                                                (Etempvar _scan (tptr tuchar))
                                                                (Econst_int (Int.repr 1) tint)
                                                                (tptr tuchar))
                                                              (tptr tuchar)))
                                                          (Sset _scan
                                                            (Etempvar _t'24 (tptr tuchar))))
                                                        (Sset _t'25
                                                          (Ecast
                                                            (Ebinop Oadd
                                                              (Etempvar _match (tptr tuchar))
                                                              (Econst_int (Int.repr 1) tint)
                                                              (tptr tuchar))
                                                            (tptr tuchar))))
                                                      (Sset _match
                                                        (Etempvar _t'25 (tptr tuchar))))
                                                    (Ssequence
                                                      (Sset _t'42
                                                        (Ederef
                                                          (Etempvar _t'24 (tptr tuchar))
                                                          tuchar))
                                                      (Ssequence
                                                        (Sset _t'43
                                                          (Ederef
                                                            (Etempvar _t'25 (tptr tuchar))
                                                            tuchar))
                                                        (Sset _t'23
                                                          (Ecast
                                                            (Ebinop Oeq
                                                              (Etempvar _t'42 tuchar)
                                                              (Etempvar _t'43 tuchar)
                                                              tint) tbool)))))
                                                  (Sset _t'23
                                                    (Econst_int (Int.repr 0) tint))))
                                              (Sifthenelse (Etempvar _t'23 tint)
                                                (Ssequence
                                                  (Ssequence
                                                    (Ssequence
                                                      (Ssequence
                                                        (Sset _t'27
                                                          (Ecast
                                                            (Ebinop Oadd
                                                              (Etempvar _scan (tptr tuchar))
                                                              (Econst_int (Int.repr 1) tint)
                                                              (tptr tuchar))
                                                            (tptr tuchar)))
                                                        (Sset _scan
                                                          (Etempvar _t'27 (tptr tuchar))))
                                                      (Sset _t'28
                                                        (Ecast
                                                          (Ebinop Oadd
                                                            (Etempvar _match (tptr tuchar))
                                                            (Econst_int (Int.repr 1) tint)
                                                            (tptr tuchar))
                                                          (tptr tuchar))))
                                                    (Sset _match
                                                      (Etempvar _t'28 (tptr tuchar))))
                                                  (Ssequence
                                                    (Sset _t'40
                                                      (Ederef
                                                        (Etempvar _t'27 (tptr tuchar))
                                                        tuchar))
                                                    (Ssequence
                                                      (Sset _t'41
                                                        (Ederef
                                                          (Etempvar _t'28 (tptr tuchar))
                                                          tuchar))
                                                      (Sset _t'26
                                                        (Ecast
                                                          (Ebinop Oeq
                                                            (Etempvar _t'40 tuchar)
                                                            (Etempvar _t'41 tuchar)
                                                            tint) tbool)))))
                                                (Sset _t'26
                                                  (Econst_int (Int.repr 0) tint))))
                                            (Sifthenelse (Etempvar _t'26 tint)
                                              (Ssequence
                                                (Ssequence
                                                  (Ssequence
                                                    (Ssequence
                                                      (Sset _t'30
                                                        (Ecast
                                                          (Ebinop Oadd
                                                            (Etempvar _scan (tptr tuchar))
                                                            (Econst_int (Int.repr 1) tint)
                                                            (tptr tuchar))
                                                          (tptr tuchar)))
                                                      (Sset _scan
                                                        (Etempvar _t'30 (tptr tuchar))))
                                                    (Sset _t'31
                                                      (Ecast
                                                        (Ebinop Oadd
                                                          (Etempvar _match (tptr tuchar))
                                                          (Econst_int (Int.repr 1) tint)
                                                          (tptr tuchar))
                                                        (tptr tuchar))))
                                                  (Sset _match
                                                    (Etempvar _t'31 (tptr tuchar))))
                                                (Ssequence
                                                  (Sset _t'38
                                                    (Ederef
                                                      (Etempvar _t'30 (tptr tuchar))
                                                      tuchar))
                                                  (Ssequence
                                                    (Sset _t'39
                                                      (Ederef
                                                        (Etempvar _t'31 (tptr tuchar))
                                                        tuchar))
                                                    (Sset _t'29
                                                      (Ecast
                                                        (Ebinop Oeq
                                                          (Etempvar _t'38 tuchar)
                                                          (Etempvar _t'39 tuchar)
                                                          tint) tbool)))))
                                              (Sset _t'29
                                                (Econst_int (Int.repr 0) tint))))
                                          (Sifthenelse (Etempvar _t'29 tint)
                                            (Sset _t'32
                                              (Ecast
                                                (Ebinop Olt
                                                  (Etempvar _scan (tptr tuchar))
                                                  (Etempvar _strend (tptr tuchar))
                                                  tint) tbool))
                                            (Sset _t'32
                                              (Econst_int (Int.repr 0) tint))))
                                        (Sifthenelse (Etempvar _t'32 tint)
                                          Sskip
                                          Sbreak)))
                                    (Ssequence
                                      (Sset _len
                                        (Ebinop Osub
                                          (Econst_int (Int.repr 258) tint)
                                          (Ecast
                                            (Ebinop Osub
                                              (Etempvar _strend (tptr tuchar))
                                              (Etempvar _scan (tptr tuchar))
                                              tlong) tint) tint))
                                      (Ssequence
                                        (Sset _scan
                                          (Ebinop Osub
                                            (Etempvar _strend (tptr tuchar))
                                            (Econst_int (Int.repr 258) tint)
                                            (tptr tuchar)))
                                        (Sifthenelse (Ebinop Ogt
                                                       (Etempvar _len tint)
                                                       (Etempvar _best_len tint)
                                                       tint)
                                          (Ssequence
                                            (Sassign
                                              (Efield
                                                (Ederef
                                                  (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                  (Tstruct _internal_state noattr))
                                                _match_start tuint)
                                              (Etempvar _cur_match tuint))
                                            (Ssequence
                                              (Sset _best_len
                                                (Etempvar _len tint))
                                              (Ssequence
                                                (Sifthenelse (Ebinop Oge
                                                               (Etempvar _len tint)
                                                               (Etempvar _nice_match tint)
                                                               tint)
                                                  Sbreak
                                                  Sskip)
                                                (Ssequence
                                                  (Ssequence
                                                    (Sset _t'37
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Etempvar _scan (tptr tuchar))
                                                          (Ebinop Osub
                                                            (Etempvar _best_len tint)
                                                            (Econst_int (Int.repr 1) tint)
                                                            tint)
                                                          (tptr tuchar))
                                                        tuchar))
                                                    (Sset _scan_end1
                                                      (Ecast
                                                        (Etempvar _t'37 tuchar)
                                                        tuchar)))
                                                  (Ssequence
                                                    (Sset _t'36
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Etempvar _scan (tptr tuchar))
                                                          (Etempvar _best_len tint)
                                                          (tptr tuchar))
                                                        tuchar))
                                                    (Sset _scan_end
                                                      (Ecast
                                                        (Etempvar _t'36 tuchar)
                                                        tuchar)))))))
                                          Sskip))))))).

Lemma lm_body_ok (Espec : OracleKind) (DS : Maps.PTree.t funspec) (Fr : list mpred) (R : ret_assert)
  (s : dstate) (p : dptrs) (nice limit bf : Z) (sf : dstate) :
  mb_ok (d_window s) ->
  field_compatible (tarray tuchar (Zlength (mb_val (d_window s)))) [] (p_window p) ->
  isptr (p_window p) ->
  d_strstart s + 258 <= Zlength (mb_val (d_window s)) ->
  Zlength (mb_val (d_window s)) <= Int.max_unsigned ->
  0 <= d_strstart s <= Int.max_unsigned ->
  Int.min_signed <= nice <= Int.max_signed -> 0 <= limit <= Int.max_unsigned ->
  semax (with_Delta_specs DS (func_tycontext f_longest_match DSpec.Vprog Gprog_longest_match nil))
   (EX (a : lm_st) (ms : Z),
      PROP (runs (lm_body nice limit) a (bf, sf); lm_s a = set_d_match_start s ms;
            0 <= ms <= Int.max_unsigned; 0 <= lm_cur a <= Int.max_unsigned; 0 <= lm_chain a <= Int.max_unsigned;
            0 <= lm_best a <= Int.max_signed; 0 <= lm_end1 a < 256; 0 <= lm_end a < 256)
      LOCAL (temp _cur_match (Vint (Int.repr (lm_cur a))); temp _chain_length (Vint (Int.repr (lm_chain a)));
             temp _best_len (Vint (Int.repr (lm_best a))); temp _scan_end1 (Vint (Int.repr (lm_end1 a)));
             temp _scan_end (Vint (Int.repr (lm_end a)));
             temp _scan (offset_val (d_strstart s) (p_window p));
             temp _strend (offset_val (d_strstart s + 258) (p_window p));
             temp _nice_match (Vint (Int.repr nice)); temp _limit (Vint (Int.repr limit)); temp _prev (p_prev p);
             temp _wmask (Vint (Int.repr (d_w_mask s))); temp _s (p_s p))
      SEP (FRZL Fr; field_at Ews t_ds (DOT _window) (p_window p) (p_s p);
           data_at Ews (tarray tuchar (Zlength (mb_val (d_window s)))) (mb_vals (d_window s)) (p_window p);
           data_at Ews (tarray tushort (Zlength (d_prev s))) (map (fun z : Z => Vint (Int.repr z)) (d_prev s)) (p_prev p);
           field_at Ews t_ds (DOT _match_start) (Vint (Int.repr ms)) (p_s p);
           field_at Ews t_ds (DOT _lookahead) (Vint (Int.repr (d_lookahead s))) (p_s p)))%argsassert
   lm_body_stmt
   (loop1_ret_assert (EX (a : lm_st) (ms : Z),
      PROP (runs_after (lm_body nice limit) (lm_next limit a) (bf, sf); lm_s a = set_d_match_start s ms;
            0 <= ms <= Int.max_unsigned; 0 <= lm_cur a <= Int.max_unsigned; 0 <= lm_chain a <= Int.max_unsigned;
            0 <= lm_best a <= Int.max_signed; 0 <= lm_end1 a < 256; 0 <= lm_end a < 256)
      LOCAL (temp _cur_match (Vint (Int.repr (lm_cur a))); temp _chain_length (Vint (Int.repr (lm_chain a)));
             temp _best_len (Vint (Int.repr (lm_best a))); temp _scan_end1 (Vint (Int.repr (lm_end1 a)));
             temp _scan_end (Vint (Int.repr (lm_end a)));
             temp _scan (offset_val (d_strstart s) (p_window p));
             temp _strend (offset_val (d_strstart s + 258) (p_window p));
             temp _nice_match (Vint (Int.repr nice)); temp _limit (Vint (Int.repr limit)); temp _prev (p_prev p);
             temp _wmask (Vint (Int.repr (d_w_mask s))); temp _s (p_s p))
      SEP (FRZL Fr; field_at Ews t_ds (DOT _window) (p_window p) (p_s p);
           data_at Ews (tarray tuchar (Zlength (mb_val (d_window s)))) (mb_vals (d_window s)) (p_window p);
           data_at Ews (tarray tushort (Zlength (d_prev s))) (map (fun z : Z => Vint (Int.repr z)) (d_prev s)) (p_prev p);
           field_at Ews t_ds (DOT _match_start) (Vint (Int.repr ms)) (p_s p);
           field_at Ews t_ds (DOT _lookahead) (Vint (Int.repr (d_lookahead s))) (p_s p)))%argsassert (overridePost (PROP (sf = set_d_match_start s (d_match_start sf); 0 <= d_match_start sf <= Int.max_unsigned;
                  0 <= bf <= Int.max_signed)
      LOCAL (temp _best_len (Vint (Int.repr bf)); temp _s (p_s p))
      SEP (FRZL Fr; field_at Ews t_ds (DOT _window) (p_window p) (p_s p);
           data_at Ews (tarray tuchar (Zlength (mb_val (d_window s)))) (mb_vals (d_window s)) (p_window p);
           data_at Ews (tarray tushort (Zlength (d_prev s))) (map (fun z : Z => Vint (Int.repr z)) (d_prev s)) (p_prev p);
           field_at Ews t_ds (DOT _match_start) (Vint (Int.repr (d_match_start sf))) (p_s p);
           field_at Ews t_ds (DOT _lookahead) (Vint (Int.repr (d_lookahead s))) (p_s p))) R)).
Proof.
  intros Hwok Hfc Hwin Ha1 HwL Hst Hnice Hlim.
  destruct R as [r1 r2 r3 r4].
  pose (Delta := @abbreviate tycontext (with_Delta_specs DS (func_tycontext f_longest_match DSpec.Vprog Gprog_longest_match nil))).
  change (with_Delta_specs DS (func_tycontext f_longest_match DSpec.Vprog Gprog_longest_match nil)) with Delta.
  cbv beta iota zeta delta - [abbreviate] in Delta.
  unfold lm_body_stmt. abbreviate_semax.
  (* the names of the script: the invariant's facts become H2 .. H9 *)
  assert (H : True) by exact I. assert (H0 : True) by exact I. assert (H1 : True) by exact I.
    Intros a ms. destruct a as [ac ach ab ae1 ae as_]. cbn [lm_cur lm_chain lm_best lm_end1 lm_end lm_s] in *. subst as_.
    pose proof H2 as Hrun0. pose proof (runs_after_of _ _ _ H2) as Hm. clear H2.
    rewrite lm_body_eq in Hm. unfold lm_body' in Hm.
    cbn [lm_s lm_cur lm_chain lm_best lm_end1 lm_end] in Hm.
    change (d_window (set_d_match_start s ms)) with (d_window s) in Hm.
    change (d_strstart (set_d_match_start s ms)) with (d_strstart s) in Hm.
    change (lm_cmp_body (set_d_match_start s ms)) with (lm_cmp_body s) in Hm.
    forward. forward.
    rewrite ?add_ptr_u, ?add_ptr_u', u32_small by (auto; rep_lia).
    destruct (mb_rd (d_window s) (ac + ab)) as [m0|] eqn:E0; cbn [bind] in Hm; [|contradiction].
    destruct (mb_rd_vals _ _ _ Hwok E0) as (Hk0 & Hz0 & Hv0).
    assert (Hfa : force_val (sem_add_ptr_int tuchar Signed (offset_val ac (p_window p)) (Vint (Int.repr ab))) =
      field_address (tarray tuchar (Zlength (mb_val (d_window s)))) [ArraySubsc (ac + ab)] (p_window p)).
    { apply win_fa_s; auto. rewrite Int.signed_repr by rep_lia. lia. }
    forward; [win_tc Hz0 | rewrite Hz0]. clear Hfa.
    destruct (Z.eq_dec m0 ae) as [Eq0|Ne0].
    2: { (* match[best_len] != scan_end *)
      rewrite (proj2 (Z.eqb_neq _ _) Ne0) in Hm. cbn [negb] in Hm.
      forward_if (temp _t'5 (Vint (Int.repr 1))). { forward. entailer!. } { dead. }
      cont_tail (mkLM ac ach ab ae1 ae (set_d_match_start s ms)) ms. }
    rewrite (proj2 (Z.eqb_eq _ _) Eq0) in Hm. cbn [negb] in Hm. subst m0.
    destruct (mb_rd (d_window s) (ac + ab - 1)) as [m1|] eqn:E1; cbn [bind] in Hm; [|contradiction].
    destruct (mb_rd_vals _ _ _ Hwok E1) as (Hk1 & Hz1 & Hv1).
    assert (Hfa : force_val (sem_add_ptr_int tuchar Signed (offset_val ac (p_window p))
        (Vint (Int.sub (Int.repr ab) (Int.repr 1)))) =
      field_address (tarray tuchar (Zlength (mb_val (d_window s)))) [ArraySubsc (ac + ab - 1)] (p_window p)).
    { apply win_fa_s; auto. rewrite signed_sub1 by rep_lia. lia. }
    destruct (Z.eq_dec m1 ae1) as [Eq1|Ne1].
    2: { (* match[best_len - 1] != scan_end1 *)
      rewrite (proj2 (Z.eqb_neq _ _) Ne1) in Hm. cbn [negb] in Hm.
      forward_if (temp _t'5 (Vint (Int.repr 1))).
      { dead. }
      { forward; [win_tc Hz1 | rewrite Hz1]. forward. entailer!; beq. }
      cont_tail (mkLM ac ach ab ae1 ae (set_d_match_start s ms)) ms. }
    rewrite (proj2 (Z.eqb_eq _ _) Eq1) in Hm. cbn [negb] in Hm. subst m1.
    forward_if (temp _t'5 (Vint (Int.repr 0))).
    { dead. }
    { forward; [win_tc Hz1 | rewrite Hz1]. forward. entailer!; beq. }
    clear Hfa.
    destruct (mb_rd (d_window s) ac) as [m2|] eqn:E2; cbn [bind] in Hm; [|contradiction].
    destruct (mb_rd_vals _ _ _ Hwok E2) as (Hkm2 & Hzm2 & Hvm2).
    destruct (mb_rd (d_window s) (d_strstart s)) as [sc0|] eqn:E3; cbn [bind] in Hm; [|contradiction].
    destruct (mb_rd_vals _ _ _ Hwok E3) as (Hks0 & Hzs0 & Hvs0).
    assert (Hfa2 : offset_val ac (p_window p) =
      field_address (tarray tuchar (Zlength (mb_val (d_window s)))) [ArraySubsc ac] (p_window p))
      by (apply win_fa; auto).
    assert (Hfa3 : offset_val (d_strstart s) (p_window p) =
      field_address (tarray tuchar (Zlength (mb_val (d_window s)))) [ArraySubsc (d_strstart s)] (p_window p))
      by (apply win_fa; auto).
    destruct (Z.eq_dec m2 sc0) as [Eq2|Ne2].
    2: { (* *match != *scan *)
      rewrite (proj2 (Z.eqb_neq _ _) Ne2) in Hm. cbn [negb] in Hm.
      forward_if (temp _t'6 (Vint (Int.repr 1))).
      { dead. }
      { forward; [win_tc Hzm2 | rewrite Hzm2]. forward; [win_tc Hzs0 | rewrite Hzs0]. forward. entailer!; beq. }
      cont_tail (mkLM ac ach ab ae1 ae (set_d_match_start s ms)) ms. }
    rewrite (proj2 (Z.eqb_eq _ _) Eq2) in Hm. cbn [negb] in Hm. subst m2.
    forward_if (temp _t'6 (Vint (Int.repr 0))).
    { dead. }
    { forward; [win_tc Hzm2 | rewrite Hzm2]. forward; [win_tc Hzs0 | rewrite Hzs0]. forward. entailer!; beq. }
    clear Hfa2 Hfa3.
    destruct (mb_rd (d_window s) (ac + 1)) as [m3|] eqn:E4; cbn [bind] in Hm; [|contradiction].
    destruct (mb_rd_vals _ _ _ Hwok E4) as (Hkm3 & Hzm3 & Hvm3).
    destruct (mb_rd (d_window s) (d_strstart s + 1)) as [sc1|] eqn:E5; cbn [bind] in Hm; [|contradiction].
    destruct (mb_rd_vals _ _ _ Hwok E5) as (Hks1 & Hzs1 & Hvs1).
    assert (Hfa4 : offset_val (ac + 1) (p_window p) =
      field_address (tarray tuchar (Zlength (mb_val (d_window s)))) [ArraySubsc (ac + 1)] (p_window p))
      by (apply win_fa; auto).
    assert (Hfa5 : force_val (sem_add_ptr_int tuchar Signed (offset_val (d_strstart s) (p_window p)) (Vint (Int.repr 1))) =
      field_address (tarray tuchar (Zlength (mb_val (d_window s)))) [ArraySubsc (d_strstart s + 1)] (p_window p))
      by (apply win_fa_s; auto; rewrite Int.signed_repr by rep_lia; lia).
    destruct (Z.eq_dec m3 sc1) as [Eq3|Ne3].
    2: { (* *++match != scan[1] *)
      rewrite (proj2 (Z.eqb_neq _ _) Ne3) in Hm. cbn [negb] in Hm.
      forward_if [temp _t'7 (Vint (Int.repr 1)); temp _match (offset_val (ac + 1) (p_window p))].
      { dead. }
      { forward. forward. rewrite ?add_ptr_s' by (auto; rep_lia).
        forward; [win_tc Hzm3 | rewrite Hzm3]. forward; [win_tc Hzs1 | rewrite Hzs1]. forward. entailer!; beq. }
      cont_tail (mkLM ac ach ab ae1 ae (set_d_match_start s ms)) ms. }
    rewrite (proj2 (Z.eqb_eq _ _) Eq3) in Hm. cbn [negb] in Hm. subst m3.
    forward_if [temp _t'7 (Vint (Int.repr 0)); temp _match (offset_val (ac + 1) (p_window p))].
    { dead. }
    { forward. forward. rewrite ?add_ptr_s' by (auto; rep_lia).
      forward; [win_tc Hzm3 | rewrite Hzm3]. forward; [win_tc Hzs1 | rewrite Hzs1]. forward. entailer!; beq. }
    clear Hfa4 Hfa5.
    forward_if.
    { dead. }
    forward. forward.
    rewrite ?add_ptr_s' by (auto; rep_lia).
    (* the inner comparison loop and the rest of the body: lemma lm_tail (separate Qed) *)
    clear Hm. destruct (lm_E_model _ _ _ _ _ _ _ _ _ _ _ _ _ Hrun0 E0 E1 E2 E3 E4 E5) as (sc & EL & Hm).
    eapply (lm_tail Espec DS Fr); eauto.
Qed.

Lemma body_longest_match : ob_longest_match.
Proof.
  unfold ob_longest_match.
  start_function.
  unfold c_longest_match in H0.
  inv_bind H0. destruct x. apply guard_inv in Ha.
  inv_bind H0. destruct x. apply guard_inv in Ha0.
  inv_bind H0. destruct x. apply guard_inv in Ha1.
  inv_bind H0. inv_bind H0.
  inv_bind H0. destruct x1 as [bf sf].
  unfold dstate_at, win_at, hash_at, match_at, cfg_at. Intros.
  freeze FR := (trees_at _ _ _ _ _) (stat_at _ _)
    (field_at _ _ (DOT _window_size) _ _) (field_at _ _ (DOT _w_bits) _ _) (field_at _ _ (DOT _high_water) _ _)
    (field_at _ _ (DOT _head) _ _) (field_at _ _ (DOT _ins_h) _ _) (field_at _ _ (DOT _hash_size) _ _)
    (field_at _ _ (DOT _hash_bits) _ _).
  freeze FR2 := (field_at _ _ (DOT _hash_mask) _ _) (field_at _ _ (DOT _hash_shift) _ _)
    (data_at _ (tarray tushort (Zlength (d_head s))) _ _)
    (field_at _ _ (DOT _block_start) _ _) (field_at _ _ (DOT _match_length) _ _)
    (field_at _ _ (DOT _prev_match) _ _) (field_at _ _ (DOT _match_available) _ _)
    (field_at _ _ (DOT _insert) _ _) (field_at _ _ (DOT _slid) _ _) (field_at _ _ (DOT _max_lazy_match) _ _).
  change DState.MIN_LOOKAHEAD with 262 in Ha4. change DState.MAX_MATCH with 258 in Ha1.
  apply Z.leb_le in Ha1.
  unfold in_int in Ha, Ha0. apply andb_prop in Ha. apply andb_prop in Ha0.
  destruct Ha as [Hb1 Hb2]. destruct Ha0 as [Hl1 Hl2].
  apply Z.leb_le in Hb1. apply Z.leb_le in Hb2. apply Z.leb_le in Hl1. apply Z.leb_le in Hl2.
  revert Ha4.
  remember (if u32 (d_nice_match s) >? d_lookahead s then d_lookahead s else d_nice_match s) as nice eqn:Enice.
  remember (if d_strstart s >? u32 (d_w_size s - 262) then u32 (d_strstart s - u32 (d_w_size s - 262)) else NIL)
    as limit eqn:Elimit.
  remember (if d_prev_length s >=? d_good_match s then Z.shiftr (d_max_chain_length s) 2
                 else d_max_chain_length s) as chain0 eqn:Echain0.
  intros Ha4.
  apply loop_runs in Ha4.
  pose proof H1 as Hr.
  destruct Hr as (_ & _ & _ & _ & _ & _ & _ & Hws & _ & Hwm & Hwok & HwL & _ & Hprev & _ & HprevL & _ & _ & _ & _ & _ &
    _ & _ & _ & _ & _ & Hst & Hms & Hla & Hpl & Hmc & _ & Hgm & Hnm & _ & _ & _).
  unfold u32_ok, s32_ok in *.
  assert (Hlim : 0 <= limit <= Int.max_unsigned).
  { rewrite Elimit. destruct (d_strstart s >? u32 (d_w_size s - 262)); [apply u32_range | unfold NIL; rep_lia]. }
  assert (Hnice : Int.min_signed <= nice <= Int.max_signed).
  { rewrite Enice. destruct (u32 (d_nice_match s) >? d_lookahead s); rep_lia. }
  assert (Hch0 : 0 <= chain0 <= Int.max_unsigned).
  { rewrite Echain0. destruct (d_prev_length s >=? d_good_match s); [|lia].
    rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|].
    apply Z.le_trans with (d_max_chain_length s); [apply Z.div_le_upper_bound; lia | lia]. }
  assert (Hlm1 : u32 (d_w_size s - 262) < d_strstart s -> limit = u32 (d_strstart s - u32 (d_w_size s - 262))).
  { intros. rewrite Elimit. dcmp. reflexivity. }
  assert (Hlm2 : d_strstart s <= u32 (d_w_size s - 262) -> limit = 0).
  { intros. rewrite Elimit. dcmp. reflexivity. }
  assert (Hc1 : d_good_match s <= d_prev_length s -> chain0 = Z.shiftr (d_max_chain_length s) 2).
  { intros. rewrite Echain0. dcmp. reflexivity. }
  assert (Hc2 : d_prev_length s < d_good_match s -> chain0 = d_max_chain_length s).
  { intros. rewrite Echain0. dcmp. reflexivity. }
  assert (Hn1 : d_lookahead s < u32 (d_nice_match s) -> nice = d_lookahead s).
  { intros. rewrite Enice. dcmp. reflexivity. }
  assert (Hn2 : u32 (d_nice_match s) <= d_lookahead s -> nice = d_nice_match s).
  { intros. rewrite Enice. dcmp. reflexivity. }
  clear Enice Elimit Echain0.
  assert_PROP (isptr (p_window p)) as Hwin by entailer!.
  assert_PROP (field_compatible (tarray tuchar (Zlength (mb_val (d_window s)))) [] (p_window p)) as Hfc by entailer!.
  unfold vi.
  forward. forward. forward. forward.
  rewrite add_ptr_u, u32_small by (auto; lia).
  forward. forward. forward.
  forward. forward.
  forward_if (temp _t'1 (Vint (Int.repr limit))).
  { forward. forward. forward. entailer!.
    rewrite ?u32_unsigned in H2. change (258 + 3 + 1) with 262 in *.
    rewrite (Hlm1 ltac:(lia)), repr_u32, repr_sub_u32. reflexivity. }
  { forward. entailer!.
    rewrite ?u32_unsigned in H2. change (258 + 3 + 1) with 262 in *.
    rewrite (Hlm2 ltac:(lia)). reflexivity. }
  forward. forward. forward. forward. forward. forward.
  rewrite add_ptr_u', u32_small, add_ptr_s, offset_offset_val by (auto; rep_lia).
  destruct (mb_rd_vals _ _ _ Hwok Ha2) as (Hk2 & Hz2 & Hv2).
  assert (Hfa : force_val (sem_add_ptr_int tuchar Signed (offset_val (d_strstart s) (p_window p))
      (Vint (Int.sub (Int.repr (d_prev_length s)) (Int.repr 1)))) =
    field_address (tarray tuchar (Zlength (mb_val (d_window s)))) [ArraySubsc (d_strstart s + d_prev_length s - 1)] (p_window p)).
  { apply win_fa_s; auto. rewrite signed_sub1 by rep_lia. lia. }
  forward; [win_tc Hz2 | rewrite Hz2]. clear Hfa.
  forward.
  destruct (mb_rd_vals _ _ _ Hwok Ha3) as (Hk3 & Hz3 & Hv3).
  assert (Hfa : force_val (sem_add_ptr_int tuchar Signed (offset_val (d_strstart s) (p_window p))
      (Vint (Int.repr (d_prev_length s)))) =
    field_address (tarray tuchar (Zlength (mb_val (d_window s)))) [ArraySubsc (d_strstart s + d_prev_length s)] (p_window p)).
  { apply win_fa_s; auto. rewrite Int.signed_repr by rep_lia. lia. }
  forward; [win_tc Hz3 | rewrite Hz3]. clear Hfa.
  forward.
  forward. forward.
  rewrite !zext8_byte by lia.
  forward_if (temp _chain_length (Vint (Int.repr chain0))).
  { forward. entailer!. rewrite (Hc1 ltac:(lia)).
    rewrite shru_repr by rep_lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity. }
  { forward. entailer!. rewrite (Hc2 ltac:(lia)). reflexivity. }
  forward.
  forward_if (temp _nice_match (Vint (Int.repr nice))).
  { forward. forward. entailer!. rewrite ?u32_unsigned in H2. rewrite (Hn1 ltac:(lia)). reflexivity. }
  { forward. entailer!. rewrite ?u32_unsigned in H2. rewrite (Hn2 ltac:(lia)). reflexivity. }
  freeze FR3 := (FRZL FR2) (FRZL FR) (field_at _ _ (DOT _w_size) _ _) (field_at _ _ (DOT _w_mask) _ _)
    (field_at _ _ (DOT _prev) _ _) (field_at _ _ (DOT _strstart) _ _) (field_at _ _ (DOT _prev_length) _ _)
    (field_at _ _ (DOT _max_chain_length) _ _) (field_at _ _ (DOT _good_match) _ _)
    (field_at _ _ (DOT _nice_match) _ _).
  forward_loop (EX a : lm_st, EX ms : Z,
      PROP (runs (lm_body nice limit) a (bf, sf); lm_s a = set_d_match_start s ms;
            0 <= ms <= Int.max_unsigned; 0 <= lm_cur a <= Int.max_unsigned; 0 <= lm_chain a <= Int.max_unsigned;
            0 <= lm_best a <= Int.max_signed; 0 <= lm_end1 a < 256; 0 <= lm_end a < 256)
      LOCAL (temp _cur_match (Vint (Int.repr (lm_cur a))); temp _chain_length (Vint (Int.repr (lm_chain a)));
             temp _best_len (Vint (Int.repr (lm_best a))); temp _scan_end1 (Vint (Int.repr (lm_end1 a)));
             temp _scan_end (Vint (Int.repr (lm_end a)));
             temp _scan (offset_val (d_strstart s) (p_window p));
             temp _strend (offset_val (d_strstart s + 258) (p_window p));
             temp _nice_match (Vint (Int.repr nice)); temp _limit (Vint (Int.repr limit)); temp _prev (p_prev p);
             temp _wmask (Vint (Int.repr (d_w_mask s))); temp _s (p_s p))
      SEP (FRZL FR3; field_at Ews t_ds (DOT _window) (p_window p) (p_s p);
           data_at Ews (tarray tuchar (Zlength (mb_val (d_window s)))) (mb_vals (d_window s)) (p_window p);
           data_at Ews (tarray tushort (Zlength (d_prev s))) (map (fun z : Z => Vint (Int.repr z)) (d_prev s)) (p_prev p);
           field_at Ews t_ds (DOT _match_start) (Vint (Int.repr ms)) (p_s p);
           field_at Ews t_ds (DOT _lookahead) (Vint (Int.repr (d_lookahead s))) (p_s p)))%assert
    continue: (EX a : lm_st, EX ms : Z,
      PROP (runs_after (lm_body nice limit) (lm_next limit a) (bf, sf); lm_s a = set_d_match_start s ms;
            0 <= ms <= Int.max_unsigned; 0 <= lm_cur a <= Int.max_unsigned; 0 <= lm_chain a <= Int.max_unsigned;
            0 <= lm_best a <= Int.max_signed; 0 <= lm_end1 a < 256; 0 <= lm_end a < 256)
      LOCAL (temp _cur_match (Vint (Int.repr (lm_cur a))); temp _chain_length (Vint (Int.repr (lm_chain a)));
             temp _best_len (Vint (Int.repr (lm_best a))); temp _scan_end1 (Vint (Int.repr (lm_end1 a)));
             temp _scan_end (Vint (Int.repr (lm_end a)));
             temp _scan (offset_val (d_strstart s) (p_window p));
             temp _strend (offset_val (d_strstart s + 258) (p_window p));
             temp _nice_match (Vint (Int.repr nice)); temp _limit (Vint (Int.repr limit)); temp _prev (p_prev p);
             temp _wmask (Vint (Int.repr (d_w_mask s))); temp _s (p_s p))
      SEP (FRZL FR3; field_at Ews t_ds (DOT _window) (p_window p) (p_s p);
           data_at Ews (tarray tuchar (Zlength (mb_val (d_window s)))) (mb_vals (d_window s)) (p_window p);
           data_at Ews (tarray tushort (Zlength (d_prev s))) (map (fun z : Z => Vint (Int.repr z)) (d_prev s)) (p_prev p);
           field_at Ews t_ds (DOT _match_start) (Vint (Int.repr ms)) (p_s p);
           field_at Ews t_ds (DOT _lookahead) (Vint (Int.repr (d_lookahead s))) (p_s p)))%assert
    break: (PROP (sf = set_d_match_start s (d_match_start sf); 0 <= d_match_start sf <= Int.max_unsigned;
                  0 <= bf <= Int.max_signed)
      LOCAL (temp _best_len (Vint (Int.repr bf)); temp _s (p_s p))
      SEP (FRZL FR3; field_at Ews t_ds (DOT _window) (p_window p) (p_s p);
           data_at Ews (tarray tuchar (Zlength (mb_val (d_window s)))) (mb_vals (d_window s)) (p_window p);
           data_at Ews (tarray tushort (Zlength (d_prev s))) (map (fun z : Z => Vint (Int.repr z)) (d_prev s)) (p_prev p);
           field_at Ews t_ds (DOT _match_start) (Vint (Int.repr (d_match_start sf))) (p_s p);
           field_at Ews t_ds (DOT _lookahead) (Vint (Int.repr (d_lookahead s))) (p_s p))).
  { (* entry *)
    Exists (mkLM cur chain0 (d_prev_length s) x x0 s) (d_match_start s).
    entailer!. cbn [lm_s lm_best]. rewrite ?set_ms_same. split; [reflexivity | rep_lia]. }
  { (* the body: lemma lm_body_ok (separate Qed) *)
    eapply (lm_body_ok Espec Delta_specs FR3); eauto. }
  { (* the loop test *)
    Intros a ms. destruct a as [ac ach ab ae1 ae as_]. cbn [lm_cur lm_chain lm_best lm_end1 lm_end lm_s] in *. subst as_.
    unfold lm_next in H2. cbn [lm_s lm_cur lm_chain lm_best lm_end1 lm_end d_prev d_w_mask set_d_match_start] in H2.
    destruct (rd (d_prev s) (Z.land ac (d_w_mask s))) as [c'|] eqn:Erd; cbn [bind] in H2; [|contradiction].
    apply rd_some in Erd. destruct Erd as [Hidx Hc'].
    assert (Hc'r : 0 <= c' < 65536) by (subst c'; eapply Forall_Znth; eauto).
    forward. 1: (go_lower; apply prop_right; rewrite Hc'; apply tc_val_tushort_repr; lia).
    rewrite Hc'.
    forward. forward.
    destruct (c' >? limit) eqn:Eg.
    - destruct (u32 (ach - 1) =? 0) eqn:Ez.
      + forward_if [temp _t'3 (Vint (Int.repr 0)); temp _chain_length (Vint (Int.repr (u32 (ach - 1))))].
        { forward. forward. forward. entailer!. rewrite ?eq_repr_u32_0, ?Ez, ?repr_u32. auto. }
        { dead. }
        forward_if.
        { dead. }
        forward. cbn in H2. inversion H2; subst bf sf.
        entailer!; try (cbn [d_match_start set_d_match_start]; auto).
      + forward_if [temp _t'3 (Vint (Int.repr 1)); temp _chain_length (Vint (Int.repr (u32 (ach - 1))))].
        { forward. forward. forward. entailer!. rewrite ?eq_repr_u32_0, ?Ez, ?repr_u32. auto. }
        { dead. }
        forward_if.
        { forward. Exists (mkLM c' (u32 (ach - 1)) ab ae1 ae (set_d_match_start s ms)) ms.
          pose proof (u32_range (ach - 1)). entailer!. cbn [lm_cur lm_chain]. split; rep_lia. }
        { dead. }
    - forward_if [temp _t'3 (Vint (Int.repr 0))].
      { dead. }
      { forward. entailer!. }
      forward_if.
      { dead. }
      forward. cbn in H2. inversion H2; subst bf sf.
      entailer!; try (cbn [d_match_start set_d_match_start]; auto). }
  (* after the loop *)
  Intros. inversion H0; subst r; clear H0.
  remember (d_match_start sf) as ms. subst sf.
  assert (Hrg : dstate_ranges (set_d_match_start s ms)) by (apply ranges_set_ms; auto).
  forward. forward_if.
  { forward. lm_fold_post s ms FR3 FR2 FR. entailer!. unfold vi. dcmp. reflexivity. }
  forward. forward. lm_fold_post s ms FR3 FR2 FR. entailer!. unfold vi. dcmp. reflexivity.
Qed.
