(* Polynomials over GF(2) modulo the CRC-32 polynomial P, in zlib's reflected representation: a 32-bit
   value a stands for the polynomial whose coefficient of x^j is bit 31 - j of a.  Multiplying by x is
   one step of the CRC register update with a zero bit (crc_step), so a(x) * b(x) mod P is the xor of
   crc_step^j b over the coefficients j of a: gf_mul, which is what crc32.c's multmodp computes.

   The facts, for 32-bit values:
   - gf_mul is linear in each argument (xor), crc_step is linear;
   - gf_mul P' b = crc_step^32 b, where P' = 0xedb88320 = x^32 mod P (checked on the 32 unit vectors);
   - gf_mul (crc_step c) b = crc_step (gf_mul c b);
   - rep a N (a represents crc_step^N: gf_mul a b = crc_step^N b for every b): 1 (bit 31) represents
     crc_step^0, and rep a N -> rep c M -> rep (gf_mul a c) (N + M);
   - the constant table x2n_table: entry k represents crc_step^(2^k) (x^(2^k) mod P), and the square of
     entry 31 is entry 0 (x^(2^32) = x mod P), so entry (k mod 32) represents crc_step^(2^k) for every k.
   Hence x2nmodp(n, k) represents crc_step^(n * 2^k) (X2n.v). *)
Require Import VST.floyd.proofauto.
Require Export Zlib.proof.crc32.IntFacts.
Require Import Coq.btauto.Btauto.

Fixpoint xsum (n: nat) (f: nat -> Z) : Z :=
  match n with O => 0 | S k => Z.lxor (xsum k f) (f k) end.

Definition gf_term (a b: Z) (j: nat) : Z :=
  if Z.testbit a (31 - Z.of_nat j) then Nat.iter j crc_step b else 0.

Definition gf_mul (a b: Z) : Z := xsum 32 (gf_term a b).

Definition is32 (x: Z) : Prop := 0 <= x < 2 ^ 32.

(* ---------------------------------------------------------------------- *)
(* xor sums                                                                *)
(* ---------------------------------------------------------------------- *)

Lemma xsum_ext n f g: (forall j, (j < n)%nat -> f j = g j) -> xsum n f = xsum n g.
Proof.
  induction n; intros H; simpl; auto. rewrite IHn by (intros; apply H; lia). rewrite H by lia. auto.
Qed.

Lemma xsum_lxor n f g: xsum n (fun j => Z.lxor (f j) (g j)) = Z.lxor (xsum n f) (xsum n g).
Proof.
  induction n; simpl; auto. rewrite IHn.
  apply Z.bits_inj'. intros i Hi. rewrite !Z.lxor_spec. btauto.
Qed.

Lemma xsum_zero n f: (forall j, (j < n)%nat -> f j = 0) -> xsum n f = 0.
Proof.
  induction n; intros H; simpl; auto. rewrite IHn by (intros; apply H; lia). rewrite H by lia. auto.
Qed.

Lemma xsum_map (h: Z -> Z) n f: (forall x y, h (Z.lxor x y) = Z.lxor (h x) (h y)) -> h 0 = 0 ->
  h (xsum n f) = xsum n (fun j => h (f j)).
Proof. intros L Z0. induction n; simpl; auto. rewrite L, IHn. auto. Qed.

Lemma xsum_range n f: (forall j, (j < n)%nat -> is32 (f j)) -> is32 (xsum n f).
Proof.
  unfold is32. induction n; intros H; cbn [xsum]; [lia | ].
  apply lxor_lt_pow2; [lia | apply IHn; intros; apply H; lia | apply H; lia].
Qed.

Lemma xsum_last_zero n f: f n = 0 -> xsum (S n) f = xsum n f.
Proof. intros. simpl. rewrite H. apply Z.lxor_0_r. Qed.

(* Terms from m on are zero: the sum is the sum of the first m. *)
Lemma xsum_tail_zero n m f: (m <= n)%nat -> (forall j, (m <= j < n)%nat -> f j = 0) -> xsum n f = xsum m f.
Proof.
  induction n; intros Hm H.
  - assert (m = 0)%nat by lia. subst. auto.
  - destruct (Nat.eq_dec m (S n)); [subst; auto | ].
    rewrite xsum_last_zero by (apply H; lia). apply IHn; [lia | intros; apply H; lia].
Qed.

(* ---------------------------------------------------------------------- *)
(* the register step                                                       *)
(* ---------------------------------------------------------------------- *)

Lemma is32_crc_step x: is32 x -> is32 (crc_step x).
Proof. apply crc_step_range. Qed.

Lemma is32_iter k x: is32 x -> is32 (Nat.iter k crc_step x).
Proof. apply iter_crc_step_range. Qed.

Lemma iter_add k m x: Nat.iter (k + m) crc_step x = Nat.iter k crc_step (Nat.iter m crc_step x).
Proof. apply Nat.iter_add. Qed.

Lemma crc_step_iter k x: crc_step (Nat.iter k crc_step x) = Nat.iter (S k) crc_step x.
Proof. reflexivity. Qed.

Lemma crc_step_nonzero x: is32 x -> x <> 0 -> crc_step x <> 0.
Proof.
  unfold is32. intros [H0 H1] Hx. unfold crc_step.
  destruct (Z.odd x) eqn:O.
  - intros E. apply Z.lxor_eq in E.
    rewrite Z.shiftr_div_pow2 in E by lia. change (2 ^ 1) with 2 in E.
    assert (x / 2 < 2 ^ 31) by (apply Z.div_lt_upper_bound; lia).
    unfold CRC_POLY in E. lia.
  - intros E. rewrite Z.shiftr_div_pow2 in E by lia. change (2 ^ 1) with 2 in E.
    assert (x = 2 * (x / 2) + x mod 2) by (apply Z.div_mod; lia).
    rewrite Zmod_odd, O in H. lia.
Qed.

Lemma iter_nonzero k x: is32 x -> x <> 0 -> Nat.iter k crc_step x <> 0.
Proof.
  induction k; simpl; auto. intros. apply crc_step_nonzero; auto. apply is32_iter; auto.
Qed.

(* ---------------------------------------------------------------------- *)
(* gf_mul: linearity                                                       *)
(* ---------------------------------------------------------------------- *)

Lemma gf_mul_range a b: is32 b -> is32 (gf_mul a b).
Proof.
  intros. apply xsum_range. intros. unfold gf_term. destruct (Z.testbit _ _).
  - apply is32_iter; auto.
  - unfold is32; lia.
Qed.

Lemma gf_mul_lxor_r a b1 b2: gf_mul a (Z.lxor b1 b2) = Z.lxor (gf_mul a b1) (gf_mul a b2).
Proof.
  unfold gf_mul. rewrite <- xsum_lxor. apply xsum_ext. intros j _. unfold gf_term.
  destruct (Z.testbit _ _); [apply iter_crc_step_lxor | reflexivity].
Qed.

Lemma gf_mul_lxor_l a1 a2 b: gf_mul (Z.lxor a1 a2) b = Z.lxor (gf_mul a1 b) (gf_mul a2 b).
Proof.
  unfold gf_mul. rewrite <- xsum_lxor. apply xsum_ext. intros j _. unfold gf_term.
  rewrite Z.lxor_spec.
  destruct (Z.testbit a1 _), (Z.testbit a2 _); simpl;
    rewrite ?Z.lxor_0_r, ?Z.lxor_0_l, ?Z.lxor_nilpotent; auto.
Qed.

Lemma gf_mul_0_l b: gf_mul 0 b = 0.
Proof. unfold gf_mul. apply xsum_zero. intros. unfold gf_term. rewrite Z.testbit_0_l. auto. Qed.

Lemma gf_mul_0_r a: gf_mul a 0 = 0.
Proof.
  unfold gf_mul. apply xsum_zero. intros. unfold gf_term.
  destruct (Z.testbit _ _); auto. apply iter_crc_step_0.
Qed.

(* A single coefficient. *)
Lemma gf_mul_pow2 s b: (s < 32)%nat ->
  gf_mul (2 ^ Z.of_nat s) b = Nat.iter (31 - s) crc_step b.
Proof.
  intros Hs. unfold gf_mul.
  rewrite (xsum_tail_zero 32 (S (31 - s))) by (try lia; intros j Hj; unfold gf_term;
    rewrite Z.pow2_bits_false by lia; auto).
  cbn [xsum]. rewrite xsum_zero.
  - rewrite Z.lxor_0_l. unfold gf_term.
    replace (31 - Z.of_nat (31 - s)) with (Z.of_nat s) by lia.
    rewrite Z.pow2_bits_true by lia. auto.
  - intros j Hj. unfold gf_term. rewrite Z.pow2_bits_false by lia. auto.
Qed.

(* ---------------------------------------------------------------------- *)
(* linear functions are determined by the unit vectors                     *)
(* ---------------------------------------------------------------------- *)

Lemma testbit_xsum_bits b n i: 0 <= i ->
  Z.testbit (xsum n (fun t => if Z.testbit b (Z.of_nat t) then 2 ^ Z.of_nat t else 0)) i =
  (Z.testbit b i && (i <? Z.of_nat n))%bool.
Proof.
  intros Hi. induction n; cbn [xsum].
  - rewrite Z.testbit_0_l. replace (i <? Z.of_nat 0) with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite andb_false_r. auto.
  - rewrite Z.lxor_spec, IHn. rewrite Nat2Z.inj_succ.
    destruct (Z.eq_dec i (Z.of_nat n)) as [E|E].
    + subst i. rewrite Z.ltb_irrefl, andb_false_r, xorb_false_l.
      replace (Z.of_nat n <? Z.succ (Z.of_nat n)) with true by (symmetry; apply Z.ltb_lt; lia).
      rewrite andb_true_r.
      destruct (Z.testbit b (Z.of_nat n)); [apply Z.pow2_bits_true; lia | apply Z.testbit_0_l].
    + replace (Z.testbit (if Z.testbit b (Z.of_nat n) then 2 ^ Z.of_nat n else 0) i) with false
        by (destruct (Z.testbit b (Z.of_nat n)); [symmetry; apply Z.pow2_bits_false; lia | rewrite Z.testbit_0_l; auto]).
      rewrite xorb_false_r. f_equal.
      destruct (Z.ltb_spec i (Z.of_nat n)), (Z.ltb_spec i (Z.succ (Z.of_nat n))); auto; lia.
Qed.

Lemma bits_decomp b: is32 b -> b = xsum 32 (fun t => if Z.testbit b (Z.of_nat t) then 2 ^ Z.of_nat t else 0).
Proof.
  unfold is32. intros Hb. apply Z.bits_inj'. intros i Hi. rewrite testbit_xsum_bits by auto.
  destruct (Z.ltb_spec i (Z.of_nat 32)); [rewrite andb_true_r; auto | ].
  rewrite andb_false_r. apply Z.bits_above_log2; [lia | ].
  destruct (Z.eq_dec b 0); [subst; simpl; lia | ].
  apply (Z.lt_le_trans _ 32); [apply Z.log2_lt_pow2; lia | simpl in *; lia].
Qed.

Definition xlinear (f: Z -> Z) : Prop := (forall x y, f (Z.lxor x y) = Z.lxor (f x) (f y)) /\ f 0 = 0.

Lemma xlinear_unit f g: xlinear f -> xlinear g ->
  (forall t, (t < 32)%nat -> f (2 ^ Z.of_nat t) = g (2 ^ Z.of_nat t)) ->
  forall b, is32 b -> f b = g b.
Proof.
  intros [Lf Zf] [Lg Zg] U b Hb. rewrite (bits_decomp b Hb).
  rewrite (xsum_map f), (xsum_map g) by auto.
  apply xsum_ext. intros j Hj. destruct (Z.testbit b (Z.of_nat j)); auto. rewrite Zf, Zg. auto.
Qed.

Lemma xlinear_iter k: xlinear (Nat.iter k crc_step).
Proof. split; [apply iter_crc_step_lxor | apply iter_crc_step_0]. Qed.

Lemma xlinear_gf_mul_r a: xlinear (gf_mul a).
Proof. split; [apply gf_mul_lxor_r | apply gf_mul_0_r]. Qed.

(* ---------------------------------------------------------------------- *)
(* x^32 = P' and the step law                                              *)
(* ---------------------------------------------------------------------- *)

Lemma gf_mul_poly_units: forall t, (t < 32)%nat ->
  gf_mul CRC_POLY (2 ^ Z.of_nat t) = Nat.iter 32 crc_step (2 ^ Z.of_nat t).
Proof.
  intros t Ht.
  do 32 (destruct t as [|t]; [vm_compute; reflexivity | ]). lia.
Qed.

Lemma gf_mul_poly b: is32 b -> gf_mul CRC_POLY b = Nat.iter 32 crc_step b.
Proof.
  apply xlinear_unit; [apply xlinear_gf_mul_r | apply xlinear_iter | apply gf_mul_poly_units].
Qed.

Lemma crc_step_pow2 s: (0 < s < 32)%nat -> crc_step (2 ^ Z.of_nat s) = 2 ^ Z.of_nat (s - 1).
Proof.
  intros Hs. rewrite crc_step_even.
  - rewrite Z.shiftr_div_pow2 by lia. rewrite <- Z.pow_sub_r by lia. f_equal. lia.
  - replace (Z.of_nat s) with (Z.succ (Z.of_nat (s - 1))) by lia.
    rewrite Z.pow_succ_r by lia. rewrite Z.odd_mul. auto.
Qed.

Lemma gf_mul_step_l c b: is32 c -> is32 b -> gf_mul (crc_step c) b = crc_step (gf_mul c b).
Proof.
  intros Hc Hb. revert c Hc.
  apply (xlinear_unit (fun c => gf_mul (crc_step c) b) (fun c => crc_step (gf_mul c b))).
  - split; [intros; rewrite crc_step_lxor, gf_mul_lxor_l; auto | rewrite crc_step_0, gf_mul_0_l; auto].
  - split; [intros; rewrite gf_mul_lxor_l, crc_step_lxor; auto | rewrite gf_mul_0_l; auto].
  - intros t Ht. destruct t as [|t].
    + change (2 ^ Z.of_nat 0) with 1. replace (crc_step 1) with CRC_POLY by reflexivity.
      rewrite gf_mul_poly by auto. rewrite (gf_mul_pow2 0) by lia.
      rewrite Nat.sub_0_r, crc_step_iter. reflexivity.
    + rewrite crc_step_pow2 by lia. rewrite !gf_mul_pow2 by lia.
      rewrite crc_step_iter. f_equal. lia.
Qed.

(* ---------------------------------------------------------------------- *)
(* representation of powers of the step                                   *)
(* ---------------------------------------------------------------------- *)

Definition rep (a: Z) (N: nat) : Prop :=
  is32 a /\ forall b, is32 b -> gf_mul a b = Nat.iter N crc_step b.

Lemma rep_one: rep (2 ^ 31) 0.
Proof.
  split; [unfold is32; lia | ]. intros b Hb.
  change (2 ^ 31) with (2 ^ Z.of_nat 31). rewrite gf_mul_pow2 by lia. reflexivity.
Qed.

Lemma rep_step c M: rep c M -> rep (crc_step c) (S M).
Proof.
  intros [Hc R]. split; [apply is32_crc_step; auto | ]. intros b Hb.
  rewrite gf_mul_step_l by auto. rewrite R by auto. reflexivity.
Qed.

Lemma rep_iter c M N: rep c M -> rep (Nat.iter N crc_step c) (N + M).
Proof.
  induction N; simpl; auto. intros. apply rep_step. auto.
Qed.

Lemma rep_mul a N c M: rep a N -> rep c M -> rep (gf_mul a c) (N + M).
Proof.
  intros [Ha Ra] Rc. rewrite Ra by (apply Rc). apply rep_iter. auto.
Qed.

Lemma rep_nonzero a N: rep a N -> a <> 0.
Proof.
  intros [Ha R] E. subst a. specialize (R 1 ltac:(unfold is32; lia)).
  rewrite gf_mul_0_l in R. symmetry in R. revert R. apply iter_nonzero; unfold is32; lia.
Qed.
