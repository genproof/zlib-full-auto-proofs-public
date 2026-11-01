(* Law inflate_check, theory part: the kit (IKTheoryDefs.ik_kit): the bit buffer under the machine's primitives, little-endian values, the reference checks. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.inflate_check.IKTheoryDefs.
Require Import Zlib.proof.crc32.Combine.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* Little-endian values                                                                           *)

Lemma ikb_le_app l1 l2 : le_val (l1 ++ l2) = le_val l1 + 2 ^ (8 * Zlength l1) * le_val l2.
Proof.
  induction l1 as [|a l1 IH]; cbn [app le_val].
  - rewrite Zlength_nil. simpl. lia.
  - rewrite IH, Zlength_cons.
    replace (8 * Z.succ (Zlength l1)) with (8 + 8 * Zlength l1) by lia.
    rewrite Z.pow_add_r by (pose proof (Zlength_nonneg l1); lia). change (2 ^ 8) with 256. ring.
Qed.

Lemma ikb_le_range l : bytes_ok l -> 0 <= le_val l < 2 ^ (8 * Zlength l).
Proof.
  induction l as [|a l IH]; intros H; cbn [le_val].
  - rewrite Zlength_nil. simpl. lia.
  - inversion H as [|? ? Ha Hl]; subst. specialize (IH Hl). rewrite Zlength_cons.
    replace (8 * Z.succ (Zlength l)) with (8 + 8 * Zlength l) by lia.
    rewrite Z.pow_add_r by (pose proof (Zlength_nonneg l); lia). change (2 ^ 8) with 256.
    change Byte.max_unsigned with 255 in Ha. lia.
Qed.

Lemma ikb_le32 l : Zlength l = 4 -> le_val l = le32 l.
Proof.
  intros H. destruct l as [|a [|b [|c [|d [|e l]]]]];
    rewrite ?Zlength_cons, ?Zlength_nil in H;
    try (match goal with t: list Z |- _ => pose proof (Zlength_nonneg t) end); try lia.
  unfold le32. cbn [le_val]. unfold Znth; cbn -[Z.pow]. ring.
Qed.

Fixpoint ikb_zup (n: nat) (z: Z) : list Z := match n with O => [] | S n' => z :: ikb_zup n' (z + 1) end.

Lemma ikb_in_zup n : forall z x, z <= x < z + Z.of_nat n -> In x (ikb_zup n z).
Proof.
  induction n as [|n IH]; intros z x H; [lia|]. cbn [ikb_zup].
  destruct (Z.eq_dec x z) as [E|E]; [left; auto|right; apply IH; lia].
Qed.

Lemma ikb_ff00_tab : forallb (fun v => Z.land v 65280 =? v / 256 * 256) (ikb_zup (Z.to_nat 65536) 0) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma ikb_ff00 y : Z.land y 65280 = (y mod 65536) / 256 * 256.
Proof.
  change 65280 with (Z.land (Z.ones 16) 65280) at 1. rewrite Z.land_assoc, Z.land_ones by lia.
  change (2 ^ 16) with 65536.
  pose proof ikb_ff00_tab as T. rewrite forallb_forall in T.
  assert (R : 0 <= y mod 65536 < 65536) by (apply Z.mod_pos_bound; lia).
  assert (I : In (y mod 65536) (ikb_zup (Z.to_nat 65536) 0))
    by (apply ikb_in_zup; change (Z.of_nat (Z.to_nat 65536)) with 65536; lia).
  specialize (T _ I). apply Z.eqb_eq in T. exact T.
Qed.

Lemma ikb_swap b0 b1 b2 b3 :
  0 <= b0 <= 255 -> 0 <= b1 <= 255 -> 0 <= b2 <= 255 -> 0 <= b3 <= 255 ->
  swap32 (b0 + 256 * (b1 + 256 * (b2 + 256 * (b3 + 256 * 0)))) = b0 * 2 ^ 24 + b1 * 2 ^ 16 + b2 * 2 ^ 8 + b3.
Proof.
  intros H0 H1 H2 H3. unfold swap32.
  rewrite !Z.shiftr_div_pow2, !Z.shiftl_mul_pow2 by lia. rewrite !ikb_ff00.
  change (2 ^ 24) with 16777216. change (2 ^ 16) with 65536. change (2 ^ 8) with 256.
  set (x := b0 + 256 * (b1 + 256 * (b2 + 256 * (b3 + 256 * 0)))).
  assert (E1 : x / 16777216 = b3)
    by (symmetry; apply Z.div_unique with (r := b0 + 256 * b1 + 65536 * b2); [left|]; unfold x; lia).
  assert (E2 : x / 256 = b1 + 256 * b2 + 65536 * b3)
    by (symmetry; apply Z.div_unique with (r := b0); [left|]; unfold x; lia).
  assert (E3 : x mod 65536 = b0 + 256 * b1)
    by (symmetry; apply Z.mod_unique with (q := b2 + 256 * b3); [left|]; unfold x; lia).
  assert (E4 : x mod 256 = b0)
    by (symmetry; apply Z.mod_unique with (q := b1 + 256 * (b2 + 256 * b3)); [left|]; unfold x; lia).
  rewrite E1, E2, E3, E4. clear E1 E2 E3 E4 x.
  assert (E5 : (b1 + 256 * b2 + 65536 * b3) mod 65536 = b1 + 256 * b2)
    by (symmetry; apply Z.mod_unique with (q := b3); [left|]; lia).
  assert (E6 : (b1 + 256 * b2) / 256 = b2) by (symmetry; apply Z.div_unique with (r := b1); [left|]; lia).
  assert (E7 : (b0 + 256 * b1) / 256 = b1) by (symmetry; apply Z.div_unique with (r := b0); [left|]; lia).
  rewrite E5, E6, E7. rewrite (Z.mod_small b3 256) by lia. lia.
Qed.

Lemma ikb_swap32 l : bytes_ok l -> Zlength l = 4 -> swap32 (le_val l) = be32 l.
Proof.
  intros Hb H. destruct l as [|a [|b [|c [|d [|e l]]]]];
    rewrite ?Zlength_cons, ?Zlength_nil in H;
    try (match goal with t: list Z |- _ => pose proof (Zlength_nonneg t) end); try lia.
  unfold be32. cbn [le_val].
  inversion Hb as [|? ? Ha Hb1]; subst. inversion Hb1 as [|? ? Hb' Hb2]; subst.
  inversion Hb2 as [|? ? Hc Hb3]; subst. inversion Hb3 as [|? ? Hd Hb4]; subst.
  change Byte.max_unsigned with 255 in *.
  rewrite ikb_swap by lia. unfold Znth; cbn -[Z.pow]. ring.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The bit buffer as values                                                                       *)

Lemma ikb_byte src i : bytes_ok src -> 0 <= i < Zlength src -> 0 <= Znth i src <= 255.
Proof.
  intros Hb Hi. unfold bytes_ok in Hb. rewrite Forall_forall in Hb.
  apply (Hb (Znth i src)), Znth_In; auto.
Qed.

Lemma ikb_prefix_range src P : bytes_ok src -> 0 <= P <= Zlength src ->
  0 <= le_val (sublist 0 P src) < 2 ^ (8 * P).
Proof.
  intros Hb HP.
  assert (B : bytes_ok (sublist 0 P src)) by (unfold bytes_ok in *; apply Forall_sublist; exact Hb).
  pose proof (ikb_le_range _ B) as R. rewrite Zlength_sublist in R by lia.
  replace (P - 0) with P in R by lia. exact R.
Qed.

Lemma ikb_split src Q P : 0 <= Q <= P -> P <= Zlength src ->
  le_val (sublist 0 P src) = le_val (sublist 0 Q src) + 2 ^ (8 * Q) * le_val (sublist Q P src).
Proof.
  intros H1 H2. rewrite (sublist_split 0 Q P) by lia. rewrite ikb_le_app, Zlength_sublist by lia.
  f_equal. f_equal. f_equal. lia.
Qed.

Lemma ikb_shiftr_add a c k s : 0 <= s <= k -> Z.shiftr (a + c * 2 ^ k) s = Z.shiftr a s + c * 2 ^ (k - s).
Proof.
  intros H. rewrite !Z.shiftr_div_pow2 by lia.
  replace (a + c * 2 ^ k) with (a + (c * 2 ^ (k - s)) * 2 ^ s).
  - rewrite Z.div_add by (apply Z.pow_nonzero; lia). reflexivity.
  - rewrite <- Z.mul_assoc, <- Z.pow_add_r by lia. f_equal. f_equal. f_equal. lia.
Qed.

Lemma ikb_shr_lt L K s : 0 <= L < 2 ^ K -> 0 <= s <= K -> 0 <= Z.shiftr L s < 2 ^ (K - s).
Proof.
  intros HL Hs. rewrite Z.shiftr_div_pow2 by lia. split.
  - apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia].
  - apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia|].
    rewrite <- Z.pow_add_r by lia. replace (s + (K - s)) with K by lia. lia.
Qed.

Lemma ikb_bb_range src P hold bits : bytes_ok src -> 0 <= P <= Zlength src ->
  ik_bitbuf src P hold bits -> 0 <= hold < 2 ^ bits.
Proof.
  intros Hb HP [Hbits ->].
  pose proof (ikb_shr_lt _ (8 * P) (8 * P - bits) (ikb_prefix_range src P Hb HP) ltac:(lia)) as R.
  replace (8 * P - (8 * P - bits)) with bits in R by lia. exact R.
Qed.

Lemma ikb_bb_init src P : bytes_ok src -> 0 <= P <= Zlength src -> ik_bitbuf src P 0 0.
Proof.
  intros Hb HP. split; [lia|]. rewrite Z.sub_0_r, Z.shiftr_div_pow2 by lia.
  rewrite Z.div_small; auto. apply ikb_prefix_range; auto.
Qed.

Lemma ikb_bb_pull src P hold bits : bytes_ok src -> 0 <= P < Zlength src -> bits <= 56 ->
  ik_bitbuf src P hold bits ->
  ik_bitbuf src (P + 1) (u64 (hold + Znth P src * 2 ^ bits)) (u32 (bits + 8)) /\
  u64 (hold + Znth P src * 2 ^ bits) = hold + Znth P src * 2 ^ bits /\ u32 (bits + 8) = bits + 8.
Proof.
  intros Hb HP H56 Hbb.
  pose proof (ikb_bb_range src P hold bits Hb ltac:(lia) Hbb) as Hr.
  destruct Hbb as [Hbits Hh].
  pose proof (ikb_byte src P Hb HP) as Hy.
  assert (E32 : u32 (bits + 8) = bits + 8) by (unfold u32; apply Z.mod_small; lia).
  assert (Hp : 0 < 2 ^ bits) by (apply Z.pow_pos_nonneg; lia).
  assert (E64 : u64 (hold + Znth P src * 2 ^ bits) = hold + Znth P src * 2 ^ bits).
  { unfold u64. apply Z.mod_small. split; [nia|].
    assert (2 ^ (bits + 8) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
    rewrite Z.pow_add_r in H by lia. change (2 ^ 8) with 256 in H. nia. }
  rewrite E32, E64. split; [|auto]. split; [lia|].
  rewrite (ikb_split src P (P + 1)) by lia. rewrite (sublist_one P (P + 1)) by lia. cbn [le_val].
  rewrite Z.mul_0_r, Z.add_0_r, (Z.mul_comm (2 ^ (8 * P))).
  replace (8 * (P + 1) - (bits + 8)) with (8 * P - bits) by lia.
  rewrite ikb_shiftr_add by lia. rewrite Hh. f_equal. f_equal. f_equal. lia.
Qed.

Lemma ikb_bb_drop src P hold bits n : 0 <= n <= bits ->
  ik_bitbuf src P hold bits -> ik_bitbuf src P (Z.shiftr hold n) (bits - n).
Proof.
  intros Hn [Hbits ->]. split; [lia|]. rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed.

Lemma ikb_bb_bytebits src P hold bits : ik_bitbuf src P hold bits ->
  ik_bitbuf src P (Z.shiftr hold (bits mod 8)) (bits - bits mod 8).
Proof.
  intros H. pose proof H as [Hbits _]. apply ikb_bb_drop; auto.
  pose proof (Z.mod_pos_bound bits 8 ltac:(lia)). split; [lia|]. apply Z.mod_le; lia.
Qed.

Lemma ikb_bb_giveback src P hold bits k : bytes_ok src -> 0 <= P <= Zlength src -> 0 <= k -> 8 * k <= bits ->
  ik_bitbuf src P hold bits -> ik_bitbuf src (P - k) (hold mod 2 ^ (bits - 8 * k)) (bits - 8 * k).
Proof.
  intros Hb HP Hk Hkb [Hbits ->]. split; [lia|].
  rewrite (ikb_split src (P - k) P) by lia.
  rewrite (Z.mul_comm (2 ^ _)), ikb_shiftr_add by lia.
  replace (8 * (P - k) - (8 * P - bits)) with (bits - 8 * k) by lia.
  rewrite Z.mod_add by (apply Z.pow_nonzero; lia).
  replace (8 * (P - k) - (bits - 8 * k)) with (8 * P - bits) by lia.
  apply Z.mod_small.
  pose proof (ikb_shr_lt _ (8 * (P - k)) (8 * P - bits) (ikb_prefix_range src (P - k) Hb ltac:(lia)) ltac:(lia)) as R.
  replace (8 * (P - k) - (8 * P - bits)) with (bits - 8 * k) in R by lia. exact R.
Qed.

Lemma ikb_bb_bytes src P hold k : bytes_ok src -> 0 <= P <= Zlength src -> 0 <= k ->
  ik_bitbuf src P hold (8 * k) -> hold = le_val (sublist (P - k) P src).
Proof.
  intros Hb HP Hk [Hbits ->].
  rewrite (ikb_split src (P - k) P) by lia.
  rewrite (Z.mul_comm (2 ^ _)), ikb_shiftr_add by lia.
  replace (8 * (P - k) - (8 * P - 8 * k)) with 0 by lia.
  rewrite Z.shiftr_div_pow2 by lia. replace (8 * P - 8 * k) with (8 * (P - k)) by lia.
  rewrite Z.div_small by (apply ikb_prefix_range; auto; lia). simpl. lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The machine's primitives                                                                       *)

Lemma ikb_same_refl m : ik_same_but_buf m m.
Proof. repeat split; reflexivity. Qed.

Lemma ikb_same_trans a b c : ik_same_but_buf a b -> ik_same_but_buf b c -> ik_same_but_buf a c.
Proof.
  intros (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14)
         (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12 & B13 & B14).
  repeat split; congruence.
Qed.

Lemma ikb_same_pull m : ik_same_but_buf m (pull m).
Proof. repeat split; reflexivity. Qed.

Lemma ikb_same_leave m : ik_same_but_buf m (set_leave m).
Proof. repeat split; reflexivity. Qed.

Lemma ikb_pull src pos inp m : ctx_ok src pos inp -> m_inp m = inp -> 0 <= m_nx m < Zlength inp ->
    m_bits m <= 56 -> ik_bitbuf src (pos + m_nx m) (m_hold m) (m_bits m) ->
    ik_bitbuf src (pos + m_nx (pull m)) (m_hold (pull m)) (m_bits (pull m)) /\
    m_nx (pull m) = m_nx m + 1 /\ m_bits (pull m) = m_bits m + 8 /\ m_leave (pull m) = m_leave m /\
    ik_same_but_buf m (pull m).
Proof.
  intros (Hpos & Hlen & Hb & Hk) Hi Hn H56 Hbb.
  assert (Eb : Znth (m_nx m) (m_inp m) = Znth (pos + m_nx m) src) by (rewrite Hi; apply Hk; lia).
  destruct (ikb_bb_pull src (pos + m_nx m) (m_hold m) (m_bits m) Hb ltac:(lia) H56 Hbb) as (B & E64 & E32).
  pose proof (ikb_same_pull m) as S.
  unfold pull in *; cbn [m_nx m_hold m_bits m_leave set_m_bits set_m_hold set_m_nx]. rewrite Eb in *.
  replace (pos + (m_nx m + 1)) with (pos + m_nx m + 1) by lia.
  split; [exact B|]. split; [reflexivity|]. split; [exact E32|]. split; [reflexivity|]. exact S.
Qed.

Lemma ikb_nb_S k n m : needbits_f (S k) n m =
  if m_bits m <? n then if m_have m =? 0 then set_leave m else needbits_f k n (pull m) else m.
Proof. reflexivity. Qed.

Lemma ikb_needbits_f src pos inp n : forall k m, ctx_ok src pos inp -> m_inp m = inp ->
    0 <= m_nx m <= Zlength inp -> 0 <= n <= 32 -> n <= m_bits m + 8 * Z.of_nat k ->
    ik_bitbuf src (pos + m_nx m) (m_hold m) (m_bits m) ->
    ik_bitbuf src (pos + m_nx (needbits_f k n m)) (m_hold (needbits_f k n m)) (m_bits (needbits_f k n m)) /\
    ik_same_but_buf m (needbits_f k n m) /\
    m_nx m <= m_nx (needbits_f k n m) <= Zlength inp /\
    m_bits (needbits_f k n m) - m_bits m = 8 * (m_nx (needbits_f k n m) - m_nx m) /\
    (m_bits m < n -> m_bits (needbits_f k n m) < n + 8) /\ (n <= m_bits m -> needbits_f k n m = m) /\
    ((m_leave (needbits_f k n m) = 1 /\ m_nx (needbits_f k n m) = Zlength inp /\ m_bits (needbits_f k n m) < n) \/
     (m_leave (needbits_f k n m) = m_leave m /\ n <= m_bits (needbits_f k n m))).
Proof.
  induction k as [|k IH]; intros m Hc Hi Hn Hn32 Hf Hbb.
  - cbn [needbits_f]. assert (n <= m_bits m) by lia.
    split; [exact Hbb|]. split; [apply ikb_same_refl|]. split; [lia|]. split; [lia|].
    split; [intros; lia|]. split; [reflexivity|]. right. split; [reflexivity|lia].
  - rewrite ikb_nb_S. destruct (m_bits m <? n) eqn:E1; [apply Z.ltb_lt in E1 | apply Z.ltb_ge in E1].
    + destruct (m_have m =? 0) eqn:E2; [apply Z.eqb_eq in E2 | apply Z.eqb_neq in E2]; unfold m_have in E2.
      * pose proof (ikb_same_leave m) as S.
        rewrite Hi in E2. unfold set_leave in *. cbn [set_m_leave m_nx m_hold m_bits m_leave].
        split; [exact Hbb|]. split; [exact S|]. split; [lia|]. split; [lia|].
        split; [intros; lia|]. split; [intros; lia|]. left. split; [reflexivity|]. split; lia.
      * rewrite Hi in E2.
        destruct (ikb_pull src pos inp m Hc Hi ltac:(lia) ltac:(lia) Hbb) as (P1 & P2 & P3 & P4 & P5).
        destruct (IH (pull m) Hc ltac:(exact Hi) ltac:(lia) Hn32 ltac:(lia) P1)
          as (A1 & A2 & A3 & A4 & A5 & A6 & A7).
        set (m2 := needbits_f k n (pull m)) in *. clearbody m2.
        rewrite P2 in A3, A4. rewrite P3 in A4, A5, A6. rewrite P4 in A7.
        split; [exact A1|]. split; [exact (ikb_same_trans _ _ _ P5 A2)|]. split; [lia|]. split; [lia|].
        split.
        { intros _. destruct (Z_lt_le_dec (m_bits m + 8) n) as [L|L]; [apply A5; lia|].
          rewrite (A6 L), P3. lia. }
        split; [intros; lia|]. exact A7.
    + split; [exact Hbb|]. split; [apply ikb_same_refl|]. split; [lia|]. split; [lia|].
      split; [intros; lia|]. split; [reflexivity|]. right. split; [reflexivity|lia].
Qed.

Lemma ikb_needbits src pos inp n m : ctx_ok src pos inp -> m_inp m = inp -> 0 <= m_nx m <= Zlength inp ->
    0 <= n <= 32 -> 0 <= m_bits m <= 32 -> ik_bitbuf src (pos + m_nx m) (m_hold m) (m_bits m) ->
    let m' := needbits n m in
    ik_bitbuf src (pos + m_nx m') (m_hold m') (m_bits m') /\ ik_same_but_buf m m' /\
    m_nx m <= m_nx m' <= Zlength inp /\ m_bits m' - m_bits m = 8 * (m_nx m' - m_nx m) /\
    (m_bits m < n -> m_bits m' < n + 8) /\ (n <= m_bits m -> m' = m) /\
    ((m_leave m' = 1 /\ m_nx m' = Zlength inp /\ m_bits m' < n) \/ (m_leave m' = m_leave m /\ n <= m_bits m')).
Proof.
  intros Hc Hi Hn Hn32 Hb Hbb. unfold needbits.
  apply (ikb_needbits_f src pos inp n 4 m Hc Hi Hn Hn32); [simpl; lia | exact Hbb].
Qed.

(* the lookups: pull while the entry needs more bits *)
Ltac ikb_lookup_tac IH src pos inp :=
  intros m here m' ok Hc Hi Hn Hb0 Hf Hbb Heq;
  repeat (match type of Heq with context [if ?c then _ else _] =>
            let E := fresh "E" in destruct c eqn:E end);
  match type of Heq with
  | (_, _, _) = (_, _, _) =>
      inversion Heq; subst;
      first
        [ (* set_leave *)
          pose proof (ikb_same_leave m) as S; unfold set_leave in *;
          cbn [set_m_leave m_nx m_hold m_bits m_leave];
          match goal with E: (m_have m =? 0) = true |- _ => apply Z.eqb_eq in E; unfold m_have in E end;
          split; [exact Hbb|]; split; [exact S|]; split; [lia|]; split; [lia|];
          split; [intros; discriminate|]; intros; reflexivity
        | split; [exact Hbb|]; split; [apply ikb_same_refl|]; split; [lia|]; split; [lia|];
          split; [intros; reflexivity|]; intros; discriminate ]
  | _ = (_, _, _) =>
      match goal with E: (m_have m =? 0) = false |- _ => apply Z.eqb_neq in E; unfold m_have in E end;
      rewrite Hi in *;
      destruct (ikb_pull src pos inp m Hc Hi ltac:(lia) ltac:(lia) Hbb) as (P1 & P2 & P3 & P4 & P5);
      destruct (IH (pull m) here m' ok Hc ltac:(exact Hi) ltac:(lia) ltac:(lia) ltac:(lia) P1 Heq)
        as (A1 & A2 & A3 & A4 & A5 & A6);
      rewrite P2 in A3, A4; rewrite P3 in A4; rewrite P4 in A5;
      split; [exact A1|]; split; [exact (ikb_same_trans _ _ _ P5 A2)|]; split; [lia|]; split; [lia|];
      split; [exact A5|exact A6]
  end.

Lemma ikb_lookup1_f src pos inp fx dx t nb : forall k m here m' ok, ctx_ok src pos inp -> m_inp m = inp ->
    0 <= m_nx m <= Zlength inp -> 0 <= m_bits m -> m_bits m + 8 * Z.of_nat k <= 64 ->
    ik_bitbuf src (pos + m_nx m) (m_hold m) (m_bits m) ->
    lookup1_f k fx dx t nb m = (here, m', ok) ->
    ik_bitbuf src (pos + m_nx m') (m_hold m') (m_bits m') /\ ik_same_but_buf m m' /\
    m_nx m <= m_nx m' <= Zlength inp /\ m_bits m' - m_bits m = 8 * (m_nx m' - m_nx m) /\
    (ok = true -> m_leave m' = m_leave m) /\ (ok = false -> m_leave m' = 1).
Proof.
  induction k as [|k IH].
  - intros m here m' ok Hc Hi Hn Hb0 Hf Hbb Heq. cbn [lookup1_f] in Heq. inversion Heq; subst.
    split; [exact Hbb|]. split; [apply ikb_same_refl|]. split; [lia|]. split; [lia|].
    split; [intros; reflexivity|]. intros; discriminate.
  - cbn [lookup1_f]. ikb_lookup_tac IH src pos inp.
Qed.

Lemma ikb_lookup2_f src pos inp fx dx t last : forall k m here m' ok, ctx_ok src pos inp -> m_inp m = inp ->
    0 <= m_nx m <= Zlength inp -> 0 <= m_bits m -> m_bits m + 8 * Z.of_nat k <= 64 ->
    ik_bitbuf src (pos + m_nx m) (m_hold m) (m_bits m) ->
    lookup2_f k fx dx t last m = (here, m', ok) ->
    ik_bitbuf src (pos + m_nx m') (m_hold m') (m_bits m') /\ ik_same_but_buf m m' /\
    m_nx m <= m_nx m' <= Zlength inp /\ m_bits m' - m_bits m = 8 * (m_nx m' - m_nx m) /\
    (ok = true -> m_leave m' = m_leave m) /\ (ok = false -> m_leave m' = 1).
Proof.
  induction k as [|k IH].
  - intros m here m' ok Hc Hi Hn Hb0 Hf Hbb Heq. cbn [lookup2_f] in Heq. inversion Heq; subst.
    split; [exact Hbb|]. split; [apply ikb_same_refl|]. split; [lia|]. split; [lia|].
    split; [intros; reflexivity|]. intros; discriminate.
  - cbn [lookup2_f]. ikb_lookup_tac IH src pos inp.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The reference checks                                                                           *)

Lemma ikb_adler_valid1 : adler_valid 1.
Proof. unfold adler_valid, adler_lo, adler_hi, ADLER_BASE. split; [lia|]. split; reflexivity. Qed.

Lemma ikb_adler_upd l d : bytes_ok l -> bytes_ok d -> adler32_z_val (ref_adler32 1 l) d = ref_adler32 1 (l ++ d).
Proof.
  intros _ _. rewrite adler32_z_val_ref by (apply ref_adler32_valid, ikb_adler_valid1).
  apply ref_adler32_app, ikb_adler_valid1.
Qed.

Lemma ikb_crc_upd l d : bytes_ok l -> bytes_ok d -> ref_crc32 (ref_crc32 0 l) d = ref_crc32 0 (l ++ d).
Proof. intros Hl _. apply ref_crc32_app. exact Hl. Qed.

Lemma ik_kit_proof : ik_kit.
Proof.
  constructor.
  - exact ikb_le_app.
  - exact ikb_le_range.
  - exact ikb_le32.
  - exact ikb_swap32.
  - exact ikb_bb_range.
  - exact ikb_bb_init.
  - exact ikb_bb_pull.
  - exact ikb_bb_drop.
  - exact ikb_bb_bytebits.
  - exact ikb_bb_giveback.
  - exact ikb_bb_bytes.
  - exact ikb_pull.
  - exact ikb_needbits.
  - intros src pos inp fx dx t nb m here m' ok Hc Hi Hn Hb Hbb Heq.
    apply (ikb_lookup1_f src pos inp fx dx t nb 3 m here m' ok); auto; simpl; lia.
  - intros src pos inp fx dx t last m here m' ok Hc Hi Hn Hb Hbb Heq.
    apply (ikb_lookup2_f src pos inp fx dx t last 3 m here m' ok); auto; simpl; lia.
  - exact ikb_adler_upd.
  - exact ikb_crc_upd.
  - reflexivity.
  - reflexivity.
Qed.
