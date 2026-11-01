(* Part of inflate_fast's decode theory (DecFastKit.v): the table walk decodes. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.rfc1951.DecFastKit.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* bits                                                                                           *)

Lemma dfw_testbit_1 : forall j, 0 <= j -> Z.testbit 1 j = (j =? 0).
Proof.
  intros j Hj. destruct (Z.eq_dec j 0) as [->|Hn]; [reflexivity|].
  rewrite (proj2 (Z.eqb_neq j 0) Hn).
  change 1 with (2 ^ 0). rewrite Z.pow2_bits_eqb by lia. apply Z.eqb_neq. lia.
Qed.

Lemma dfw_rl_bits : forall k i r c m, 0 <= m ->
  Z.testbit (ref.reverse_loop k i r c) m =
  if m <? Z.of_nat k then Z.testbit c (i + Z.of_nat k - 1 - m) else Z.testbit r (m - Z.of_nat k).
Proof.
  induction k; intros i r c m Hm; cbn [ref.reverse_loop].
  - change (Z.of_nat 0) with 0. destruct (m <? 0) eqn:E; [lia|]. f_equal; lia.
  - rewrite IHk by lia. rewrite Nat2Z.inj_succ.
    destruct (Z.lt_trichotomy m (Z.of_nat k)) as [Hl|[He|Hg]].
    + rewrite (proj2 (Z.ltb_lt _ _) Hl), (proj2 (Z.ltb_lt m (Z.succ (Z.of_nat k)))) by lia.
      f_equal; lia.
    + subst m. rewrite Z.ltb_irrefl, (proj2 (Z.ltb_lt _ _)) by lia.
      rewrite Z.sub_diag, Z.lor_spec, Z.shiftl_spec_low, Z.land_spec, Z.shiftr_spec by lia.
      simpl. rewrite andb_true_r. f_equal; lia.
    + rewrite (proj2 (Z.ltb_ge m (Z.of_nat k))), (proj2 (Z.ltb_ge m (Z.succ (Z.of_nat k)))) by lia.
      rewrite Z.lor_spec, Z.shiftl_spec_high, Z.land_spec, dfw_testbit_1 by lia.
      rewrite (proj2 (Z.eqb_neq _ 0)) by lia. rewrite andb_false_r, orb_false_r. f_equal; lia.
Qed.

Lemma dfw_rev_bits : forall c n m, 0 <= n -> 0 <= m ->
  Z.testbit (ref.reverse_bits c n) m = (m <? n) && Z.testbit c (n - 1 - m).
Proof.
  intros. unfold ref.reverse_bits. rewrite dfw_rl_bits by lia. rewrite Z2Nat.id by lia.
  destruct (m <? n); simpl. f_equal; lia. apply Z.testbit_0_l.
Qed.

Lemma dfw_bval_nonneg : forall bs, 0 <= bval bs.
Proof. induction bs as [|b r IH]; simpl; [lia|]. destruct b; simpl; lia. Qed.

Lemma dfw_bval_testbit : forall bs m, 0 <= m -> Z.testbit (bval bs) m = nth (Z.to_nat m) bs false.
Proof.
  induction bs as [|b r IH]; intros m Hm.
  - simpl. rewrite Z.testbit_0_l. destruct (Z.to_nat m); reflexivity.
  - simpl bval. destruct (Z.eq_dec m 0) as [->|Hn].
    + destruct b; simpl Z.b2z.
      * rewrite Z.add_comm. apply Z.testbit_odd_0.
      * rewrite Z.add_0_l. apply Z.testbit_even_0.
    + replace m with (Z.succ (m - 1)) by lia.
      rewrite Z2Nat.inj_succ by lia. simpl nth.
      rewrite <- IH by lia.
      destruct b; simpl Z.b2z.
      * rewrite Z.add_comm. apply Z.testbit_odd_succ. lia.
      * rewrite Z.add_0_l. apply Z.testbit_even_succ. lia.
Qed.

Lemma dfw_bval_app : forall a b, bval (a ++ b) = bval a + 2 ^ Zlength a * bval b.
Proof.
  induction a as [|x r IH]; intros b; simpl.
  - lia.
  - rewrite IH, Zlength_cons, Z.pow_succ_r by (apply Zlength_nonneg). ring.
Qed.

Lemma dfw_bits_le_len : forall v n, 0 <= n -> Zlength (bits_le v n) = n.
Proof.
  intros. unfold bits_le. rewrite Zlength_map, Zlength_correct, seq_length. lia.
Qed.

Lemma dfw_bval_msb : forall c n, 0 <= n -> bval (bits_msb c n) = ref.reverse_bits c n.
Proof.
  intros c n Hn. apply Z.bits_inj'. intros m Hm.
  rewrite dfw_bval_testbit, dfw_rev_bits by lia. unfold bits_msb.
  assert (Hl: length (bits_le c n) = Z.to_nat n).
  { unfold bits_le. rewrite map_length, seq_length. reflexivity. }
  destruct (m <? n) eqn:E.
  - apply Z.ltb_lt in E. rewrite rev_nth by lia. rewrite Hl.
    unfold bits_le.
    rewrite (nth_indep _ false (Z.testbit c (Z.of_nat 0))) by (rewrite map_length, seq_length; lia).
    rewrite (map_nth (fun i : nat => Z.testbit c (Z.of_nat i))), seq_nth by lia. simpl. f_equal. lia.
  - apply Z.ltb_ge in E. apply nth_overflow. rewrite rev_length, Hl. lia.
Qed.

Lemma dfw_bytes_bits_len : forall l, Zlength (bytes_bits l) = 8 * Zlength l.
Proof.
  induction l as [|b r IH]; unfold bytes_bits in *; cbn [flat_map].
  - reflexivity.
  - rewrite Zlength_app, IH, dfw_bits_le_len, Zlength_cons by lia. lia.
Qed.

(* the hold starts with the code of sy *)
Lemma dfw_hold_split : forall G c hold bits lens sy,
  hold_ok G c hold bits -> 0 <= Znth sy lens <= bits ->
  sublist (8 * c - bits) (8 * c - bits + Znth sy lens) (sbits G) = send_sym lens sy ->
  hold = Z.lor (ref.reverse_bits (code lens sy) (Znth sy lens))
               (Z.shiftl (bval (sublist (8 * c - bits + Znth sy lens) (8 * c) (sbits G))) (Znth sy lens)).
Proof.
  intros G c hold bits lens sy (Hb & Hc & ->) Hl Hs.
  set (l := Znth sy lens) in *.
  assert (HL: Zlength (sbits G) = 8 * Zlength (dc_src G)) by apply dfw_bytes_bits_len.
  rewrite (sublist_split (8 * c - bits) (8 * c - bits + l) (8 * c)) by lia.
  rewrite dfw_bval_app, Zlength_sublist by lia. rewrite Hs.
  unfold send_sym. fold l. rewrite dfw_bval_msb by lia.
  set (R := ref.reverse_bits (code lens sy) l).
  set (x := bval _).
  replace (8 * c - bits + l - (8 * c - bits)) with l by lia.
  rewrite Z.shiftl_mul_pow2 by lia.
  assert (Hland: Z.land R (x * 2 ^ l) = 0).
  { apply Z.bits_inj'. intros m Hm. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases m l).
    - rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
    - unfold R. rewrite dfw_rev_bits by lia. rewrite (proj2 (Z.ltb_ge m l)) by lia. reflexivity. }
  rewrite (Z.mul_comm (2 ^ l) x), <- Z.add_lor_land, Hland. ring.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* entries                                                                                        *)

Lemma dfw_extra_bound : forall l i, Forall (fun x => 0 <= x <= 13) l -> 0 <= Znth i l <= 13.
Proof.
  intros l i F. destruct (Z_lt_dec i 0); [rewrite Znth_underflow by lia; unfold Inhabitant_Z; lia|].
  destruct (Z_lt_dec i (Zlength l)); [|rewrite Znth_overflow by lia; unfold Inhabitant_Z; lia].
  rewrite Forall_forall in F. apply F, Znth_In. lia.
Qed.

Lemma dfw_16 : forall x, 0 <= x <= 13 -> Z.land (16 + x) 16 <> 0.
Proof.
  intros x Hx.
  assert (x = 0 \/ x = 1 \/ x = 2 \/ x = 3 \/ x = 4 \/ x = 5 \/ x = 6 \/ x = 7 \/ x = 8 \/ x = 9 \/
          x = 10 \/ x = 11 \/ x = 12 \/ x = 13) by lia.
  repeat (destruct H as [->|H]; [cbv; discriminate|]). subst. cbv; discriminate.
Qed.

Lemma dfw_64 : forall op, Z.land op 112 = 64 -> Z.land op 64 <> 0.
Proof.
  intros op H. replace (Z.land op 64) with (Z.land (Z.land op 112) 64).
  - rewrite H. cbv; discriminate.
  - rewrite <- Z.land_assoc. reflexivity.
Qed.

Lemma dfw_nolink : forall type il sy op val,
  ((type = LENS /\ il = len_link) \/ (type = DISTS /\ il = dist_link)) ->
  ref.means_symbol type sy op val = true -> il op = false.
Proof.
  intros type il sy op val Hil M.
  assert (FL: Forall (fun x => 0 <= x <= 13) ref.rfc_len_extra)
    by (unfold ref.rfc_len_extra; repeat (apply Forall_cons; [lia|]); apply Forall_nil).
  assert (FD: Forall (fun x => 0 <= x <= 13) ref.rfc_dist_extra)
    by (unfold ref.rfc_dist_extra; repeat (apply Forall_cons; [lia|]); apply Forall_nil).
  unfold ref.means_symbol, ref.sym_kind, ref.sym_extra in M.
  destruct Hil as [[-> ->]|[-> ->]]; cbn [Z.eqb] in M |- *.
  - unfold LENS, CODES in M. cbn - [Znth] in M.
    unfold len_link.
    destruct (sy <? 256) eqn:E1; [apply andb_prop in M; destruct M as [M _]; apply Z.eqb_eq in M; subst; reflexivity|].
    destruct (sy =? 256) eqn:E2; cbn in M.
    + apply Z.eqb_eq in M; subst; reflexivity.
    + destruct (sy <=? 285) eqn:E3; cbn - [Znth] in M.
      * apply andb_prop in M; destruct M as [M _]; apply Z.eqb_eq in M; subst.
        pose proof (dfw_16 _ (dfw_extra_bound _ (sy - 257) FL)) as N.
        apply Z.eqb_neq in N. rewrite N. rewrite orb_true_r. reflexivity.
      * apply Z.eqb_eq in M. apply dfw_64, Z.eqb_neq in M. rewrite M. rewrite !orb_true_r. reflexivity.
  - unfold DISTS, CODES, LENS in M. cbn - [Znth] in M.
    unfold dist_link.
    destruct (sy <=? 29) eqn:E3; cbn - [Znth] in M.
    + apply andb_prop in M; destruct M as [M _]; apply Z.eqb_eq in M; subst.
      pose proof (dfw_16 _ (dfw_extra_bound _ sy FD)) as N.
      apply Z.eqb_neq in N. rewrite N. reflexivity.
    + apply Z.eqb_eq in M. apply dfw_64, Z.eqb_neq in M. rewrite M. rewrite !orb_true_r. reflexivity.
Qed.

Lemma dfw_link : forall type il,
  ((type = LENS /\ il = len_link) \/ (type = DISTS /\ il = dist_link)) ->
  forall o, 1 <= o <= 15 -> il o = true.
Proof.
  intros type il Hil o Ho.
  assert (o = 1 \/ o = 2 \/ o = 3 \/ o = 4 \/ o = 5 \/ o = 6 \/ o = 7 \/ o = 8 \/ o = 9 \/
          o = 10 \/ o = 11 \/ o = 12 \/ o = 13 \/ o = 14 \/ o = 15) by lia.
  destruct Hil as [[_ ->]|[_ ->]];
    repeat (destruct H as [->|H]; [reflexivity|]); subst; reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the walk                                                                                       *)

Lemma dfw_hb_s : forall m h b, m_s (set_m_bits (set_m_hold m h) b) = m_s m.
Proof. intros; destruct m; reflexivity. Qed.
Lemma dfw_hb_hold : forall m h b, m_hold (set_m_bits (set_m_hold m h) b) = h.
Proof. intros; destruct m; reflexivity. Qed.
Lemma dfw_hb_bits : forall m h b, m_bits (set_m_bits (set_m_hold m h) b) = b.
Proof. intros; destruct m; reflexivity. Qed.
Lemma dfw_hb_hb : forall m h1 b1 h2 b2,
  set_m_bits (set_m_hold (set_m_bits (set_m_hold m h1) b1) h2) b2 = set_m_bits (set_m_hold m h2) b2.
Proof. intros; destruct m; reflexivity. Qed.

Lemma dfw_fwalk_S : forall k il t here m,
  fwalk_f lenfix_list distfix_list (S k) il t here m =
  (let m1 := set_m_bits (set_m_hold m (Z.shiftr (m_hold m) (e_bits here))) (u32 (m_bits m - e_bits here)) in
   if il (e_op here)
   then fwalk_f lenfix_list distfix_list k il t
          (tab_entry lenfix_list distfix_list (m_s m1) t (e_val here + m_hold m1 mod 2 ^ e_op here)) m1
   else (here, m1)).
Proof. reflexivity. Qed.

Lemma dfw_u32 : forall x, 0 <= x <= 64 -> u32 x = x.
Proof. intros. unfold u32. apply Z.mod_small. lia. Qed.

Lemma dfw_twalk_nonneg : forall kind s t root pat op val n,
  tvalid kind lenfix_list distfix_list s t root ->
  twalk s t root pat = Some (op, val, n) -> 0 <= n.
Proof.
  intros kind s t root pat op val n [sz [_ [Hrb _ Hroot]]] Tw.
  assert (P: 0 < 2 ^ root) by (apply Z.pow_pos_nonneg; lia).
  assert (Hi: 0 <= pat mod 2 ^ root < 2 ^ root) by (apply Z.mod_pos_bound; lia).
  specialize (Hroot _ Hi). cbv zeta in Hroot. unfold twalk in Tw. cbv zeta in Tw.
  set (e := tab_entry lenfix_list distfix_list s t (pat mod 2 ^ root)) in *.
  destruct Hroot as [Eok Hc].
  destruct (ref.is_link (e_op e)) eqn:L.
  - assert (IL: islink kind (e_op e) = true).
    { unfold ref.is_link in L. apply andb_prop in L. destruct L as [L1 L2].
      unfold islink. rewrite L2, L1. destruct (kind =? DISTS); reflexivity. }
    rewrite IL in Hc. destruct Hc as (B & O1 & O2 & Hsub).
    set (j := Z.shiftr pat (e_bits e) mod 2 ^ e_op e) in *.
    assert (Hj: 0 <= j < 2 ^ e_op e) by (apply Z.mod_pos_bound, Z.pow_pos_nonneg; lia).
    destruct (Hsub j Hj) as (_ & Eok2 & _ & _ & _). cbv zeta in Eok2.
    set (e2 := tab_entry lenfix_list distfix_list s t (e_val e + j)) in *.
    destruct (ref.is_link (e_op e2)); [discriminate|]. injection Tw as E1 E2 E3. subst op val n.
    destruct Eok2 as (_ & ? & _). lia.
  - injection Tw as E1 E2 E3. subst op val n. destruct Eok as (_ & ? & _). lia.
Qed.

Lemma dfw_walk : forall kind il t root m op val n,
  tvalid kind lenfix_list distfix_list (m_s m) t root ->
  twalk (m_s m) t root (m_hold m) = Some (op, val, n) ->
  il op = false -> (forall o, 1 <= o <= 15 -> il o = true) ->
  0 <= m_bits m -> n <= m_bits m <= 64 ->
  let '(here, m') := fwalk_f lenfix_list distfix_list 2 il t
                       (tab_entry lenfix_list distfix_list (m_s m) t (m_hold m mod 2 ^ root)) m in
  e_op here = op /\ e_val here = val /\
  m' = set_m_bits (set_m_hold m (Z.shiftr (m_hold m) n)) (m_bits m - n).
Proof.
  intros kind il t root m op val n Hv Tw Hop Hlk Hb0 Hb.
  pose proof (dfw_twalk_nonneg _ _ _ _ _ _ _ _ Hv Tw) as Hn.
  destruct Hv as [sz [_ [Hrb _ Hroot]]].
  assert (P: 0 < 2 ^ root) by (apply Z.pow_pos_nonneg; lia).
  assert (Hi: 0 <= m_hold m mod 2 ^ root < 2 ^ root) by (apply Z.mod_pos_bound; lia).
  specialize (Hroot _ Hi). cbv zeta in Hroot. unfold twalk in Tw. cbv zeta in Tw.
  set (e := tab_entry lenfix_list distfix_list (m_s m) t (m_hold m mod 2 ^ root)) in *.
  destruct Hroot as [Eok Hc].
  rewrite dfw_fwalk_S. cbv zeta. rewrite dfw_hb_s, dfw_hb_hold.
  destruct (ref.is_link (e_op e)) eqn:L.
  - assert (IL: islink kind (e_op e) = true).
    { unfold ref.is_link in L. apply andb_prop in L. destruct L as [L1 L2].
      unfold islink. rewrite L2, L1. destruct (kind =? DISTS); reflexivity. }
    rewrite IL in Hc. destruct Hc as (B & O1 & O2 & Hsub).
    set (j := Z.shiftr (m_hold m) (e_bits e) mod 2 ^ e_op e) in *.
    assert (Hj: 0 <= j < 2 ^ e_op e) by (apply Z.mod_pos_bound, Z.pow_pos_nonneg; lia).
    destruct (Hsub j Hj) as (_ & Eok2 & _ & _ & _). cbv zeta in Eok2.
    rewrite (Hlk (e_op e)) by lia.
    set (e2 := tab_entry lenfix_list distfix_list (m_s m) t (e_val e + j)) in *.
    destruct (ref.is_link (e_op e2)); [discriminate|]. injection Tw as E1 E2 E3. subst op val n.
    rewrite dfw_fwalk_S. cbv zeta. rewrite Hop. rewrite dfw_hb_hold, dfw_hb_bits, dfw_hb_hb.
    destruct Eok2 as (_ & ? & _).
    split; [reflexivity|]. split; [reflexivity|].
    rewrite Z.shiftr_shiftr by lia. f_equal.
    rewrite (dfw_u32 (m_bits m - e_bits e)) by lia. rewrite dfw_u32 by lia. lia.
  - injection Tw as E1 E2 E3. subst op val n. rewrite Hop.
    split; [reflexivity|]. split; [reflexivity|].
    rewrite dfw_u32 by lia. reflexivity.
Qed.

Lemma dfw : walk_stmt.
Proof.
  intros G c m type il t root lens sy Hh Hbytes Hb64 Htd Htv Hil Hsy Hnz Hle Hsub l.
  destruct Htd as [Hroot [Htd _]].
  destruct (Htd sy Hsy Hnz 0 (Z.le_refl 0)) as (op0 & val0 & Tw0 & _).
  pose proof (dfw_twalk_nonneg _ _ _ _ _ _ _ _ Htv Tw0) as Hl0.
  pose proof Hh as Hh'. destruct Hh' as (Hb0 & _).
  pose proof (dfw_hold_split G c (m_hold m) (m_bits m) lens sy Hh ltac:(lia) Hsub) as Hhold.
  destruct (Htd sy Hsy Hnz _ (dfw_bval_nonneg (sublist (8 * c - m_bits m + Znth sy lens) (8 * c) (sbits G)))) as (op & val & Tw & Ms).
  rewrite <- Hhold in Tw.
  pose proof (dfw_walk type il t root m op val (Znth sy lens) Htv Tw (dfw_nolink _ _ _ _ _ Hil Ms)
                (dfw_link _ _ Hil) ltac:(lia) ltac:(lia)) as W.
  destruct (fwalk_f _ _ _ _ _ _ _) as [here m'].
  destruct W as (E1 & E2 & E3). subst l. rewrite E1, E2. split; assumption.
Qed.
