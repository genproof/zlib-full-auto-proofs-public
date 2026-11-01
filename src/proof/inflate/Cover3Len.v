(* The length bound of Cover3.v's cover3_stmt (StepInv.v's cover3_stmt and Inv2.v's form
   cover3_len_inv2): the length tables inflate_table builds (LENS) have len_ok entries (base + extra
   bits <= 258) in their used region.  From the model of src/proof/inftrees (model.v) and its facts. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.inflate.StepInv.
Require Zlib.proof.inflate.Inv2.
Require Import Zlib.proof.inftrees.facts.
Require Import Zlib.proof.inftrees.fact_result.
Require Import Zlib.proof.inftrees.part_result.
Require Import Zlib.proof.inftrees.decode_defs.
Require Import Zlib.proof.inftrees.decode_step.
Require Import Zlib.proof.inftrees.decode_run.
Require Import Zlib.proof.inftrees.part_decode.
Require Zlib.proof.inftrees.part_sorted.
Require Zlib.proof.inftrees.part_rfc.
Require Zlib.proof.inftrees.part_bits.
Require Zlib.proof.inftrees.part_subbits.
Require Zlib.proof.inftrees.part_size.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* The entries inflate_table writes into a length table are len_ok.                               *)

Definition c3_chk : bool :=
  forallb (fun i => let o := Znth i lext in
                    negb ((16 <=? o) && (o <=? 21)) || (Znth i lbase + 2 ^ (o - 16) <=? 259))
          (zseq 0 31).

Lemma c3_chk_ok : c3_chk = true.
Proof. vm_compute. reflexivity. Qed.

Lemma c3_sym_len_ok : forall s b, len_ok (sym_entry LENS s b).
Proof.
  intros. unfold len_ok, sym_entry. cbv zeta.
  change (match_of LENS) with 257. change (extra_of LENS) with lext. change (base_of LENS) with lbase.
  destruct (s + 1 <? 257); [cbn [e_op]; lia|].
  destruct (257 <=? s); [|cbn [e_op]; lia].
  cbn [e_op e_val].
  destruct (Z_lt_dec (s - 257) 0); [intros Ho; rewrite (Znth_underflow (s - 257) lext) in Ho by lia; unfold Inhabitant_Z in Ho; lia|].
  destruct (Z_lt_dec (s - 257) 31);
    [|intros Ho; rewrite (Znth_overflow (s - 257) lext) in Ho by (cbn; lia); unfold Inhabitant_Z in Ho; lia].
  pose proof c3_chk_ok as H. unfold c3_chk in H. rewrite forallb_forall in H.
  specialize (H (s - 257) (proj2 (In_zseq 31 0 (s - 257)) ltac:(lia))). cbv zeta in H.
  intros Ho. rewrite orb_true_iff, negb_true_iff, andb_false_iff, !Z.leb_gt, Z.leb_le in H. lia.
Qed.

Lemma c3_invalid_len_ok : forall b, len_ok (invalid_entry b).
Proof. intros. unfold len_ok, invalid_entry. cbn [e_op]. lia. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Arithmetic.                                                                                    *)

Lemma c3_find : forall (f: Z -> Z) X n, f 0 <= X -> X < f (Z.of_nat n) ->
  exists j, 0 <= j < Z.of_nat n /\ f j <= X < f (j + 1).
Proof.
  intros f X n H0. induction n as [|n IH]; intros H1; [cbn in H1; lia|].
  destruct (Z_lt_dec X (f (Z.of_nat n))) as [L|L].
  - destruct (IH L) as (j & Hj & Hx). exists j. split; [lia|auto].
  - exists (Z.of_nat n). split; [lia|]. rewrite Nat2Z.inj_succ in H1. rewrite <- Z.add_1_r in H1. lia.
Qed.

Lemma c3_pow_split : forall a b, 0 <= a <= b -> 2 ^ b = 2 ^ (b - a) * 2 ^ a.
Proof. intros. rewrite <- Z.pow_add_r by lia. f_equal. lia. Qed.

Lemma c3_pow_pos : forall a, 0 <= a -> 0 < 2 ^ a.
Proof. intros. apply Z.pow_pos_nonneg; lia. Qed.

Lemma c3_div_pin : forall a b x, 0 < b -> a * b <= x < (a + 1) * b -> x / b = a.
Proof. intros. symmetry. apply Z.div_unique with (x - a * b); lia. Qed.

Lemma c3_cancel_le : forall a b e, 0 < e -> a * e <= b * e -> a <= b.
Proof. intros. nia. Qed.

Lemma c3_cancel_lt : forall a b e, 0 < e -> a * e < b * e -> a < b.
Proof. intros. nia. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Coverage: every entry of [0, used) of a complete code's table is a fill or a link.             *)

Section Cov.
Context (W ls: list Z) (root: Z) (t: list entry).
Context (Hrange : Forall (fun l => 1 <= l <= MAXBITS) ls).
Context (Hsorted : forall a b, 0 <= a -> a <= b < Zlength ls -> Znth a ls <= Znth b ls).
Context (HN : 0 < Zlength ls).
Context (Hroot : Znth 0 ls <= root <= Znth (Zlength ls - 1) ls).
Context (Hk : ksum ls = 2 ^ MAXBITS).
Context (Hbits : bits_stmt).
Context (Hfill : forall j, 0 <= j < Zlength ls -> fills_done LENS W ls root j t).
Context (Hlink : forall j, 0 <= j < Zlength ls -> link_done ls root j t).

Lemma c3_root : 1 <= root <= MAXBITS.
Proof.
  pose proof (ls_range ls Hrange 0 ltac:(lia)). pose proof (ls_range ls Hrange (Zlength ls - 1) ltac:(lia)).
  lia.
Qed.

Lemma c3_C : forall j, 0 <= j < Zlength ls ->
  0 <= kpre ls j / 2 ^ (MAXBITS - Znth j ls) /\
  kpre ls j = kpre ls j / 2 ^ (MAXBITS - Znth j ls) * 2 ^ (MAXBITS - Znth j ls) /\
  kpre ls (j + 1) = (kpre ls j / 2 ^ (MAXBITS - Znth j ls) + 1) * 2 ^ (MAXBITS - Znth j ls) /\
  kpre ls j / 2 ^ (MAXBITS - Znth j ls) + 1 <= 2 ^ Znth j ls.
Proof.
  intros. destruct (C_facts 1 ls root Hrange Hsorted HN ltac:(lia) ltac:(unfold LENS; lia) j H)
    as (A & B & C & D & _). auto.
Qed.

Lemma c3_find_j : forall X, 0 <= X < 2 ^ MAXBITS ->
  exists j, 0 <= j < Zlength ls /\ kpre ls j <= X < kpre ls (j + 1).
Proof.
  intros. destruct (c3_find (kpre ls) X (Z.to_nat (Zlength ls))) as (j & Hj & Hx).
  - rewrite kpre_0. lia.
  - rewrite Z2Nat.id by lia. rewrite kpre_full. lia.
  - rewrite Z2Nat.id in Hj by lia. exists j. auto.
Qed.

Lemma c3_gmax_le : forall q, gmax ls root q <= MAXBITS.
Proof.
  intros. destruct (gmax_props ls root q) as (_ & _ & [G|(j & Hj & _ & _ & G)]); [unfold MAXBITS; lia|].
  rewrite G. pose proof (ls_range ls Hrange j Hj). lia.
Qed.

Lemma c3_link_ok : forall j, len_ok (dlink ls root j).
Proof.
  intros. unfold len_ok, dlink. cbn [e_op]. pose proof (c3_gmax_le (pfx ls root j)). unfold MAXBITS in *.
  pose proof c3_root. lia.
Qed.

Lemma c3_cov_root : forall P, 0 <= P < 2 ^ root -> len_ok (Znth P t).
Proof.
  intros P HP. pose proof Hbits as (B1 & B2 & B3 & B4 & B5). pose proof c3_root as Hr.
  assert (HM: MAXBITS = 15) by reflexivity.
  set (r := reverse_bits P root).
  assert (Hr0: 0 <= r < 2 ^ root) by (apply B1; lia).
  assert (Hrr: reverse_bits r root = P) by (apply B3; lia).
  set (E := 2 ^ (MAXBITS - root)).
  assert (HE: 0 < E) by (apply c3_pow_pos; lia).
  assert (H15: 2 ^ MAXBITS = 2 ^ root * E) by (unfold E; rewrite <- Z.pow_add_r by lia; f_equal; lia).
  destruct (c3_find_j (r * E) ltac:(nia)) as (j & Hj & Hlo & Hhi).
  destruct (c3_C j Hj) as (HC0 & HK & HS & HCl).
  pose proof (ls_range ls Hrange j Hj) as Hl.
  set (l := Znth j ls) in *. set (C := kpre ls j / 2 ^ (MAXBITS - l)) in *.
  set (D := 2 ^ (MAXBITS - l)) in *.
  assert (HD: 0 < D) by (apply c3_pow_pos; lia).
  destruct (Z_le_gt_dec l root) as [S|L].
  - (* a short code: P is one of its fills *)
    set (A := 2 ^ (root - l)).
    assert (HA: 0 < A) by (apply c3_pow_pos; lia).
    assert (EDA: D = A * E) by (unfold D, A, E; rewrite <- Z.pow_add_r by lia; f_equal; lia).
    assert (Hra: r / A = C).
    { apply c3_div_pin; auto. split.
      - apply (c3_cancel_le _ _ E); auto. rewrite <- Z.mul_assoc, <- EDA. lia.
      - apply (c3_cancel_lt _ _ E); auto. rewrite <- Z.mul_assoc, <- EDA. lia. }
    assert (Hmod: P mod 2 ^ l = dhuff ls j).
    { rewrite <- ds_land_mod by lia. rewrite <- Hrr. rewrite B2 by lia. fold A. rewrite Hra. reflexivity. }
    destruct (Hfill j Hj) as (F & _). fold l in F.
    assert (H2l: 0 < 2 ^ l) by (apply c3_pow_pos; lia).
    assert (Hk0: 0 <= P / 2 ^ l < 2 ^ (root - l)).
    { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; auto.
      rewrite <- Z.pow_add_r by lia. replace (l + (root - l)) with root by lia. lia. }
    specialize (F S (P / 2 ^ l) Hk0).
    rewrite <- Hmod in F. rewrite (Z.mul_comm (P / 2 ^ l)), Z.add_comm, <- Z.div_mod in F by lia.
    rewrite F. apply c3_sym_len_ok.
  - (* a long code: P is the link of its group *)
    set (A := 2 ^ (l - root)).
    assert (HA: 0 < A) by (apply c3_pow_pos; lia).
    assert (EDA: E = A * D) by (unfold D, A, E; rewrite <- Z.pow_add_r by lia; f_equal; lia).
    assert (HCr: C = r * A).
    { assert (C <= r * A) by (apply (c3_cancel_le _ _ D); auto; rewrite <- Z.mul_assoc, <- EDA; lia).
      assert (r * A < C + 1) by (apply (c3_cancel_lt _ _ D); auto; rewrite <- Z.mul_assoc, <- EDA; lia).
      lia. }
    assert (Hp: pfx ls root j = r).
    { unfold pfx. fold E. rewrite HK, HCr, EDA. rewrite <- Z.mul_assoc. apply Z.div_mul. lia. }
    assert (L': root < Znth j ls) by (fold l; lia).
    pose proof (Hlink j Hj L') as Lk. rewrite Hp, Hrr in Lk. rewrite Lk. apply c3_link_ok.
Qed.

Lemma c3_cov_sub : forall P, 2 ^ root <= P < 2 ^ root + sumq ls root (2 ^ root) -> len_ok (Znth P t).
Proof.
  intros P HP. pose proof Hbits as (B1 & B2 & B3 & B4 & B5). pose proof c3_root as Hr.
  assert (HM: MAXBITS = 15) by reflexivity.
  set (E := 2 ^ (MAXBITS - root)).
  assert (HE: 0 < E) by (apply c3_pow_pos; lia).
  assert (H15: 2 ^ MAXBITS = 2 ^ root * E) by (unfold E; rewrite <- Z.pow_add_r by lia; f_equal; lia).
  assert (H2r: 0 < 2 ^ root) by (apply c3_pow_pos; lia).
  (* the group q of P *)
  destruct (c3_find (sumq ls root) (P - 2 ^ root) (Z.to_nat (2 ^ root))) as (q & Hq & Hqlo & Hqhi).
  { change (sumq ls root 0) with 0. lia. }
  { rewrite Z2Nat.id by lia. lia. }
  rewrite Z2Nat.id in Hq by lia. rewrite sumq_succ in Hqhi by lia.
  assert (Hfq: fq ls root q <> 0) by lia.
  destruct (fq_nonzero ls root q Hfq) as (j0 & Hj0 & Hl0 & Hp0).
  destruct (gmax_props ls root q) as (G1 & G2 & _).
  set (g := gmax ls root q) in *.
  assert (Hg0: Znth j0 ls <= g) by (apply G2; auto).
  pose proof (c3_gmax_le q) as Hg15. fold g in Hg15.
  assert (Efq: fq ls root q = 2 ^ (g - root)) by (unfold fq; fold g; destruct (g =? 0) eqn:Eg; [apply Z.eqb_eq in Eg; lia|auto]).
  rewrite Efq in Hqhi.
  set (p' := P - 2 ^ root - sumq ls root q).
  assert (Hp': 0 <= p' < 2 ^ (g - root)) by (unfold p'; lia).
  set (r' := reverse_bits p' (g - root)).
  assert (Hr': 0 <= r' < 2 ^ (g - root)) by (apply B1; lia).
  assert (Hrr': reverse_bits r' (g - root) = p') by (apply B3; lia).
  set (G := 2 ^ (MAXBITS - g)).
  assert (HG: 0 < G) by (apply c3_pow_pos; lia).
  assert (EEG: E = 2 ^ (g - root) * G) by (unfold E, G; rewrite <- Z.pow_add_r by lia; f_equal; lia).
  set (Q := q * E).
  set (X := Q + r' * G).
  assert (HX: Q <= X < Q + E) by (unfold X; nia).
  assert (HXm: X < 2 ^ MAXBITS) by (unfold Q in HX; nia).
  (* the group start j0 lies in [Q, Q + E) *)
  assert (Hk0: Q <= kpre ls j0 < Q + E).
  { pose proof (Z.div_mod (kpre ls j0) E ltac:(lia)). pose proof (Z.mod_pos_bound (kpre ls j0) E HE).
    fold E in Hp0. rewrite Hp0 in H. unfold Q. lia. }
  destruct (c3_find_j X ltac:(unfold Q in *; nia)) as (j & Hj & Hlo & Hhi).
  destruct (c3_C j Hj) as (HC0 & HK & HS & HCl).
  pose proof (ls_range ls Hrange j Hj) as Hl.
  set (l := Znth j ls) in *. set (C := kpre ls j / 2 ^ (MAXBITS - l)) in *.
  set (D := 2 ^ (MAXBITS - l)) in *.
  assert (HD: 0 < D) by (apply c3_pow_pos; lia).
  assert (L: root < l).
  { destruct (Z_le_gt_dec l root) as [S|L]; [exfalso|lia].
    set (A := 2 ^ (root - l)).
    assert (HA: 0 < A) by (apply c3_pow_pos; lia).
    assert (EDA: D = A * E) by (unfold D, A, E; rewrite <- Z.pow_add_r by lia; f_equal; lia).
    assert (C * A < q + 1).
    { apply (c3_cancel_lt _ _ E); auto. rewrite <- Z.mul_assoc, <- EDA. unfold Q in HX. lia. }
    assert (q < (C + 1) * A).
    { apply (c3_cancel_lt _ _ E); auto. rewrite <- Z.mul_assoc, <- EDA. unfold Q in HX. lia. }
    assert (A1: kpre ls j <= kpre ls j0).
    { rewrite HK, EDA. replace (C * (A * E)) with (C * A * E) by ring.
      apply Z.le_trans with (q * E); [apply Z.mul_le_mono_nonneg_r; lia | unfold Q in Hk0; lia]. }
    assert (A2: kpre ls j0 < kpre ls (j + 1)).
    { rewrite HS, EDA. replace ((C + 1) * (A * E)) with ((C + 1) * A * E) by ring.
      apply Z.lt_le_trans with ((q + 1) * E); [unfold Q in Hk0; lia | apply Z.mul_le_mono_nonneg_r; lia]. }
    destruct (Z_lt_ge_dec j0 j) as [J|J].
    - pose proof (kpre_mono ls (j0 + 1) j ltac:(lia) ltac:(lia)). rewrite kpre_S in H1 by lia.
      pose proof (c3_pow_pos (MAXBITS - Znth j0 ls)). lia.
    - destruct (Z_lt_ge_dec j j0) as [J'|J'].
      + pose proof (kpre_mono ls (j + 1) j0 ltac:(lia) ltac:(lia)). lia.
      + assert (j = j0) by lia. subst j0. fold l in Hl0. lia. }
  set (A := 2 ^ (l - root)).
  assert (HA: 0 < A) by (apply c3_pow_pos; lia).
  assert (EDA: E = A * D) by (unfold D, A, E; rewrite <- Z.pow_add_r by lia; f_equal; lia).
  set (d := C - q * A).
  assert (Hd: 0 <= d < A).
  { unfold d. split.
    - assert (q * A < C + 1); [|lia]. apply (c3_cancel_lt _ _ D); auto. rewrite <- Z.mul_assoc, <- EDA.
      unfold Q in HX. lia.
    - assert (C < q * A + A); [|lia]. apply (c3_cancel_lt _ _ D); auto.
      replace ((q * A + A) * D) with (q * E + E) by (rewrite EDA; ring). unfold Q in HX. lia. }
  assert (Hpj: pfx ls root j = q).
  { unfold pfx. fold E. apply c3_div_pin; auto. rewrite HK, EDA. replace C with (q * A + d) by (unfold d; lia).
    assert (0 <= d * D < A * D) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_lt_mono_pos_r; lia]).
    replace ((q * A + d) * D) with (q * (A * D) + d * D) by ring.
    replace ((q + 1) * (A * D)) with (q * (A * D) + A * D) by ring. lia. }
  assert (Hlg: l <= g) by (apply G2; auto; fold E; rewrite <- Hpj; reflexivity).
  set (B := 2 ^ (g - l)).
  assert (HB: 0 < B) by (apply c3_pow_pos; lia).
  assert (EDB: D = B * G) by (unfold D, B, G; rewrite <- Z.pow_add_r by lia; f_equal; lia).
  assert (Hrd: r' / B = d).
  { apply c3_div_pin; auto. split.
    - apply (c3_cancel_le _ _ G); auto. rewrite <- Z.mul_assoc, <- EDB.
      assert (kpre ls j = Q + d * D) by (rewrite HK; unfold Q, d; rewrite EDA; ring). unfold X in Hlo. lia.
    - apply (c3_cancel_lt _ _ G); auto. rewrite <- Z.mul_assoc, <- EDB.
      assert (kpre ls (j + 1) = Q + (d + 1) * D) by (rewrite HS; unfold Q, d; rewrite EDA; ring).
      unfold X in Hhi. lia. }
  (* the fill of j that hits P *)
  set (h := dhuff ls j).
  assert (Hh: 0 <= h < 2 ^ l) by (apply B1; lia).
  assert (HhC: reverse_bits h l = C) by (apply B3; lia).
  assert (Hhr: 0 <= h / 2 ^ root < A).
  { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; auto.
    unfold A. rewrite <- Z.pow_add_r by lia. replace (root + (l - root)) with l by lia. lia. }
  assert (HCd: C mod A = d).
  { unfold d. rewrite <- (Z.mod_unique C A q (C - q * A)); auto; lia. }
  assert (Hd': reverse_bits (h / 2 ^ root) (l - root) = d).
  { rewrite <- HCd. unfold A. rewrite <- ds_land_mod by lia. rewrite <- HhC. rewrite B2 by lia.
    f_equal. f_equal. f_equal. lia. }
  assert (Hpm: p' mod A = h / 2 ^ root).
  { unfold A. rewrite <- ds_land_mod by lia. rewrite <- Hrr'. rewrite B2 by lia.
    replace (g - root - (l - root)) with (g - l) by lia. fold B. rewrite Hrd. rewrite <- Hd'.
    apply B3; [lia|exact Hhr]. }
  destruct (Hfill j Hj) as (_ & F). fold l in F. rewrite Hpj in F. fold g in F.
  assert (Hkk: 0 <= p' / A < 2 ^ (g - l)).
  { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; auto. unfold A.
    rewrite <- Z.pow_add_r by lia. replace (l - root + (g - l)) with (g - root) by lia. lia. }
  specialize (F L (p' / A) Hkk). fold A in F. fold h in F.
  rewrite Z.shiftr_div_pow2 in F by lia. rewrite <- Hpm in F.
  assert (Ep: p' mod A + p' / A * A = p') by (pose proof (Z.div_mod p' A ltac:(lia)); lia).
  rewrite <- Z.add_assoc, Ep in F.
  unfold dnxt, p' in F. replace (2 ^ root + sumq ls root q + (P - 2 ^ root - sumq ls root q)) with P in F by lia.
  rewrite F. apply c3_sym_len_ok.
Qed.

End Cov.

Lemma cover3_len_proof : cover3_stmt.
Proof.
  intros lens req old root used t Hin Hcap Hold Hmodel i Hi.
  pose proof Hin as Hin'. destruct Hin' as (Ht & Hcodes & Hl & Hreq).
  pose proof part_sorted.sorted_ok2 as Hso. pose proof part_rfc.rfc_ok2 as Hrfc.
  pose proof part_bits.bits_ok2 as Hbits. pose proof part_subbits.subbits_ok2 as Hsub.
  pose proof (part_size.size_ok2 Hso Hrfc Hbits) as Hsize.
  pose proof (fact_result_ok Hso Hrfc Hbits Hsub Hsize LENS lens req old Hin Hcap Hold) as FR.
  destruct (expected_call LENS lens req) as [[want r0] size] eqn:Eec.
  rewrite Hmodel in FR. destruct FR as (_ & Er & Eu & Hu & _ & Hlen & _).
  unfold expected_call in Eec. injection Eec as Ew Er0 Es.
  assert (HM: MAXBITS = 15) by reflexivity.
  unfold inflate_table_model in Hmodel.
  destruct (maxlen lens =? 0) eqn:Emx.
  - (* no symbol: two invalid entries *)
    inversion Hmodel; subst root used t; clear Hmodel.
    destruct Hcap as (_ & HcL & _). specialize (HcL eq_refl). unfold ENOUGH_LENS in HcL.
    assert (i = 0 \/ i = 1) as [-> | ->] by lia.
    + rewrite upd_Znth_diff by (rewrite ?upd_Znth_Zlength; lia). rewrite upd_Znth_same by lia.
      apply c3_invalid_len_ok.
    + rewrite upd_Znth_same by (rewrite ?upd_Znth_Zlength; lia). apply c3_invalid_len_ok.
  - apply Z.eqb_neq in Emx.
    destruct (left_final (counts lens)) as [lft|] eqn:Eleft; [|discriminate].
    destruct ((0 <? lft) && ((LENS =? CODES) || negb (maxlen lens =? 1))) eqn:Etest; [discriminate|].
    destruct (over LENS (Z.shiftl 1 (root_of req lens))) eqn:Eover; [discriminate|].
    assert (Hd: dhyps LENS lens (sorted_syms lens) (sl lens) (root_of req lens) old)
      by (eapply dsetup_ok; eauto).
    assert (Hfin: exists s, used = s_used s /\ t = finish s /\ root = root_of req lens /\
      (run LENS lens (sorted_syms lens) (root_of req lens) (maxlen lens) (length (sorted_syms lens))
         (init_state lens (root_of req lens) old) = Break s \/
       run LENS lens (sorted_syms lens) (root_of req lens) (maxlen lens) (length (sorted_syms lens))
         (init_state lens (root_of req lens) old) = Continue s)).
    { destruct (run LENS lens (sorted_syms lens) (root_of req lens) (maxlen lens) (length (sorted_syms lens))
                  (init_state lens (root_of req lens) old)) eqn:Er';
        inversion Hmodel; subst; eexists; eauto. }
    destruct Hfin as (s & Eus & Ets & Ers & Hrun).
    destruct dstep_last_ok as [Hstep Hlast].
    pose proof (drun_ok LENS lens req old s Hso Hbits Hsub Hstep Hlast Hl Emx Hd Hrun) as Hf.
    rewrite <- Eus, <- Ets, <- Ers in Hf. rewrite <- Ers in Hd.
    destruct Hd as (Hrange & Hsorted & HN & HWls & HWr & Hroot & Hk & Hinc & _ & _ & _ & Hcap0 & _ & _).
    destruct Hf as (Hfl & H2r & _ & Hincf).
    destruct (Z.eq_dec (ksum (sl lens)) (2 ^ MAXBITS)) as [Hc|Hc].
    + (* a complete code *)
      destruct (Hso lens Hl) as (_ & _ & _ & _ & _ & _ & Sk & _ & _).
      pose proof (c3_root (sl lens) root Hrange HN Hroot) as Hr.
      assert (Hus: used <= 2 ^ root + sumq (sl lens) root (2 ^ root)).
      { rewrite Eu, <- Es, Er0, <- Er, Hsize by (auto; lia). unfold sumq. lia. }
      destruct (Z_lt_dec i (2 ^ root)).
      * apply (c3_cov_root (sorted_syms lens) (sl lens) root t Hrange Hsorted HN Hroot Hc Hbits);
          [intros j Hj; apply (proj1 (Hfl j Hj)) | intros j Hj; apply (proj2 (Hfl j Hj)) | lia].
      * apply (c3_cov_sub (sorted_syms lens) (sl lens) root t Hrange Hsorted HN Hroot Hc Hbits);
          [intros j Hj; apply (proj1 (Hfl j Hj)) | lia].
    + (* an incomplete code: one code of length 1, root 1 *)
      destruct (Hincf ltac:(lia)) as (EN & E0 & -> & -> & Hent).
      assert (i = 0 \/ i = 1) as [-> | ->] by lia.
      * destruct (Hfl 0 ltac:(lia)) as ((F & _) & _).
        rewrite E0 in F. specialize (F ltac:(lia) 0 ltac:(cbn; lia)).
        replace (dhuff (sl lens) 0 + 0 * 2 ^ 1) with 0 in F.
        { rewrite F. apply c3_sym_len_ok. }
        unfold dhuff, dcode. rewrite E0, kpre_0, Z.div_0_l, reverse_bits_0 by (cbn; lia). lia.
      * rewrite Hent. apply c3_invalid_len_ok.
Qed.

(* the same, with Inv2.v's len_ok (for Cover3.v's cover3_proof) *)
Lemma cover3_len_inv2 : forall lens req old root used t,
  inputs_ok LENS lens req -> cap_ok LENS lens req (Zlength old) -> Forall entry_ok old ->
  inflate_table_model LENS lens req old = ROk root used t ->
  forall i, 0 <= i < used -> Inv2.len_ok (Znth i t).
Proof.
  intros lens req old root used t A B C D i Hi R.
  pose proof (cover3_len_proof lens req old root used t A B C D i Hi R). lia.
Qed.
