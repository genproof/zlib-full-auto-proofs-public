(* Part of fact_decode: walk (ref.v) on the final table dfinal decodes every code. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.inftrees.facts.
Require Import Zlib.proof.inftrees.fact_result.
Require Import Zlib.proof.inftrees.model_inv.
Require Import Zlib.proof.inftrees.decode_defs.
Import ListNotations.
Local Open Scope Z_scope.

Lemma dw_lor_add : forall h x l, 0 <= l -> 0 <= h < 2 ^ l -> 0 <= x ->
  Z.lor h (Z.shiftl x l) = h + x * 2 ^ l.
Proof.
  intros. rewrite Z.shiftl_mul_pow2 by lia.
  assert (E: Z.land h (x * 2 ^ l) = 0).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
    destruct (Z_lt_le_dec n l).
    - rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
    - rewrite <- (Z.mod_small h (2 ^ l)) by lia. rewrite Z.mod_pow2_bits_high by lia. reflexivity. }
  rewrite <- Z.lxor_lor by auto. rewrite <- Z.add_nocarry_lxor by auto. reflexivity.
Qed.

Lemma dw_mask : forall a m, 0 <= m -> Z.land a (Z.shiftl 1 m - 1) = a mod 2 ^ m.
Proof.
  intros. rewrite pow2_shiftl by lia.
  replace (2 ^ m - 1) with (Z.ones m) by (rewrite Z.ones_equiv; lia). apply Z.land_ones. lia.
Qed.

Lemma dw_split_mod : forall h x l m, 0 <= l <= m -> 0 <= h < 2 ^ l -> 0 <= x ->
  (h + x * 2 ^ l) mod 2 ^ m = h + (x mod 2 ^ (m - l)) * 2 ^ l.
Proof.
  intros h x l m Hl Hh Hx.
  assert (HP: 2 ^ m = 2 ^ l * 2 ^ (m - l)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  assert (HQ: 0 < 2 ^ (m - l)) by (apply Z.pow_pos_nonneg; lia).
  pose proof (Z.div_mod x (2 ^ (m - l)) ltac:(lia)) as Hd.
  pose proof (Z.mod_pos_bound x (2 ^ (m - l)) HQ) as Hr.
  set (q := x / 2 ^ (m - l)) in *. set (r := x mod 2 ^ (m - l)) in *.
  replace (h + x * 2 ^ l) with ((h + r * 2 ^ l) + q * 2 ^ m) by (rewrite Hd, HP; ring).
  rewrite Z.mod_add by lia. apply Z.mod_small. nia.
Qed.

Lemma dw_mix_lt : forall a b A B, 0 <= a < A -> 0 <= b < B -> a + b * A < B * A.
Proof. intros. nia. Qed.

Lemma dw_sym_op : forall type s b, e_op (sym_entry type s b) = e_op (sym_entry type s 0).
Proof. intros. unfold sym_entry. repeat destruct (_ <? _); try destruct (_ <=? _); reflexivity. Qed.

Lemma dw_sym_val : forall type s b, e_val (sym_entry type s b) = e_val (sym_entry type s 0).
Proof. intros. unfold sym_entry. repeat destruct (_ <? _); try destruct (_ <=? _); reflexivity. Qed.

Lemma dw_sym_bits : forall type s b, e_bits (sym_entry type s b) = b.
Proof. intros. unfold sym_entry. repeat destruct (_ <? _); try destruct (_ <=? _); reflexivity. Qed.

Lemma dw_is_link_small : forall o, 1 <= o <= 15 -> is_link o = true.
Proof.
  intros. assert (o = 1 \/ o = 2 \/ o = 3 \/ o = 4 \/ o = 5 \/ o = 6 \/ o = 7 \/ o = 8 \/
                  o = 9 \/ o = 10 \/ o = 11 \/ o = 12 \/ o = 13 \/ o = 14 \/ o = 15) by lia.
  repeat destruct H0 as [H0|H0]; subst; reflexivity.
Qed.

Lemma dwalk_ok : dwalk_stmt.
Proof.
  intros type lens W ls root old used t Hd Hbits Hnl Hf j x Hj Hx.
  destruct Hd as (Hrange & Hsorted & HN & HWls & HWr & Hroot & Hk & Hinc & Htype & Hcodes & Hcap & Hcap0 & Hold & Hone).
  destruct Hf as (Hfl & Hused & Hsub & _).
  destruct (Hfl j Hj) as [[Fs Fl] Lk].
  pose proof (l_range ls Hrange j Hj) as Hl.
  pose proof (root_range ls root Hrange HN Hroot) as Hr.
  set (l := Znth j ls) in *.
  set (h := dhuff ls j) in *.
  destruct Hbits as (B1 & B2 & B3 & B4 & B5) eqn:EB.
  assert (Hh: 0 <= h < 2 ^ l) by (apply B1; lia).
  rewrite dw_lor_add by lia.
  unfold walk. rewrite dw_mask by lia.
  destruct (Z_le_gt_dec l root) as [Hs|Hlong].
  - (* short code *)
    rewrite dw_split_mod by lia.
    set (k := x mod 2 ^ (root - l)).
    assert (Hk0: 0 <= k < 2 ^ (root - l)) by (apply Z.mod_pos_bound, Z.pow_pos_nonneg; lia).
    assert (HP: 2 ^ root = 2 ^ l * 2 ^ (root - l)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    assert (Hi: h + k * 2 ^ l < 2 ^ root) by (rewrite HP; pose proof (dw_mix_lt h k (2 ^ l) (2 ^ (root - l)) Hh Hk0); lia).
    destruct (used <=? h + k * 2 ^ l) eqn:E; [apply Z.leb_le in E; lia|].
    rewrite (Fs Hs k Hk0). rewrite (Hnl j l Hj).
    rewrite dw_sym_op, dw_sym_val, dw_sym_bits. reflexivity.
  - (* long code *)
    assert (Hlt: root < l) by lia. clear Hlong. rename Hlt into Hlong.
    assert (HPl: 2 ^ l = 2 ^ (l - root) * 2 ^ root) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    assert (HPr: 0 < 2 ^ root) by (apply Z.pow_pos_nonneg; lia).
    assert (HPlr: 0 < 2 ^ (l - root)) by (apply Z.pow_pos_nonneg; lia).
    assert (Ei: (h + x * 2 ^ l) mod 2 ^ root = reverse_bits (pfx ls root j) root).
    { replace (h + x * 2 ^ l) with (h + (x * 2 ^ (l - root)) * 2 ^ root) by (rewrite HPl; ring).
      rewrite Z.mod_add by lia. rewrite <- dw_mask by lia.
      unfold h, dhuff, dcode. apply (huff_mask ls root Hrange HN Hroot Hbits j Hj). lia. }
    pose proof (pfx_range ls root Hrange HN Hroot Hk j Hj) as Hpr.
    assert (Hi: 0 <= reverse_bits (pfx ls root j) root < 2 ^ root) by (apply B1; lia).
    rewrite Ei.
    destruct (used <=? reverse_bits (pfx ls root j) root) eqn:E; [apply Z.leb_le in E; lia|].
    rewrite (Lk Hlong). unfold dlink. cbn [e_op e_bits e_val].
    pose proof (gmax_long ls root Hrange j Hj Hlong) as Hg.
    pose proof (Hsub j Hj Hlong) as Hsj.
    set (g := gmax ls root (pfx ls root j)) in *.
    set (nx := dnxt ls root (pfx ls root j)) in *.
    rewrite dw_is_link_small by (unfold MAXBITS in *; lia).
    replace (root + (g - root)) with g by lia.
    destruct (MAXBITS <? g) eqn:E2; [apply Z.ltb_lt in E2; lia|].
    rewrite dw_mask by lia. rewrite dw_split_mod by lia.
    set (k := x mod 2 ^ (g - l)).
    assert (Hk0: 0 <= k < 2 ^ (g - l)) by (apply Z.mod_pos_bound, Z.pow_pos_nonneg; lia).
    assert (Ej: Z.shiftr (h + k * 2 ^ l) root = Z.shiftr h root + k * 2 ^ (l - root)).
    { rewrite !Z.shiftr_div_pow2 by lia. rewrite HPl, Z.mul_assoc, Z.div_add by lia. reflexivity. }
    rewrite Ej.
    assert (Hhr: Z.shiftr h root < 2 ^ (l - root)).
    { rewrite Z.shiftr_div_pow2 by lia. apply Z.div_lt_upper_bound; lia. }
    assert (Hhr0: 0 <= Z.shiftr h root) by (apply Z.shiftr_nonneg; lia).
    assert (HPg: 2 ^ (g - root) = 2 ^ (g - l) * 2 ^ (l - root)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    destruct (used <=? nx + (Z.shiftr h root + k * 2 ^ (l - root))) eqn:E3; [apply Z.leb_le in E3;
      pose proof (dw_mix_lt _ _ _ _ (conj Hhr0 Hhr) Hk0); lia|].
    rewrite Z.add_assoc, (Fl Hlong k Hk0). rewrite (Hnl j (l - root) Hj).
    rewrite dw_sym_op, dw_sym_val, dw_sym_bits. f_equal. f_equal. lia.
Qed.
