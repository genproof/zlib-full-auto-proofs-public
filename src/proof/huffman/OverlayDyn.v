(** * Lemma (i), proved: [Overlay.overlay_statement]

    The three outcomes of [flush_call]: no call (stored block); the static call ([FlushStatic.static_overlay]); the
    dynamic call, from [DynSum.dyn_sum]: the empty block cannot be dynamic (opt_len >= 26 > static_len = 7); for
    lit_bufsize <= 2048 the lengths are the Huffman depths and [BlockFacts.block_facts] holds with shifts 0
    ([CertData.overlay_bound_75], the header against bit-length codes from [ds_tau] at lit_bufsize <= 256); for
    lit_bufsize >= 4096 [BlockFactsD.block_facts_d] holds for the Huffman depths [dd] / [dd0] and the repair overhead
    X of the actual lengths is at most 632 (L + 2) / 540 <= slack L ([CertD.overlay_bound_d]).  The header writes
    stay below the symbols because the bound at k = 0 puts the bit position after the header below 8 L. *)

From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.huffman.Model Zlib.proof.huffman.HuffAbs Zlib.proof.huffman.Bits
               Zlib.proof.huffman.Overlay Zlib.proof.huffman.Header Zlib.proof.huffman.BlockFacts
               Zlib.proof.huffman.BlockFactsD Zlib.proof.huffman.Cert Zlib.proof.huffman.CertData
               Zlib.proof.huffman.CertD Zlib.proof.huffman.FlushStatic Zlib.proof.huffman.DynSum.
Import ListNotations.
Local Open Scope Z_scope.

(** ** Sums *)

Lemma zsum_ext' : forall n g h, (forall i, 0 <= i < n -> g i = h i) -> zsum n g = zsum n h.
Proof. intros n g h H. rewrite !zsum_rs. apply rs_ext. intros i Hi. apply H. lia. Qed.

Lemma zsum_le' : forall n g h, (forall i, 0 <= i < n -> g i <= h i) -> zsum n g <= zsum n h.
Proof. intros n g h H. rewrite !zsum_rs. apply rs_le. intros i Hi. apply H. lia. Qed.

Lemma zsum_nonneg' : forall n g, (forall i, 0 <= i < n -> 0 <= g i) -> 0 <= zsum n g.
Proof. intros n g H. rewrite !zsum_rs. apply rs_nonneg. intros i Hi. apply H. lia. Qed.

Lemma zsum_sub : forall n g h, zsum n (fun i => g i - h i) = zsum n g - zsum n h.
Proof.
  intros n g h. rewrite !zsum_rs.
  rewrite (rs_ext _ 0 (fun i => g i - h i) (fun i => g i + (-1) * h i)) by (intros; lia).
  rewrite rs_add, rs_scal. lia.
Qed.

Lemma zsum_mul_sub : forall n f a b,
  zsum n (fun i => f i * (a i - b i)) = zsum n (fun i => f i * a i) - zsum n (fun i => f i * b i).
Proof.
  intros. rewrite <- zsum_sub. apply zsum_ext'. intros; ring.
Qed.

Lemma lfreq_nonneg : forall syms c, 0 <= lfreq syms c.
Proof.
  intros. unfold lfreq. assert (H := Zlength_nonneg (filter (fun s => lcode_of s =? c) syms)).
  destruct (c =? END_BLOCK); lia.
Qed.

Lemma dfreq_nonneg : forall syms d, 0 <= dfreq syms d.
Proof. intros. apply Zlength_nonneg. Qed.

Lemma dyn_stat_diff : forall syms ll dl0,
  dyn_data syms ll dl0 - stat_data syms =
  zsum L_CODES (fun c => lfreq syms c * (Znth c ll - Znth c static_ltree_len)) +
  zsum D_CODES (fun d => dfreq syms d * (Znth d dl0 - 5)).
Proof.
  intros. unfold dyn_data, stat_data.
  assert (A := zsum_sub L_CODES (fun c => lfreq syms c * (Znth c ll + xl c))
                 (fun c => lfreq syms c * (Znth c static_ltree_len + xl c))).
  assert (B := zsum_sub D_CODES (fun d => dfreq syms d * (Znth d dl0 + xd d)) (fun d => dfreq syms d * (5 + xd d))).
  rewrite (zsum_ext' L_CODES (fun c => lfreq syms c * (Znth c ll - Znth c static_ltree_len))
             (fun c => lfreq syms c * (Znth c ll + xl c) - lfreq syms c * (Znth c static_ltree_len + xl c)))
    by (intros; ring).
  rewrite (zsum_ext' D_CODES (fun d => dfreq syms d * (Znth d dl0 - 5))
             (fun d => dfreq syms d * (Znth d dl0 + xd d) - dfreq syms d * (5 + xd d))) by (intros; ring).
  rewrite A, B. ring.
Qed.

(** The empty block: only END_BLOCK. *)
Lemma empty_diff : forall ll dl0,
  dyn_data [] ll dl0 - stat_data [] = Znth END_BLOCK ll - Znth END_BLOCK static_ltree_len.
Proof.
  intros. rewrite dyn_stat_diff.
  rewrite (zsum_ext' D_CODES _ (fun _ => 0)) by (intros; unfold dfreq; simpl filter; rewrite Zlength_nil; lia).
  rewrite (zsum_ext' L_CODES _ (fun c => if c =? END_BLOCK then Znth END_BLOCK ll - Znth END_BLOCK static_ltree_len else 0)).
  2:{ intros c Hc. unfold lfreq. simpl filter. rewrite Zlength_nil.
      destruct (Z.eqb_spec c END_BLOCK); subst; lia. }
  rewrite !zsum_rs, rs_ind by (unfold END_BLOCK, L_CODES; simpl; lia).
  rewrite rs_zero by (intros; reflexivity). lia.
Qed.

(** ** The repair overhead of a prefix *)

Section Ovh.
Variables (ll dl0 dd dd0 : list Z).

Definition h1 (j : Z) : Z := Z.max 0 (Znth j ll - Znth j dd).
Definition h2 (j : Z) : Z := if j =? 30 then 0 else Z.max 0 (Znth j dl0 - Znth j dd0).
Definition ovh (x : Z * Z) : Z := h1 (lcode_of x) + h2 (dkey x).

Lemma ovh_nonneg : forall x, 0 <= ovh x.
Proof. intros. unfold ovh, h1, h2. destruct (dkey x =? 30); lia. Qed.

Lemma sym_ovh : forall x, valid_sym (fst x) (snd x) ->
  sym_cost ll dl0 (fst x) (snd x) <= sym_cost dd dd0 (fst x) (snd x) + ovh x.
Proof.
  intros x Hv. unfold ovh, h1, h2, sym_cost.
  destruct (lcode_range cert128 x Hv) as [[E1 [E2 _]]|[E1 [E2 _]]];
  destruct (dkey_range cert128 x Hv) as [[F1 F2]|[F1 [F2 [F3 _]]]]; try congruence.
  - rewrite E1, E2, F2. simpl. lia.
  - rewrite E2, F2. replace (fst x =? 0) with false by (symmetry; apply Z.eqb_neq; auto).
    replace (d_code (fst x - 1) =? 30) with false by (symmetry; apply Z.eqb_neq; lia). lia.
Qed.

Lemma prefix_ovh : forall l k, (forall x, In x l -> valid_sym (fst x) (snd x)) ->
  cost_sum ll dl0 (firstn k l) <= cost_sum dd dd0 (firstn k l) + hsum (map ovh l).
Proof.
  induction l as [|x l IH]; intros k Hv.
  - destruct k; simpl; lia.
  - destruct k as [|k].
    + simpl. assert (0 <= hsum (map ovh l)) by (apply sumZ_nonneg; intros; apply ovh_nonneg).
      assert (H0 := ovh_nonneg x). lia.
    + destruct x as [d c]. cbn [firstn cost_sum map HuffAbs.sumZ].
      assert (H1 := sym_ovh (d, c) (Hv _ (or_introl eq_refl))). simpl in H1.
      assert (H2 := IH k ltac:(intros; apply Hv; right; auto)). lia.
Qed.

Lemma ovh_sum : forall syms, (forall x, In x syms -> valid_sym (fst x) (snd x)) ->
  hsum (map ovh syms) <=
  zsum L_CODES (fun c => lfreq syms c * Z.max 0 (Znth c ll - Znth c dd)) +
  zsum D_CODES (fun d => dfreq syms d * Z.max 0 (Znth d dl0 - Znth d dd0)).
Proof.
  intros syms Hv. unfold ovh. rewrite (hsum_map_add (fun x => h1 (lcode_of x)) (fun x => h2 (dkey x))).
  assert (K1 : forall x, In x syms -> 0 <= lcode_of x < 286).
  { intros x Hx. destruct (lcode_range cert128 x (Hv x Hx)) as [[_ [-> ?]]|[_ [-> [? _]]]]; lia. }
  assert (K2 : forall x, In x syms -> 0 <= dkey x < 31).
  { intros x Hx. destruct (dkey_range cert128 x (Hv x Hx)) as [[_ ->]|[_ [-> [? _]]]]; lia. }
  rewrite (sum_by_key lcode_of h1 286 syms K1), (sum_by_key dkey h2 31 syms K2).
  apply Z.add_le_mono.
  - apply zsum_le'. intros j Hj. unfold lfreq, h1.
    assert (0 <= Z.max 0 (Znth j ll - Znth j dd)) by lia.
    assert (0 <= (if j =? END_BLOCK then 1 else 0)) by (destruct (j =? END_BLOCK); lia). nia.
  - rewrite !zsum_rs. change (Z.to_nat 31) with (S 30). rewrite rs_snoc. simpl (0 + Z.of_nat 30).
    unfold h2 at 2. rewrite Z.eqb_refl, Z.mul_0_l, Z.add_0_r. change (Z.to_nat D_CODES) with 30%nat.
    apply Z.eq_le_incl. apply rs_ext. intros d Hd. unfold h2.
    replace (d =? 30) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Z.mul_comm. f_equal.
    unfold dfreq. f_equal. apply filter_ext_in. intros x Hx. unfold dkey.
    destruct (Z.eqb_spec (fst x) 0).
    + cbn [negb andb]. apply Z.eqb_neq. lia.
    + reflexivity.
Qed.

End Ovh.

(** ** The bound for a dynamic block *)

Lemma dyn_bound : forall s syms stored_len s' olb slb mbi ll dl0 dd dd0 Hh E,
  flush_pre s syms -> dyn_sum s syms stored_len s' olb slb mbi ll dl0 dd dd0 Hh E ->
  Hh + dyn_data syms ll dl0 + E + 1 <= stat_data syms -> syms <> [] ->
  forall k, (k <= length syms)%nat ->
    o_bi_valid (tr_out s) + 3 + Hh + cost_sum ll dl0 (firstn k syms) <= 8 * (tr_lit_bufsize s + 3 * Z.of_nat k).
Proof.
  intros s syms stored_len s' olb slb mbi ll dl0 dd dd0 Hh E HP HD HA Hne k Hk.
  destruct HP as [[ml [Hml EL]] [Hok [Hp0 [Hbv HlenO]]] [Hsn [Hn [Hval Hsy]]] _ _ _ _].
  destruct HD as [Hprep Hkeep Hlists Hguard Hlmax Hdmax Hllen Hdlen Hforced Hkraft Hcodes Hhdr HH Htau Hlenb HE
                  Hcg Hcd Hcs Hddlen Hddkraft Hddcaps Hddopt Hddle Hddrep Hddsmall].
  assert (Hb0 : 0 <= o_bi_valid (tr_out s) <= 7) by (destruct Hok; lia).
  assert (Hn1 : 1 <= Zlength syms).
  { destruct syms as [|x r]; [congruence|]. rewrite Zlength_cons. pose proof (Zlength_nonneg r). lia. }
  assert (Hdiff := dyn_stat_diff syms ll dl0).
  destruct HE as [HE _].
  destruct (Z_le_gt_dec ml 5) as [Hsm|Hbig].
  - assert (HL : tr_lit_bufsize s <= 2048) by (rewrite EL; change 2048 with (2 ^ 11); apply Z.pow_le_mono_r; lia).
    destruct (Hddsmall HL Hne) as [Sl Sd].
    apply (overlay_bound_75 (tr_lit_bufsize s) _ syms ll dl0 (tr_lmax s') (tr_dmax s') Hh 0 0);
      [|intros HL' tau Ht; specialize (Htau ltac:(lia) tau Ht); lia|exact Hk].
    destruct Hddcaps as [Cl Cd]. destruct Hkraft as [Kl Kd]. destruct Hlists as [Ll [Ld _]].
    constructor.
    + exists ml; split; [lia|exact EL].
    + exact Hb0.
    + lia.
    + exact Hval.
    + unfold HEAP_SIZE, L_CODES in *. lia.
    + intros c Hc. destruct (Hllen c Hc) as [_ [_ [A B]]]. split; [apply A|]. intros; apply B; auto.
    + intros c Hc. destruct (Hllen c Hc) as [A [B _]]. split; auto.
    + unfold D_CODES in *. lia.
    + intros d Hd. destruct (Hdlen d Hd) as [_ [_ A]]. exact A.
    + intros d Hd. destruct (Hdlen d Hd) as [A [B _]]. split; auto.
    + exact Hforced.
    + exact Kl.
    + exact Kd.
    + lia.
    + intros c Hc Hf. replace (Znth c ll + 1 - 0) with (Znth c dd + 1) by (rewrite Sl by exact Hc; lia). auto.
    + intros d Hd Hf. replace (Znth d dl0 + 1 - 0) with (Znth d dd0 + 1) by (rewrite Sd by exact Hd; lia). auto.
    + lia.
    + lia.
    + intros HL' tau Ht. specialize (Htau HL' tau Ht). lia.
  - assert (HL : 4096 <= tr_lit_bufsize s) by (rewrite EL; change 4096 with (2 ^ 12); apply Z.pow_le_mono_r; lia).
    set (X := zsum L_CODES (fun c => lfreq syms c * Z.max 0 (Znth c ll - Znth c dd)) +
              zsum D_CODES (fun d => dfreq syms d * Z.max 0 (Znth d dl0 - Znth d dd0))).
    assert (HX0 : 0 <= X).
    { unfold X. assert (0 <= zsum L_CODES (fun c => lfreq syms c * Z.max 0 (Znth c ll - Znth c dd)))
        by (apply zsum_nonneg'; intros; pose proof (lfreq_nonneg syms i); nia).
      assert (0 <= zsum D_CODES (fun d => dfreq syms d * Z.max 0 (Znth d dl0 - Znth d dd0)))
        by (apply zsum_nonneg'; intros; pose proof (dfreq_nonneg syms i); nia).
      lia. }
    assert (HXs : X <= slack (tr_lit_bufsize s)).
    { fold X in Hddrep. assert (Hc : ml = 6 \/ ml = 7 \/ ml = 8 \/ ml = 9) by lia.
      destruct Hc as [-> | [-> | [-> | ->]]]; simpl in EL; rewrite EL in Hddrep |- *; unfold slack; simpl; lia. }
    assert (Hpre := prefix_ovh ll dl0 dd dd0 syms k Hval).
    assert (Hos := ovh_sum ll dl0 dd dd0 syms Hval). fold X in Hos.
    assert (HBD : block_facts_d (tr_lit_bufsize s) (o_bi_valid (tr_out s)) syms dd dd0 Hh).
    { destruct Hddlen as [Dl Dd]. destruct Hddkraft as [Kl Kd]. destruct Hddcaps as [Cl Cd].
      destruct Hlists as [_ [_ [Ll Ld]]].
      assert (A1 := zsum_mul_sub L_CODES (lfreq syms) (fun c => Znth c dd) (fun c => Znth c static_ltree_len)).
      assert (A2 := zsum_mul_sub L_CODES (lfreq syms) (fun c => Znth c ll) (fun c => Znth c static_ltree_len)).
      assert (A3 := zsum_mul_sub D_CODES (dfreq syms) (fun d => Znth d dd0) (fun _ => 5)).
      assert (A4 := zsum_mul_sub D_CODES (dfreq syms) (fun d => Znth d dl0) (fun _ => 5)).
      cbv beta in A1, A2, A3, A4.
      constructor.
      + exists ml; split; [lia|exact EL].
      + exact Hb0.
      + lia.
      + exact Hval.
      + lia.
      + intros c Hc. apply (Dl c Hc). exact Hne.
      + intros c Hc. apply (Dl c Hc).
      + intros d Hd. apply (Dd d Hd).
      + intros d Hd. apply (Dd d Hd).
      + exact (Kl Hne).
      + exact Kd.
      + exact Cl.
      + exact Cd.
      + lia.
      + lia. }
    assert (Hd := overlay_bound_d _ _ _ _ _ _ X HBD (conj HX0 HXs) k Hk).
    lia.
Qed.

(** Frequencies of the codes a symbol of the block uses. *)
Lemma lfreq_in : forall syms x, In x syms -> 0 < lfreq syms (lcode_of x).
Proof.
  intros syms x Hx. unfold lfreq.
  assert (Hi : In x (filter (fun s => lcode_of s =? lcode_of x) syms)) by (apply filter_In; split; auto; apply Z.eqb_refl).
  destruct (filter (fun s => lcode_of s =? lcode_of x) syms) as [|y r]; [contradiction|].
  rewrite Zlength_cons. pose proof (Zlength_nonneg r). destruct (lcode_of x =? END_BLOCK); lia.
Qed.

Lemma dfreq_in : forall syms x, In x syms -> fst x <> 0 -> 0 < dfreq syms (d_code (fst x - 1)).
Proof.
  intros syms x Hx Hd. unfold dfreq.
  assert (Hi : In x (filter (fun s => negb (fst s =? 0) && (d_code (fst s - 1) =? d_code (fst x - 1))) syms)).
  { apply filter_In; split; auto. rewrite Z.eqb_refl. apply Z.eqb_neq in Hd. rewrite Hd. reflexivity. }
  destruct (filter _ syms) as [|y r]; [contradiction|].
  rewrite Zlength_cons. pose proof (Zlength_nonneg r). lia.
Qed.

Lemma lfreq_end : forall syms, 1 <= lfreq syms END_BLOCK.
Proof. intros. unfold lfreq. rewrite Z.eqb_refl. pose proof (Zlength_nonneg (filter (fun s => lcode_of s =? END_BLOCK) syms)). lia. Qed.

(** ** The dynamic call *)

Lemma dyn_overlay : forall s syms stored_len s' olb slb mbi ll dl0 dd dd0 Hh E last,
  flush_pre s syms -> dyn_sum s syms stored_len s' olb slb mbi ll dl0 dd dd0 Hh E -> 0 <= last <= 1 -> slb <> olb ->
  overlay_ok (tr_lit_bufsize s) syms
    (send_all_trees (send_bits (tr_out s') (Z.shiftl DYN_TREES 1 + last) 3)
       (tr_ltree s') (tr_dtree s') (tr_bltree s') (tr_lmax s' + 1) (tr_dmax s' + 1) (mbi + 1),
     fc (tr_ltree s'), dl (tr_ltree s'), fc (tr_dtree s'), dl (tr_dtree s')).
Proof.
  intros s syms stored_len s' olb slb mbi ll dl0 dd dd0 Hh E last HP HD Hlast Hneq.
  assert (HA : Hh + dyn_data syms ll dl0 + E + 1 <= stat_data syms).
  { destruct (ds_lenb _ _ _ _ _ _ _ _ _ _ _ _ _ HD) as [Eslb Eolb]. rewrite Eolb in Hneq.
    destruct ((slb <=? (Hh + dyn_data syms ll dl0 + E + 10) / 8) || (tr_strategy s =? Z_FIXED)) eqn:C;
      [congruence|].
    apply orb_false_iff in C. destruct C as [C1 _]. apply Z.leb_gt in C1. rewrite Eslb in C1.
    destruct (Z_le_gt_dec (stat_data syms) (Hh + dyn_data syms ll dl0 + E)) as [Hle|Hgt]; [|lia].
    assert ((stat_data syms + 10) / 8 <= (Hh + dyn_data syms ll dl0 + E + 10) / 8) by (apply Z.div_le_mono; lia).
    lia. }
  assert (Hne : syms <> []).
  { intros ->. assert (D := empty_diff ll dl0).
    assert (S7 : Znth END_BLOCK static_ltree_len = 7) by reflexivity.
    destruct (ds_llen _ _ _ _ _ _ _ _ _ _ _ _ _ HD END_BLOCK ltac:(unfold END_BLOCK, L_CODES; lia)) as [L0 _].
    destruct (ds_H _ _ _ _ _ _ _ _ _ _ _ _ _ HD) as [H26 _].
    destruct (ds_E _ _ _ _ _ _ _ _ _ _ _ _ _ HD) as [[E0 _] _].
    lia. }
  assert (Hbound := dyn_bound s syms stored_len s' olb slb mbi ll dl0 dd dd0 Hh E HP HD HA Hne).
  destruct (ds_keep _ _ _ _ _ _ _ _ _ _ _ _ _ HD) as [K1 [K2 [K3 K4]]].
  destruct (ds_codes _ _ _ _ _ _ _ _ _ _ _ _ _ HD) as [Cl Cd].
  assert (Hllen := ds_llen _ _ _ _ _ _ _ _ _ _ _ _ _ HD).
  assert (Hdlen := ds_dlen _ _ _ _ _ _ _ _ _ _ _ _ _ HD).
  assert (Hcg := ds_cost_guard _ _ _ _ _ _ _ _ _ _ _ _ _ HD).
  destruct HP as [_ [Hok [Hp0 [Hbv HlenO]]] [Hsn [Hn [Hval Hsy]]] _ _ _ _].
  rewrite K1.
  assert (Hval3 : 0 <= Z.shiftl DYN_TREES 1 + last < 2 ^ 3)
    by (change (Z.shiftl DYN_TREES 1) with 4; change (2 ^ 3) with 8; lia).
  destruct (send_bits_spec (tr_out s) (Z.shiftl DYN_TREES 1 + last) 3 Hok ltac:(lia) Hval3) as [B1 [_ [Ok1 [_ W1]]]].
  set (o1 := send_bits (tr_out s) (Z.shiftl DYN_TREES 1 + last) 3) in *.
  destruct (ds_hdr _ _ _ _ _ _ _ _ _ _ _ _ _ HD o1 Ok1) as [Ok2 [B2 W2]].
  set (o2 := send_all_trees o1 (tr_ltree s') (tr_dtree s') (tr_bltree s') (tr_lmax s' + 1) (tr_dmax s' + 1) (mbi + 1))
    in *.
  assert (Hpend : o_pending o2 <= tr_lit_bufsize s).
  { assert (H0 := Hbound O ltac:(lia)). cbn [firstn cost_sum Z.of_nat] in H0. destruct Ok2 as [V2 _].
    unfold Bits.bitpos, Header.bitpos in B2, B1. lia. }
  destruct W1 as [W1a [W1b [W1c W1d]]]. destruct W2 as [W2a [W2b [W2c W2d]]].
  assert (Hsc : forall x, In x syms ->
            sym_codes_ok (fc (tr_ltree s')) (dl (tr_ltree s')) (fc (tr_dtree s')) (dl (tr_dtree s')) (fst x) (snd x)).
  { intros x Hx. assert (Hv := Hval x Hx). assert (Hf := lfreq_in syms x Hx). unfold sym_codes_ok.
    destruct (lcode_range cert128 x Hv) as [[E1 [E2 R]]|[E1 [E2 [R _]]]].
    - rewrite E1, Z.eqb_refl. rewrite E2 in Hf. apply Cl; [unfold L_CODES; lia|].
      apply (Hllen (snd x) ltac:(unfold L_CODES; lia)). exact Hf.
    - replace (fst x =? 0) with false by (symmetry; apply Z.eqb_neq; auto). rewrite E2 in Hf. split.
      + apply Cl; [unfold L_CODES; lia|].
        assert (Hr : 0 <= Znth (snd x) length_code_tab + 257 < L_CODES) by (unfold L_CODES; lia).
        apply (Hllen _ Hr). exact Hf.
      + assert (Hg := dfreq_in syms x Hx E1). destruct Hv as [_ Hv].
        destruct (dist_code_facts (fst x - 1) ltac:(lia)) as [D1 _].
        apply Cd; [unfold D_CODES; lia|].
        assert (Hr : 0 <= d_code (fst x - 1) < D_CODES) by (unfold D_CODES; lia).
        apply (Hdlen _ Hr). exact Hg. }
  unfold overlay_ok. split; [exact Ok2|]. split; [lia|]. split.
  { intros i Hi. rewrite W2d by lia. rewrite W1d by lia. apply Hsy; auto. }
  split; [exact Hsc|].
  split.
  { apply Cl; [unfold END_BLOCK, L_CODES; lia|]. apply (Hllen END_BLOCK ltac:(unfold END_BLOCK, L_CODES; lia)).
    pose proof (lfreq_end syms). lia. }
  intros k Hk.
  assert (Hs : forall x, In x (firstn k syms) -> valid_sym (fst x) (snd x) /\
               sym_codes_ok (fc (tr_ltree s')) (dl (tr_ltree s')) (fc (tr_dtree s')) (dl (tr_dtree s')) (fst x) (snd x))
    by (intros x Hx; apply firstn_In in Hx; split; [apply Hval, Hx|apply Hsc, Hx]).
  destruct (compress_sep_spec (firstn k syms) o2 _ _ _ _ Ok2 Hs) as [_ [Hb _]].
  rewrite Hb, Hcg. assert (Hk' := Hbound k Hk). unfold Bits.bitpos, Header.bitpos in *. lia.
Qed.

Theorem overlay_proof : dyn_sum_statement -> overlay_statement.
Proof.
  intros Hds s syms buf stored_len last HP Hlast c Hc.
  assert (Hstat : forall s', tr_out s' = tr_out s ->
            overlay_ok (tr_lit_bufsize s) syms (send_bits (tr_out s') (Z.shiftl STATIC_TREES 1 + last) 3,
              static_ltree_code, static_ltree_len, static_dtree_code, static_dtree_len)).
  { intros s' E. rewrite E.
    destruct HP as [[ml [Hml EL]] [Hok [Hp0 [Hbv HlenO]]] [Hsn [Hn [Hval Hsy]]] _ _ _ _].
    assert (HL : 128 <= tr_lit_bufsize s) by (rewrite EL; change 128 with (2 ^ 7); apply Z.pow_le_mono_r; lia).
    apply static_overlay; auto. }
  unfold flush_call in Hc.
  destruct (Z_lt_le_dec 0 (tr_level s)) as [Hlv|Hlv].
  - destruct (Hds s syms stored_len HP Hlv) as (s' & olb & slb & mbi & ll & dl0 & dd & dd0 & Hh & E & HD).
    rewrite (ds_prep _ _ _ _ _ _ _ _ _ _ _ _ _ HD) in Hc.
    destruct (ds_keep _ _ _ _ _ _ _ _ _ _ _ _ _ HD) as [K1 [K2 [K3 K4]]].
    destruct buf as [b|].
    + destruct (u64 (stored_len + 4) <=? olb); [discriminate|].
      destruct (Z.eqb_spec slb olb) as [Eq|Neq]; injection Hc as <-.
      * apply Hstat; exact K1.
      * eapply dyn_overlay; eauto.
    + destruct (Z.eqb_spec slb olb) as [Eq|Neq]; injection Hc as <-.
      * apply Hstat; exact K1.
      * eapply dyn_overlay; eauto.
  - unfold flush_prep in Hc.
    replace (tr_level s >? 0) with false in Hc by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
    rewrite Z.eqb_refl in Hc. destruct buf as [b|].
    + destruct (u64 (stored_len + 4) <=? u64 (stored_len + 5)); [discriminate|].
      injection Hc as <-. apply Hstat; reflexivity.
    + injection Hc as <-. apply Hstat; reflexivity.
Qed.
