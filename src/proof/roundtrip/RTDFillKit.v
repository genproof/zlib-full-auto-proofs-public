(* RT-D part FILL: kit of rtd_fill_ok: the hash-priming identity, the chains with their positions
   below strstart, and the effect of each step of fill_window on the window, the chains and ins_h. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDSpecs.
Require Export Zlib.proof.roundtrip.RTDLTCFill.
Require Export Zlib.proof.roundtrip.RTDLTCFillKit.
Import ListNotations.
Local Open Scope Z_scope.

(** ** UPDATE_HASH bit by bit *)
Lemma uh_testbit s h c n : prm s ->
  Z.testbit (update_hash s h c) n =
    (n <? d_hash_bits s) && xorb (Z.testbit h (n - d_hash_shift s)) (Z.testbit c n).
Proof.
  intros (_ & _ & _ & Hhb & Hhs & Hhm & Hsh & _).
  assert (Hsh0 : 0 <= d_hash_shift s) by (rewrite Hsh; apply Z.div_pos; lia).
  destruct (Z_lt_le_dec n 0) as [Hn|Hn].
  { rewrite !Z.testbit_neg_r by lia.
    destruct (n <? d_hash_bits s); reflexivity. }
  unfold update_hash.
  assert (Hm : d_hash_mask s = Z.ones (d_hash_bits s)) by (rewrite Hhm, Hhs, Z.ones_equiv; lia).
  rewrite Hm.
  assert (Hr : 0 <= Z.land (Z.lxor (u32 (Z.shiftl h (d_hash_shift s))) c) (Z.ones (d_hash_bits s)) < 4294967296).
  { rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound (Z.lxor (u32 (Z.shiftl h (d_hash_shift s))) c) (2 ^ d_hash_bits s)
      ltac:(apply Z.pow_pos_nonneg; lia)).
    assert (2 ^ d_hash_bits s <= 2 ^ 16) by (apply Z.pow_le_mono_r; lia). change (2 ^ 16) with 65536 in *. lia. }
  unfold u32 at 1. rewrite Z.mod_small by exact Hr.
  rewrite Z.land_spec, Z.lxor_spec.
  destruct (Z_lt_le_dec n (d_hash_bits s)) as [Hlt|Hge].
  - rewrite Z.ones_spec_low by lia. replace (n <? d_hash_bits s) with true by (symmetry; apply Z.ltb_lt; lia).
    unfold u32. change 4294967296 with (2 ^ 32). rewrite Z.mod_pow2_bits_low by lia.
    destruct (Z_lt_le_dec n (d_hash_shift s)).
    + rewrite Z.shiftl_spec_low by lia. rewrite (Z.testbit_neg_r h (n - d_hash_shift s)) by lia. rewrite !andb_true_r. reflexivity.
    + rewrite Z.shiftl_spec by lia. rewrite andb_true_r. reflexivity.
  - rewrite Z.ones_spec_high by lia. replace (n <? d_hash_bits s) with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite andb_false_r. reflexivity.
Qed.

(** three UPDATE_HASHes forget the initial value *)
Lemma uh3 s h0 a b c : prm s ->
  update_hash s (update_hash s (update_hash s h0 a) b) c = update_hash s (update_hash s a b) c.
Proof.
  intros P. pose proof P as (_ & _ & _ & Hhb & _ & _ & Hsh & _).
  assert (Hsh3 : d_hash_bits s <= 3 * d_hash_shift s).
  { rewrite Hsh. pose proof (Z.mul_div_le (d_hash_bits s + 2) 3 ltac:(lia)).
    pose proof (Z.mod_pos_bound (d_hash_bits s + 2) 3 ltac:(lia)).
    pose proof (Z.div_mod (d_hash_bits s + 2) 3 ltac:(lia)). lia. }
  assert (Hsh0 : 0 <= d_hash_shift s) by (rewrite Hsh; apply Z.div_pos; lia).
  apply Z.bits_inj'. intros n Hn.
  rewrite !uh_testbit by exact P.
  destruct (Z.ltb_spec n (d_hash_bits s)); [|reflexivity]. rewrite !andb_true_l.
  replace (n - d_hash_shift s <? d_hash_bits s) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (n - d_hash_shift s - d_hash_shift s <? d_hash_bits s) with true by (symmetry; apply Z.ltb_lt; lia).
  rewrite !andb_true_l.
  rewrite (Z.testbit_neg_r h0 (n - d_hash_shift s - d_hash_shift s - d_hash_shift s)) by lia. reflexivity.
Qed.

Lemma uh0 s c : prm s -> 0 <= c < 256 -> update_hash s 0 c = c.
Proof.
  intros P Hc. pose proof P as (_ & _ & _ & Hhb & Hhs & Hhm & Hsh & _).
  assert (Hsh0 : 0 <= d_hash_shift s) by (rewrite Hsh; apply Z.div_pos; lia).
  apply Z.bits_inj'. intros n Hn. rewrite uh_testbit by exact P.
  rewrite Z.testbit_0_l. cbn [xorb].
  destruct (Z.ltb_spec n (d_hash_bits s)); [reflexivity|].
  symmetry. apply (Z.bits_above_log2 c n); [lia|].
  destruct (Z.eq_dec c 0) as [->|Hc0]; [cbn; lia|].
  assert (Z.log2 c < 8) by (apply Z.log2_lt_pow2; lia). lia.
Qed.

(** INSERT_STRING with ins_h primed for p computes h3 p *)
Lemma primed_h3 s p : prm s -> primed s p ->
  update_hash s (d_ins_h s) (Znth (p + 2) (mb_val (d_window s))) = h3 s p.
Proof.
  intros P [h0 E]. rewrite E, uh3 by exact P. unfold h3. replace (p + 1 + 1) with (p + 2) by lia. reflexivity.
Qed.

(** ** The chains with their positions below strstart (chain_hok and chain_ok together) *)
Definition chk2 (s : dstate) : Prop :=
  forall b, 0 <= b < d_hash_size s ->
  exists Gb : Z -> Prop,
    Gb (Znth b (d_head s)) /\
    forall q, Gb q -> 0 < q -> lim s <= q ->
      q < d_strstart s /\ q + 2 < d_strstart s + d_lookahead s /\ h3 s q = b /\
      Gb (Znth (Z.land q (d_w_mask s)) (d_prev s)).

Lemma chk2_hok s : chk2 s -> chain_hok s.
Proof.
  intros C b Hb. destruct (C b Hb) as (Gb & G1 & G2). exists Gb. split; [exact G1|].
  intros q Gq Hq Hl. destruct (G2 q Gq Hq Hl) as (_ & A & B & D). auto.
Qed.

Lemma hok_chk2 s : chain_ok s -> chain_hok s -> chk2 s.
Proof.
  intros (G & G1 & G2 & G3) C b Hb. destruct (C b Hb) as (Gb & B1 & B2).
  exists (fun q => Gb q /\ G q). split; [split; [exact B1|apply G2; exact Hb]|].
  intros q [Gq Gq'] Hq Hl. destruct (B2 q Gq Hq Hl) as (A1 & A2 & A3).
  split; [destruct (G1 q Gq'); lia|]. split; [exact A1|]. split; [exact A2|].
  split; [exact A3|]. apply G3; auto.
Qed.

(* ins_h primed for strstart once lookahead >= MIN_MATCH *)
Definition Pr (s : dstate) : Prop :=
  MIN_MATCH <= d_lookahead s -> d_insert s = 0 /\ primed s (d_strstart s).

Lemma uh_keep s s' : fw_keep s' = fw_keep s -> update_hash s' = update_hash s.
Proof.
  intros E. assert (E1 := f_equal d_hash_shift E). assert (E2 := f_equal d_hash_mask E). cbn in E1, E2.
  unfold update_hash. rewrite E1, E2. reflexivity.
Qed.

(** ** The slide *)
Lemma slide_shape s s1 m1 : fill_pre s ->
  c_fw_slide s (u32 (d_window_size s - d_lookahead s - d_strstart s)) = Some (s1, m1) ->
  s1 = s \/
  (d_w_size s + MAX_DIST s <= d_strstart s /\ d_strstart s1 = d_strstart s - d_w_size s /\
   d_lookahead s1 = d_lookahead s /\ d_insert s1 = Z.min (d_insert s) (d_strstart s - d_w_size s) /\
   d_ins_h s1 = d_ins_h s /\ d_head s1 = map (slide_entry (d_w_size s)) (d_head s) /\
   d_prev s1 = map (slide_entry (d_w_size s)) (d_prev s) /\ fw_keep s1 = fw_keep s /\
   (forall i, 0 <= i < d_strstart s + d_lookahead s - d_w_size s ->
      Znth i (mb_val (d_window s1)) = Znth (i + d_w_size s) (mb_val (d_window s)))).
Proof.
  intros Hf. pose proof Hf as Hf0. destruct Hf as (Hp & Hws & Hwp & Hww & Hc).
  pose proof Hp as Hp0. destruct Hp as (Hwb & Hw & Hm & Hhb & Hhs & _).
  destruct Hws as (Hlv & Hok & Hwsz & Hlp & Hlh).
  destruct Hwp as (Hla & Hss & Hsl & Hbs & Hbd & Hbn & Hins & Hinsw & Hhw).
  assert (MD : MAX_DIST s = d_w_size s - 262) by reflexivity.
  assert (W1 : 512 <= d_w_size s <= 32768).
  { rewrite Hw. split; [change 512 with (2 ^ 9)|change 32768 with (2 ^ 15)];
      apply Z.pow_le_mono_r; lia. }
  assert (Emore : u32 (d_window_size s - d_lookahead s - d_strstart s) =
                  d_window_size s - d_lookahead s - d_strstart s) by (apply u32_small; lia).
  rewrite Emore. unfold c_fw_slide.
  assert (Eg : u32 (d_w_size s + u32 (d_w_size s - MIN_LOOKAHEAD)) = d_w_size s + MAX_DIST s).
  { rewrite MD. change MIN_LOOKAHEAD with 262. rewrite (u32_small (d_w_size s - 262)) by lia.
    apply u32_small; lia. }
  rewrite Eg.
  destruct (d_strstart s >=? d_w_size s + MAX_DIST s) eqn:Ess.
  2:{ intros E. injection E as <- _. left. reflexivity. }
  rewrite Z.geb_leb, Z.leb_le in Ess.
  set (w := d_w_size s) in *. set (ss := d_strstart s) in *. set (la := d_lookahead s) in *.
  assert (E1 : u32 (w - (d_window_size s - la - ss)) = ss + la - w) by (rewrite u32_small by lia; lia).
  rewrite E1. replace (ss + la - w <=? w) with true by (symmetry; apply Z.leb_le; lia). cbn [guard bind].
  assert (E2 : mb_read (d_window s) w (ss + la - w) = Some (sublist w (ss + la) (mb_val (d_window s)))).
  { unfold mb_read. rewrite mb_definedb_true by (try lia; intros i Hi; apply Hww; lia).
    replace (0 <=? ss + la - w) with true by (symmetry; apply Z.leb_le; lia). cbn. f_equal; f_equal; lia. }
  rewrite E2. cbn [bind].
  destruct (mb_write (d_window s) 0 (sublist w (ss + la) (mb_val (d_window s)))) as [win|] eqn:Ew.
  2:{ rewrite mb_write_some in Ew. discriminate. lia. rewrite Zlength_sublist; lia. }
  cbn [bind]. fw_proj.
  replace (in_long (d_block_start s - w)) with true by (symmetry; unfold in_long; apply andb_true_iff; split; apply Z.leb_le; lia).
  cbn [guard bind]. change (d_strstart s) with ss.
  rewrite (u32_small (ss - w)) by lia.
  set (s1' := if d_insert s >? ss - w then _ else _).
  assert (S1 : d_window s1' = win /\ d_strstart s1' = ss - w /\ d_insert s1' = Z.min (d_insert s) (ss - w) /\
    d_head s1' = d_head s /\ d_prev s1' = d_prev s /\ d_lookahead s1' = la /\ d_ins_h s1' = d_ins_h s /\
    d_hash_size s1' = d_hash_size s /\ d_w_size s1' = w /\ fw_keep s1' = fw_keep s).
  { subst s1'. destruct (d_insert s >? ss - w) eqn:Ei.
    - rewrite Z.gtb_ltb, Z.ltb_lt in Ei. unfold fw_keep. fw_proj.
      repeat split; try reflexivity. lia.
    - rewrite Z.gtb_ltb, Z.ltb_ge in Ei. unfold fw_keep. fw_proj.
      repeat split; try reflexivity. lia. }
  clearbody s1'.
  destruct S1 as (S1w & S1ss & S1ins & S1h & S1p & S1la & S1ih & S1hs & S1ws & S1k).
  unfold c_slide_hash. rewrite S1h, S1p, S1hs, S1ws, Hlh, Hlp, !Z.eqb_refl.
  replace (1 <=? d_hash_size s) with true by (symmetry; apply Z.leb_le; rewrite Hhs; assert (0 < 2 ^ d_hash_bits s) by (apply Z.pow_pos_nonneg; lia); lia).
  replace (1 <=? w) with true by (symmetry; apply Z.leb_le; lia).
  cbn [andb guard bind].
  intros E. injection E as <- _. right.
  pose proof (mb_write_spec _ _ _ _ Hok Ew) as (_ & Wl & Wlv & Wld & WZ & Wok).
  rewrite Zlength_sublist in Wl, WZ by lia.
  fw_proj. rewrite S1ss, S1la, S1ins, S1ih, S1w, S1p.
  split; [lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  split; [rewrite <- S1k; unfold fw_keep; fw_proj; reflexivity|].
  intros i Hi. destruct (WZ i ltac:(lia)) as [_ D]. rewrite D.
  replace ((0 <=? i) && (i <? 0 + (ss + la - w))) with true
    by (symmetry; apply andb_true_iff; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
  rewrite Znth_sublist by lia. f_equal; lia.
Qed.

Lemma keep_hash s s' : fw_keep s' = fw_keep s ->
  d_w_size s' = d_w_size s /\ d_w_mask s' = d_w_mask s /\ d_hash_size s' = d_hash_size s /\
  MAX_DIST s' = MAX_DIST s /\ update_hash s' = update_hash s.
Proof.
  intros E. assert (E1 := f_equal d_w_size E). assert (E2 := f_equal d_w_mask E).
  assert (E3 := f_equal d_hash_size E). cbn in E1, E2, E3.
  split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [unfold MAX_DIST; rewrite E1; reflexivity|].
  apply uh_keep; exact E.
Qed.

Lemma slide_props s s1 m1 H : fill_pre s ->
  c_fw_slide s (u32 (d_window_size s - d_lookahead s - d_strstart s)) = Some (s1, m1) ->
  (kwin H s -> kwin H s1) /\ (chk2 s -> chk2 s1) /\ (Pr s -> Pr s1).
Proof.
  intros Hf E. destruct (slide_shape s s1 m1 Hf E) as [->|(Hge & Ss & La & Ins & Ih & Hd & Pv & K & Wv)];
    [auto|].
  pose proof Hf as (Hp & (Hl & Hok & Hwz & Hlp & Hlh) & (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9) & Hww & _).
  pose proof (prm_wsize s Hp) as Hws.
  destruct (fi_prm_facts s Hp) as (_ & _ & _ & Hwm & _).
  destruct (keep_hash s s1 K) as (Kw & Km & Kh & Kd & Ku).
  assert (MD : MAX_DIST s = d_w_size s - 262) by reflexivity.
  set (w := d_w_size s) in *.
  split; [|split].
  - intros (Hk1 & Hk2). unfold kwin. rewrite Ss, La. split; [lia|].
    intros i Hi. rewrite Wv by lia. rewrite Hk2 by lia. f_equal. lia.
  - intros C b Hb. rewrite Kh in Hb. destruct (C b Hb) as (Gb & G1 & G2).
    exists (fun v => exists u, Gb u /\ v = slide_entry w u).
    rewrite Hd, Znth_map by lia. split; [eexists; split; [exact G1|reflexivity]|].
    intros q (u & Gu & ->) Hq Hlq. unfold slide_entry in Hq, Hlq |- *. rewrite Z.geb_leb in Hq, Hlq |- *.
    destruct (Z.leb_spec w u) as [Hu|Hu]; [|unfold NIL in Hq; lia].
    assert (Hlu : lim s <= u).
    { unfold lim in Hlq |- *. rewrite Ss, Kd in Hlq.
      replace (d_strstart s >? MAX_DIST s) with true by (symmetry; apply Z.gtb_lt; lia).
      destruct (Z.gtb_spec (d_strstart s - w) (MAX_DIST s)); lia. }
    destruct (G2 u Gu ltac:(lia) Hlu) as (A1 & A2 & A3 & A4).
    rewrite Ss, La. split; [lia|]. split; [lia|]. split.
    + rewrite <- A3. unfold h3. rewrite Ku, !Wv by lia. f_equal; [f_equal|]; f_equal; lia.
    + rewrite Pv, Km, !Hwm.
      replace ((u - w) mod w) with (u mod w)
        by (replace (u - w) with (u + (-1) * w) by lia; rewrite Z_mod_plus_full; reflexivity).
      rewrite Znth_map by (rewrite Hlp; apply Z.mod_pos_bound; lia).
      eexists; split; [|reflexivity]. rewrite <- Hwm. exact A4.
  - intros Hpr Hla. rewrite La in Hla. unfold MIN_MATCH in Hla. destruct (Hpr ltac:(unfold MIN_MATCH; lia)) as (I0 & h0 & Eh).
    split; [rewrite Ins, I0; lia|]. exists h0. rewrite Ih, Ku, Eh, Ss, !Wv by lia.
    f_equal; [f_equal|]; f_equal; lia.
Qed.

(** ** The hash insertion of fill_window *)
Lemma fi_body' s : fill_pre s -> 0 < d_insert s -> 3 <= d_lookahead s + d_insert s ->
  fw_insert_body (s, d_strstart s - d_insert s) =
    let h := update_hash s (d_ins_h s) (Znth (d_strstart s - d_insert s + 2) (mb_val (d_window s))) in
    if d_lookahead s + d_insert s - 1 <? 3 then Some (inr (fi_next s h))
    else Some (inl (fi_next s h, d_strstart s - d_insert s + 1)).
Proof.
  intros Hf Hi H3. pose proof Hf as (P & Ws & Wp & Ww & _).
  destruct (fi_prm_facts s P) as (Hws & Hhs & Hsh & Hwm & _).
  pose proof Wp as (Wp1 & Wp2 & Wp3 & Wp4 & Wp5 & Wp6 & Wp7 & Wp8 & Wp9).
  pose proof Ws as (Hl & Hok & Hwz & Hlp & Hlh).
  set (str := d_strstart s - d_insert s).
  destruct (fi_mb_rd s (str + 2) Ws Wp Ww) as [Erd Hc]; [unfold str; lia|].
  unfold fw_insert_body. replace (d_insert s =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  unfold guard. replace (d_hash_shift s <? 32) with true by (symmetry; apply Z.ltb_lt; lia). cbn [bind].
  replace (u32 (str + MIN_MATCH - 1)) with (str + 2) by (unfold u32, MIN_MATCH; rewrite Z.mod_small; unfold str; lia).
  rewrite Erd. cbn [bind].
  pose proof (fi_uh_range s (d_ins_h s) (Znth (str + 2) (mb_val (d_window s))) P) as Hh.
  set (h := update_hash s (d_ins_h s) (Znth (str + 2) (mb_val (d_window s)))) in *.
  change (d_head (set_d_ins_h s h)) with (d_head s). change (d_ins_h (set_d_ins_h s h)) with h.
  change (d_prev (set_d_ins_h s h)) with (d_prev s). change (d_w_mask (set_d_ins_h s h)) with (d_w_mask s).
  rewrite fi_rd by lia. cbn [bind].
  rewrite fi_wr by (rewrite Hwm, Hlp; apply Z.mod_pos_bound; lia). cbn [bind].
  change (d_head (set_d_prev (set_d_ins_h s h) ?p)) with (d_head s).
  change (d_ins_h (set_d_prev (set_d_ins_h s h) ?p)) with h.
  rewrite fi_wr by lia. cbn [bind].
  cbn [d_insert d_lookahead set_d_insert set_d_head set_d_prev set_d_ins_h].
  replace (u32 (d_insert s - 1)) with (d_insert s - 1) by (unfold u32; rewrite Z.mod_small; lia).
  replace (u32 (d_lookahead s + (d_insert s - 1))) with (d_lookahead s + d_insert s - 1)
    by (unfold u32; rewrite Z.mod_small; lia).
  replace (u16 str) with str by (unfold u16; rewrite Z.mod_small; unfold str; lia).
  replace (u32 (str + 1)) with (str + 1) by (unfold u32; rewrite Z.mod_small; unfold str; lia).
  unfold MIN_MATCH. reflexivity.
Qed.

(* two live positions in the same prev slot are equal *)
Lemma slot_eq s q str : prm s -> lim s <= q -> 0 < q < d_strstart s ->
  d_strstart s - d_w_size s <= str < d_strstart s -> 0 <= str ->
  Z.land q (d_w_mask s) = Z.land str (d_w_mask s) -> q = str.
Proof.
  intros P Hl Hq Hs Hs0 E.
  destruct (fi_prm_facts s P) as (Hws & _ & _ & Hwm & _).
  rewrite !Hwm in E.
  assert (Hq' : d_strstart s - d_w_size s < q).
  { unfold lim, MAX_DIST, MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in Hl.
    destruct (Z.gtb_spec (d_strstart s) (d_w_size s - (258 + 3 + 1))); lia. }
  assert (D : (q - str) mod d_w_size s = 0) by (rewrite Zminus_mod, E, Z.sub_diag; reflexivity).
  apply Z.mod_divide in D; [|lia]. destruct D as (k & Hk).
  destruct (Z.lt_trichotomy k 0) as [Hk0|[Hk0|Hk0]]; [nia| |nia]. subst k. lia.
Qed.

Lemma chk2_step s : fill_pre s -> chk2 s -> 0 < d_insert s -> 3 <= d_lookahead s + d_insert s ->
  primed s (d_strstart s - d_insert s) ->
  chk2 (fi_next s (h3 s (d_strstart s - d_insert s))).
Proof.
  intros Hf C Hi H3 Hpr.
  pose proof Hf as (P & (Hl & Hok & Hwz & Hlp & Hlh) & (Wp1 & Wp2 & Wp3 & Wp4 & Wp5 & Wp6 & Wp7 & Wp8 & Wp9) & _).
  destruct (fi_prm_facts s P) as (Hws & Hhs & _ & Hwm & _).
  set (str := d_strstart s - d_insert s) in *.
  set (h := h3 s str).
  assert (Hh : 0 <= h < d_hash_size s) by (apply fi_uh_range; exact P).
  assert (Hsl : forall q, 0 <= q -> 0 <= Z.land q (d_w_mask s) < Zlength (d_prev s))
    by (intros q Hq; rewrite Hwm, Hlp; apply Z.mod_pos_bound; lia).
  intros b Hb. change (d_hash_size (fi_next s h)) with (d_hash_size s) in Hb.
  destruct (C b Hb) as (Gb & G1 & G2).
  change (lim (fi_next s h)) with (lim s). change (d_strstart (fi_next s h)) with (d_strstart s).
  change (d_lookahead (fi_next s h)) with (d_lookahead s). change (h3 (fi_next s h)) with (h3 s).
  change (d_w_mask (fi_next s h)) with (d_w_mask s).
  change (d_head (fi_next s h)) with (upd_Znth h (d_head s) str).
  change (d_prev (fi_next s h)) with (upd_Znth (Z.land str (d_w_mask s)) (d_prev s) (Znth h (d_head s))).
  destruct (Z.eq_dec b h) as [->|Nb].
  - exists (fun q => Gb q \/ q = str). rewrite upd_Znth_same by lia. split; [right; reflexivity|].
    intros q Gq Hq Hlq.
    assert (Hstr : forall q', q' = str -> q' < d_strstart s /\ q' + 2 < d_strstart s + d_lookahead s /\ h3 s q' = h /\
        ((Gb (Znth (Z.land q' (d_w_mask s)) (upd_Znth (Z.land str (d_w_mask s)) (d_prev s) (Znth h (d_head s))))) \/
         Znth (Z.land q' (d_w_mask s)) (upd_Znth (Z.land str (d_w_mask s)) (d_prev s) (Znth h (d_head s))) = str)).
    { intros q' ->. split; [unfold str; lia|]. split; [unfold str; lia|]. split; [reflexivity|].
      left. rewrite upd_Znth_same by (apply Hsl; unfold str; lia). exact G1. }
    destruct Gq as [Gq| ->]; [|apply Hstr; reflexivity].
    destruct (G2 q Gq Hq Hlq) as (A1 & A2 & A3 & A4).
    destruct (Z.eq_dec (Z.land q (d_w_mask s)) (Z.land str (d_w_mask s))) as [Es|Ns].
    + assert (q = str) by (apply (slot_eq s); auto; unfold str; lia). apply Hstr. assumption.
    + split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. left.
      rewrite upd_Znth_diff by (try apply Hsl; unfold str in *; lia). exact A4.
  - exists Gb. rewrite upd_Znth_diff by lia. split; [exact G1|].
    intros q Gq Hq Hlq. destruct (G2 q Gq Hq Hlq) as (A1 & A2 & A3 & A4).
    split; [exact A1|]. split; [exact A2|]. split; [exact A3|].
    destruct (Z.eq_dec (Z.land q (d_w_mask s)) (Z.land str (d_w_mask s))) as [Es|Ns].
    + assert (q = str) by (apply (slot_eq s); auto; unfold str; lia). subst q. exfalso. apply Nb. rewrite <- A3. reflexivity.
    + rewrite upd_Znth_diff by (try apply Hsl; unfold str in *; lia). exact A4.
Qed.

Lemma primed_step s p : primed (fi_next s (h3 s p)) (p + 1).
Proof.
  exists (Znth p (mb_val (d_window s))). change (d_ins_h (fi_next s (h3 s p))) with (h3 s p).
  change (update_hash (fi_next s (h3 s p))) with (update_hash s).
  change (d_window (fi_next s (h3 s p))) with (d_window s).
  unfold h3. replace (p + 1 + 1) with (p + 2) by lia. reflexivity.
Qed.

Definition fiI (s0 : dstate) (a : dstate * Z) : Prop :=
  fill_pre (fst a) /\ snd a = d_strstart (fst a) - d_insert (fst a) /\
  3 <= d_lookahead (fst a) + d_insert (fst a) /\ primed (fst a) (snd a) /\ (chk2 s0 -> chk2 (fst a)).

Lemma fi_runs s0 a r : runs fw_insert_body a r -> fiI s0 a -> (chk2 s0 -> chk2 r) /\ Pr r.
Proof.
  induction 1 as [[s str] r Eb|[s str] a' r Eb Hr IH]; intros (Hf & Hstr & H3 & Hpr & Hc); cbn [fst snd] in *; subst str.
  - destruct (Z.eq_dec (d_insert s) 0) as [I0|I0].
    + unfold fw_insert_body in Eb. rewrite I0, Z.eqb_refl in Eb. injection Eb as <-.
      split; [exact Hc|]. unfold Pr; intros _. split; [exact I0|]. rewrite I0, Z.sub_0_r in Hpr. exact Hpr.
    + pose proof Hf as (_ & _ & (_ & _ & _ & _ & _ & _ & Hi & _) & _ & _).
      rewrite (fi_body' s Hf ltac:(lia) H3) in Eb. cbv zeta in Eb.
      destruct (Z.ltb_spec (d_lookahead s + d_insert s - 1) 3) as [Lt|Ge]; [|discriminate].
      injection Eb as <-. rewrite primed_h3 by (try apply Hf; exact Hpr).
      split; [intros C; apply chk2_step; auto; lia|].
      unfold Pr; intros Hla. exfalso. change (d_lookahead (fi_next s (h3 s (d_strstart s - d_insert s)))) with (d_lookahead s) in Hla.
      unfold MIN_MATCH in Hla. lia.
  - destruct (Z.eq_dec (d_insert s) 0) as [I0|I0].
    { unfold fw_insert_body in Eb. rewrite I0, Z.eqb_refl in Eb. discriminate. }
    pose proof Hf as (P & _ & (_ & _ & _ & _ & _ & _ & Hi & _) & _ & _).
    rewrite (fi_body' s Hf ltac:(lia) H3) in Eb. cbv zeta in Eb.
    destruct (Z.ltb_spec (d_lookahead s + d_insert s - 1) 3) as [Lt|Ge]; [discriminate|].
    injection Eb as <-. rewrite primed_h3 in IH by (try apply Hf; exact Hpr).
    apply IH. cbn [fst snd].
    split; [apply fi_next_pre; auto; try lia; apply fi_uh_range; exact P|].
    split; [cbn; lia|]. split; [cbn; lia|].
    split; [apply primed_step|]. intros C; apply chk2_step; auto; lia.
Qed.

Lemma chk2_ins_h s x : chk2 s -> chk2 (set_d_ins_h s x).
Proof. intros C. exact C. Qed.

Lemma ins_props s s' : fill_pre s -> c_fw_insert s = Some s' ->
  fill_pre s' /\ set_d_insert (hc_keep s') 0 = set_d_insert (hc_keep s) 0 /\ (chk2 s -> chk2 s') /\ Pr s'.
Proof.
  intros Hf E.
  destruct (fw_insert_ok s Hf) as (s'' & E'' & Hf'' & K''). rewrite E in E''. injection E'' as <-.
  split; [exact Hf''|]. split; [exact K''|].
  revert E.
  pose proof Hf as (P & Ws & Wp & Ww & _).
  pose proof Ws as (Wl & Wok & Wwz & Wlp & Wlh).
  destruct (fi_prm_facts s P) as (Hws & Hhs & Hsh & Hwm & _).
  pose proof Wp as (Wp1 & Wp2 & Wp3 & Wp4 & Wp5 & Wp6 & Wp7 & Wp8 & Wp9).
  unfold c_fw_insert.
  replace (u32 (d_lookahead s + d_insert s)) with (d_lookahead s + d_insert s) by (unfold u32; rewrite Z.mod_small; lia).
  destruct (d_lookahead s + d_insert s >=? MIN_MATCH) eqn:E3.
  2: { intros E. injection E as <-. split; [auto|]. unfold Pr; intros Hla. exfalso. rewrite Z.geb_leb, Z.leb_gt in E3. unfold MIN_MATCH in *. lia. }
  apply Z.geb_le in E3. unfold MIN_MATCH in E3.
  replace (u32 (d_strstart s - d_insert s)) with (d_strstart s - d_insert s) by (unfold u32; rewrite Z.mod_small; lia).
  set (str := d_strstart s - d_insert s).
  destruct (fi_mb_rd s str Ws Wp Ww) as [Erd0 Hc0]; [unfold str; lia|].
  rewrite Erd0. cbn [bind].
  change (d_hash_shift (set_d_ins_h s (Znth str (mb_val (d_window s))))) with (d_hash_shift s).
  unfold guard. replace (d_hash_shift s <? 32) with true by (symmetry; apply Z.ltb_lt; lia). cbn [bind].
  change (d_window (set_d_ins_h s (Znth str (mb_val (d_window s))))) with (d_window s).
  replace (u32 (str + 1)) with (str + 1) by (unfold u32; rewrite Z.mod_small; unfold str; lia).
  destruct (fi_mb_rd s (str + 1) Ws Wp Ww) as [Erd1 _]; [unfold str; lia|].
  rewrite Erd1. cbn [bind].
  intros E. apply loop_runs in E. apply (fi_runs s) in E; [exact E|].
  split; [apply fi_ins_h_pre, fi_ins_h_pre; exact Hf|]. cbn [fst snd].
  split; [reflexivity|]. split; [exact E3|]. split.
  - exists 0. cbn. change (update_hash (set_d_ins_h s (Znth str (mb_val (d_window s))))) with (update_hash s).
    rewrite <- (uh0 s (Znth str (mb_val (d_window s)))) at 1 by assumption. reflexivity.
  - intros C. apply chk2_ins_h, chk2_ins_h. exact C.
Qed.

(** ** Window writes above strstart + lookahead *)
Lemma chk2_win s w' la' : chk2 s -> d_lookahead s <= la' ->
  (forall i, 0 <= i < d_strstart s + d_lookahead s -> Znth i (mb_val w') = Znth i (mb_val (d_window s))) ->
  chk2 (set_d_lookahead (set_d_window s w') la').
Proof.
  intros C Hla Hw b Hb. destruct (C b Hb) as (Gb & G1 & G2). exists Gb. split; [exact G1|].
  intros q Gq Hq Hl. change (lim (set_d_lookahead (set_d_window s w') la')) with (lim s) in Hl.
  destruct (G2 q Gq Hq Hl) as (A1 & A2 & A3 & A4).
  change (d_strstart (set_d_lookahead (set_d_window s w') la')) with (d_strstart s).
  change (d_lookahead (set_d_lookahead (set_d_window s w') la')) with la'.
  split; [exact A1|]. split; [lia|]. split; [|exact A4].
  rewrite <- A3. unfold h3. change (d_window (set_d_lookahead (set_d_window s w') la')) with w'.
  change (update_hash (set_d_lookahead (set_d_window s w') la')) with (update_hash s).
  rewrite !Hw by lia. reflexivity.
Qed.

Lemma Pr_win s w' : Pr s -> 0 <= d_strstart s ->
  (forall i, 0 <= i < d_strstart s + d_lookahead s -> Znth i (mb_val w') = Znth i (mb_val (d_window s))) ->
  Pr (set_d_window s w').
Proof.
  intros P Hs Hw Hla. destruct (P Hla) as (I0 & h0 & E). split; [exact I0|]. exists h0.
  change (d_ins_h (set_d_window s w')) with (d_ins_h s). change (d_window (set_d_window s w')) with w'.
  change (d_strstart (set_d_window s w')) with (d_strstart s). rewrite E. unfold MIN_MATCH in Hla.
  change (d_lookahead (set_d_window s w')) with (d_lookahead s) in Hla.
  change (update_hash (set_d_window s w')) with (update_hash s). rewrite !Hw by lia. reflexivity.
Qed.

Lemma kwin_win H s w' : kwin H s ->
  (forall i, 0 <= i < d_strstart s + d_lookahead s -> Znth i (mb_val w') = Znth i (mb_val (d_window s))) ->
  kwin H (set_d_window s w').
Proof.
  intros (K1 & K2) Hw. split; [exact K1|]. intros i Hi. change (d_window (set_d_window s w')) with w'. rewrite Hw by exact Hi.
  apply K2. exact Hi.
Qed.

Lemma kwin_app H s w' data : kwin H s ->
  (forall i, 0 <= i < d_strstart s + d_lookahead s -> Znth i (mb_val w') = Znth i (mb_val (d_window s))) ->
  (forall i, 0 <= i < Zlength data -> Znth (d_strstart s + d_lookahead s + i) (mb_val w') = Znth i data) ->
  kwin (H ++ data) (set_d_lookahead (set_d_window s w') (d_lookahead s + Zlength data)).
Proof.
  intros (K1 & K2) Hw Hd. pose proof (Zlength_nonneg data).
  unfold kwin. change (d_strstart (set_d_lookahead (set_d_window s w') (d_lookahead s + Zlength data))) with (d_strstart s).
  change (d_lookahead (set_d_lookahead (set_d_window s w') (d_lookahead s + Zlength data))) with (d_lookahead s + Zlength data).
  change (d_window (set_d_lookahead (set_d_window s w') (d_lookahead s + Zlength data))) with w'.
  rewrite Zlength_app.
  split; [lia|]. intros i Hi.
  destruct (Z_lt_le_dec i (d_strstart s + d_lookahead s)) as [Lt|Ge].
  - rewrite Hw by lia. rewrite K2 by lia. rewrite app_Znth1 by lia. f_equal. lia.
  - replace i with (d_strstart s + d_lookahead s + (i - (d_strstart s + d_lookahead s))) at 1 by lia.
    rewrite Hd by lia. rewrite app_Znth2 by lia. f_equal. lia.
Qed.

Lemma read_data s z size z' data : c_read_buf s z size = Some (z', data) ->
  data = sublist (z_next_in z) (z_next_in z + Zlength data) (z_in z).
Proof.
  unfold c_read_buf. destruct (_ =? 0).
  - intros E. injection E as _ <-. rewrite Zlength_nil, Z.add_0_r, sublist_nil. reflexivity.
  - unfold rds. cbn [set_z_avail_in z_in z_next_in].
    destruct (_ && _ && _) eqn:C; [|discriminate]. cbn [bind].
    intros E. injection E as _ <-. apply andb_true_iff in C as [C C3]. apply andb_true_iff in C as [C1 C2].
    apply Z.leb_le in C1, C2. rewrite Zlength_sublist by (apply Z.leb_le in C3; lia). f_equal. lia.
Qed.

(** ** The WIN_INIT zeroing *)
Lemma hw_vals s s' : fill_pre s -> c_fw_high_water s = Some s' ->
  s' = set_d_high_water (set_d_window s (d_window s')) (d_high_water s') /\
  forall i, 0 <= i < d_strstart s + d_lookahead s -> Znth i (mb_val (d_window s')) = Znth i (mb_val (d_window s)).
Proof.
  intros Hf E. destruct (fw_high_proof s Hf) as (s'' & E'' & _ & Eq & _). rewrite E in E''. injection E'' as <-.
  split; [exact Eq|].
  pose proof Hf as (_ & (Wl & Wok & Wz & _) & (P1 & P2 & P3 & _) & _).
  revert E. unfold c_fw_high_water.
  destruct (d_high_water s <? d_window_size s); [|intros E; injection E as <-; reflexivity].
  destruct (Z.ltb_spec (d_high_water s) (d_strstart s + d_lookahead s)) as [L1|L1].
  - destruct (mb_write _ _ _) as [win|] eqn:Ew; [|discriminate]. cbn [bind]. intros E. injection E as <-.
    intros i Hi. destruct (mb_write_spec _ _ _ _ Wok Ew) as (_ & _ & _ & _ & WZ & _).
    change (d_window (set_d_high_water (set_d_window s win) ?x)) with win. destruct (WZ i ltac:(lia)) as [_ ->].
    replace ((d_strstart s + d_lookahead s <=? i) && _) with false; [reflexivity|].
    symmetry. apply andb_false_iff. left. apply Z.leb_gt. lia.
  - destruct (_ <? _); [|intros E; injection E as <-; reflexivity].
    destruct (mb_write _ _ _) as [win|] eqn:Ew; [|discriminate]. cbn [bind]. intros E. injection E as <-.
    intros i Hi. destruct (mb_write_spec _ _ _ _ Wok Ew) as (_ & _ & _ & _ & WZ & _).
    change (d_window (set_d_high_water (set_d_window s win) ?x)) with win. destruct (WZ i ltac:(lia)) as [_ ->].
    replace ((d_high_water s <=? i) && _) with false; [reflexivity|].
    symmetry. apply andb_false_iff. left. apply Z.leb_gt. lia.
Qed.

(** ** One iteration of the do-while loop *)
Lemma body_props s z H x s' z' d k :
  fill_pre s -> zall z -> adler_ok (d_wrap s) (z_adler z) -> fw_body (s, z) = Some x ->
  (x = inl (s', z') \/ x = inr (s', z')) -> fwstep s z s' z' d k ->
  (kwin H s -> kwin (H ++ sublist (z_next_in z) (z_next_in z + k) (z_in z)) s') /\
  (chk2 s -> chk2 s') /\ (z_avail_in z <> 0 -> Pr s') /\ (Pr s -> Pr s').
Proof.
  intros Hf Hz Ha Ex Hx Hst.
  destruct Hst as (_ & (_ & _ & Nk & _) & _).
  revert Ex.
  destruct (fw_slide_ok s Hf) as (s1 & dd & Esl & Hf1 & K1 & La1 & _).
  destruct (keep_fields s s1 K1) as (Wr1 & Ws1 & Wz1 & Md1).
  destruct (slide_props s s1 _ H Hf Esl) as (Sk & Sc & Sp).
  unfold fw_body. rewrite Esl. cbn [bind].
  destruct (Z.eqb_spec (z_avail_in z) 0) as [A0|A0].
  { intros E. injection E as <-. destruct Hx as [Hx|Hx]; [discriminate|]. injection Hx as <- <-.
    assert (k = 0) by lia. subst k. rewrite Z.add_0_r, sublist_nil, app_nil_r.
    split; [exact Sk|]. split; [exact Sc|]. split; [intros C; contradiction|exact Sp]. }
  pose proof Hf1 as (Hp1 & (W1 & W2 & W3 & W4 & W5) & (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9) & Hw1 & Hc1).
  pose proof (prm_wsize s1 Hp1) as Hws.
  destruct (read_ok s1 z (d_window_size s1 - d_lookahead s1 - d_strstart s1)) as
    (z1 & data & Er & Hlen & Hdb & Hst & Hz1 & Ha1); [exact Hz|rewrite Wr1; exact Ha|lia|].
  pose proof (read_data _ _ _ _ _ Er) as Hdata.
  pose proof (Zlength_nonneg data) as Hdn.
  rewrite Er. cbn [bind].
  rewrite (mb_write_some (d_window s1) (d_strstart s1 + d_lookahead s1) data) by lia.
  cbn [bind].
  set (win := mkMB _ _).
  assert (Ew : mb_write (d_window s1) (d_strstart s1 + d_lookahead s1) data = Some win)
    by (apply mb_write_some; lia).
  change (d_lookahead (set_d_window s1 win)) with (d_lookahead s1).
  rewrite (u32_id' (d_lookahead s1 + Zlength data)) by lia.
  assert (F := fill_pre_write s1 win (d_strstart s1 + d_lookahead s1) data (d_lookahead s1 + Zlength data)
                 (d_high_water s1) Hf1 Ew Hdb ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros i Hi; lia)).
  change (d_high_water s1) with (d_high_water (set_d_lookahead (set_d_window s1 win) (d_lookahead s1 + Zlength data))) in F.
  rewrite set_hw_same in F.
  pose proof (mb_write_spec _ _ _ _ W2 Ew) as (_ & _ & _ & _ & WZ & _).
  assert (Hlo : forall i, 0 <= i < d_strstart s1 + d_lookahead s1 ->
            Znth i (mb_val win) = Znth i (mb_val (d_window s1))).
  { intros i Hi. destruct (WZ i ltac:(lia)) as [_ ->].
    replace ((d_strstart s1 + d_lookahead s1 <=? i) && _) with false; [reflexivity|].
    symmetry. apply andb_false_iff. left. apply Z.leb_gt. lia. }
  assert (Hhi : forall i, 0 <= i < Zlength data ->
            Znth (d_strstart s1 + d_lookahead s1 + i) (mb_val win) = Znth i data).
  { intros i Hi. destruct (WZ (d_strstart s1 + d_lookahead s1 + i) ltac:(lia)) as [_ ->].
    replace ((d_strstart s1 + d_lookahead s1 <=? _) && _) with true.
    - f_equal. lia.
    - symmetry. apply andb_true_iff. split; [apply Z.leb_le|apply Z.ltb_lt]; lia. }
  set (s2 := set_d_lookahead (set_d_window s1 win) (d_lookahead s1 + Zlength data)) in F |- *.
  destruct (fw_insert_ok s2 F) as (s3 & Ei & _ & _).
  destruct (ins_props s2 s3 F Ei) as (_ & K3 & Ic & Ip).
  destruct (hc_fields s2 s3 K3) as (_ & Ss3 & _ & _ & La3).
  assert (Wd3 : d_window s3 = d_window s2) by exact (f_equal d_window K3).
  rewrite Ei. cbn [bind].
  intros E. assert (Es : s' = s3 /\ z' = z1).
  { destruct ((d_lookahead s3 <? MIN_LOOKAHEAD) && negb (z_avail_in z1 =? 0));
      injection E as <-; destruct Hx as [Hx|Hx]; inversion Hx; subst; auto. }
  destruct Es as [-> ->].
  destruct Hst as (_ & _ & Nk1 & _).
  assert (Ek : k = Zlength data) by lia. subst k.
  split; [|split; [|split]].
  - intros Hk. rewrite <- Hdata.
    assert (Hk2 : kwin (H ++ data) s2) by (apply kwin_app; auto).
    destruct Hk2 as (Q1 & Q2). split; [rewrite Ss3, La3; exact Q1|].
    rewrite Ss3, La3, Wd3. exact Q2.
  - intros C. apply Ic. apply chk2_win; auto. lia.
  - intros _. exact Ip.
  - intros _. exact Ip.
Qed.

(** ** The do-while loop *)
Definition fwI (s0 : dstate) (z0 : strm) (H : list Z) (a : dstate * strm) : Prop :=
  fill_pre (fst a) /\ zall (snd a) /\ adler_ok (d_wrap s0) (z_adler (snd a)) /\
  exists d k, fwstep s0 z0 (fst a) (snd a) d k /\
    (kwin H s0 -> kwin (H ++ sublist (z_next_in z0) (z_next_in z0 + k) (z_in z0)) (fst a)) /\
    (chain_hok s0 -> chk2 (fst a)) /\
    ((0 < k \/ (d_insert s0 = 0 /\ primed s0 (d_strstart s0))) -> Pr (fst a)).

Lemma fw_step1 s0 z0 H s z x s' z' :
  fill_pre s0 -> zall z0 -> adler_ok (d_wrap s0) (z_adler z0) ->
  fwI s0 z0 H (s, z) -> fw_body (s, z) = Some x -> (x = inl (s', z') \/ x = inr (s', z')) ->
  fwI s0 z0 H (s', z').
Proof.
  intros Hf0 Hz0 Ha0 (Hf & Hz & Ha & d & k & Hs & Ik & Ic & Ip) Eb Hx. cbn [fst snd] in *.
  pose proof Hs as (K & _).
  destruct (keep_fields s0 s K) as (Wr & _ & _ & _).
  rewrite <- Wr in Ha.
  destruct (body_ok s z Hf Hz Ha) as (s'' & z'' & d' & k' & b & Eb' & Hf' & Hz' & Ha' & Hs' & _).
  rewrite Eb in Eb'. injection Eb' as Ex.
  assert (Es : s'' = s' /\ z'' = z').
  { destruct b; subst x; destruct Hx as [Hx|Hx]; inversion Hx; subst; auto. }
  destruct Es as [-> ->].
  assert (Hx' : x = inl (s', z') \/ x = inr (s', z')) by exact Hx.
  destruct (body_props s z (H ++ sublist (z_next_in z0) (z_next_in z0 + k) (z_in z0)) x s' z' d' k' Hf Hz Ha Eb Hx' Hs') as (Bk & Bc & Bp1 & Bp2).
  assert (Hs'' := fwstep_trans s0 z0 s z s' z' d k d' k' Hf0 Hz0 Ha0 Hs Hs').
  pose proof Hs as (_ & (Zi & Zk & Zn & _) & _).
  pose proof Hs' as (_ & (Zi' & Zk' & Zn' & _) & _).
  pose proof Hz as [(_ & Zn0 & Zav & Zl & _) _].
  pose proof Hz0 as [(_ & Zn00 & _ & _ & _) _].
  split; [exact Hf'|]. split; [exact Hz'|]. split; [rewrite <- Wr; exact Ha'|].
  exists (d + d'), (k + k'). split; [exact Hs''|]. split; [|split].
  - intros Hk. specialize (Bk (Ik Hk)). rewrite Zi, Zn in Bk. rewrite Zi in Zl. rewrite <- app_assoc in Bk.
    rewrite sublist_rejoin in Bk by lia. replace (z_next_in z0 + (k + k')) with (z_next_in z0 + k + k') by lia.
    exact Bk.
  - intros C. apply Bc, Ic, C.
  - intros Hc. destruct (Z_lt_le_dec 0 k') as [Lk|Lk].
    + apply Bp1. lia.
    + apply Bp2, Ip. destruct Hc as [Hc|Hc]; [left; lia|right; exact Hc].
Qed.

Lemma fw_runs s0 z0 H a r :
  fill_pre s0 -> zall z0 -> adler_ok (d_wrap s0) (z_adler z0) ->
  runs fw_body a r -> fwI s0 z0 H a -> fwI s0 z0 H r.
Proof.
  intros Hf0 Hz0 Ha0 R. induction R as [[s z] [s' z'] Eb|[s z] [s' z'] r Eb R IH]; intros I.
  - eapply fw_step1; eauto.
  - apply IH. eapply fw_step1; eauto.
Qed.
