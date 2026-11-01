(** * The deflateBound accounting for any sizes: the cost of the blocks a compression call emits

    LTBEvent.chain_acct without the limit [E + sum_len evs <= 2^20], the last block leaving the margin [slk]
    (LTWBArith). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTWBArith.
Require Import Zlib.proof.deflate.LTBStatic Zlib.proof.deflate.LTBFlush Zlib.proof.deflate.LTBEvent.
Require Import Zlib.proof.huffman.DynSum.
Require Import Zlib.proof.deflate.LTBEvArith Zlib.proof.deflate.LTBEvStatic Zlib.proof.deflate.LTBEvFlush.
Import ListNotations.
Local Open Scope Z_scope.

Lemma slk_range : forall n, 0 <= slk n <= 1.
Proof. intros n; unfold slk; destruct (n <? 33554432); lia. Qed.

(** LTBEvent.fin_byte for any size: a tight / store block of at most [B + 5] bytes keeps the accounting, or, if
    it is the last one, leaves the margin. *)
Lemma fin_byte_w : forall c h E k B a last, c <> BFixed -> 0 <= k -> minblk c * k <= E -> 0 <= B ->
  a <= 8 * (h + E + 5 * k + B + 5) -> (last = 0 -> minblk c <= B) ->
  (last = 0 -> acct c h (E + B) (k + 1) a) /\ (last = 1 -> a + slk (E + B) <= 8 * (h + body c (E + B))).
Proof.
  intros c h E k B a last Hc Hk HE HB Ha Hm; split; intros Hl.
  - specialize (Hm Hl); unfold acct, xb; destruct c; [| congruence |]; repeat split; lia.
  - pose proof (acc_byte_last_w c h E k B Hc Hk HE HB). pose proof (slk_range (E + B)); lia.
Qed.

(** The last block, fixed, Huffman-coded, in a stream of at least 2^25 bytes: the [9 B + 10] bits of
    LTWBArith.acc_fixed_huff_w and the up to 7 bits of padding of the last byte still leave the margin bit
    (the bound has a slack of about [n / 130] bits there). *)
Lemma acc_fixed_huff_far : forall h e k B, 0 <= k -> 255 * k <= e -> 0 <= B -> 33554432 <= e + B ->
  8 * h + 9 * e + 10 * k + 9 * B + 18 <= 8 * (h + body BFixed (e + B)).
Proof. intros h e k B Hk Hke HB Hn. rewrite !body_div. dv. lia. Qed.

(** LTBEvent.ev_step for any size: one event of a compression call moves the accounting of the class of the
    stream; the last block leaves the margin [slk]. *)
Lemma ev_step_w : block_bound_statement -> forall s0 flush e h E k,
  prm s0 -> (flush = Z_NO_FLUSH \/ flush = Z_FINISH) -> ev_ok s0 flush e -> ev_lvl s0 e ->
  acct (bcls_of s0) h E k (ev_g e) -> 0 <= h ->
  0 <= ev_len e /\
  (ev_last e = 0 -> acct (bcls_of s0) h (E + ev_len e) (k + 1) (ev_after e)) /\
  (ev_last e = 1 -> ev_after e + slk (E + ev_len e) <= 8 * (h + body (bcls_of s0) (E + ev_len e))).
Proof.
  intros Hbb s0 flush e h E k Hprm Hfl Hok Hlvl Hacc Hh.
  pose proof (bcls_spec s0) as [HcT [HcF HcS]].
  destruct Hprm as (Hwb & Hws & _ & Hhb & _ & _ & _ & HL & Hpbs & _ & _ & _ & Hlv & Hst & _).
  destruct Hacc as (Hk & Hmk & Hgx).
  destruct e as [g t syms buf sl last | g len last]; cbn [ev_ok ev_lvl ev_g ev_len ev_last ev_after] in *.
  - destruct Hok as (_ & Hpre & [T [HT Hg]] & HLt & Hlvt & Hstt & Hlast & Hfin & Hnl & Hsl & Hbuf & Hdist & Hfar).
    pose proof (syms_valid_pre _ _ Hpre) as Hsv. pose proof (blk_len_ge syms Hsv) as Hge.
    pose proof (Zlength_nonneg syms). pose proof (syms_len_pre _ _ Hpre) as Hsl'.
    pose proof (bitpos_pre _ _ Hpre) as Hp.
    assert (Hnl' : last = 0 -> Zlength syms = d_L s0 - 1)
      by (intro H0; destruct (Hnl H0) as [?|[? ?]]; [auto | destruct Hfl; contradiction]).
    clear Hnl.
    assert (Hlt : 0 < tr_level t) by lia.
    split; [lia|].
    unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH, TOO_FAR, Z_FILTERED in *.
    set (p' := bitpos (tr_out (fst (tr_flush_block t buf sl last)))) in *.
    destruct (bcls_of s0) eqn:Hc; cbn [xb minblk] in Hgx, Hmk.
    + (* tight *)
      destruct (HcT eq_refl) as (Hw15 & Hh15 & Hfx).
      rewrite Hh15 in HL; cbn in HL. rewrite Hw15 in Hws; cbn in Hws.
      assert (Hby : 8 * T + p' <= 8 * (h + E + 5 * k + sl + 5)).
      { destruct buf as [b|].
        - apply (flush_byte t syms (Some b) sl last T); try lia; auto.
        - destruct (Z.eq_dec (d_strategy s0) 4) as [Hs4|Hs4].
          + specialize (Hfx Hs4).
            apply (flush_byte t syms None sl last T); try lia; auto.
            rewrite Hsl; apply stat_far; auto; try lia;
              try (intros x Hx Hx0; specialize (Hdist x Hx Hx0); lia); try (apply Hfar; lia).
          + apply (Hbb t syms None sl last T); try lia; auto.
            unfold Z_FIXED; split; [lia | split; lia]. }
      apply fin_byte_w; cbn [minblk]; try lia; try discriminate;
        try (intros H0; specialize (Hnl' H0); lia).
    + (* fixed *)
      destruct (HcF eq_refl) as (Hwh & Hl0).
      pose proof (pow2_256 (d_hash_bits s0) (d_w_bits s0) ltac:(lia) Hwh).
      assert (Hb' : match buf with Some b => sl <= 65535 /\ sl <= Zlength b | None => True end)
        by (destruct buf; [lia | auto]).
      pose proof (flush_block_cost t syms buf sl last Hpre Hlast Hlt Hsl Hb') as Hcost; cbv zeta in Hcost.
      fold p' in Hcost. unfold rnd in Hcost.
      pose proof (stat_9 syms Hsv) as H9.
      unfold acct; cbn [xb minblk].
      split; intros Hl; subst last.
      * change (0 =? 0) with true in Hcost; cbv iota beta in Hcost. specialize (Hnl' eq_refl).
        destruct Hcost as [[H1 _] | [_ [_ Heq]]].
        -- repeat split; lia.
        -- pose proof (div8_le (bitpos (tr_out t) + 10)). repeat split; lia.
      * change (1 =? 0) with false in Hcost; cbv iota beta in Hcost.
        destruct Hcost as [[H1 _] | [_ [Hst8 Heq]]].
        -- pose proof (acc_fixed_huff_w h E k sl Hk ltac:(cbn in Hmk; lia) ltac:(lia)).
           pose proof (div8_le (bitpos (tr_out t) + 3 + stat_data syms + 7)).
           unfold slk in *; destruct (Z.ltb_spec (E + sl) 33554432); [lia|].
           pose proof (acc_fixed_huff_far h E k sl Hk ltac:(cbn in Hmk; lia) ltac:(lia) ltac:(lia)). lia.
        -- pose proof (acc_fixed_stored_w h E k sl g Hk ltac:(cbn in Hmk; lia) ltac:(lia) ltac:(lia)) as Hfs.
           replace (g + 10) with (T * 8 + (bitpos (tr_out t) + 10)) in Hfs by lia.
           rewrite Z.div_add_l in Hfs by lia. lia.
    + (* store *)
      assert (Hhw : d_hash_bits s0 < d_w_bits s0) by (destruct (HcS eq_refl); lia).
      pose proof (pow2_cases_hb (d_hash_bits s0) Hhb).
      assert (Hby : 8 * T + p' <= 8 * (h + E + 5 * k + sl + 5)).
      { destruct buf as [b|].
        - apply (flush_byte t syms (Some b) sl last T); try lia; auto.
        - pose proof (pow2_4L (d_hash_bits s0) (d_w_bits s0) ltac:(lia) Hhw).
          apply (flush_byte t syms None sl last T); try lia; auto.
          rewrite Hsl; apply (stat_win syms (d_w_bits s0)); auto; try lia.
          intros x Hx Hx0; specialize (Hdist x Hx Hx0); lia. }
      apply fin_byte_w; cbn [minblk]; try lia; try discriminate;
        try (intros H0; specialize (Hnl' H0); lia).
  - destruct Hok as (Hl0 & Hlen & Hlast & Hfin & Hnl).
    split; [lia|].
    pose proof (div8_le (g + 10)).
    pose proof (pow2_cases_hb (d_hash_bits s0) Hhb). pose proof (pow2_ge_512 (d_w_bits s0) Hwb).
    destruct (bcls_of s0) eqn:Hc; cbn [xb minblk] in Hgx, Hmk.
    + destruct (HcT eq_refl) as (Hw15 & Hh15 & _).
      rewrite Hh15 in HL; cbn in HL. rewrite Hw15 in Hws; cbn in Hws.
      apply fin_byte_w; cbn [minblk]; try lia; try discriminate;
        try (intros H0; destruct (Hnl H0) as [[? ?]|?]; [destruct Hfl; contradiction | lia]).
    + destruct (HcF eq_refl); contradiction.
    + apply fin_byte_w; cbn [minblk]; try lia; try discriminate;
        try (intros H0; destruct (Hnl H0) as [[? ?]|?]; [destruct Hfl; contradiction | lia]).
Qed.

Lemma chain_acct_w : block_bound_statement -> forall s0 flush evs g g' h E k,
  prm s0 -> (flush = Z_NO_FLUSH \/ flush = Z_FINISH) ->
  Forall (ev_ok s0 flush) evs -> Forall (ev_lvl s0) evs -> ev_chain g evs g' ->
  acct (bcls_of s0) h E k g -> 0 <= h ->
  0 <= sum_len evs /\
  (Forall (fun e => ev_last e = 0) evs -> exists k', acct (bcls_of s0) h (E + sum_len evs) k' g') /\
  (last_ev evs -> g' + slk (E + sum_len evs) <= 8 * (h + body (bcls_of s0) (E + sum_len evs))).
Proof.
  intros Hbb s0 flush evs.
  induction evs as [|e r IH]; intros g g' h E k Hprm Hfl Hok Hlv Hch Hacc Hh.
  - cbn in Hch; subst g'. change (sum_len []) with 0 in *. rewrite Z.add_0_r.
    split; [lia | split].
    + intros _; exists k; exact Hacc.
    + intros (evs0 & e & Heq & _); destruct evs0; discriminate.
  - rewrite sum_len_cons in *.
    inversion Hok as [|? ? Hoke Hokr]; subst. inversion Hlv as [|? ? Hlve Hlvr]; subst.
    destruct Hch as [Hge Hch]; subst g.
    pose proof (sum_len_nonneg _ _ _ Hokr) as Hr0.
    destruct (ev_step_w Hbb s0 flush e h E k Hprm Hfl Hoke Hlve Hacc Hh) as [Hl0 [Hnl Hla]].
    split; [lia | split].
    + intros Hall; inversion Hall as [|? ? Hle Hallr]; subst.
      destruct (IH (ev_after e) g' h (E + ev_len e) (k + 1) Hprm Hfl Hokr Hlvr Hch (Hnl Hle) Hh)
        as [_ [IH2 _]].
      destruct (IH2 Hallr) as [k' Hk']; exists k'. rewrite Z.add_assoc; exact Hk'.
    + intros (evs0 & e' & Heq & Hl1 & Hall0).
      destruct evs0 as [|e0 evs0].
      * cbn in Heq; injection Heq as He' Hr; subst e' r. cbn in Hch; subst g'.
        change (sum_len []) with 0; rewrite Z.add_0_r. auto.
      * cbn in Heq; injection Heq as He0 Hr; subst e0 r. inversion Hall0 as [|? ? Hle Hallr]; subst.
        destruct (IH (ev_after e) g' h (E + ev_len e) (k + 1) Hprm Hfl Hokr Hlvr Hch (Hnl Hle) Hh)
          as [_ [_ IH3]].
        rewrite Z.add_assoc; apply IH3. exists evs0, e'; auto.
Qed.
