(** * deflate_bound theory: the cost of the blocks a compression call emits

    [ev_step]: one event of [cpost] (LTDefs.dev) moves the accounting of the class of the stream: a non-last
    block of [B] bytes (at least [minblk]) from [xb c h E k] to [xb c h (E + B) (k + 1)]; the last block to at most
    [8 (h + body c (E + B))].  From lemma (ii) (tight class), LTBFlush.flush_block_cost with the static costs of
    LTBStatic (Z_FIXED with buf = NULL at memLevel 8; the fixed and store classes), the stored blocks' bit count
    [ev_after], and LTBArith. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTBArith.
Require Import Zlib.proof.deflate.LTBStatic Zlib.proof.deflate.LTBFlush.
Require Import Zlib.proof.huffman.DynSum.
Require Import Zlib.proof.deflate.LTBEvArith Zlib.proof.deflate.LTBEvStatic Zlib.proof.deflate.LTBEvFlush.
Import ListNotations.
Local Open Scope Z_scope.

(** ** Helpers *)

Lemma bcls_spec : forall s,
  (bcls_of s = BTight -> d_w_bits s = 15 /\ d_hash_bits s = 15 /\
     (d_strategy s = 4 -> d_level s < 1 \/ 3 < d_level s)) /\
  (bcls_of s = BFixed -> d_w_bits s <= d_hash_bits s /\ d_level s <> 0) /\
  (bcls_of s = BStore -> d_level s = 0 \/ d_hash_bits s < d_w_bits s).
Proof.
  intros s; unfold bcls_of, tight_b.
  destruct (Z.eqb_spec (d_w_bits s) 15); destruct (Z.eqb_spec (d_hash_bits s) (8 + 7));
  destruct (Z.eqb_spec (d_strategy s) Z_FIXED); destruct (Z.geb_spec (d_level s) 1);
  destruct (Z.leb_spec (d_level s) 3); destruct (Z.leb_spec (d_w_bits s) (d_hash_bits s));
  destruct (Z.eqb_spec (d_level s) 0); cbn; unfold Z_FIXED in *;
  repeat split; intros; try discriminate; lia.
Qed.

Lemma div8_le : forall x, 8 * (x / 8) <= x.
Proof. intros; apply Z.mul_div_le; lia. Qed.

Lemma bitpos_pre : forall t syms, flush_pre t syms -> 0 <= bitpos (tr_out t) <= 7.
Proof.
  intros t syms H; destruct (fp_out _ _ H) as [[Hb _] [Hp [Hv _]]].
  unfold bitpos; lia.
Qed.

Lemma syms_valid_pre : forall t syms, flush_pre t syms -> syms_valid syms.
Proof. intros t syms H; destruct (fp_syms _ _ H) as [_ [_ [Hv _]]]; exact Hv. Qed.

Lemma syms_len_pre : forall t syms, flush_pre t syms -> Zlength syms <= tr_lit_bufsize t - 1.
Proof. intros t syms H; destruct (fp_syms _ _ H) as [_ [Hl _]]; exact Hl. Qed.

(** A block at level > 0 costs at most [B + 5] bytes, given the static cost when buf = NULL. *)
Lemma flush_byte : forall t syms buf B last T A,
  flush_pre t syms -> 0 <= last <= 1 -> 0 < tr_level t -> B = blk_len syms ->
  match buf with Some b => B <= 65535 /\ B <= Zlength b | None => stat_data syms <= 8 * B + 37 end ->
  0 <= T -> 8 * T + bitpos (tr_out t) <= 8 * A ->
  8 * T + bitpos (tr_out (fst (tr_flush_block t buf B last))) <= 8 * (A + B + 5).
Proof.
  intros t syms buf B last T A Hpre Hl Hlv HB Hbuf HT Hg.
  pose proof (bitpos_pre _ _ Hpre) as Hp.
  assert (Hb' : match buf with Some b => B <= 65535 /\ B <= Zlength b | None => True end)
    by (destruct buf; auto).
  pose proof (flush_block_cost t syms buf B last Hpre Hl Hlv HB Hb') as Hc; cbv zeta in Hc.
  unfold rnd in Hc.
  set (p := bitpos (tr_out t)) in *.
  set (p' := bitpos (tr_out (fst (tr_flush_block t buf B last)))) in *.
  destruct buf as [b|].
  - destruct Hc as [[_ H2] | [_ [_ Heq]]].
    + specialize (H2 ltac:(discriminate)).
      destruct (Z.eqb_spec last 0).
      * lia.
      * pose proof (div8_le (p + 8 * B + 24 + 7)). lia.
    + pose proof (div8_le (p + 10)). lia.
  - destruct Hc as [[H1 _] | [Hne _]]; [|congruence].
    destruct (Z.eqb_spec last 0).
    + lia.
    + pose proof (div8_le (p + 3 + stat_data syms + 7)). lia.
Qed.

Lemma pow2_cases_hb : forall hb, 8 <= hb <= 16 -> 128 <= 2 ^ (hb - 1).
Proof.
  intros hb H.
  assert (hb = 8 \/ hb = 9 \/ hb = 10 \/ hb = 11 \/ hb = 12 \/ hb = 13 \/ hb = 14 \/ hb = 15 \/ hb = 16)
    by lia.
  repeat destruct H0 as [H0|H0]; subst; cbn; lia.
Qed.

Lemma pow2_ge_512 : forall wb, 9 <= wb <= 15 -> 512 <= 2 ^ wb.
Proof.
  intros wb H.
  assert (wb = 9 \/ wb = 10 \/ wb = 11 \/ wb = 12 \/ wb = 13 \/ wb = 14 \/ wb = 15) by lia.
  repeat destruct H0 as [H0|H0]; subst; cbn; lia.
Qed.

Lemma pow2_4L : forall hb wb, 8 <= hb -> hb < wb -> 4 * 2 ^ (hb - 1) <= 2 ^ wb.
Proof.
  intros hb wb H1 H2.
  replace (4 * 2 ^ (hb - 1)) with (2 ^ (hb + 1)).
  - apply Z.pow_le_mono_r; lia.
  - replace (hb + 1) with ((hb - 1) + 2) by lia. rewrite Z.pow_add_r by lia. cbn. lia.
Qed.

Lemma pow2_256 : forall hb wb, 9 <= wb -> wb <= hb -> 256 <= 2 ^ (hb - 1).
Proof.
  intros hb wb H1 H2.
  replace 256 with (2 ^ 8) by reflexivity. apply Z.pow_le_mono_r; lia.
Qed.

Lemma fin_byte : forall c h E k B a last, c <> BFixed -> 0 <= k -> minblk c * k <= E -> 0 <= B ->
  E + B <= 1048576 -> a <= 8 * (h + E + 5 * k + B + 5) -> (last = 0 -> minblk c <= B) ->
  (last = 0 -> acct c h (E + B) (k + 1) a) /\ (last = 1 -> a <= 8 * (h + body c (E + B))).
Proof.
  intros c h E k B a last Hc Hk HE HB HEB Ha Hm; split; intros Hl.
  - specialize (Hm Hl); unfold acct, xb; destruct c; [| congruence |]; repeat split; lia.
  - pose proof (acc_byte_last c h E k B Hc Hk HE HB HEB); lia.
Qed.

Lemma ev_step : block_bound_statement -> forall s0 flush e h E k,
  prm s0 -> (flush = Z_NO_FLUSH \/ flush = Z_FINISH) -> ev_ok s0 flush e -> ev_lvl s0 e ->
  acct (bcls_of s0) h E k (ev_g e) -> 0 <= h -> E + ev_len e <= 1048576 ->
  0 <= ev_len e /\
  (ev_last e = 0 -> acct (bcls_of s0) h (E + ev_len e) (k + 1) (ev_after e)) /\
  (ev_last e = 1 -> ev_after e <= 8 * (h + body (bcls_of s0) (E + ev_len e))).
Proof.
  intros Hbb s0 flush e h E k Hprm Hfl Hok Hlvl Hacc Hh HE.
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
      apply fin_byte; cbn [minblk]; try lia; try discriminate;
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
        -- pose proof (acc_fixed_huff h E k sl Hk ltac:(cbn in Hmk; lia) ltac:(lia) HE).
           pose proof (div8_le (bitpos (tr_out t) + 3 + stat_data syms + 7)). lia.
        -- pose proof (acc_fixed_stored h E k sl g Hk ltac:(cbn in Hmk; lia) ltac:(lia) HE ltac:(lia)) as Hfs.
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
      apply fin_byte; cbn [minblk]; try lia; try discriminate;
        try (intros H0; specialize (Hnl' H0); lia).
  - destruct Hok as (Hl0 & Hlen & Hlast & Hfin & Hnl).
    split; [lia|].
    pose proof (div8_le (g + 10)).
    pose proof (pow2_cases_hb (d_hash_bits s0) Hhb). pose proof (pow2_ge_512 (d_w_bits s0) Hwb).
    destruct (bcls_of s0) eqn:Hc; cbn [xb minblk] in Hgx, Hmk.
    + destruct (HcT eq_refl) as (Hw15 & Hh15 & _).
      rewrite Hh15 in HL; cbn in HL. rewrite Hw15 in Hws; cbn in Hws.
      apply fin_byte; cbn [minblk]; try lia; try discriminate;
        try (intros H0; destruct (Hnl H0) as [[? ?]|?]; [destruct Hfl; contradiction | lia]).
    + destruct (HcF eq_refl); contradiction.
    + apply fin_byte; cbn [minblk]; try lia; try discriminate;
        try (intros H0; destruct (Hnl H0) as [[? ?]|?]; [destruct Hfl; contradiction | lia]).
Qed.

Lemma ev_len_nonneg : forall s0 flush e, ev_ok s0 flush e -> 0 <= ev_len e.
Proof.
  intros s0 flush e; destruct e as [g t syms buf sl last | g len last]; cbn [ev_ok ev_len]; intros H.
  - destruct H as (_ & Hpre & _ & _ & _ & _ & _ & _ & _ & Hsl & _).
    pose proof (blk_len_ge _ (syms_valid_pre _ _ Hpre)); pose proof (Zlength_nonneg syms); lia.
  - lia.
Qed.

Lemma sum_len_cons : forall e r, sum_len (e :: r) = ev_len e + sum_len r.
Proof. reflexivity. Qed.

Lemma sum_len_nonneg : forall s0 flush evs, Forall (ev_ok s0 flush) evs -> 0 <= sum_len evs.
Proof.
  intros s0 flush evs H; induction H as [|e r He Hr IH].
  - cbn; lia.
  - rewrite sum_len_cons; pose proof (ev_len_nonneg _ _ _ He); lia.
Qed.

(** All the events of one call. *)
Lemma chain_acct : block_bound_statement -> forall s0 flush evs g g' h E k,
  prm s0 -> (flush = Z_NO_FLUSH \/ flush = Z_FINISH) ->
  Forall (ev_ok s0 flush) evs -> Forall (ev_lvl s0) evs -> ev_chain g evs g' ->
  acct (bcls_of s0) h E k g -> 0 <= h -> E + sum_len evs <= 1048576 ->
  0 <= sum_len evs /\
  (Forall (fun e => ev_last e = 0) evs -> exists k', acct (bcls_of s0) h (E + sum_len evs) k' g') /\
  (last_ev evs -> g' <= 8 * (h + body (bcls_of s0) (E + sum_len evs))).
Proof.
  intros Hbb s0 flush evs.
  induction evs as [|e r IH]; intros g g' h E k Hprm Hfl Hok Hlv Hch Hacc Hh HE.
  - cbn in Hch; subst g'. change (sum_len []) with 0 in *. rewrite Z.add_0_r.
    split; [lia | split].
    + intros _; exists k; exact Hacc.
    + intros (evs0 & e & Heq & _); destruct evs0; discriminate.
  - rewrite sum_len_cons in *.
    inversion Hok as [|? ? Hoke Hokr]; subst. inversion Hlv as [|? ? Hlve Hlvr]; subst.
    destruct Hch as [Hge Hch]; subst g.
    pose proof (sum_len_nonneg _ _ _ Hokr) as Hr0.
    destruct (ev_step Hbb s0 flush e h E k Hprm Hfl Hoke Hlve Hacc Hh ltac:(lia)) as [Hl0 [Hnl Hla]].
    split; [lia | split].
    + intros Hall; inversion Hall as [|? ? Hle Hallr]; subst.
      destruct (IH (ev_after e) g' h (E + ev_len e) (k + 1) Hprm Hfl Hokr Hlvr Hch (Hnl Hle) Hh ltac:(lia))
        as [_ [IH2 _]].
      destruct (IH2 Hallr) as [k' Hk']; exists k'. rewrite Z.add_assoc; exact Hk'.
    + intros (evs0 & e' & Heq & Hl1 & Hall0).
      destruct evs0 as [|e0 evs0].
      * cbn in Heq; injection Heq as He' Hr; subst e' r. cbn in Hch; subst g'.
        change (sum_len []) with 0; rewrite Z.add_0_r. auto.
      * cbn in Heq; injection Heq as He0 Hr; subst e0 r. inversion Hall0 as [|? ? Hle Hallr]; subst.
        destruct (IH (ev_after e) g' h (E + ev_len e) (k + 1) Hprm Hfl Hokr Hlvr Hch (Hnl Hle) Hh ltac:(lia))
          as [_ [_ IH3]].
        rewrite Z.add_assoc; apply IH3. exists evs0, e'; auto.
Qed.
