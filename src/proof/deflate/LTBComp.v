(** * deflate_bound theory: the compression stage of deflate() inside [Mid]

    [cf_compress] (core_facts) and its [cpost]; the accounting of the blocks by LTBEvent.chain_acct; at level 0
    with Z_FINISH and room for everything, [cf_stored_live]. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTBOut Zlib.proof.deflate.LTBEvent.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

Require Zlib.proof.crc32.Combine.

(** ** Local copies of LTBArith's facts (the proof of LTBArith.arith_proof, under names of this file). *)
Lemma cs_body_div : forall c n, body c n =
  match c with
  | BTight => n + n / 4096 + n / 16384 + n / 33554432 + 7
  | BFixed => n + n / 8 + n / 256 + n / 512 + 4
  | BStore => n + n / 32 + n / 128 + n / 2048 + 7
  end.
Proof.
  intros c n; destruct c; unfold body; rewrite !Z.shiftr_div_pow2 by lia; reflexivity.
Qed.

Lemma cs_divb : forall n d, 0 < d -> d * (n / d) <= n < d * (n / d) + d.
Proof. intros n d Hd. split; [apply Z.mul_div_le; lia|]. pose proof (Z.mul_succ_div_gt n d Hd). lia. Qed.

Ltac cs_dv := repeat match goal with |- context [?n / ?d] =>
  let q := fresh "q" in pose proof (cs_divb n d ltac:(lia)); set (q := n / d) in *; clearbody q end.

Lemma cs_body_range : forall c n, 0 <= n <= 1048576 -> n + 4 <= body c n <= 2 * n + 7.
Proof. intros c n Hn. rewrite !cs_body_div. destruct c; cs_dv; lia. Qed.

Lemma cs_acc_mid : forall c h e k n, 0 <= h -> 0 <= k -> minblk c * k <= e -> e <= n <= 1048576 ->
  xb c h e k + 10 <= 8 * (h + body c n).
Proof.
  intros c h e k n Hh Hk Hke Hn. rewrite !cs_body_div. destruct c; unfold xb, minblk in *; cs_dv.
  all: lia.
Qed.

Lemma cs_stored_room : forall c n, c <> BFixed -> 0 <= n <= 1048576 ->
  6 + 5 * (n / 65535) + n <= body c n.
Proof. intros c n Hc Hn. rewrite !cs_body_div. destruct c; try congruence; cs_dv; lia. Qed.

(** ** Helpers *)
Lemma cs_adler_ok : forall w0 a data, adler_ok w0 a -> bytes data -> adler_ok w0 (adler_upd w0 a data).
Proof.
  intros w0 a data [H1 H2] Hb. unfold adler_upd. split; intros E; subst w0; cbn.
  - apply Zlib.proof.adler32.Model.ref_adler32_valid. auto.
  - apply Zlib.proof.crc32.Combine.ref_crc32_range. unfold Zlib.proof.adler32.Bytes.is_bytes.
    unfold bytes in Hb. eapply Forall_impl; [|exact Hb]. intros y Hy. cbn in Hy. change Integers.Byte.max_unsigned with 255. lia.
Qed.

(** The state after the compression function: last_flush possibly set to -1, status possibly FINISH. *)
Definition cs_like (s1 s2 : dstate) : Prop :=
  core_eq s1 s2 /\ (outok s1 -> outok s2) /\ d_wrap s2 = d_wrap s1 /\ d_gzhead s2 = d_gzhead s1 /\
  d_pending s2 = d_pending s1 /\ d_po s2 = d_po s1 /\ d_bi_valid s2 = d_bi_valid s1 /\
  (d_last_flush s2 = d_last_flush s1 \/ d_last_flush s2 = -1).

Lemma cs_like_lf : forall s1 (c : bool), cs_like s1 (if c then set_d_last_flush s1 (-1) else s1) /\
  d_status (if c then set_d_last_flush s1 (-1) else s1) = d_status s1.
Proof.
  intros s1 c. destruct c.
  - destruct s1. unfold cs_like. split; [|reflexivity].
    split; [unfold core_eq; repeat split; reflexivity|]. split; [intros H; exact H|].
    repeat split; auto.
  - unfold cs_like. split; [|reflexivity]. split; [apply core_eq_refl|]. split; [intros H; exact H|].
    repeat split; auto.
Qed.

Lemma cs_like_st : forall s1 st, cs_like s1 (set_d_status s1 st) /\ d_status (set_d_status s1 st) = st.
Proof.
  intros s1 st. destruct s1. unfold cs_like. split; [|reflexivity].
  split; [unfold core_eq; repeat split; reflexivity|]. split; [intros H; exact H|].
  repeat split; auto.
Qed.

Lemma cs_like_trans : forall s1 s2 s3, cs_like s1 s2 -> cs_like s2 s3 -> cs_like s1 s3.
Proof.
  intros s1 s2 s3 (A1 & B1 & C1 & D1 & E1 & F1 & G1 & H1) (A2 & B2 & C2 & D2 & E2 & F2 & G2 & H2).
  split; [eapply core_eq_trans; eauto|]. split; [auto|]. repeat split; try congruence.
  destruct H1, H2; [left|right|right|right]; congruence.
Qed.

(** The statement of LTBEvent.chain_acct, taken as a premise of [comp_stage_fx]. *)
Definition chain_acct_stmt : Prop := forall s0 flush evs g g' h E k,
  prm s0 -> (flush = Z_NO_FLUSH \/ flush = Z_FINISH) ->
  Forall (ev_ok s0 flush) evs -> Forall (ev_lvl s0) evs -> ev_chain g evs g' ->
  acct (bcls_of s0) h E k g -> 0 <= h -> E + sum_len evs <= 1048576 ->
  0 <= sum_len evs /\
  (Forall (fun e => ev_last e = 0) evs -> exists k', acct (bcls_of s0) h (E + sum_len evs) k' g') /\
  (last_ev evs -> g' <= 8 * (h + body (bcls_of s0) (E + sum_len evs))).

Section Comp.
Variable W : dstate -> Prop.
Variable HI : hdr_inv.
Hypothesis CF : core_facts W.
Hypothesis HF : hdr_facts HI.
Hypothesis BB : block_bound_statement.
Hypothesis CX : cpost_extra W.

Lemma cs_mid_after : forall n b pos0 inb aout tin0 tout0 flush gz0 s z s2 z' kk x H w0,
  Mid W HI n b pos0 inb aout tin0 tout0 flush gz0 s z -> z_next_in z = 0 ->
  zstep (d_wrap s) z z' kk x -> bytes x -> 0 <= z_avail_out z' -> z_total_out z <= 1099511627776 ->
  W s2 -> outok s2 -> d_gzhead s2 = d_gzhead s -> -2 <= d_last_flush s2 <= 5 -> gzh_ok s2 ->
  0 <= w0 <= 2 -> b = Zlength H + body (bcls_of s2) n + tlen w0 -> Zlength H <= 16384 ->
  bphase HI n (pos0 + kk) (flush =? Z_FINISH) s2 (z_total_out z') (z_adler z') H w0 ->
  Mid W HI n b pos0 inb aout tin0 tout0 flush gz0 s2 z'.
Proof.
  intros n b pos0 inb aout tin0 tout0 flush gz0 s z s2 z' kk x H w0
    ((Hin & _ & Hav & Htin & Hao & Hol & Hto & Hby) & Hbytes & Hpos0 & Hle & Hfl & Hfin & Haout &
     Htin0 & Htout0 & Hgz & Hbr) Hni
    (Zin & Hk & Zni & Zai & Ztin & Zad & Zout & Zxl & Zao & Zto & Zmsg) Hbx Hao' Htob
    HW2 Ho2 Egz Hlf2 Hgz2 Hw0 Hb HH Hph.
  destruct Hbr as (H1 & w1 & _ & _ & _ & _ & _ & Hn & Hpos & Htinb & Htout & _).
  rewrite Hni in *.
  pose proof (Zlength_nonneg x). pose proof (Zlength_nonneg (z_out z)).
  assert (Etin : z_total_in z' = z_total_in z + kk) by (rewrite Ztin; unfold u64; apply Z.mod_small; lia).
  assert (Etout : z_total_out z' = z_total_out z + Zlength x)
    by (rewrite Zto; unfold u64; apply Z.mod_small; lia).
  split.
  { unfold cframe. rewrite Zin, Zni, Zai, Etin, Etout, Zout, Zlength_app.
    repeat split; try lia; try assumption. unfold bytes in *. apply Forall_app. split; assumption. }
  split; [exact Hbytes|]. split; [exact Hpos0|]. split; [exact Hle|]. split; [exact Hfl|].
  split; [exact Hfin|]. split; [exact Haout|]. split; [exact Htin0|]. split; [exact Htout0|].
  split; [congruence|].
  rewrite Zni.
  exists H, w0. split; [exact HW2|]. split; [exact Ho2|]. split; [exact Hw0|]. split; [exact Hb|].
  split; [exact HH|]. split; [exact Hn|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [exact Hgz2|]. split; [exact Hlf2|]. exact Hph.
Qed.

Lemma comp_stage_fx : chain_acct_stmt -> hdr_facts HI ->
  (forall s z flush s' z' bs evs, cpost W s z flush s' z' bs evs -> 0 <= z_avail_out z') ->
  forall n b pos0 inb aout tin0 tout0 flush gz0 s z,
  Mid W HI n b pos0 inb aout tin0 tout0 flush gz0 s z -> z_next_in z = 0 ->
  (d_status s = BUSY_STATE \/ d_status s = FINISH_STATE) -> d_pending s = 0 -> d_po s = 0 ->
  d_bi_valid s <= 7 -> (d_status s = FINISH_STATE -> z_avail_in z = 0) ->
  exists s3 z3 o, c_deflate_compress s z flush = Some (s3, z3, o) /\
    Mid W HI n b pos0 inb aout tin0 tout0 flush gz0 s3 z3 /\
    (o = None -> flush = Z_NO_FLUSH \/
                 (d_status s3 = FINISH_STATE /\ d_pending s3 = 0 /\ d_po s3 = 0 /\ z_avail_in z3 = 0)) /\
    (forall c, o = Some c -> c = Z_OK) /\
    (flush = Z_FINISH -> pos0 = 0 -> b <= tout0 + aout -> d_status s = BUSY_STATE -> o = None).
Proof.
  intros CA HF0 AO n b pos0 inb aout tin0 tout0 flush gz0 s z HM Hni Hst Hpd Hpo Hbi Hfa.
  pose proof HM as HM0.
  destruct HM as ((Hin & _ & Hav & Htin & Hao & Hol & Hto & Hby) & Hbytes & Hpos0 & Hle & Hfl & Hfin & Haout &
                  Htin0 & Htout0 & Hgz & Hbr).
  rewrite Hni in *.
  destruct Hbr as (H & w0 & HW & Ho & Hw0 & Hb & HH & Hn & Hpos & Htinb & Htout & Hgzok & Hlf & Hph).
  destruct (cf_pos W CF s HW) as (L1 & L2 & L3 & L4).
  unfold c_deflate_compress.
  destruct (negb (z_avail_in z =? 0) || negb (d_lookahead s =? 0) ||
            (negb (flush =? Z_NO_FLUSH) && negb (d_status s =? FINISH_STATE))) eqn:G.
  2:{ exists s, z, None. split; [reflexivity|]. split; [exact HM0|].
      split; [|split; [intros c Hc; discriminate Hc|intros; reflexivity]].
      intros _. apply orb_false_iff in G. destruct G as [G1 G2]. apply orb_false_iff in G1.
      destruct G1 as [G0 _]. apply negb_false_iff, Z.eqb_eq in G0.
      apply andb_false_iff in G2. destruct G2 as [G2|G2]; apply negb_false_iff, Z.eqb_eq in G2.
      - left; exact G2.
      - right. auto. }
  destruct Hph as [P0|[P1|[P2|P3]]].
  { exfalso. destruct P0 as (Hs0 & _). rewrite Hs0 in Hst.
    unfold BUSY_STATE, FINISH_STATE, INIT_STATE, GZIP_STATE in Hst. destruct (w0 =? 2); lia. }
  { exfalso. destruct P1 as (_ & _ & (k & HI1 & _) & _).
    destruct (hf_status HI HF0 _ _ _ _ HI1) as (_ & _ & Hs1 & _).
    unfold BUSY_STATE, FINISH_STATE, EXTRA_STATE, NAME_STATE, COMMENT_STATE, HCRC_STATE in *. lia. }
  2:{ exfalso. destruct P3 as (Hs3 & _ & _ & Hub & _). unfold ub in Hub.
      assert (Hla : d_lookahead s = 0) by lia. rewrite (Hfa Hs3), Hla, Hs3 in G.
      repeat rewrite Z.eqb_refl in G. cbn in G. destruct (negb (flush =? Z_NO_FLUSH)); discriminate G. }
  destruct P2 as (Hs2 & Hwr & _ & Had & E & k & HE & Hk0 & Hmk & Hg).
  pose proof (cf_prm W CF s HW) as Hprm.
  assert (Hbi0 : 0 <= d_bi_valid s)
    by (destruct Ho as (_ & (B1 & _ & B3) & _); unfold d_bi_valid; lia).
  assert (Hmb : 0 < minblk (bcls_of s)) by (destruct (bcls_of s); cbn; lia).
  unfold ub in HE.
  assert (HE0 : 0 <= E) by nia.
  pose proof (cs_acc_mid (bcls_of s) (Zlength H) E k n (Zlength_nonneg H) Hk0 Hmk ltac:(lia)) as Ham.
  pose proof (cs_body_range (bcls_of s) n Hn) as Hbr.
  pose proof (Zlength_nonneg H) as HH0.
  assert (Htob : z_total_out z <= 1099511627776) by (unfold Gb in Hg; lia).
  assert (Hzin : zin_ok z).
  { pose proof (Zlength_nonneg inb). pose proof (Zlength_nonneg (z_out z)).
    unfold zin_ok. rewrite Hin, Hni. repeat split; first [exact Hbytes | lia]. }
  assert (Hq : quiet s) by (unfold quiet; auto).
  assert (Hfr : 0 <= flush <= 5) by (destruct Hfl as [-> | ->]; unfold Z_NO_FLUSH, Z_FINISH; lia).
  assert (Hap : adler_pre (d_wrap s) (z_adler z))
    by (unfold adler_pre; destruct Had as [A1 A2]; split; intros Hw1; [apply A1|apply A2]; congruence).
  destruct (cf_compress W CF s z flush HW Ho Hq Hfr Hzin ltac:(lia) Hap) as (s' & z' & bs & evs & Ec & Hcp).
  destruct (CX _ _ _ _ _ _ _ Hcp) as [Hlvl [Hbi' _]].
  pose proof (AO _ _ _ _ _ _ _ Hcp) as Hao'.
  destruct Hcp as (HW' & Ho' & Hsp & Hae & (kk & x & Hzs & Hbx & Hkk) & Hch & Hevok & Hbs).
  pose proof Hzs as Hzs0. destruct Hzs as (Zin & Hk & Zni & Zai & Ztin & Zad & Zout & Zxl & Zao & Zto & Zmsg).
  rewrite Hni in *.
  destruct (cf_pos W CF s' HW') as (M1 & M2 & M3 & M4).
  destruct (CA s flush evs _ _ (Zlength H) E k Hprm Hfl Hevok Hlvl Hch (conj Hk0 (conj Hmk Hg)) HH0
              ltac:(unfold ub in *; lia)) as (Hsl & Hmid & Hlast).
  assert (Ecl : bcls_of s' = bcls_of s)
    by (destruct Hsp as (A1 & A2 & A3 & A4 & A5 & A6 & A7); unfold bcls_of, tight_b; rewrite A1, A3, A6, A7;
        reflexivity).
  destruct Hae as (Est' & Ewr' & Egz' & Egi' & Elf' & _).
  pose proof (Zlength_nonneg inb) as Hib. pose proof (Zlength_nonneg (z_out z)) as Hzo.
  pose proof (Zlength_nonneg x) as Hx0.
  assert (Ebs : E + sum_len evs + ub s' = pos0 + kk) by (unfold ub in *; lia).
  assert (Hub' : 0 <= ub s') by (unfold ub; lia).
  assert (Etout : z_total_out z' = z_total_out z + Zlength x)
    by (rewrite Zto; unfold u64; apply Z.mod_small; lia).
  assert (Ho'r : 0 <= d_pending s' /\ 0 <= d_bi_valid s')
    by (destruct Ho' as (_ & (B1 & _ & B3) & _); unfold d_bi_valid, d_pending; lia).
  assert (Had' : adler_ok w0 (z_adler z')).
  { rewrite Zad, Hwr, Hin. apply cs_adler_ok; [exact Had|]. apply Forall_sublist. exact Hbytes. }
  (* the state after the call, in every case *)
  assert (Hafter : forall s2, cs_like s' s2 ->
    bphase HI n (pos0 + kk) (flush =? Z_FINISH) s2 (z_total_out z') (z_adler z') H w0 ->
    Mid W HI n b pos0 inb aout tin0 tout0 flush gz0 s2 z').
  { intros s2 (Hce & Hoo & Ew & Eg & Ep & Epo & Eb & Elf1) Hph2.
    apply (cs_mid_after n b pos0 inb aout tin0 tout0 flush gz0 s z s2 z' kk x H w0 HM0 Hni Hzs0 Hbx Hao' Htob).
    - exact (cf_frame W CF s' s2 HW' Hce).
    - exact (Hoo Ho').
    - congruence.
    - destruct Elf1; lia.
    - unfold gzh_ok in *. rewrite Eg, Egz'. exact Hgzok.
    - exact Hw0.
    - rewrite (bcls_core_eq s' s2 Hce), Ecl. exact Hb.
    - exact HH.
    - exact Hph2. }
  (* deflate_stored with room for everything finishes *)
  assert (Hlive : flush = Z_FINISH -> pos0 = 0 -> b <= tout0 + aout -> d_level s = 0 -> bs = finish_done).
  { intros Hf Hp0 Hbo Hl0. subst flush.
    assert (Hk00 : k = 0) by (destruct (bcls_of s); cbn [minblk] in Hmk; lia). subst k.
    assert (Hcl : bcls_of s <> BFixed).
    { unfold bcls_of. destruct (tight_b s); [discriminate|]. rewrite Hl0. cbn.
      rewrite andb_false_r. discriminate. }
    pose proof (cs_stored_room (bcls_of s) n Hcl Hn) as Hsr.
    assert (Hsh : stored_hdr s <= 6).
    { unfold stored_hdr. change (o_bi_valid (tr_out (d_tr s))) with (d_bi_valid s). unfold u32.
      rewrite (Z.mod_small (d_bi_valid s)) by lia. rewrite Z.mod_small by lia.
      rewrite Z.shiftr_div_pow2 by lia.
      assert ((d_bi_valid s + 42) / 2 ^ 3 < 7) by (apply Z.div_lt_upper_bound; cbn; lia). lia. }
    assert (Hxb : xb (bcls_of s) (Zlength H) E 0 = 8 * Zlength H) by (unfold xb; destruct (bcls_of s); lia).
    rewrite Hxb in Hg. unfold Gb in Hg. unfold tlen in Hb.
    apply (cf_stored_live W CF s z s' z' bs HW Ho Hq Hzin ltac:(lia) Hap Hl0); [|exact Ec].
    unfold ub. assert (Hu0 : d_strstart s - d_block_start s + d_lookahead s = 0) by lia. rewrite Hu0.
    assert (Hai : z_avail_in z = n) by lia. rewrite Hai.
    rewrite Z.add_0_l. destruct (w0 =? 1), (w0 =? 2); unfold MAX_STORED; lia. }
  (* after the last block *)
  assert (HP3 : forall s2, cs_like s' s2 -> d_status s2 = FINISH_STATE -> flush = Z_FINISH ->
            z_avail_in z' = 0 -> ub s' = 0 -> d_sym_next s' = 0 -> d_bi_valid s' = 0 -> last_ev evs ->
            Mid W HI n b pos0 inb aout tin0 tout0 flush gz0 s2 z').
  { intros s2 Hcl Hst2 Hf Hai0 Hu0 Hsy Hb0 Hle'. apply Hafter; [exact Hcl|].
    destruct Hcl as (Hce & _ & Ew & _ & Ep & _ & Eb & _).
    pose proof (core_eq_fields s' s2 Hce) as (_ & _ & _ & _ & _ & _ & _ & _ & Esy & _).
    assert (Hpn : pos0 + kk = n) by (specialize (Hfin Hf); lia).
    right; right; right. split; [exact Hst2|]. split; [rewrite Hf; reflexivity|]. split; [exact Hpn|].
    split; [rewrite (ub_core_eq s' s2 Hce); exact Hu0|]. split; [congruence|]. split; [congruence|].
    split; [exact Had'|]. left. split; [congruence|].
    rewrite (bcls_core_eq s' s2 Hce), Ecl. specialize (Hlast Hle').
    assert (En : E + sum_len evs = n) by lia. rewrite En in Hlast. unfold Gb in *. rewrite Ep, Eb. exact Hlast. }
  rewrite Ec. cbn [bind].
  destruct bs.
  - (* need_more *)
    destruct Hbs as (Hall & _ & Hnm). destruct (Hmid Hall) as (k' & Hk'0 & Hmk' & Hg').
    destruct (cs_like_lf s' (z_avail_out z' =? 0)) as [Hcl Hst1].
    eexists _, z', (Some Z_OK). split; [reflexivity|].
    split.
    { apply Hafter; [exact Hcl|]. right; right; left.
      destruct Hcl as (Hce & _ & Ew & _ & Ep & _ & Eb & _).
      split; [congruence|]. split; [congruence|]. split; [rewrite Eb; exact (Hbi' eq_refl)|].
      split; [exact Had'|]. exists (E + sum_len evs), k'.
      split; [rewrite (ub_core_eq s' _ Hce); lia|].
      rewrite (bcls_core_eq s' _ Hce), Ecl. unfold Gb in *. rewrite Ep, Eb.
      split; [exact Hk'0|]. split; [exact Hmk'|]. exact Hg'. }
    split; [intros Hc; discriminate Hc|]. split; [intros c Hc; injection Hc; auto|].
    intros Hf Hp0 Hbo _. exfalso.
    destruct (Z.eq_dec (d_level s) 0) as [Hl0|Hl0]; [specialize (Hlive Hf Hp0 Hbo Hl0); discriminate Hlive|].
    destruct Hnm as [Hnf|[Ha0|Hl]]; [rewrite Hf in Hnf; discriminate Hnf| |contradiction].
    pose proof (cs_acc_mid (bcls_of s) (Zlength H) (E + sum_len evs) k' n HH0 Hk'0 Hmk' ltac:(lia)) as Ham'.
    assert (Hla : Zlength (z_out z') = Zlength (z_out z) + Zlength x) by (rewrite Zout; apply Zlength_app).
    unfold Gb in Hg'. unfold tlen in Hb. destruct (w0 =? 1), (w0 =? 2); lia.
  - (* block_done: not for Z_NO_FLUSH / Z_FINISH *)
    exfalso. destruct Hbs as (_ & Hn1 & Hn2 & _). destruct Hfl; contradiction.
  - (* finish_started *)
    destruct Hbs as (Hle' & Hff & Hai0 & Hu0 & Hsy & Hb0 & Ha0 & Hpw).
    destruct (cs_like_st s' FINISH_STATE) as [Hc1 Hs1].
    destruct (cs_like_lf (set_d_status s' FINISH_STATE) (z_avail_out z' =? 0)) as [Hc2 Hs2'].
    eexists _, z', (Some Z_OK). split; [reflexivity|].
    split.
    { apply HP3; [exact (cs_like_trans _ _ _ Hc1 Hc2)|congruence|exact Hff|exact Hai0|exact Hu0|exact Hsy|
                  exact Hb0|exact Hle']. }
    split; [intros Hc; discriminate Hc|]. split; [intros c Hc; injection Hc; auto|].
    intros Hf Hp0 Hbo _. exfalso.
    destruct (Z.eq_dec (d_level s) 0) as [Hl0|Hl0]; [specialize (Hlive Hf Hp0 Hbo Hl0); discriminate Hlive|].
    specialize (Hlast Hle'). specialize (Hpw Hl0).
    assert (En : E + sum_len evs = n) by (specialize (Hfin Hf); lia). rewrite En in Hlast.
    assert (Hla : Zlength (z_out z') = Zlength (z_out z) + Zlength x) by (rewrite Zout; apply Zlength_app).
    unfold Gb in Hlast. rewrite Hb0 in Hlast. unfold tlen in Hb.
    destruct Hpw as [Hpw|Hpw]; [|rewrite Hwr in Hpw];
      destruct (Z.eqb_spec w0 1), (Z.eqb_spec w0 2); lia.
  - (* finish_done *)
    destruct Hbs as (Hle' & Hff & Hai0 & Hu0 & Hsy & Hq' & Hb0).
    destruct (cs_like_st s' FINISH_STATE) as [Hc1 Hs1].
    exists (set_d_status s' FINISH_STATE), z', None. split; [reflexivity|].
    split; [apply HP3; [exact Hc1|exact Hs1|exact Hff|exact Hai0|exact Hu0|exact Hsy|exact Hb0|exact Hle']|].
    split.
    { intros _. right. destruct Hq' as (Q1 & Q2 & _).
      split; [exact Hs1|]. split; [exact Q1|]. split; [exact Q2|exact Hai0]. }
    split; [intros c Hc; discriminate Hc|]. intros; reflexivity.
Qed.

(** The target under the two fixes (Section hypothesis [hdr_facts HI]; [0 <= z_avail_out z'] in cpost_extra):
    with LTBEvent.chain_acct. *)
Lemma comp_stage_fixed : hdr_facts HI ->
  (forall s z flush s' z' bs evs, cpost W s z flush s' z' bs evs -> 0 <= z_avail_out z') ->
  forall n b pos0 inb aout tin0 tout0 flush gz0 s z,
  Mid W HI n b pos0 inb aout tin0 tout0 flush gz0 s z -> z_next_in z = 0 ->
  (d_status s = BUSY_STATE \/ d_status s = FINISH_STATE) -> d_pending s = 0 -> d_po s = 0 ->
  d_bi_valid s <= 7 -> (d_status s = FINISH_STATE -> z_avail_in z = 0) ->
  exists s3 z3 o, c_deflate_compress s z flush = Some (s3, z3, o) /\
    Mid W HI n b pos0 inb aout tin0 tout0 flush gz0 s3 z3 /\
    (o = None -> flush = Z_NO_FLUSH \/
                 (d_status s3 = FINISH_STATE /\ d_pending s3 = 0 /\ d_po s3 = 0 /\ z_avail_in z3 = 0)) /\
    (forall c, o = Some c -> c = Z_OK) /\
    (flush = Z_FINISH -> pos0 = 0 -> b <= tout0 + aout -> d_status s = BUSY_STATE -> o = None).
Proof. intros HF' AO. exact (comp_stage_fx (chain_acct BB) HF' AO). Qed.

Lemma comp_stage : forall n b pos0 inb aout tin0 tout0 flush gz0 s z,
  Mid W HI n b pos0 inb aout tin0 tout0 flush gz0 s z -> z_next_in z = 0 ->
  (d_status s = BUSY_STATE \/ d_status s = FINISH_STATE) -> d_pending s = 0 -> d_po s = 0 ->
  d_bi_valid s <= 7 -> (d_status s = FINISH_STATE -> z_avail_in z = 0) ->
  exists s3 z3 o, c_deflate_compress s z flush = Some (s3, z3, o) /\
    Mid W HI n b pos0 inb aout tin0 tout0 flush gz0 s3 z3 /\
    (o = None -> flush = Z_NO_FLUSH \/
                 (d_status s3 = FINISH_STATE /\ d_pending s3 = 0 /\ d_po s3 = 0 /\ z_avail_in z3 = 0)) /\
    (forall c, o = Some c -> c = Z_OK) /\
    (flush = Z_FINISH -> pos0 = 0 -> b <= tout0 + aout -> d_status s = BUSY_STATE -> o = None).
Proof.
  exact (comp_stage_fixed HF (fun s z f s' z' bs evs H => proj2 (proj2 (CX s z f s' z' bs evs H)))).
Qed.

End Comp.
