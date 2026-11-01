(** * The deflateBound accounting for the short laws: stage 8 of deflate() (the compression) inside [MidW]

    Port of LTBComp.comp_stage to the invariants of LTWBDefs.v: [cw_compress] (LTWIface.core_facts_w) and its
    [cpost], the blocks accounted by LTWBEvent.chain_acct_w (no size limit), at level 0 with Z_FINISH and room
    for everything [cw_stored_live].  At level 0 with a flush other than Z_NO_FLUSH the caller gives either
    [cw_compress]'s condition [ub s + avail_in < 2^32] (res_bound: the bytes in the window and the bytes offered
    are at most the n < 2^32 bytes of the stream) or the result of the compression call itself (the clip() loops
    of LawFactsW2: from LTWIfaceClip.cw_compress_clip).  After the stage the window ([ub]) is the one the compressor
    left, if it was called: only in BUSY_STATE.  The call offers at most 2^32-1 bytes (avail_in is a 32-bit field). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTWBKit.
Require Import Zlib.proof.deflate.LTWBEvent.
Require Import Zlib.proof.deflate.LTBComp.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** LTBound.cpost_extra_ok for any [W]: every DFlush event is at level > 0, need_more leaves at most 7 bits in the
    bit buffer, the output space is not overrun (all three are read off [cpost] itself). *)
Lemma cpost_extra_w : forall W, cpost_extra W.
Proof.
  intros W s z flush s' z' bs evs (_ & _ & _ & _ & (k & x & Hz & _) & _ & Hev & Hbs).
  split; [|split].
  - eapply Forall_impl; [|exact Hev]. intros [g t syms buf sl last|g len last]; cbn; [tauto|auto].
  - intros ->. destruct Hbs as (_ & Hb & _). exact Hb.
  - destruct Hz as (_ & _ & _ & _ & _ & _ & _ & Hx & Ha & _). pose proof (Zlength_nonneg x). lia.
Qed.

(** LTBComp.cs_mid_after for [MidW]: after the compression function ([zstep] consumed [kk] bytes and produced
    [x]), [MidW] holds again for a state [s2] of the phase [bphase] at the new position.  total_out stays
    below 2^64 (it is at most the bound [b <= 2^63+2^62] plus at most 2^32-1 bytes of output space), so the model's wrap-around does not
    occur. *)
Lemma cs_mid_after_w : forall W HI n b pos0 inb aout tin0 tout0 flush gz0 s z s2 z' kk x H w0,
  MidW W HI n b pos0 inb aout tin0 tout0 flush gz0 s z -> z_next_in z = 0 ->
  zstep (d_wrap s) z z' kk x -> bytes x -> 0 <= z_avail_out z' -> z_total_out z <= 13835058055282163712 ->
  W s2 -> outok s2 -> d_gzhead s2 = d_gzhead s -> -2 <= d_last_flush s2 <= 5 -> gzh_ok_w s2 ->
  0 <= w0 <= 2 -> b = Zlength H + body (bcls_of s2) n + tlen w0 -> Zlength H <= 17179869184 ->
  bphase HI n (pos0 + kk) (flush =? Z_FINISH) s2 (z_total_out z') (z_adler z') H w0 ->
  MidW W HI n b pos0 inb aout tin0 tout0 flush gz0 s2 z'.
Proof.
  intros W HI n b pos0 inb aout tin0 tout0 flush gz0 s z s2 z' kk x H w0
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

Lemma comp_stage_w : block_bound_statement -> forall W HI, core_facts_w W -> hdr_facts_w HI ->
  forall n b pos0 inb aout tin0 tout0 flush gz0 s z,
  MidW W HI n b pos0 inb aout tin0 tout0 flush gz0 s z -> z_next_in z = 0 -> Zlength inb <= 4294967295 ->
  (d_status s = BUSY_STATE \/ d_status s = FINISH_STATE) -> d_pending s = 0 -> d_po s = 0 ->
  d_bi_valid s <= 7 -> (d_status s = FINISH_STATE -> z_avail_in z = 0) ->
  ((d_level s = 0 -> flush <> Z_NO_FLUSH -> ub s + z_avail_in z <= 4294967295) \/
   (exists s' z' bs evs, c_compress_func s z flush = Some (s', z', bs) /\ cpost W s z flush s' z' bs evs)) ->
  exists s3 z3 o, c_deflate_compress s z flush = Some (s3, z3, o) /\
    MidW W HI n b pos0 inb aout tin0 tout0 flush gz0 s3 z3 /\ 0 <= z_avail_in z3 /\
    ((ub s3 = ub s /\ d_level s3 = d_level s) \/
     (d_status s = BUSY_STATE /\
      exists s' z' bs, c_compress_func s z flush = Some (s', z', bs) /\ ub s3 = ub s' /\ d_level s3 = d_level s)) /\
    (o = None -> flush = Z_NO_FLUSH \/
                 (d_status s3 = FINISH_STATE /\ d_pending s3 = 0 /\ d_po s3 = 0 /\ z_avail_in z3 = 0)) /\
    (forall c, o = Some c -> c = Z_OK) /\
    (flush = Z_FINISH -> pos0 = 0 -> b <= tout0 + aout -> d_status s = BUSY_STATE -> o = None).
Proof.
  intros BB W HI CF HF n b pos0 inb aout tin0 tout0 flush gz0 s z HM Hni Hib Hst Hpd Hpo Hbi Hfa Hcall.
  pose proof HM as HM0.
  destruct HM as ((Hin & _ & Hav & Htin & Hao & Hol & Hto & Hby) & Hbytes & Hpos0 & Hle & Hfl & Hfin & Haout &
                  Htin0 & Htout0 & Hgz & Hbr).
  pose proof (brunw_facts W HI CF HF _ _ _ _ _ _ _ _ Hbr) as (_ & _ & _ & Htb & Hb33 & _ & Hn32 & Htinr & _).
  rewrite Hni in *.
  destruct Hbr as (H & w0 & HW & Ho & Hw0 & Hb & HH & Hn & Hpos & Htinb & Htout & Hgzok & Hlf & Hph).
  destruct (cw_pos W CF s HW) as (L1 & L2 & L3 & L4).
  pose proof (Zlength_nonneg inb) as Hib0.
  unfold c_deflate_compress.
  destruct (negb (z_avail_in z =? 0) || negb (d_lookahead s =? 0) ||
            (negb (flush =? Z_NO_FLUSH) && negb (d_status s =? FINISH_STATE))) eqn:G.
  2:{ exists s, z, None. split; [reflexivity|]. split; [exact HM0|]. split; [lia|]. split; [left; split; reflexivity|].
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
    destruct (hw_status HI HF _ _ _ _ HI1) as (_ & _ & Hs1 & _).
    unfold BUSY_STATE, FINISH_STATE, EXTRA_STATE, NAME_STATE, COMMENT_STATE, HCRC_STATE in *. lia. }
  2:{ exfalso. destruct P3 as (Hs3 & _ & _ & Hub & _). unfold ub in Hub.
      assert (Hla : d_lookahead s = 0) by lia. rewrite (Hfa Hs3), Hla, Hs3 in G.
      repeat rewrite Z.eqb_refl in G. cbn in G. destruct (negb (flush =? Z_NO_FLUSH)); discriminate G. }
  destruct P2 as (Hs2 & Hwr & _ & Had & E & k & HE & Hk0 & Hmk & Hg).
  pose proof (cw_prm W CF s HW) as Hprm.
  assert (Hbi0 : 0 <= d_bi_valid s)
    by (destruct Ho as (_ & (B1 & _ & B3) & _); unfold d_bi_valid; lia).
  assert (Hmb : 0 < minblk (bcls_of s)) by (destruct (bcls_of s); cbn; lia).
  unfold ub in HE.
  assert (HE0 : 0 <= E) by nia.
  pose proof (acc_mid_w (bcls_of s) (Zlength H) E k n (Zlength_nonneg H) Hk0 Hmk ltac:(lia)) as Ham.
  pose proof (body_range_w (bcls_of s) n (proj1 Hn)) as Hbr.
  pose proof (Zlength_nonneg H) as HH0.
  assert (Htob : z_total_out z <= 13835058055282163712) by lia.
  assert (Hzin : zin_okw z).
  { pose proof (Zlength_nonneg (z_out z)).
    unfold zin_okw. rewrite Hin, Hni. repeat split; first [exact Hbytes | lia]. }
  assert (Hq : quiet s) by (unfold quiet; auto).
  assert (Hfr : 0 <= flush <= 5) by (destruct Hfl as [-> | ->]; unfold Z_NO_FLUSH, Z_FINISH; lia).
  assert (Hap : adler_pre (d_wrap s) (z_adler z))
    by (unfold adler_pre; destruct Had as [A1 A2]; split; intros Hw1; [apply A1|apply A2]; congruence).
  assert (Hex : exists s' z' bs evs, c_compress_func s z flush = Some (s', z', bs) /\ cpost W s z flush s' z' bs evs).
  { destruct Hcall as [Hl0c|Hx]; [exact (cw_compress W CF s z flush HW Ho Hq Hfr Hzin ltac:(lia) Hap)|exact Hx]. }
  clear Hcall. destruct Hex as (s' & z' & bs & evs & Ec & Hcp).
  destruct (cpost_extra_w _ _ _ _ _ _ _ _ Hcp) as [Hlvl [Hbi' Hao']].
  destruct Hcp as (HW' & Ho' & Hsp & Hae & (kk & x & Hzs & Hbx & Hkk) & Hch & Hevok & Hbs).
  pose proof Hzs as Hzs0. destruct Hzs as (Zin & Hk & Zni & Zai & Ztin & Zad & Zout & Zxl & Zao & Zto & Zmsg).
  rewrite Hni in *.
  destruct (cw_pos W CF s' HW') as (M1 & M2 & M3 & M4).
  destruct (chain_acct_w BB s flush evs _ _ (Zlength H) E k Hprm Hfl Hevok Hlvl Hch (conj Hk0 (conj Hmk Hg)) HH0)
    as (Hsl & Hmid & Hlast).
  assert (Ecl : bcls_of s' = bcls_of s)
    by (destruct Hsp as (A1 & A2 & A3 & A4 & A5 & A6 & A7); unfold bcls_of, tight_b; rewrite A1, A3, A6, A7;
        reflexivity).
  destruct Hae as (Est' & Ewr' & Egz' & Egi' & Elf' & _).
  pose proof (Zlength_nonneg (z_out z)) as Hzo.
  pose proof (Zlength_nonneg x) as Hx0.
  assert (Ebs : E + sum_len evs + ub s' = pos0 + kk) by (unfold ub in *; lia).
  assert (Hub' : 0 <= ub s') by (unfold ub; lia).
  assert (Etout : z_total_out z' = z_total_out z + Zlength x)
    by (rewrite Zto; unfold u64; apply Z.mod_small; lia).
  assert (Ho'r : 0 <= d_pending s' /\ 0 <= d_bi_valid s')
    by (destruct Ho' as (_ & (B1 & _ & B3) & _); unfold d_bi_valid, d_pending; lia).
  assert (Had' : adler_ok w0 (z_adler z')).
  { rewrite Zad, Hwr, Hin. apply cs_adler_ok; [exact Had|]. apply Forall_sublist. exact Hbytes. }
  assert (Hai' : 0 <= z_avail_in z') by lia.
  (* the state after the call, in every case *)
  assert (Hafter : forall s2, cs_like s' s2 ->
    bphase HI n (pos0 + kk) (flush =? Z_FINISH) s2 (z_total_out z') (z_adler z') H w0 ->
    MidW W HI n b pos0 inb aout tin0 tout0 flush gz0 s2 z').
  { intros s2 (Hce & Hoo & Ew & Eg & Ep & Epo & Eb & Elf1) Hph2.
    apply (cs_mid_after_w W HI n b pos0 inb aout tin0 tout0 flush gz0 s z s2 z' kk x H w0 HM0 Hni Hzs0 Hbx Hao'
             Htob).
    - exact (cw_frame W CF s' s2 HW' Hce).
    - exact (Hoo Ho').
    - congruence.
    - destruct Elf1; lia.
    - unfold gzh_ok_w in *. rewrite Eg, Egz'. exact Hgzok.
    - exact Hw0.
    - rewrite (bcls_core_eq s' s2 Hce), Ecl. exact Hb.
    - exact HH.
    - exact Hph2. }
  (* the window and the level after the call *)
  assert (Hul : forall s2, cs_like s' s2 -> ub s2 = ub s' /\ d_level s2 = d_level s).
  { intros s2 (Hce & _).
    pose proof (core_eq_fields s' s2 Hce) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & El2 & _).
    destruct Hsp as (_ & _ & _ & _ & _ & El' & _).
    split; [exact (ub_core_eq s' s2 Hce)|congruence]. }
  (* deflate_stored with room for everything finishes *)
  assert (Hlive : flush = Z_FINISH -> pos0 = 0 -> b <= tout0 + aout -> d_level s = 0 -> bs = finish_done).
  { intros Hf Hp0 Hbo Hl0. subst flush.
    assert (Hk00 : k = 0) by (destruct (bcls_of s); cbn [minblk] in Hmk; lia). subst k.
    assert (Hcl : bcls_of s <> BFixed).
    { unfold bcls_of. destruct (tight_b s); [discriminate|]. rewrite Hl0. cbn.
      rewrite andb_false_r. discriminate. }
    pose proof (stored_room_w (bcls_of s) n Hcl (proj1 Hn)) as Hsr.
    assert (Hsh : stored_hdr s <= 6).
    { unfold stored_hdr. change (o_bi_valid (tr_out (d_tr s))) with (d_bi_valid s). unfold u32.
      rewrite (Z.mod_small (d_bi_valid s)) by lia. rewrite Z.mod_small by lia.
      rewrite Z.shiftr_div_pow2 by lia.
      assert ((d_bi_valid s + 42) / 2 ^ 3 < 7) by (apply Z.div_lt_upper_bound; cbn; lia). lia. }
    assert (Hxb : xb (bcls_of s) (Zlength H) E 0 = 8 * Zlength H) by (unfold xb; destruct (bcls_of s); lia).
    rewrite Hxb in Hg. unfold Gb in Hg. unfold tlen in Hb.
    apply (cw_stored_live W CF s z s' z' bs HW Ho Hq Hzin ltac:(lia) Hap Hl0); [|exact Ec].
    unfold ub. assert (Hu0 : d_strstart s - d_block_start s + d_lookahead s = 0) by lia. rewrite Hu0.
    assert (Hai : z_avail_in z = n) by lia. rewrite Hai.
    rewrite Z.add_0_l. destruct (w0 =? 1), (w0 =? 2); unfold MAX_STORED; lia. }
  (* after the last block *)
  assert (HP3 : forall s2, cs_like s' s2 -> d_status s2 = FINISH_STATE -> flush = Z_FINISH ->
            z_avail_in z' = 0 -> ub s' = 0 -> d_sym_next s' = 0 -> d_bi_valid s' = 0 -> last_ev evs ->
            MidW W HI n b pos0 inb aout tin0 tout0 flush gz0 s2 z').
  { intros s2 Hcl Hst2 Hf Hai0 Hu0 Hsy Hb0 Hle'. apply Hafter; [exact Hcl|].
    destruct Hcl as (Hce & _ & Ew & _ & Ep & _ & Eb & _).
    pose proof (core_eq_fields s' s2 Hce) as (_ & _ & _ & _ & _ & _ & _ & _ & Esy & _).
    assert (Hpn : pos0 + kk = n) by (specialize (Hfin Hf); lia).
    right; right; right. split; [exact Hst2|]. split; [rewrite Hf; reflexivity|]. split; [exact Hpn|].
    split; [rewrite (ub_core_eq s' s2 Hce); exact Hu0|]. split; [congruence|]. split; [congruence|].
    split; [exact Had'|]. left. split; [congruence|].
    rewrite (bcls_core_eq s' s2 Hce), Ecl. specialize (Hlast Hle').
    assert (En : E + sum_len evs = n) by lia. rewrite En in Hlast.
    pose proof (slk_range n). unfold Gb in *. rewrite Ep, Eb. lia. }
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
    split; [exact Hai'|].
    split; [right; split; [exact Hs2|eexists _, _, _; split; [reflexivity|exact (Hul _ Hcl)]]|].
    split; [intros Hc; discriminate Hc|]. split; [intros c Hc; injection Hc; auto|].
    intros Hf Hp0 Hbo _. exfalso.
    destruct (Z.eq_dec (d_level s) 0) as [Hl0|Hl0]; [specialize (Hlive Hf Hp0 Hbo Hl0); discriminate Hlive|].
    destruct Hnm as [Hnf|[Ha0|Hl]]; [rewrite Hf in Hnf; discriminate Hnf| |contradiction].
    pose proof (acc_mid_w (bcls_of s) (Zlength H) (E + sum_len evs) k' n HH0 Hk'0 Hmk' ltac:(lia)) as Ham'.
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
    split; [exact Hai'|].
    split; [right; split; [exact Hs2|eexists _, _, _;
                              split; [reflexivity|exact (Hul _ (cs_like_trans _ _ _ Hc1 Hc2))]]|].
    split; [intros Hc; discriminate Hc|]. split; [intros c Hc; injection Hc; auto|].
    intros Hf Hp0 Hbo _. exfalso.
    destruct (Z.eq_dec (d_level s) 0) as [Hl0|Hl0]; [specialize (Hlive Hf Hp0 Hbo Hl0); discriminate Hlive|].
    specialize (Hlast Hle'). specialize (Hpw Hl0).
    assert (En : E + sum_len evs = n) by (specialize (Hfin Hf); lia). rewrite En in Hlast.
    pose proof (slk_range n).
    assert (Hla : Zlength (z_out z') = Zlength (z_out z) + Zlength x) by (rewrite Zout; apply Zlength_app).
    unfold Gb in Hlast. rewrite Hb0 in Hlast. unfold tlen in Hb.
    destruct Hpw as [Hpw|Hpw]; [|rewrite Hwr in Hpw];
      destruct (Z.eqb_spec w0 1), (Z.eqb_spec w0 2); lia.
  - (* finish_done *)
    destruct Hbs as (Hle' & Hff & Hai0 & Hu0 & Hsy & Hq' & Hb0).
    destruct (cs_like_st s' FINISH_STATE) as [Hc1 Hs1].
    exists (set_d_status s' FINISH_STATE), z', None. split; [reflexivity|].
    split; [apply HP3; [exact Hc1|exact Hs1|exact Hff|exact Hai0|exact Hu0|exact Hsy|exact Hb0|exact Hle']|].
    split; [exact Hai'|].
    split; [right; split; [exact Hs2|eexists _, _, _; split; [reflexivity|exact (Hul _ Hc1)]]|].
    split.
    { intros _. right. destruct Hq' as (Q1 & Q2 & _).
      split; [exact Hs1|]. split; [exact Q1|]. split; [exact Q2|exact Hai0]. }
    split; [intros c Hc; discriminate Hc|]. intros; reflexivity.
Qed.
