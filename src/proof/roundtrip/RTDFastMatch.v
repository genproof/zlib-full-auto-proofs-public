(** * RT-D part FAST, piece: fmatch_stmt (statement and definitions: RTDFastKit.v). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDFastKit.
Require Import Zlib.proof.roundtrip.RTDFastMatchLoop.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** Lists (fm_lz_copy, fm_syms_data_app, fm_syms_rok_app: copies of those of RTDSlowFMatch.v) *)

(* the overlapping copy of n bytes at distance d after the first q bytes of H *)
Lemma fm_lz_copy (H : list Z) d : forall n q,
  1 <= d <= q -> q + Z.of_nat n <= Zlength H ->
  (forall i, 0 <= i < Z.of_nat n -> Znth (q - d + i) H = Znth (q + i) H) ->
  F.lz_copy n d (sublist 0 q H) = sublist 0 (q + Z.of_nat n) H.
Proof.
  induction n as [|n IH]; intros q Hd Hl Hi.
  - cbn. rewrite Z.add_0_r. reflexivity.
  - cbn [F.lz_copy].
    rewrite Nat2Z.inj_succ in Hl, Hi.
    assert (Hz : Zlength (sublist 0 q H) = q) by (rewrite Zlength_sublist by lia; lia).
    rewrite Hz, Znth_sublist by lia. rewrite Z.add_0_r.
    rewrite <- (Z.add_0_r (q - d)), Hi, Z.add_0_r by lia.
    rewrite <- sublist_last_1 by lia.
    rewrite IH by (try lia; intros i Hi'; replace (q + 1 - d + i) with (q - d + (i + 1)) by lia;
                   replace (q + 1 + i) with (q + (i + 1)) by lia; apply Hi; lia).
    f_equal. rewrite Nat2Z.inj_succ. lia.
Qed.

Lemma fm_syms_data_app out a b :
  F.syms_data out (map fsym (a ++ b)) = F.syms_data (F.syms_data out (map fsym a)) (map fsym b).
Proof. unfold F.syms_data. rewrite map_app, fold_left_app. reflexivity. Qed.

Lemma fm_syms_rok_app wmax : forall a out b,
  syms_rok wmax out (a ++ b) <-> syms_rok wmax out a /\ syms_rok wmax (F.syms_data out (map fsym a)) b.
Proof.
  induction a as [|x a IH]; intros out b.
  - cbn. tauto.
  - cbn [app syms_rok map]. rewrite IH. unfold F.syms_data. cbn [fold_left]. tauto.
Qed.

(** ** kt after the match: the symbol Ref ml dist expands to the next ml bytes *)
Lemma fm_kt dict D BS syms s s3 ml dist :
  kt dict D BS syms s -> d_window s3 = d_window s -> d_w_bits s3 = d_w_bits s ->
  d_strstart s3 = d_strstart s + ml -> d_lookahead s3 = d_lookahead s - ml ->
  d_block_start s3 = d_block_start s ->
  3 <= ml <= 258 -> ml <= d_lookahead s -> 0 <= d_strstart s ->
  1 <= dist <= d_strstart s -> dist <= 2 ^ d_w_bits s ->
  (forall i, 0 <= i < ml ->
     Znth (d_strstart s - dist + i) (mb_val (d_window s)) = Znth (d_strstart s + i) (mb_val (d_window s))) ->
  khash s3 ->
  kt dict D BS (syms ++ [(dist, ml - 3)]) s3.
Proof.
  intros (K1 & K4 & K5 & K6 & K7 & _) Ew Eb Ess Ela Ebs Hml Hla Hss Hd Hdw Hm Hh.
  unfold kt in *. cbv zeta in *.
  set (H := dict ++ D) in *.
  assert (HS : d_strstart s3 + d_lookahead s3 = d_strstart s + d_lookahead s) by lia.
  destruct K1 as (Kl & Kw).
  rewrite HS, Eb, Ebs, Ess.
  split; [unfold kwin; rewrite HS, Ew; split; [exact Kl|exact Kw]|].
  split; [exact K4|]. split; [exact K5|].
  assert (Hlo : Zlength (sublist 0 (Zlength H - (d_strstart s + d_lookahead s) + d_strstart s) H) =
                Zlength H - d_lookahead s) by (rewrite Zlength_sublist by lia; lia).
  split.
  { apply fm_syms_rok_app. split; [exact K6|]. rewrite K7. cbn [syms_rok fst snd].
    replace (dist =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    rewrite Hlo. split; [|exact I]. split; [lia|]. split; [lia|]. exact Hdw. }
  split; [|exact Hh].
  rewrite fm_syms_data_app, K7. unfold F.syms_data. cbn [map fold_left]. unfold fsym. cbn [fst snd].
  replace (dist =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  cbn [F.sym_data]. replace (ml - 3 + 3) with ml by lia.
  rewrite fm_lz_copy.
  - rewrite Z2Nat.id by lia. f_equal. lia.
  - lia.
  - rewrite Z2Nat.id by lia. lia.
  - rewrite Z2Nat.id by lia. intros i Hi.
    replace (Zlength H - (d_strstart s + d_lookahead s) + d_strstart s - dist + i)
      with (Zlength H - (d_strstart s + d_lookahead s) + (d_strstart s - dist + i)) by lia.
    replace (Zlength H - (d_strstart s + d_lookahead s) + d_strstart s + i)
      with (Zlength H - (d_strstart s + d_lookahead s) + (d_strstart s + i)) by lia.
    rewrite <- (Kw (d_strstart s - dist + i)) by lia. rewrite <- (Kw (d_strstart s + i)) by lia.
    apply Hm. lia.
Qed.

(** ** Chains and ins_h *)
Lemma fm_chain_hok_mono x y :
  d_hash_size y = d_hash_size x -> d_head y = d_head x -> d_w_mask y = d_w_mask x -> d_prev y = d_prev x ->
  d_window y = d_window x -> d_hash_shift y = d_hash_shift x -> d_hash_mask y = d_hash_mask x ->
  lim x <= lim y -> d_strstart x + d_lookahead x <= d_strstart y + d_lookahead y ->
  chain_hok x -> chain_hok y.
Proof.
  intros E1 E2 E3 E4 E5 E6 E7 Hl Hs H b Hb. rewrite E1 in Hb. destruct (H b Hb) as (G & G0 & GS).
  exists G. rewrite E2. split; [exact G0|]. intros q Gq q0 ql.
  destruct (GS q Gq q0 ltac:(lia)) as (A & B & C). split; [lia|]. split.
  - unfold h3, update_hash in *. rewrite E5, E6, E7. exact B.
  - rewrite E3, E4. exact C.
Qed.

(* the chain entries of a chain_with below n: their 3 bytes are below a new, smaller end of the data *)
Lemma fm_chain_hok_cut x y n l G :
  d_hash_size y = d_hash_size x -> d_head y = d_head x -> d_w_mask y = d_w_mask x -> d_prev y = d_prev x ->
  d_window y = d_window x -> d_hash_shift y = d_hash_shift x -> d_hash_mask y = d_hash_mask x ->
  lim x <= lim y -> l <= lim y -> n + 1 < d_strstart y + d_lookahead y ->
  chain_hok x -> chain_with x n l G -> chain_hok y.
Proof.
  intros E1 E2 E3 E4 E5 E6 E7 Hl Hl' Hs H (C1 & C2 & C3) b Hb. rewrite E1 in Hb. destruct (H b Hb) as (Gb & G0 & GS).
  exists (fun q => Gb q /\ G q). rewrite E2. split; [split; [exact G0|apply C2; exact Hb]|].
  intros q (Gq & Gq') q0 ql.
  destruct (GS q Gq q0 ltac:(lia)) as (A & B & C).
  split; [destruct (C1 q Gq'); lia|]. split.
  - unfold h3, update_hash in *. rewrite E5, E6, E7. exact B.
  - rewrite E3, E4. split; [exact C|]. apply C3; [exact Gq'|exact q0|lia].
Qed.

Lemma fm_primed x y p :
  d_ins_h y = d_ins_h x -> d_window y = d_window x -> d_hash_shift y = d_hash_shift x ->
  d_hash_mask y = d_hash_mask x -> primed x p -> primed y p.
Proof.
  intros E1 E2 E3 E4 (h0 & H). exists h0. unfold update_hash in *. rewrite E1, E2, E3, E4. exact H.
Qed.

(* UPDATE_HASH from 0 with a byte: the byte (hash_bits >= 8) *)
Lemma fm_uh0 s c : prm s -> 0 <= c < 256 -> update_hash s 0 c = c.
Proof.
  intros (_ & _ & _ & Hhb & Hhs & Hhm & _) Hc. unfold update_hash.
  rewrite Z.shiftl_0_l. change (u32 0) with 0. rewrite Z.lxor_0_l, Hhm, Hhs.
  replace (2 ^ d_hash_bits s - 1) with (Z.ones (d_hash_bits s)) by (rewrite Z.ones_equiv; lia).
  rewrite Z.land_ones by lia.
  assert (256 <= 2 ^ d_hash_bits s) by (change 256 with (2 ^ 8); apply Z.pow_le_mono_r; lia).
  rewrite Z.mod_small by lia. unfold u32. apply Z.mod_small. lia.
Qed.

Theorem fmatch_ok : fmatch_stmt.
Proof.
  intros s s2 s3 bf dict D BS syms Htal Hfins HW Ho Hq Hfn Hrd Hla HSR Hml Hbd HbD Hkc Hch2 Hpr2 Hmw.
  pose proof Htal as [_ Htd].
  assert (Hins := insloop_ok (proj1 lm_ok)).
  destruct HSR as (Hk2 & Hws2 & [G HG] & Hml2 & Hmm).
  destruct (Hmm Hml) as (Hmla & Hlim & Hms).
  assert (HW0 := HW).
  destruct HW as (Hp & Hws & Hpos & Hwin & Hh & Hm & _ & symsW & Hwt).
  assert (Ha : d_match_available s = 0).
  { destruct Hm as (_ & _ & [A|A] & _ & B); [exact A|]. destruct (B A) as (C & _). lia. }
  destruct (kcore_kt dict D BS syms s Ha Hkc) as (Hkt & Hwt').
  assert (Esy : symsW = syms) by exact (wtrees_uniq s _ _ Hwt Hwt'). subst symsW. clear Hwt'.
  assert (Hkh : khash s) by exact (proj2 (proj2 (proj2 (proj2 (proj2 Hkt))))).
  assert (Hwt0 := Hwt).
  sr_field Hk2 d_window Ewin. sr_field Hk2 d_window_size Ewsz. sr_field Hk2 d_strstart Ess.
  sr_field Hk2 d_lookahead Ela. sr_field Hk2 d_tr Etr. sr_field Hk2 d_pbm Epbm.
  sr_field Hk2 d_w_size Ewsize. sr_field Hk2 d_max_lazy_match Elazy. sr_field Hk2 d_hash_shift Ehshift.
  sr_field Hk2 d_high_water Ehw. sr_field Hk2 d_hash_mask Ehmask.
  assert (Elim2 : lim s2 = lim s) by (unfold lim, MAX_DIST; rewrite Ess, Ewsize; reflexivity).
  assert (Hlev := fn_of_fast s Hp Hfn).
  assert (Hp0 := Hp).
  destruct Hp as (Hwb & Hwsz & Hwm & Hhb & Hhs & Hhm & Hhsh & HL & Hpbs & Hob & Hpbm & Hse & Hlv & Hstrat & Hmeth).
  destruct Hpos as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
  destruct Hwt as (Ht1 & HL2 & Hf & _ & Hb).
  assert (HL15 : d_L s <= 32768).
  { rewrite HL. change 32768 with (2 ^ 15). apply Z.pow_le_mono_r; lia. }
  assert (Hw15 : d_w_size s <= 32768).
  { rewrite Hwsz. change 32768 with (2 ^ 15). apply Z.pow_le_mono_r; lia. }
  assert (Hw9 : 512 <= d_w_size s).
  { rewrite Hwsz. change 512 with (2 ^ 9). apply Z.pow_le_mono_r; lia. }
  assert (Hsb : d_strstart s - d_block_start s <= 8453628).
  { assert (Hbl := blk_len_bound syms (proj1 (proj2 (proj2 (proj2 Ht1))))).
    rewrite Hb in Hbl by lia. rewrite Ha in Hbl. lia. }
  assert (Hws0 := Hws). destruct Hws as (Hwl & Hwok & Hwss & Hpl & Hhl).
  set (ml := d_match_length s2) in *.
  set (dist := d_strstart s - d_match_start s2).
  assert (Hd : 1 <= dist <= MAX_DIST s).
  { unfold dist. unfold lim in Hlim.
    destruct (Z.gtb_spec (d_strstart s) (MAX_DIST s)); unfold MAX_DIST, MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in *; lia. }
  assert (Hd' : 1 <= dist <= 32768) by (unfold MAX_DIST, MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in Hd; lia).
  assert (Hdss : dist <= d_strstart s) by (unfold dist; lia).
  assert (Hdw : dist <= 2 ^ d_w_bits s) by (rewrite <- Hwsz; unfold MAX_DIST, MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in Hd; lia).
  assert (Hmw' : forall i, 0 <= i < ml -> Znth (d_strstart s - dist + i) (mb_val (d_window s)) =
                                          Znth (d_strstart s + i) (mb_val (d_window s))).
  { intros i Hi. replace (d_strstart s - dist + i) with (d_match_start s2 + i) by (unfold dist; lia).
    apply Hmw. exact Hi. }
  assert (Hlen : 0 <= ml - 3 <= 255) by (unfold MAX_MATCH, MIN_MATCH in *; lia).
  destruct (Htd (d_tr s) (d_pbm s) syms dist (ml - 3) Ht1 HL2 HL15 Hd' Hlen) as (t' & m' & Etl & Ht' & Hfr).
  assert (Hfr0 := Hfr).
  destruct Hfr0 as (_ & _ & _ & Fbb & Fbv & _).
  unfold fmatch. fold ml. rewrite Ess.
  rewrite (mt_u32_id (d_strstart s - d_match_start s2)) by lia. fold dist.
  rewrite (mt_u32_id (ml - MIN_MATCH)) by (unfold MIN_MATCH, MAX_MATCH in *; lia).
  unfold c_dtally_dist, d_trm. rewrite Etr, Epbm. change MIN_MATCH with 3. rewrite Etl.
  cbn [bind]. unfold set_d_trm. cbn [fst snd]. autorewrite with fproj. fold ml.
  rewrite ?Ela, ?Ess, ?Ewin, ?Ehshift, ?Elazy.
  rewrite (mt_u32_id (d_lookahead s - ml)) by lia.
  set (sin := set_d_lookahead (set_d_pbm (set_d_tr s2 t') m') (d_lookahead s - ml)).
  assert (Hkin : mt_keep sin = mt_keep (set_d_pbm (set_d_tr s t') m')).
  { unfold sin. rewrite mt_keep_sr, Hk2. reflexivity. }
  assert (Hsin : d_strstart sin = d_strstart s /\ d_window sin = d_window s /\ d_w_size sin = d_w_size s /\
                 d_head sin = d_head s2 /\ d_prev sin = d_prev s2 /\ d_hash_size sin = d_hash_size s2 /\
                 d_w_mask sin = d_w_mask s2 /\ d_hash_shift sin = d_hash_shift s /\ wstruct sin /\
                 d_lookahead sin = d_lookahead s - ml /\ d_hash_mask sin = d_hash_mask s2 /\
                 d_ins_h sin = d_ins_h s2).
  { unfold sin, wstruct. autorewrite with fproj. rewrite Ess, Ewin, Ewsize, Ehshift.
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [rewrite <- Ewin, <- Ewsize; exact Hws2|]. split; [reflexivity|]. split; reflexivity. }
  destruct Hsin as (Si1 & Si2 & Si3 & Si4 & Si5 & Si6 & Si7 & Si8 & Si9 & Si10 & Si11 & Si12).
  clearbody sin.
  mt_fld Hkin d_block_start Ibs. mt_fld Hkin d_insert Iins. mt_fld Hkin d_high_water Ihw.
  mt_fld Hkin d_window_size Iwsz.
  unfold MIN_MATCH, MAX_MATCH in Hml, Hml2.
  destruct ((ml <=? d_max_lazy_match s) && (d_lookahead s - ml >=? 3)) eqn:Ec.
  - apply andb_true_iff in Ec. destruct Ec as [Ec1 Ec2]. apply Z.leb_le in Ec1. apply Z.geb_le in Ec2.
    rewrite (mt_u32_id (ml - 1)) by lia.
    assert (Hlim1 : lim (set_d_match_length sin (ml - 1)) = lim s).
    { unfold lim, MAX_DIST. autorewrite with fproj. rewrite Si1, Si3. reflexivity. }
    destruct (Hins (set_d_match_length sin (ml - 1)) (lim s) G) as (s' & G' & Eloop & Hil & Hws' & Hss' & Hml' & Hch').
    + apply (mt_prm s _ t' m' (syms ++ [(dist, ml - 3)]) Hp0 Hfr Ht'). rewrite mt_keep_ml. exact Hkin.
    + unfold wstruct. autorewrite with fproj. exact Si9.
    + apply (mt_chain_eq s2); autorewrite with fproj; try assumption. rewrite Si1. exact HG.
    + autorewrite with fproj. lia.
    + autorewrite with fproj. lia.
    + autorewrite with fproj. rewrite ?Si1, ?Si3. lia.
    + autorewrite with fproj. rewrite ?Si1, ?Si2, ?Hwl. lia.
    + autorewrite with fproj. rewrite Si1, Si2. intros i Hi. apply Hwin. lia.
    + autorewrite with fproj. rewrite ?Si1, ?Si3. unfold lim, MAX_DIST, MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH.
      destruct (Z.gtb_spec (d_strstart s) (d_w_size s - (258 + 3 + 1))); lia.
    + destruct (fil_loop_fok Hfins (set_d_match_length sin (ml - 1)) (lim s) G s') as (Fch & Fpr).
      * apply (mt_prm s _ t' m' (syms ++ [(dist, ml - 3)]) Hp0 Hfr Ht'). rewrite mt_keep_ml. exact Hkin.
      * unfold wstruct. autorewrite with fproj. exact Si9.
      * apply (mt_chain_eq s2); autorewrite with fproj; try assumption. rewrite Si1. exact HG.
      * autorewrite with fproj. lia.
      * autorewrite with fproj. lia.
      * autorewrite with fproj. rewrite ?Si1, ?Si3. lia.
      * autorewrite with fproj. rewrite ?Si1, ?Si2, ?Hwl. lia.
      * autorewrite with fproj. rewrite Si1, Si2. intros i Hi. apply Hwin. lia.
      * autorewrite with fproj. rewrite ?Si1, ?Si3. unfold lim, MAX_DIST, MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH.
        destruct (Z.gtb_spec (d_strstart s) (d_w_size s - (258 + 3 + 1))); lia.
      * rewrite Hlim1. lia.
      * autorewrite with fproj. rewrite Si10. lia.
      * intros pp Hpp. autorewrite with fproj in Hpp. rewrite Si1 in Hpp.
        unfold wpos, MAX_DIST in *. autorewrite with fproj. rewrite Si10, Ibs, Iins, Ihw, Iwsz, Si3.
        split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
        split; [intros Hn; specialize (P6 Hn); lia|]. lia.
      * apply (fm_chain_hok_cut s2 _ (d_strstart s + 1) (lim s) G); autorewrite with fproj;
          rewrite ?Si6, ?Si4, ?Si7, ?Si5, ?Si2, ?Si8, ?Si11, ?Ewin, ?Ehshift; try reflexivity.
        -- rewrite Elim2. change (lim s <= lim (set_d_match_length sin (ml - 1))). lia.
        -- change (lim s <= lim (set_d_match_length sin (ml - 1))). lia.
        -- rewrite Si1, Si10. lia.
        -- exact Hch2.
        -- exact HG.
      * apply (fm_primed s2); autorewrite with fproj; rewrite ?Si12, ?Si2, ?Si8, ?Si11, ?Ewin, ?Ehshift;
          try reflexivity.
        rewrite Si1. apply Hpr2. unfold MIN_MATCH. lia.
      * exact Eloop.
      * autorewrite with fproj in Hss'. rewrite Si1 in Hss'.
        rewrite Eloop. cbn [bind].
        rewrite (mt_u32_id (d_strstart s' + 1)) by lia.
        assert (Ela' := f_equal d_lookahead Hil). unfold il_keep, hc_keep in Ela'. autorewrite with fproj in Ela'.
        intros E. injection E as E3 <-.
        assert (Hk3 : mt_keep s3 = mt_keep (set_d_pbm (set_d_tr s t') m')).
        { rewrite <- E3, mt_keep_ss, (mt_keep_il _ _ Hil), mt_keep_ml. exact Hkin. }
        assert (E3ss : d_strstart s3 = d_strstart s + ml) by (rewrite <- E3; autorewrite with fproj; lia).
        assert (E3la : d_lookahead s3 = d_lookahead s - ml) by (rewrite <- E3; autorewrite with fproj; rewrite Ela', Si10; reflexivity).
        assert (HTS : TS s3 (syms ++ [(dist, ml - 3)]) (3 * Zlength syms + 3 =? tr_sym_end (d_tr s))).
        { apply (mt_core s s3 syms t' m' ml dist G' HW0 Ho Hq Hfn Hwt0 Ht' Hfr).
          - exact Hk3.
          - rewrite <- E3. unfold wstruct. autorewrite with fproj. exact Hws'.
          - exact E3ss.
          - exact E3la.
          - rewrite <- E3. autorewrite with fproj. exact Hml'.
          - rewrite <- E3. autorewrite with fproj. apply (mt_chain_eq s'); autorewrite with fproj; try reflexivity.
            exact Hch'.
          - lia.
          - exact Hd.
          - lia. }
        mt_fld Hk3 d_window E3w. mt_fld Hk3 d_w_bits E3wb. mt_fld Hk3 d_block_start E3bs.
        mt_fld Hk3 d_insert E3ins. mt_fld Hk3 d_tr E3tr.
        exists (syms ++ [(dist, ml - 3)]). split; [exact HTS|]. split.
        -- apply (fm_kt dict D BS syms s s3 ml dist Hkt E3w E3wb E3ss E3la E3bs); try lia; [exact Hmw'|].
           destruct HTS as ((Hp3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfn3 & _) & _).
           assert (Hlv3 := fn_of_fast s3 Hp3 Hfn3).
           unfold khash. rewrite (proj2 (Z.eqb_neq (d_level s3) 0)) by lia. split.
           ++ rewrite <- E3. apply (fm_chain_hok_mono s'); autorewrite with fproj; try reflexivity; [|lia|exact Fch].
              apply mt_lim_mono; autorewrite with fproj; [reflexivity|lia].
           ++ intros _ H3. split.
              ** rewrite E3ins. apply (proj2 Hkh (or_introl Hfn)). unfold MIN_MATCH in *. lia.
              ** rewrite <- E3. autorewrite with fproj. apply (fm_primed s'); autorewrite with fproj; try reflexivity.
                 exact Fpr.
        -- unfold bibits, d_bi_valid. rewrite E3tr, Fbb, Fbv. reflexivity.
  - assert (Hrd2 : d_strstart s + ml + 1 < Z.max (d_strstart s + d_lookahead s) (d_high_water s) /\
                   d_strstart s + ml < d_window_size s).
    { unfold ready in Hrd. unfold MAX_DIST, MIN_LOOKAHEAD, WIN_INIT in *. unfold MAX_MATCH, MIN_MATCH in *.
      destruct Hrd as [R|R]; lia. }
    rewrite (mt_u32_id (d_strstart s + ml)) by lia.
    rewrite (mt_rd s (d_strstart s + ml) Hws0 Hwin) by lia. cbn [bind].
    autorewrite with fproj. rewrite Si8.
    assert (Hsh : d_hash_shift s < 32) by (rewrite Hhsh; apply Z.div_lt_upper_bound; lia).
    rewrite (proj2 (Z.ltb_lt _ _) Hsh). cbn [guard bind]. rewrite Si2.
    rewrite (mt_u32_id (d_strstart s + ml + 1)) by lia.
    rewrite (mt_rd s (d_strstart s + ml + 1) Hws0 Hwin) by lia. cbn [bind].
    intros E. injection E as E3 <-.
    assert (Hk3 : mt_keep s3 = mt_keep (set_d_pbm (set_d_tr s t') m')).
    { rewrite <- E3, mt_keep_ih, mt_keep_ih, mt_keep_ml, mt_keep_ss. exact Hkin. }
    assert (E3ss : d_strstart s3 = d_strstart s + ml) by (rewrite <- E3; autorewrite with fproj; reflexivity).
    assert (E3la : d_lookahead s3 = d_lookahead s - ml) by (rewrite <- E3; autorewrite with fproj; exact Si10).
    assert (HTS : TS s3 (syms ++ [(dist, ml - 3)]) (3 * Zlength syms + 3 =? tr_sym_end (d_tr s))).
    { apply (mt_core s s3 syms t' m' ml dist G HW0 Ho Hq Hfn Hwt0 Ht' Hfr).
      - exact Hk3.
      - rewrite <- E3. unfold wstruct. autorewrite with fproj. exact Si9.
      - exact E3ss.
      - exact E3la.
      - rewrite <- E3. autorewrite with fproj. reflexivity.
      - rewrite <- E3. autorewrite with fproj. apply (mt_chain_eq s2); try assumption.
        apply (mt_chain_mono s2 _ _ _ _ G HG); lia.
      - lia.
      - exact Hd.
      - lia. }
    mt_fld Hk3 d_window E3w. mt_fld Hk3 d_w_bits E3wb. mt_fld Hk3 d_block_start E3bs.
    mt_fld Hk3 d_insert E3ins. mt_fld Hk3 d_tr E3tr.
    exists (syms ++ [(dist, ml - 3)]). split; [exact HTS|]. split.
    + apply (fm_kt dict D BS syms s s3 ml dist Hkt E3w E3wb E3ss E3la E3bs); try lia; [exact Hmw'|].
      destruct HTS as ((Hp3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfn3 & _) & _).
      assert (Hlv3 := fn_of_fast s3 Hp3 Hfn3).
      unfold khash. rewrite (proj2 (Z.eqb_neq (d_level s3) 0)) by lia. split.
      * apply (fm_chain_hok_mono s2); try exact Hch2.
        -- rewrite <- E3. autorewrite with fproj. exact Si6.
        -- rewrite <- E3. autorewrite with fproj. exact Si4.
        -- rewrite <- E3. autorewrite with fproj. exact Si7.
        -- rewrite <- E3. autorewrite with fproj. exact Si5.
        -- rewrite E3w. symmetry. exact Ewin.
        -- rewrite <- E3. autorewrite with fproj. rewrite Si8. symmetry. exact Ehshift.
        -- rewrite <- E3. autorewrite with fproj. exact Si11.
        -- rewrite Elim2. apply mt_lim_mono; [|lia]. rewrite <- E3. autorewrite with fproj. exact Si3.
        -- rewrite E3ss, E3la, Ess, Ela. lia.
      * intros _ H3. split.
        -- rewrite E3ins. apply (proj2 Hkh (or_introl Hfn)). unfold MIN_MATCH in *. lia.
        -- exists 0. rewrite E3w, E3ss.
           assert (Hc0 : 0 <= Znth (d_strstart s + ml) (mb_val (d_window s)) < 256).
           { destruct Hwok as (Hwd & Hwb8). apply Hwb8; [rewrite Hwl; lia|apply Hwin; lia]. }
           rewrite (fm_uh0 s3 _ Hp3 Hc0).
           rewrite <- E3. autorewrite with fproj. unfold update_hash. autorewrite with fproj. reflexivity.
    + unfold bibits, d_bi_valid. rewrite E3tr, Fbb, Fbv. reflexivity.
Qed.
