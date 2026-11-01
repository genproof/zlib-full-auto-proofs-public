(* RT-D part RLE: the run branch (rdist, distance 1) (statement: RTDRleKit.v; model on RTDLTCRleDist.rdist_ok). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDRleKit.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

Lemma rfd_lz_copy1 (H : list Z) : forall n a,
  1 <= a -> a + Z.of_nat n <= Zlength H ->
  (forall i, 0 <= i < Z.of_nat n -> Znth (a + i) H = Znth (a - 1) H) ->
  F.lz_copy n 1 (sublist 0 a H) = sublist 0 (a + Z.of_nat n) H.
Proof.
  induction n as [|n IH]; intros a Ha Hl Hi.
  - cbn. rewrite Z.add_0_r. reflexivity.
  - cbn [F.lz_copy].
    assert (Hz : Zlength (sublist 0 a H) = a) by (rewrite Zlength_sublist by lia; lia).
    rewrite Hz, Znth_sublist by lia. rewrite Z.add_0_r.
    rewrite <- (Hi 0) by lia. rewrite Z.add_0_r.
    rewrite <- sublist_last_1 by lia.
    rewrite IH by (try lia; intros i Hi'; replace (a + 1 + i) with (a + (i + 1)) by lia;
                   replace (a + 1 - 1) with (a + 0) by lia; rewrite !Hi by lia; reflexivity).
    f_equal. lia.
Qed.

Theorem rfdist_ok : tally_spec2 -> rfdist_stmt.
Proof.
  intros [_ Htd] s ml s3 bf dict D BS syms HW Ho Hq Hfn Hrd Hml Hmla Hss1 Hrun Hdict HD Hwt Hk Hrdist.
  assert (HW0 := HW).
  destruct HW as (Hp & Hws & Hpos & Hwin & Hh & Hm & _).
  assert (Hwt0 := Hwt).
  destruct Hp as (Hwb & Hwsz & Hwm & Hhb & Hhs & Hhm & Hhsh & HL & Hpbs & Hob & Hpbm & Hse & Hlv & Hstrat & Hmeth).
  destruct Hpos as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
  destruct Hwt as (Ht1 & HL2 & Hf & _ & Hb).
  assert (HL15 : d_L s <= 32768).
  { rewrite HL. change 32768 with (2 ^ 15). apply Z.pow_le_mono_r; lia. }
  assert (Hw15 : d_w_size s <= 32768).
  { rewrite Hwsz. change 32768 with (2 ^ 15). apply Z.pow_le_mono_r; lia. }
  assert (Hws0 := Hws). destruct Hws as (Hwl & Hwok & Hwss & Hpl & Hhl).
  assert (Hlen : 0 <= ml - 3 <= 255) by (unfold MAX_MATCH, MIN_MATCH in *; lia).
  destruct (Htd (d_tr s) (d_pbm s) syms 1 (ml - 3) Ht1 HL2 HL15 ltac:(lia) Hlen) as (t' & m' & Etl & Ht' & Hfr).
  assert (Hwin3 : d_strstart s + ml < d_window_size s).
  { unfold rready in Hrd. unfold MAX_DIST, MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in *. destruct Hrd as [R|R]; lia. }
  unfold rdist, c_dtally_dist, d_trm in Hrdist. autorewrite with fproj in Hrdist.
  rewrite (rd_u32_id (ml - MIN_MATCH)) in Hrdist by (unfold MIN_MATCH, MAX_MATCH in *; lia).
  change MIN_MATCH with 3 in Hrdist. rewrite Etl in Hrdist.
  cbn [bind] in Hrdist. unfold set_d_trm in Hrdist. cbn [fst snd] in Hrdist. autorewrite with fproj in Hrdist.
  rewrite (rd_u32_id (d_lookahead s - ml)) in Hrdist by lia.
  rewrite (rd_u32_id (d_strstart s + ml)) in Hrdist by lia.
  injection Hrdist as Es3 Ebf. subst bf.
  unfold MIN_MATCH in Hml.
  assert (HC : RTS s3 (syms ++ [(1, ml - 3)]) (3 * Zlength syms + 3 =? tr_sym_end (d_tr s)) /\ fr s s3 /\
               d_lookahead s3 < d_lookahead s).
  { subst s3. apply (rd_core s _ syms t' m' ml HW0 Ho Hq Hfn Hwt0 Ht' Hfr).
    all: try (autorewrite with fproj; reflexivity).
    all: try (unfold wstruct; autorewrite with fproj; exact Hws0).
    all: try (unfold MAX_MATCH in *; lia). }
  destruct HC as (HRTS & _ & _).
  assert (Ewin : d_window s3 = d_window s) by (subst s3; autorewrite with fproj; reflexivity).
  assert (Ess : d_strstart s3 = d_strstart s + ml) by (subst s3; autorewrite with fproj; reflexivity).
  assert (Ela : d_lookahead s3 = d_lookahead s - ml) by (subst s3; autorewrite with fproj; reflexivity).
  assert (Esum : d_strstart s3 + d_lookahead s3 = d_strstart s + d_lookahead s) by lia.
  assert (Ewb : d_w_bits s3 = d_w_bits s) by (subst s3; autorewrite with fproj; reflexivity).
  assert (Ewsize : d_w_size s3 = d_w_size s) by (subst s3; autorewrite with fproj; reflexivity).
  assert (Ebs : d_block_start s3 = d_block_start s) by (subst s3; autorewrite with fproj; reflexivity).
  assert (Ehead : d_head s3 = d_head s) by (subst s3; autorewrite with fproj; reflexivity).
  assert (Eprev : d_prev s3 = d_prev s) by (subst s3; autorewrite with fproj; reflexivity).
  assert (Ehsz : d_hash_size s3 = d_hash_size s) by (subst s3; autorewrite with fproj; reflexivity).
  assert (Ewmask : d_w_mask s3 = d_w_mask s) by (subst s3; autorewrite with fproj; reflexivity).
  assert (Ehshift : d_hash_shift s3 = d_hash_shift s) by (subst s3; autorewrite with fproj; reflexivity).
  assert (Ehmask : d_hash_mask s3 = d_hash_mask s) by (subst s3; autorewrite with fproj; reflexivity).
  exists (syms ++ [(1, ml - 3)]).
  split; [exact HRTS|].
  split; [|split].
  3: { assert (Hq3 : quiet s3) by (destruct HRTS as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _) & _); exact X).
       rewrite !rk_quiet_pend by assumption. reflexivity. }
  2: { destruct Hfr as (_ & _ & _ & Hbb & Hbv & _).
       unfold bibits, d_bi_valid. subst s3. autorewrite with fproj. rewrite Hbb, Hbv. reflexivity. }
  unfold rkt in *. cbv zeta in *. destruct Hk as (K1 & K2 & K3 & K4 & K5 & K6).
  rewrite Esum, Ewb, Ebs, Ess.
  set (H := dict ++ D) in *.
  set (off := Zlength H - (d_strstart s + d_lookahead s)) in *.
  assert (K1' := K1). destruct K1' as (Kl & Kw).
  assert (Hoff : 0 <= off) by (unfold off; lia).
  assert (Hw1 : 1 <= 2 ^ d_w_bits s) by (change 1 with (2 ^ 0); apply Z.pow_le_mono_r; lia).
  split; [unfold kwin in *; rewrite Esum, Ewin; exact K1|].
  split; [exact K2|].
  split; [exact K3|].
  split.
  { apply rk_syms_rok_app. split; [exact K4|]. rewrite K5. cbn [syms_rok fst snd Z.eqb].
    rewrite Zlength_sublist by lia. split; [lia|exact I]. }
  split.
  { rewrite rk_syms_data_app, K5. unfold F.syms_data. cbn [map fold_left]. unfold fsym. cbn [fst snd Z.eqb].
    cbn [F.sym_data]. replace (ml - 3 + 3) with ml by lia.
    assert (Hrun' : forall i, 0 <= i < ml -> Znth (off + d_strstart s + i) H = Znth (off + d_strstart s - 1) H).
    { intros i Hi. unfold off.
      replace (Zlength H - (d_strstart s + d_lookahead s) + d_strstart s + i)
        with (Zlength H - (d_strstart s + d_lookahead s) + (d_strstart s + i)) by lia.
      replace (Zlength H - (d_strstart s + d_lookahead s) + d_strstart s - 1)
        with (Zlength H - (d_strstart s + d_lookahead s) + (d_strstart s - 1)) by lia.
      rewrite <- !Kw by lia. apply Hrun; lia. }
    rewrite rfd_lz_copy1, Z2Nat.id by (try lia; rewrite ?Z2Nat.id by lia; try lia;
      intros i Hi; apply Hrun'; lia).
    f_equal. lia. }
  unfold chain_hok in *. rewrite Ehsz. intros b Hb0. destruct (K6 b Hb0) as (G & G0 & GS).
  exists G. rewrite Ehead. split; [exact G0|].
  assert (Hlim : lim s <= lim s3) by (apply rd_lim_mono; [exact Ewsize|lia]).
  intros q Gq q0 ql. destruct (GS q Gq q0 ltac:(lia)) as (A & B & C).
  split; [lia|]. split.
  - unfold h3, update_hash in *. rewrite Ewin, Ehshift, Ehmask. exact B.
  - rewrite Ewmask, Eprev. exact C.
Qed.
