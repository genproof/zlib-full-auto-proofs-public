(* RT-D part SLOW: the functional part fend_part of deflate_slow (statement: RTDSlowKit.v). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDSlowKit.
Require Import Zlib.proof.roundtrip.RTDLTCSlowEnd Zlib.proof.roundtrip.RTDLTCSlowFbo.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** Helpers *)

(* the pending literal (RTDLTCSlowEnd.se_lit with the symbols of kcore3) *)
Lemma fe_lit s syms : tally_spec2 -> W2 s -> wtrees s syms -> d_lookahead s = 0 -> d_level s <> 0 ->
  exists t m syms1,
    (forall z flush, dsl_end s z flush = c_deflate_tail (se_s2 s t m) z flush) /\
    tree_ok t m syms1 /\ Zlength syms1 <= d_L s - 1 /\ Forall (sym_ok s) syms1 /\
    blk_len syms1 = d_strstart s - d_block_start s /\ tally_frame (d_tr s) (d_pbm s) t m /\
    ((d_match_available s = 0 /\ syms1 = syms) \/
     (d_match_available s = 1 /\ 1 <= d_strstart s /\ 0 <= Znth (d_strstart s - 1) (mb_val (d_window s)) < 256 /\
      syms1 = syms ++ [(0, Znth (d_strstart s - 1) (mb_val (d_window s)))])).
Proof.
  intros [Htl _] [HW _] Htr Hla Hlev.
  destruct HW as (Hp & Hs & Hpos & Hw & Hh & Hm & H0 & _).
  destruct Htr as (Ht & Hlen & Hsy & Hl0 & Hbl).
  specialize (Hbl Hlev).
  destruct Hm as (Hml & Hpl & Hav & Ha0 & Ha1).
  destruct (se_prm_bounds s Hp) as [Hws HL].
  destruct Hav as [A|A].
  - exists (d_tr s), (d_pbm s), syms. split.
    { intros z flush. unfold dsl_end, se_s2. rewrite A. cbn [negb Z.eqb bind].
      rewrite (se_trm_eta s A). reflexivity. }
    split; [exact Ht|]. split; [lia|]. split; [exact Hsy|]. split; [rewrite Hbl, A; lia|].
    split; [apply se_frame_refl|]. left. split; [exact A|reflexivity].
  - destruct (Ha1 A) as (_ & Hss1 & _).
    destruct Hs as (S1 & S2 & S3 & S4 & S5).
    destruct Hpos as (Q1 & Q2 & Q3 & _).
    assert (Eu : u32 (d_strstart s - 1) = d_strstart s - 1).
    { unfold u32. apply Z.mod_small. lia. }
    assert (Hdef : Znth (d_strstart s - 1) (mb_def (d_window s)) = true).
    { apply Hw. lia. }
    assert (Hrd : mb_rd (d_window s) (u32 (d_strstart s - 1)) = Some (Znth (d_strstart s - 1) (mb_val (d_window s)))).
    { rewrite Eu. unfold mb_rd, in_range. rewrite Hdef.
      replace ((0 <=? d_strstart s - 1) && (d_strstart s - 1 <? Zlength (mb_val (d_window s)))) with true
        by (symmetry; apply andb_true_iff; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
      reflexivity. }
    set (c := Znth (d_strstart s - 1) (mb_val (d_window s))) in *.
    assert (Hc : 0 <= c < 256).
    { destruct S2 as [_ S2]. apply S2; [lia|exact Hdef]. }
    destruct (Htl (d_tr s) (d_pbm s) syms c Ht ltac:(unfold d_L in Hlen; lia) ltac:(unfold d_L in HL; lia) Hc)
      as (t' & m' & Etl & Ht' & Hfr).
    exists t', m', (syms ++ [(0, c)]). split.
    { intros z flush. unfold dsl_end, se_s2. rewrite A. cbn [negb Z.eqb bind Pos.eqb]. rewrite Hrd.
      cbn [bind]. unfold c_dtally_lit, d_trm. rewrite Etl. cbn [bind]. reflexivity. }
    split; [exact Ht'|].
    split; [rewrite Zlength_app, Zlength_cons, Zlength_nil; lia|].
    split.
    { apply Forall_app. split; [exact Hsy|]. constructor; [|constructor].
      unfold sym_ok, valid_sym. cbn [fst snd]. split; [lia|]. split; intros; lia. }
    split; [rewrite se_blk_len_app, Hbl, A; unfold sym_len; cbn [fst snd Z.eqb]; lia|].
    split; [exact Hfr|]. right. split; [exact A|]. split; [lia|]. split; [exact Hc|reflexivity].
Qed.

Lemma fe_syms_data_snoc out l x :
  F.syms_data out (map fsym (l ++ [x])) = F.sym_data (F.syms_data out (map fsym l)) (fsym x).
Proof. unfold F.syms_data. rewrite map_app, fold_left_app. reflexivity. Qed.

Lemma fe_syms_rok_snoc w out l x :
  syms_rok w out l ->
  (if fst x =? 0 then 0 <= snd x < 256
   else 0 <= snd x <= 255 /\ 1 <= fst x <= Zlength (F.syms_data out (map fsym l)) /\ fst x <= w) ->
  syms_rok w out (l ++ [x]).
Proof.
  revert out. induction l as [|y l IH]; intros out H1 H2.
  - cbn [app syms_rok]. split; [exact H2|exact I].
  - cbn [app syms_rok] in *. destruct H1 as [H1 H1']. split; [exact H1|].
    apply IH; [exact H1'|exact H2].
Qed.

(* the fields chain_hok and kwin read are kept by the end *)
Lemma fe_kp_kwin H a b : se_kp a = se_kp b -> kwin H a -> kwin H b.
Proof.
  intros E. unfold kwin.
  assert (E1 : d_strstart a = d_strstart b) by exact (f_equal d_strstart E).
  assert (E2 : d_lookahead a = d_lookahead b) by exact (f_equal d_lookahead E).
  assert (E3 : d_window a = d_window b) by exact (f_equal d_window E).
  rewrite E1, E2, E3. exact (fun h => h).
Qed.

Lemma fe_kp_chain a b : se_kp a = se_kp b -> chain_hok a -> chain_hok b.
Proof.
  intros E. unfold chain_hok, lim, h3, update_hash, MAX_DIST.
  assert (E1 : d_strstart a = d_strstart b) by exact (f_equal d_strstart E).
  assert (E2 : d_lookahead a = d_lookahead b) by exact (f_equal d_lookahead E).
  assert (E3 : d_window a = d_window b) by exact (f_equal d_window E).
  assert (E4 : d_hash_size a = d_hash_size b) by exact (f_equal d_hash_size E).
  assert (E5 : d_head a = d_head b) by exact (f_equal d_head E).
  assert (E6 : d_prev a = d_prev b) by exact (f_equal d_prev E).
  assert (E7 : d_w_mask a = d_w_mask b) by exact (f_equal d_w_mask E).
  assert (E8 : d_w_size a = d_w_size b) by exact (f_equal d_w_size E).
  assert (E9 : d_hash_shift a = d_hash_shift b) by exact (f_equal d_hash_shift E).
  assert (E10 : d_hash_mask a = d_hash_mask b) by exact (f_equal d_hash_mask E).
  rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9, E10. exact (fun h => h).
Qed.

Lemma fe_kp_wbits a b : se_kp a = se_kp b -> d_w_bits a = d_w_bits b.
Proof. intros E. exact (f_equal d_w_bits E). Qed.

(* kcore3 at the end: no pending byte, no symbols, the blocks up to strstart *)
Lemma fe_kcore dict D BS s s3 syms0 :
  let H := dict ++ D in
  let off := Zlength H - (d_strstart s + d_lookahead s) in
  kwin H s -> chain_hok s -> d_lookahead s = 0 -> 128 <= d_L s ->
  se_kp s3 = se_kp s -> d_match_available s3 = 0 -> d_block_start s3 = d_strstart s ->
  tree_ok (d_tr s3) (d_pbm s3) [] -> d_L s3 = d_L s -> d_level s3 <> 0 ->
  F.blocks_ok (2 ^ d_w_bits s) dict BS -> F.expand dict BS = sublist 0 (off + d_strstart s) H ->
  wtrees s syms0 ->
  kcore3 dict D BS [] s3.
Proof.
  intros H off Hw Hch Hla HL Hk Ha Hb Ht HL3 Hlev Hbo Hex _.
  assert (E1 : d_strstart s3 = d_strstart s) by exact (f_equal d_strstart Hk).
  assert (E2 : d_lookahead s3 = d_lookahead s) by exact (f_equal d_lookahead Hk).
  rewrite <- (fe_kp_wbits _ _ Hk) in Hbo.
  split.
  - unfold kdata3. cbv zeta. fold H.
    split; [exact (fe_kp_kwin H s s3 (eq_sym Hk) Hw)|].
    split; [unfold kmatch3; rewrite Ha; intros C; discriminate C|].
    split.
    { unfold wtrees. split; [exact Ht|]. split; [rewrite Zlength_nil; lia|]. split; [constructor|].
      split; [intros _; reflexivity|]. intros _. rewrite se_blk_len_nil, Hb, E1, Ha. lia. }
    split; [exact Hbo|].
    rewrite E1, E2, Hb, Ha, (proj2 (Z.eqb_neq _ _) Hlev), Z.sub_0_r. fold off.
    split; [exact Hex|]. split; [exact I|]. exact Hex.
  - split.
    + rewrite (proj2 (Z.eqb_neq _ _) Hlev). exact (fe_kp_chain s s3 (eq_sym Hk) Hch).
    + intros _ L. rewrite E2, Hla in L. unfold MIN_MATCH in L. lia.
Qed.

Theorem fend_ok : fend_part.
Proof.
  intros dict D BS p s0 z0 flush s z evs s' z' bs Hss Hfs HSI Hla Hai Hnf Hssz HG HF E.
  pose proof Hss as (Hfill & Hins & Hlm & Htal & Hfbo & Hfp).
  pose proof Hfs as (_ & _ & _ & _ & Hfbof).
  destruct HF as (k & x0 & BS' & syms & Hzs & Hk & Hbits).
  set (D' := D ++ sublist (z_next_in z0) (z_next_in z0 + k) (z_in z0)) in Hk |- *.
  set (H := dict ++ D').
  pose proof HSI as (HW2 & Hq & HL & HE).
  pose proof HE as (Hc0 & Hfn0 & Ho & Hsp & Hapi & Hz & Had & _ & _ & _).
  assert (Hlev : d_level s <> 0).
  { destruct Hsp as (_ & _ & _ & _ & _ & E' & _). rewrite E'. intro E0.
    unfold fn_of in Hfn0. rewrite E0 in Hfn0. cbn [Z.eqb] in Hfn0. discriminate. }
  destruct Hk as ((Hkw & Hkm & Hwt & Hbo & Hex & Hsr & Hsd) & Hkh).
  fold H in Hkw, Hex, Hsd.
  rewrite (proj2 (Z.eqb_neq _ _) Hlev) in Hsd.
  destruct Hkh as [Hch _]. rewrite (proj2 (Z.eqb_neq _ _) Hlev) in Hch.
  destruct (fe_lit s syms Htal HW2 Hwt Hla Hlev) as (t & m & syms1 & Hdsl & Ht1 & Hlen1 & Hsy1 & Hblk1 & Hfr & Hcase).
  rewrite Hdsl in E.
  pose proof HW2 as [HW _]. pose proof HW as (Hp & Hs & Hpos & Hw & Hh & Hm & _ & _).
  destruct (se_prm_bounds s Hp) as [Hws HLb].
  pose proof Hpos as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & _).
  pose proof Hs as (S1 & S2 & S3 & S4 & S5).
  pose proof Hfr as (Hcfg & Hmt & Hpd & Hbb & Hbv & Hbu & Hg).
  assert (E_L : tr_lit_bufsize t = d_L s) by exact (f_equal (fun c => fst (fst (fst c))) Hcfg).
  assert (E_lev : tr_level t = d_level s) by exact (f_equal (fun c => snd (fst c)) Hcfg).
  assert (E_str : tr_strategy t = d_strategy s) by exact (f_equal (fun c => snd c) Hcfg).
  assert (HE2 := se_EI s0 z0 flush s z evs t m HE Hfr).
  assert (Hq2 := se_quiet s t m Hq Hfr).
  assert (Hp2 := se_prm s t m Hp Hfr).
  assert (Hsy2 : Forall (sym_ok (se_s2 s t m)) syms1).
  { eapply Forall_impl; [|exact Hsy1]. intros y Hy. unfold sym_ok in *.
    change (d_level (se_s2 s t m)) with (tr_level t). change (d_strategy (se_s2 s t m)) with (tr_strategy t).
    rewrite E_lev, E_str. exact Hy. }
  assert (Hpre : forall last, 0 <= last <= 1 -> fbo_pre (se_s2 s t m) z syms1 last).
  { intros last Hl. unfold fbo_pre.
    split; [exact Hp2|]. split; [exact Hs|].
    split; [change (0 < tr_level t); rewrite E_lev;
            destruct Hp as (_&_&_&_&_&_&_&_&_&_&_&_&P13&_); lia|].
    split; [exact Ht1|]. split; [change (Zlength syms1 <= tr_lit_bufsize t - 1); rewrite E_L; exact Hlen1|].
    split; [exact Hblk1|]. split; [exact Q4|]. split; [exact Q5|].
    split.
    { intros Hb0. change (0 <= d_block_start s) in Hb0. unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in Hssz.
      split; [change (d_strstart s - d_block_start s <= 65535); lia|].
      split; [change (d_strstart s <= Zlength (mb_val (d_window s))); lia|].
      intros i Hi. apply Hw. rewrite Hla. change (d_block_start s <= i < d_strstart s) in Hi. lia. }
    split; [exact (proj1 (proj2 (proj2 HE2)))|]. split; [exact Hq2|]. split; [exact Hl|].
    destruct Hz as [_ Hzo]. exact Hzo. }
  (* the functional facts on the symbols after the pending literal *)
  assert (Hoff : Zlength H - (d_strstart s + d_lookahead s) + d_strstart s = Zlength H).
  { rewrite Hla. lia. }
  assert (Hfun : syms_rok (2 ^ d_w_bits s) (F.expand dict (BS ++ BS')) syms1 /\
                 F.syms_data (F.expand dict (BS ++ BS')) (map fsym syms1) =
                   sublist 0 (Zlength H - (d_strstart s + d_lookahead s) + d_strstart s) H).
  { destruct Hcase as [(A & ->) | (A & A1 & Hc & ->)].
    - rewrite A, Z.sub_0_r in Hsd. split; [exact Hsr|exact Hsd].
    - split.
      + apply fe_syms_rok_snoc; [exact Hsr|]. cbn [fst snd Z.eqb]. exact Hc.
      + rewrite fe_syms_data_snoc, Hsd, A. unfold fsym. cbn [fst snd Z.eqb]. cbn [F.sym_data].
        destruct Hkw as [Hkw1 Hkw2]. rewrite (Hkw2 (d_strstart s - 1)) by lia.
        rewrite Hoff. rewrite Hla, Z.add_0_r in Hkw1 |- *.
        replace (Zlength H - d_strstart s + (d_strstart s - 1)) with (Zlength H - 1) by lia.
        replace (Zlength H - (d_strstart s + 0) + (d_strstart s - 1)) with (Zlength H - 1) by lia.
        rewrite <- sublist_last_1 by lia. f_equal. lia. }
  destruct Hfun as [Hsr1 Hsd1].
  (* the bits on the state after the literal *)
  assert (Hbits2 : F.bytes_bits (x0 ++ pend (se_s2 s t m)) ++ bibits (se_s2 s t m) = bibits s0 ++ enc_out p BS' false).
  { rewrite (pend_quiet _ Hq2). rewrite (pend_quiet _ Hq) in Hbits.
    replace (bibits (se_s2 s t m)) with (bibits s); [exact Hbits|].
    unfold bibits, d_bi_valid.
    change (F.bits_le (o_bi_buf (tr_out (d_tr s))) (o_bi_valid (tr_out (d_tr s))) =
            F.bits_le (o_bi_buf (tr_out t)) (o_bi_valid (tr_out t))).
    rewrite Hbb, Hbv. reflexivity. }
  pose proof Hc0 as (_ & Ho0 & _ & _ & Hzi0 & _ & Had0).
  assert (Hbv0 : 0 <= d_bi_valid s0).
  { destruct Ho0 as (_ & (Hb0 & _) & _). unfold d_bi_valid. lia. }
  pose proof HG as (_ & _ & Hp0 & Hal0).
  (* after FLUSH_BLOCK_ONLY *)
  assert (Hafter : forall last s3 z3,
    0 <= last <= 1 -> c_flush_block_only (se_s2 s t m) z last = Some (s3, z3) ->
    fbo_keep s3 = fbo_keep (se_s2 s t m) -> d_block_start s3 = d_strstart s ->
    tree_ok (d_tr s3) (d_pbm s3) [] -> tr_cfg (d_tr s3) = tr_cfg t -> 0 <= z_avail_out z3 ->
    exists x BS'',
      zstep (d_wrap s0) z0 z3 k x /\ kcore3 dict D' (BS ++ BS'') [] s3 /\
      F.bytes_bits (x ++ pend s3) ++ bibits s3 = bibits s0 ++ enc_out p BS'' (last =? 1) /\ BS'' <> []).
  { intros last s3 z3 Hl Hc Hk3 Hb3 Ht3 Hcfg3 Hao3.
    destruct (fbo_bits_step s0 (se_s2 s t m) z s3 z3 syms1 last dict D' BS BS' p x0 Hfbof (Hpre last Hl)
                Hkw Hbo Hex Hsr1 Hsd1 Hp0 Hal0 Hbv0 Hbits2 Hc) as (x & blk & Hzo & Hbo3 & Hex3 & Hbits3).
    exists (x0 ++ x), (BS' ++ [blk]).
    split.
    { replace k with (k + 0) by lia. apply (zstep_trans (d_wrap s0) z0 z z3 k x0 0 x).
      - destruct Hzi0 as (A1 & A2 & A3 & A4 & _ & A6 & _). split; [exact A1|]. split; [exact A2|].
        split; [exact A3|]. split; [exact A4|]. lia.
      - exact Had0.
      - exact Hzs.
      - exact (zout_only_zstep _ _ _ _ Hz Had Hzo Hao3). }
    split.
    { rewrite app_assoc. apply (fe_kcore dict D' ((BS ++ BS') ++ [blk]) s s3 syms Hkw Hch Hla ltac:(lia)).
      - unfold se_kp. rewrite Hk3. exact (se_kp_s2 s t m).
      - exact (f_equal d_match_available Hk3).
      - exact Hb3.
      - exact Ht3.
      - transitivity (tr_lit_bufsize t); [exact (f_equal (fun c => fst (fst (fst c))) Hcfg3)|exact E_L].
      - change (tr_level (d_tr s3) <> 0).
        rewrite (f_equal (fun c => snd (fst c)) Hcfg3 : tr_level (d_tr s3) = tr_level t), E_lev. exact Hlev.
      - exact Hbo3.
      - exact Hex3.
      - exact Hwt. }
    split; [exact Hbits3|].
    intros C. destruct BS'; discriminate C. }
  pose proof (fboev_ok Hfbo) as Hfboev.
  unfold c_deflate_tail in E.
  destruct (Z.eqb_spec flush Z_FINISH) as [EF|EF].
  - destruct (Hfboev s0 z0 flush (se_s2 s t m) z evs syms1 1 HE2 (Hpre 1 ltac:(lia)) Hsy2
                (fun _ => EF) ltac:(intros C; discriminate C) Q6)
      as (s3 & z3 & e & Hc & _ & HE3 & Hk3 & Hbs3 & Ht3 & Hcfg3 & _).
    pose proof HE3 as (_ & _ & _ & _ & _ & (_ & (Hao3 & _)) & _).
    destruct (Hafter 1 s3 z3 ltac:(lia) Hc Hk3 Hbs3 Ht3 Hcfg3 Hao3) as (x & BS'' & Hzs3 & Hk3' & Hbits3 & Hne).
    unfold c_flush_block in E. rewrite Hc in E. cbn [bind] in E.
    destruct (_ && _) in E; injection E as <- <- <-;
      exists k, x, BS'', []; (split; [exact Hzs3|]); (split; [exact Hk3'|]);
      (split; [exact Hbits3|intros _; exact Hne]).
  - destruct (Z.eqb_spec (d_sym_next (se_s2 s t m)) 0) as [S0|S0]; cbn [negb] in E.
    + assert (Hsy : syms1 = []).
      { destruct Ht1 as (_ & _ & T3 & _). change (tr_sym_next t = 0) in S0. rewrite S0 in T3.
        destruct syms1 as [|y syms1]; [reflexivity|]. rewrite Zlength_cons in T3.
        pose proof (Zlength_nonneg syms1). lia. }
      subst syms1. rewrite se_blk_len_nil in Hblk1.
      injection E as <- <- <-.
      exists k, x0, BS', []. split; [exact Hzs|].
      split.
      { apply (fe_kcore dict D' (BS ++ BS') s (se_s2 s t m) syms Hkw Hch Hla ltac:(lia)).
        - exact (se_kp_s2 s t m).
        - reflexivity.
        - change (d_block_start s = d_strstart s). lia.
        - exact Ht1.
        - exact E_L.
        - change (tr_level t <> 0). rewrite E_lev. exact Hlev.
        - exact Hbo.
        - replace (d_block_start s) with (d_strstart s) in Hex by lia. exact Hex.
        - exact Hwt. }
      split; [exact Hbits2|]. intros C; discriminate C.
    + destruct (Hfboev s0 z0 flush (se_s2 s t m) z evs syms1 0 HE2 (Hpre 0 ltac:(lia)) Hsy2
                  ltac:(intros C; discriminate C) ltac:(intros _; right; split; assumption) Q6)
        as (s3 & z3 & e & Hc & _ & HE3 & Hk3 & Hbs3 & Ht3 & Hcfg3 & _).
      pose proof HE3 as (_ & _ & _ & _ & _ & (_ & (Hao3 & _)) & _).
      destruct (Hafter 0 s3 z3 ltac:(lia) Hc Hk3 Hbs3 Ht3 Hcfg3 Hao3) as (x & BS'' & Hzs3 & Hk3' & Hbits3 & Hne).
      unfold c_flush_block in E. rewrite Hc in E. cbn [bind] in E.
      destruct (_ && _) in E; injection E as <- <- <-;
        exists k, x, BS'', []; (split; [exact Hzs3|]); (split; [exact Hk3'|]);
        (split; [exact Hbits3|intros C; discriminate C]).
Qed.
