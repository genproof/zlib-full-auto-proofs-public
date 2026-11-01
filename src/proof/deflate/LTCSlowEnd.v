(** * deflate_slow, part End: [end_ok].  Invariant, split and statements: LTCSlowInv.v. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTCSlowInv.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** Helpers *)

Lemma se_sumZ_app a b : HuffAbs.sumZ (a ++ b) = HuffAbs.sumZ a + HuffAbs.sumZ b.
Proof. induction a as [|x a IH]; cbn [app HuffAbs.sumZ]; [lia|]. rewrite IH. lia. Qed.

Lemma se_blk_len_app syms x : blk_len (syms ++ [x]) = blk_len syms + sym_len x.
Proof. unfold blk_len. rewrite map_app, se_sumZ_app. cbn [map HuffAbs.sumZ]. lia. Qed.

Lemma se_blk_len_nil : blk_len [] = 0.
Proof. reflexivity. Qed.

(** The state after the pending literal and s->insert. *)
Definition se_s2 (s : dstate) (t : tstate) (m : list bool) : dstate :=
  set_insert_end (set_d_match_available (set_d_trm s (t, m)) 0).

(** The fields FLUSH_BLOCK_ONLY, the literal and set_insert_end may change, blanked. *)
Definition se_kp (s : dstate) : dstate := set_d_insert (set_d_match_available (fbo_keep s) 0) 0.

Lemma se_kp_s2 s t m : se_kp (se_s2 s t m) = se_kp s.
Proof. reflexivity. Qed.

Lemma se_trm_eta s : d_match_available s = 0 -> set_d_match_available (set_d_trm s (d_tr s, d_pbm s)) 0 = s.
Proof. destruct s; cbn; intros ->; reflexivity. Qed.

Lemma se_frame_refl t m : tally_frame t m t m.
Proof.
  unfold tally_frame, pb_grow. do 6 (split; [reflexivity|]).
  split; [reflexivity|]. split; [reflexivity|]. split; [intros i H; exact H|intros H; exact H].
Qed.

Lemma se_prm_bounds s : prm s -> 512 <= d_w_size s <= 32768 /\ 128 <= d_L s <= 32768.
Proof.
  intros (P1 & P2 & _ & P4 & _ & _ & _ & P8 & _).
  split.
  - rewrite P2. split.
    + replace 512 with (2 ^ 9) by reflexivity. apply Z.pow_le_mono_r; lia.
    + replace 32768 with (2 ^ 15) by reflexivity. apply Z.pow_le_mono_r; lia.
  - rewrite P8. split.
    + replace 128 with (2 ^ 7) by reflexivity. apply Z.pow_le_mono_r; lia.
    + replace 32768 with (2 ^ 15) by reflexivity. apply Z.pow_le_mono_r; lia.
Qed.

(** The pending literal. *)
Lemma se_lit s : tally_spec2 -> W2 s -> d_lookahead s = 0 -> d_level s <> 0 ->
  exists t m syms1,
    (forall z flush, dsl_end s z flush = c_deflate_tail (se_s2 s t m) z flush) /\
    tree_ok t m syms1 /\ Zlength syms1 <= d_L s - 1 /\ Forall (sym_ok s) syms1 /\
    blk_len syms1 = d_strstart s - d_block_start s /\ tally_frame (d_tr s) (d_pbm s) t m.
Proof.
  intros [Htl _] [HW _] Hla Hlev.
  destruct HW as (Hp & Hs & Hpos & Hw & Hh & Hm & H0 & syms & Htr).
  destruct Htr as (Ht & Hlen & Hsy & Hl0 & Hbl).
  specialize (Hbl Hlev).
  destruct Hm as (Hml & Hpl & Hav & Ha0 & Ha1).
  destruct (se_prm_bounds s Hp) as [Hws HL].
  destruct Hav as [A|A].
  - exists (d_tr s), (d_pbm s), syms. split.
    { intros z flush. unfold dsl_end, se_s2. rewrite A. cbn [negb Z.eqb bind].
      rewrite (se_trm_eta s A). reflexivity. }
    split; [exact Ht|]. split; [lia|]. split; [exact Hsy|]. split; [rewrite Hbl, A; lia|].
    apply se_frame_refl.
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
    exact Hfr.
Qed.

(** EI, quiet and prm carry over to the state after the literal. *)
Lemma se_EI s0 z0 flush s z evs t m :
  EI s0 z0 flush s z evs -> tally_frame (d_tr s) (d_pbm s) t m -> EI s0 z0 flush (se_s2 s t m) z evs.
Proof.
  intros (Hc & Hf & Ho & Hsp & Hapi & Hz & Ha & Hk & Hch & Hev) Hfr.
  pose proof Hfr as (Hcfg & Hmt & Hpd & Hbb & Hbv & Hbu & Hg).
  assert (E_L : tr_lit_bufsize t = d_L s) by exact (f_equal (fun c => fst (fst (fst c))) Hcfg).
  assert (E_lev : tr_level t = d_level s) by exact (f_equal (fun c => snd (fst c)) Hcfg).
  assert (E_str : tr_strategy t = d_strategy s) by exact (f_equal (fun c => snd c) Hcfg).
  split; [exact Hc|]. split; [exact Hf|].
  split.
  { apply (outok_grow s); [exact Ho|exact Hg|reflexivity|exact Hpd|reflexivity|].
    destruct Ho as (_ & Hbo & _). change (bits_ok (tr_out t)). unfold bits_ok in *.
    rewrite Hbv, Hbb, Hpd. exact Hbo. }
  split.
  { destruct Hsp as (A1 & A2 & A3 & A4 & A5 & A6 & A7).
    split; [exact A1|]. split; [exact A2|]. split; [exact A3|].
    split; [change (tr_lit_bufsize t = d_L s0); rewrite E_L; exact A4|].
    split; [exact A5|]. split; [change (tr_level t = d_level s0); rewrite E_lev; exact A6|].
    change (tr_strategy t = d_strategy s0); rewrite E_str; exact A7. }
  split; [exact Hapi|]. split; [exact Hz|]. split; [exact Ha|]. split; [exact Hk|].
  split; [|exact Hev].
  replace (Gb (se_s2 s t m) (z_total_out z)) with (Gb s (z_total_out z)); [exact Hch|].
  change (8 * (z_total_out z + o_pending (tr_out (d_tr s))) + o_bi_valid (tr_out (d_tr s)) =
          8 * (z_total_out z + o_pending (tr_out t)) + o_bi_valid (tr_out t)).
  rewrite Hpd, Hbv. reflexivity.
Qed.

Lemma se_quiet s t m : quiet s -> tally_frame (d_tr s) (d_pbm s) t m -> quiet (se_s2 s t m).
Proof.
  intros (Q1 & Q2 & Q3) (_ & _ & Hpd & _ & Hbv & _).
  split; [change (o_pending (tr_out t) = 0); rewrite Hpd; exact Q1|].
  split; [exact Q2|]. change (o_bi_valid (tr_out t) <= 7). rewrite Hbv. exact Q3.
Qed.

Lemma se_prm s t m : prm s -> tally_frame (d_tr s) (d_pbm s) t m -> prm (se_s2 s t m).
Proof.
  intros Hp (Hcfg & _ & _ & _ & _ & _ & G1 & G2 & _).
  assert (E_L : tr_lit_bufsize t = d_L s) by exact (f_equal (fun c => fst (fst (fst c))) Hcfg).
  assert (E_se : tr_sym_end t = tr_sym_end (d_tr s)) by exact (f_equal (fun c => snd (fst (fst c))) Hcfg).
  assert (E_lev : tr_level t = d_level s) by exact (f_equal (fun c => snd (fst c)) Hcfg).
  assert (E_str : tr_strategy t = d_strategy s) by exact (f_equal (fun c => snd c) Hcfg).
  destruct Hp as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15).
  split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P5|].
  split; [exact P6|]. split; [exact P7|].
  split; [change (tr_lit_bufsize t = 2 ^ (d_hash_bits s - 1)); rewrite E_L; exact P8|].
  split; [change (d_pending_buf_size s = 4 * tr_lit_bufsize t); rewrite E_L; exact P9|].
  split; [change (Zlength (o_buf (tr_out t)) = 4 * tr_lit_bufsize t); rewrite E_L, G1; exact P10|].
  split; [change (Zlength m = 4 * tr_lit_bufsize t); rewrite E_L, G2; exact P11|].
  split; [change (tr_sym_end t = 3 * (tr_lit_bufsize t - 1)); rewrite E_L, E_se; exact P12|].
  split; [change (0 <= tr_level t <= 9); rewrite E_lev; exact P13|].
  split; [change (0 <= tr_strategy t <= 4); rewrite E_str; exact P14|].
  exact P15.
Qed.

(** W2 at the end: the window, chains and matches of [s], no pending literal, an empty block. *)
Lemma se_W2_fin s s' :
  W2 s -> d_lookahead s = 0 -> d_level s <> 0 ->
  se_kp s' = se_kp s -> d_match_available s' = 0 ->
  d_insert s' = (if d_strstart s <? MIN_MATCH - 1 then d_strstart s else MIN_MATCH - 1) ->
  d_block_start s' = d_strstart s ->
  tree_ok (d_tr s') (d_pbm s') [] -> tr_cfg (d_tr s') = tr_cfg (d_tr s) -> d_matches s' = 0 ->
  W2 s'.
Proof.
  intros [HW Hx] Hla Hlev Hk Ha Hi Hb Ht Hcfg Hmt.
  destruct HW as (Hp & Hs & Hpos & Hw & Hh & Hm & _ & _).
  destruct (se_prm_bounds s Hp) as [Hws HL].
  assert (E_wb : d_w_bits s' = d_w_bits s) by exact (f_equal d_w_bits Hk).
  assert (E_ws : d_w_size s' = d_w_size s) by exact (f_equal d_w_size Hk).
  assert (E_wm : d_w_mask s' = d_w_mask s) by exact (f_equal d_w_mask Hk).
  assert (E_hb : d_hash_bits s' = d_hash_bits s) by exact (f_equal d_hash_bits Hk).
  assert (E_hs : d_hash_size s' = d_hash_size s) by exact (f_equal d_hash_size Hk).
  assert (E_hm : d_hash_mask s' = d_hash_mask s) by exact (f_equal d_hash_mask Hk).
  assert (E_hsh : d_hash_shift s' = d_hash_shift s) by exact (f_equal d_hash_shift Hk).
  assert (E_pbs : d_pending_buf_size s' = d_pending_buf_size s) by exact (f_equal d_pending_buf_size Hk).
  assert (E_me : d_method s' = d_method s) by exact (f_equal d_method Hk).
  assert (E_win : d_window s' = d_window s) by exact (f_equal d_window Hk).
  assert (E_wsz : d_window_size s' = d_window_size s) by exact (f_equal d_window_size Hk).
  assert (E_prev : d_prev s' = d_prev s) by exact (f_equal d_prev Hk).
  assert (E_head : d_head s' = d_head s) by exact (f_equal d_head Hk).
  assert (E_la : d_lookahead s' = d_lookahead s) by exact (f_equal d_lookahead Hk).
  assert (E_ss : d_strstart s' = d_strstart s) by exact (f_equal d_strstart Hk).
  assert (E_hw : d_high_water s' = d_high_water s) by exact (f_equal d_high_water Hk).
  assert (E_ml : d_match_length s' = d_match_length s) by exact (f_equal d_match_length Hk).
  assert (E_pl : d_prev_length s' = d_prev_length s) by exact (f_equal d_prev_length Hk).
  assert (E_L : d_L s' = d_L s) by exact (f_equal (fun c => fst (fst (fst c))) Hcfg).
  assert (E_se : tr_sym_end (d_tr s') = tr_sym_end (d_tr s)) by exact (f_equal (fun c => snd (fst (fst c))) Hcfg).
  assert (E_lev : d_level s' = d_level s) by exact (f_equal (fun c => snd (fst c)) Hcfg).
  assert (E_str : d_strategy s' = d_strategy s) by exact (f_equal (fun c => snd c) Hcfg).
  (* the matches of [s] are short *)
  destruct Hm as (Hml & Hpl & Hav & Ha0 & Ha1).
  assert (Hshort : d_match_length s < MIN_MATCH /\ d_prev_length s < MIN_MATCH).
  { destruct Hav as [A|A]; [exact (Ha0 A)|].
    destruct (Ha1 A) as (_ & _ & Hc).
    assert (Hml3 : d_match_length s < MIN_MATCH).
    { destruct (Z_lt_le_dec (d_match_length s) MIN_MATCH) as [L|L]; [exact L|].
      destruct (Hc L) as (Hc1 & _). unfold MIN_MATCH in *. lia. }
    split; [exact Hml3|].
    destruct (Z_lt_le_dec (d_prev_length s) MIN_MATCH) as [L|L]; [exact L|].
    specialize (Hx A L). lia. }
  pose proof Ht as (T1 & T2 & T3 & _).
  split.
  2:{ unfold slow_extra. rewrite Ha. intros; lia. }
  split.
  { (* prm *)
    destruct Hp as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15).
    unfold prm. rewrite E_wb, E_ws, E_wm, E_hb, E_hs, E_hm, E_hsh, E_L, E_pbs, E_se, E_lev, E_str, E_me.
    unfold d_L in T1, T2. unfold d_L in E_L. rewrite E_L in T1, T2.
    split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P5|].
    split; [exact P6|]. split; [exact P7|]. split; [exact P8|]. split; [exact P9|].
    split; [exact T1|]. split; [exact T2|]. split; [exact P12|]. split; [exact P13|]. split; [exact P14|].
    exact P15. }
  split.
  { unfold wstruct. rewrite E_win, E_wsz, E_ws, E_prev, E_head, E_hs. exact Hs. }
  split.
  { destruct Hpos as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
    unfold wpos. rewrite E_la, E_ss, E_wsz, Hb, Hi, E_ws, E_hw. unfold MAX_DIST. rewrite E_ws.
    change (MIN_MATCH - 1) with 2.
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    destruct (Z.ltb_spec (d_strstart s) 2); repeat split; lia. }
  split.
  { unfold wwin. rewrite E_win, E_ss, E_la, E_hw. exact Hw. }
  split.
  { unfold whash in *. rewrite E_lev. rewrite (proj2 (Z.eqb_neq _ _) Hlev) in Hh |- *.
    split; [exact Hmt|]. destruct Hh as [_ Hco].
    unfold chain_ok, chain_with, lim, MAX_DIST in *.
    rewrite E_ss, E_ws, E_head, E_prev, E_hs, E_wm. exact Hco. }
  split.
  { unfold wmatch. rewrite E_ml, E_pl, Ha. unfold MIN_MATCH, MAX_MATCH in *.
    split; [lia|]. split; [lia|]. split; [left; reflexivity|]. split; [intros; lia|]. intros; lia. }
  split; [intros E0; rewrite E_lev in E0; contradiction|].
  exists []. unfold wtrees. split; [exact Ht|]. split; [rewrite Zlength_nil, E_L; lia|].
  split; [constructor|]. split; [intros; reflexivity|].
  intros _. rewrite se_blk_len_nil, Hb, E_ss, Ha. lia.
Qed.

(** cpost from EI. *)
Lemma se_cpost s0 z0 flush s z bs evs :
  W2 s -> EI s0 z0 flush s z evs ->
  match bs with
  | need_more =>
      Forall (fun e => ev_last e = 0) evs /\ d_bi_valid s <= 7 /\
      (flush = Z_NO_FLUSH \/ z_avail_out z = 0 \/ d_level s0 = 0)
  | block_done =>
      Forall (fun e => ev_last e = 0) evs /\ flush <> Z_NO_FLUSH /\ flush <> Z_FINISH /\
      z_avail_in z = 0 /\ ub s = 0 /\ quiet s /\ d_sym_next s = 0
  | finish_started =>
      last_ev evs /\ flush = Z_FINISH /\ z_avail_in z = 0 /\ ub s = 0 /\ d_sym_next s = 0 /\
      d_bi_valid s = 0 /\ z_avail_out z = 0 /\ (d_level s0 <> 0 -> d_pending s <> 0 \/ d_wrap s0 <> 0)
  | finish_done =>
      last_ev evs /\ flush = Z_FINISH /\ z_avail_in z = 0 /\ ub s = 0 /\ d_sym_next s = 0 /\
      quiet s /\ d_bi_valid s = 0
  end ->
  cpost W2 s0 z0 flush s z bs evs.
Proof.
  intros HW (_ & _ & Ho & Hsp & Hapi & _ & _ & Hz & Hc & He) Hb.
  unfold cpost. split; [exact HW|]. split; [exact Ho|]. split; [exact Hsp|]. split; [exact Hapi|].
  split; [exact Hz|]. split; [exact Hc|]. split; [exact He|]. exact Hb.
Qed.

Lemma se_last_ev evs e : Forall (fun e => ev_last e = 0) evs -> ev_last e = 1 -> last_ev (evs ++ [e]).
Proof. intros H1 H2. exists evs, e. split; [reflexivity|]. split; assumption. Qed.

Lemma se_last0 evs e : Forall (fun e => ev_last e = 0) evs -> ev_last e = 0 ->
  Forall (fun e => ev_last e = 0) (evs ++ [e]).
Proof. intros H1 H2. apply Forall_app. split; [exact H1|]. constructor; [exact H2|constructor]. Qed.

(** The state after FLUSH_BLOCK_ONLY at the end. *)
Lemma se_after s t m s3 :
  W2 s -> d_lookahead s = 0 -> d_level s <> 0 -> tally_frame (d_tr s) (d_pbm s) t m ->
  fbo_keep s3 = fbo_keep (se_s2 s t m) -> d_block_start s3 = d_strstart (se_s2 s t m) ->
  tree_ok (d_tr s3) (d_pbm s3) [] -> tr_cfg (d_tr s3) = tr_cfg (d_tr (se_s2 s t m)) -> d_matches s3 = 0 ->
  W2 s3 /\ ub s3 = 0 /\ d_sym_next s3 = 0.
Proof.
  intros HW2 Hla Hlev Hfr Hk Hbs3 Ht3 Hcfg3 Hm3.
  pose proof Hfr as (Hcfg & _).
  assert (E_ss3 : d_strstart s3 = d_strstart s) by exact (f_equal d_strstart Hk).
  assert (E_la3 : d_lookahead s3 = d_lookahead s) by exact (f_equal d_lookahead Hk).
  assert (Hbs3' : d_block_start s3 = d_strstart s) by exact Hbs3.
  split.
  { apply (se_W2_fin s s3 HW2 Hla Hlev).
    - unfold se_kp. rewrite Hk. exact (se_kp_s2 s t m).
    - exact (f_equal d_match_available Hk).
    - exact (f_equal d_insert Hk).
    - exact Hbs3'.
    - exact Ht3.
    - rewrite Hcfg3. exact Hcfg.
    - exact Hm3. }
  split.
  - unfold ub. rewrite E_ss3, E_la3, Hbs3', Hla. lia.
  - destruct Ht3 as (_ & _ & T3 & _). unfold d_sym_next. rewrite T3. reflexivity.
Qed.

Theorem end_ok : tally_spec2 -> fboev_part -> end_part.
Proof.
  intros Htal Hfbo s0 z0 flush s z evs HSI Hla Hai Hnf Hss.
  pose proof HSI as (HW2 & Hq & HL & HE).
  pose proof HE as (Hc0 & Hfn0 & Ho & Hsp & Hapi & Hz & Had & _ & _ & _).
  assert (Hlev : d_level s <> 0).
  { destruct Hsp as (_ & _ & _ & _ & _ & E & _). rewrite E. intro E0.
    unfold fn_of in Hfn0. rewrite E0 in Hfn0. cbn [Z.eqb] in Hfn0. discriminate. }
  destruct (se_lit s Htal HW2 Hla Hlev) as (t & m & syms1 & Hdsl & Ht1 & Hlen1 & Hsy1 & Hblk1 & Hfr).
  rewrite Hdsl.
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
  assert (Hmat : d_matches s = 0).
  { unfold whash in Hh. rewrite (proj2 (Z.eqb_neq _ _) Hlev) in Hh. exact (proj1 Hh). }
  assert (Hsy2 : Forall (sym_ok (se_s2 s t m)) syms1).
  { eapply Forall_impl; [|exact Hsy1]. intros x Hx. unfold sym_ok in *.
    change (d_level (se_s2 s t m)) with (tr_level t). change (d_strategy (se_s2 s t m)) with (tr_strategy t).
    rewrite E_lev, E_str. exact Hx. }
  assert (Hpre : forall last, 0 <= last <= 1 -> fbo_pre (se_s2 s t m) z syms1 last).
  { intros last Hl. unfold fbo_pre.
    split; [exact Hp2|]. split; [exact Hs|].
    split; [change (0 < tr_level t); rewrite E_lev;
            destruct Hp as (_&_&_&_&_&_&_&_&_&_&_&_&P13&_); lia|].
    split; [exact Ht1|]. split; [change (Zlength syms1 <= tr_lit_bufsize t - 1); rewrite E_L; exact Hlen1|].
    split; [exact Hblk1|]. split; [exact Q4|]. split; [exact Q5|].
    split.
    { intros Hb0. change (0 <= d_block_start s) in Hb0. unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in Hss.
      split; [change (d_strstart s - d_block_start s <= 65535); lia|].
      split; [change (d_strstart s <= Zlength (mb_val (d_window s))); lia|].
      intros i Hi. apply Hw. rewrite Hla. change (d_block_start s <= i < d_strstart s) in Hi. lia. }
    split; [exact (proj1 (proj2 (proj2 HE2)))|]. split; [exact Hq2|]. split; [exact Hl|].
    destruct Hz as [_ Hzo]. exact Hzo. }
  unfold c_deflate_tail.
  destruct (Z.eqb_spec flush Z_FINISH) as [EF|EF].
  - destruct (Hfbo s0 z0 flush (se_s2 s t m) z evs syms1 1 HE2 (Hpre 1 ltac:(lia)) Hsy2
                (fun _ => EF) ltac:(intros H; discriminate H) Q6)
      as (s3 & z3 & e & Hc & Hlast & HE3 & Hk & Hbs3 & Ht3 & Hcfg3 & Hm3 & Hbv3 & Hbv31 & Hpz & Hai3).
    specialize (Hbv31 eq_refl).
    destruct (se_after s t m s3 HW2 Hla Hlev Hfr Hk Hbs3 Ht3 Hcfg3 Hm3) as (HW3 & Hub3 & Hsn3).
    pose proof HE3 as (_ & _ & Ho3 & Hsp3 & Hapi3 & _).
    assert (Hlev_ := se_last_ev evs e HL Hlast).
    assert (Hstarted : z_avail_out z3 = 0 -> d_pending s3 <> 0 \/ d_wrap s3 <> 0 ->
              cpost W2 s0 z0 flush s3 z3 finish_started (evs ++ [e])).
    { intros E PW. apply se_cpost; [exact HW3|exact HE3|]. hnf.
      split; [exact Hlev_|]. split; [exact EF|]. split; [rewrite Hai3; exact Hai|]. split; [exact Hub3|].
      split; [exact Hsn3|]. split; [exact Hbv31|]. split; [exact E|].
      intros _. destruct Hapi3 as (_ & Hwr & _). rewrite <- Hwr. exact PW. }
    assert (Hdone : d_pending s3 = 0 -> cpost W2 s0 z0 flush s3 z3 finish_done (evs ++ [e])).
    { intros P0. apply se_cpost; [exact HW3|exact HE3|]. hnf.
      split; [exact Hlev_|]. split; [exact EF|]. split; [rewrite Hai3; exact Hai|]. split; [exact Hub3|].
      split; [exact Hsn3|]. split; [|exact Hbv31].
      split; [exact P0|]. split; [|lia]. destruct Ho3 as (_ & _ & _ & _ & _ & Ho3'). exact (Ho3' P0). }
    unfold c_flush_block. rewrite Hc. cbn [bind].
    destruct (Z.eqb_spec (z_avail_out z3) 0) as [E|E];
      destruct (Z.eqb_spec (d_pending s3) 0) as [P|P];
      destruct (Z.eqb_spec (d_wrap s3) 0) as [Wr|Wr]; cbn [andb orb negb Z.eqb Pos.eqb bind].
    + exists s3, z3, finish_done, (evs ++ [e]). split; [reflexivity|]. exact (Hdone P).
    + exists s3, z3, finish_started, (evs ++ [e]). split; [reflexivity|]. exact (Hstarted E (or_intror Wr)).
    + exists s3, z3, finish_started, (evs ++ [e]). split; [reflexivity|]. exact (Hstarted E (or_introl P)).
    + exists s3, z3, finish_started, (evs ++ [e]). split; [reflexivity|]. exact (Hstarted E (or_introl P)).
    + exists s3, z3, finish_done, (evs ++ [e]). split; [reflexivity|]. exact (Hdone P).
    + exists s3, z3, finish_done, (evs ++ [e]). split; [reflexivity|]. exact (Hdone P).
    + destruct Hpz; contradiction.
    + destruct Hpz; contradiction.
  - destruct (Z.eqb_spec (d_sym_next (se_s2 s t m)) 0) as [S0|S0]; cbn [negb].
    + assert (Hsy : syms1 = []).
      { destruct Ht1 as (_ & _ & T3 & _). change (tr_sym_next t = 0) in S0. rewrite S0 in T3.
        destruct syms1 as [|y syms1]; [reflexivity|]. rewrite Zlength_cons in T3.
        pose proof (Zlength_nonneg syms1). lia. }
      subst syms1. rewrite se_blk_len_nil in Hblk1.
      exists (se_s2 s t m), z, block_done, evs. split; [reflexivity|].
      apply se_cpost; [|exact HE2|].
      { apply (se_W2_fin s _ HW2 Hla Hlev).
        - exact (se_kp_s2 s t m).
        - reflexivity.
        - reflexivity.
        - change (d_block_start s = d_strstart s). lia.
        - exact Ht1.
        - exact Hcfg.
        - change (tr_matches t = 0). rewrite Hmt. exact Hmat. }
      hnf. split; [exact HL|]. split; [exact Hnf|]. split; [exact EF|]. split; [exact Hai|].
      split; [change (d_strstart s - d_block_start s + d_lookahead s = 0); lia|].
      split; [exact Hq2|]. exact S0.
    + destruct (Hfbo s0 z0 flush (se_s2 s t m) z evs syms1 0 HE2 (Hpre 0 ltac:(lia)) Hsy2
                  ltac:(intros H; discriminate H) ltac:(intros _; right; split; assumption) Q6)
        as (s3 & z3 & e & Hc & Hlast & HE3 & Hk & Hbs3 & Ht3 & Hcfg3 & Hm3 & Hbv3 & _ & Hpz & Hai3).
      destruct (se_after s t m s3 HW2 Hla Hlev Hfr Hk Hbs3 Ht3 Hcfg3 Hm3) as (HW3 & Hub3 & Hsn3).
      pose proof HE3 as (_ & _ & Ho3 & _).
      assert (HL3 := se_last0 evs e HL Hlast).
      unfold c_flush_block. rewrite Hc. cbn [bind].
      destruct (Z.eqb_spec (z_avail_out z3) 0) as [E|E]; cbn [andb orb negb Z.eqb Pos.eqb bind].
      * exists s3, z3, need_more, (evs ++ [e]). split; [reflexivity|].
        apply se_cpost; [exact HW3|exact HE3|]. hnf. split; [exact HL3|]. split; [exact Hbv3|]. right; left; exact E.
      * exists s3, z3, block_done, (evs ++ [e]). split; [reflexivity|].
        assert (P0 : d_pending s3 = 0) by (destruct Hpz; [assumption|contradiction]).
        apply se_cpost; [exact HW3|exact HE3|]. hnf.
        split; [exact HL3|]. split; [exact Hnf|]. split; [exact EF|]. split; [rewrite Hai3; exact Hai|].
        split; [exact Hub3|]. split; [|exact Hsn3].
        split; [exact P0|]. split; [|exact Hbv3].
        destruct Ho3 as (_ & _ & _ & _ & _ & Ho3'). exact (Ho3' P0).
Qed.
