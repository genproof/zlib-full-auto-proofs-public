(** * Core part of the deflate law theory: the small facts of core_facts for [W]
    (cf_prm, cf_pos, cf_frame, cf_tune, cf_full, cf_params) and the dispatch of c_compress_func. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTCLib.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

Lemma W_prm : forall s, W s -> prm s.
Proof. intros s H. destruct H as [H _]. exact H. Qed.

Lemma W_pos : forall s, W s ->
    0 <= d_lookahead s /\ 0 <= d_strstart s /\ - 1099511627776 <= d_block_start s <= d_strstart s /\
    d_strstart s + d_lookahead s <= 2 * d_w_size s.
Proof.
  intros s (Hp & (_ & _ & Hws & _) & (P1 & P2 & P3 & P4 & P5 & _) & _). rewrite Hws in P3. lia.
Qed.

(** The fields [W] depends on. *)
Record wsame (s s' : dstate) : Prop := {
  ws_wsize : d_w_size s' = d_w_size s; ws_wbits : d_w_bits s' = d_w_bits s; ws_wmask : d_w_mask s' = d_w_mask s;
  ws_window : d_window s' = d_window s; ws_wsz : d_window_size s' = d_window_size s;
  ws_prev : d_prev s' = d_prev s; ws_head : d_head s' = d_head s;
  ws_hsize : d_hash_size s' = d_hash_size s; ws_hbits : d_hash_bits s' = d_hash_bits s;
  ws_hmask : d_hash_mask s' = d_hash_mask s; ws_hshift : d_hash_shift s' = d_hash_shift s;
  ws_bs : d_block_start s' = d_block_start s; ws_ml : d_match_length s' = d_match_length s;
  ws_ma : d_match_available s' = d_match_available s; ws_ss : d_strstart s' = d_strstart s;
  ws_ms : d_match_start s' = d_match_start s; ws_la : d_lookahead s' = d_lookahead s;
  ws_pl : d_prev_length s' = d_prev_length s; ws_ins : d_insert s' = d_insert s;
  ws_hw : d_high_water s' = d_high_water s; ws_pbs : d_pending_buf_size s' = d_pending_buf_size s;
  ws_method : d_method s' = d_method s;
  ws_lt : tr_ltree (d_tr s') = tr_ltree (d_tr s); ws_dt : tr_dtree (d_tr s') = tr_dtree (d_tr s);
  ws_blt : tr_bltree (d_tr s') = tr_bltree (d_tr s); ws_wk : tr_wk (d_tr s') = tr_wk (d_tr s);
  ws_sn : tr_sym_next (d_tr s') = tr_sym_next (d_tr s); ws_se : tr_sym_end (d_tr s') = tr_sym_end (d_tr s);
  ws_mt : tr_matches (d_tr s') = tr_matches (d_tr s); ws_lb : tr_lit_bufsize (d_tr s') = tr_lit_bufsize (d_tr s);
  ws_lv : tr_level (d_tr s') = tr_level (d_tr s); ws_st : tr_strategy (d_tr s') = tr_strategy (d_tr s);
  ws_obl : Zlength (o_buf (tr_out (d_tr s'))) = Zlength (o_buf (tr_out (d_tr s)));
  ws_pbl : Zlength (d_pbm s') = Zlength (d_pbm s);
  ws_sym : sym_region s' = sym_region s
}.

Lemma W_transfer s s' : wsame s s' -> W s -> W s'.
Proof.
  intros HS HW. destruct HS.
  unfold W, prm, wstruct, wpos, wwin, whash, chain_ok, chain_with, lim, slide_hc, wmatch, fn_of, wtrees, tree_ok,
    sym_ok, sym_region, d_L, d_level, d_strategy, d_matches, d_sym_next, MAX_DIST in *.
  cbn [d_strstart d_w_size d_hash_size d_head d_prev d_w_mask set_d_prev set_d_head] in *.
  rewrite ws_wsize0, ws_wbits0, ws_wmask0, ws_window0, ws_wsz0, ws_prev0, ws_head0, ws_hsize0, ws_hbits0, ws_hmask0,
    ws_hshift0, ws_bs0, ws_ml0, ws_ma0, ws_ss0, ws_ms0, ws_la0, ws_pl0, ws_ins0, ws_hw0, ws_pbs0, ws_method0, ws_lt0,
    ws_dt0, ws_blt0, ws_wk0, ws_sn0, ws_se0, ws_mt0, ws_lb0, ws_lv0, ws_st0, ws_obl0, ws_pbl0.
  rewrite ws_sn0, ws_lb0 in ws_sym0.
  destruct HW as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & syms & (T1 & T2 & T3 & T4 & T5 & T6 & T7) & R).
  rewrite T3 in ws_sym0. injection ws_sym0 as E1 E2.
  refine (conj A1 (conj A2 (conj A3 (conj A4 (conj A5 (conj A6 (conj A7 (ex_intro _ syms
    (conj (conj T1 (conj T2 (conj T3 (conj T4 (conj _ (conj _ T7)))))) R)))))))));
    [rewrite E1; exact T5 | rewrite E2; exact T6].
Qed.

Lemma wsame_core_eq s s' : core_eq s s' -> wsame s s'.
Proof.
  intros (Hs & Hsym & Hl1 & Hl2).
  constructor; try assumption.
  - exact (f_equal (fun x => d_w_size x) Hs).
  - exact (f_equal (fun x => d_w_bits x) Hs).
  - exact (f_equal (fun x => d_w_mask x) Hs).
  - exact (f_equal (fun x => d_window x) Hs).
  - exact (f_equal (fun x => d_window_size x) Hs).
  - exact (f_equal (fun x => d_prev x) Hs).
  - exact (f_equal (fun x => d_head x) Hs).
  - exact (f_equal (fun x => d_hash_size x) Hs).
  - exact (f_equal (fun x => d_hash_bits x) Hs).
  - exact (f_equal (fun x => d_hash_mask x) Hs).
  - exact (f_equal (fun x => d_hash_shift x) Hs).
  - exact (f_equal (fun x => d_block_start x) Hs).
  - exact (f_equal (fun x => d_match_length x) Hs).
  - exact (f_equal (fun x => d_match_available x) Hs).
  - exact (f_equal (fun x => d_strstart x) Hs).
  - exact (f_equal (fun x => d_match_start x) Hs).
  - exact (f_equal (fun x => d_lookahead x) Hs).
  - exact (f_equal (fun x => d_prev_length x) Hs).
  - exact (f_equal (fun x => d_insert x) Hs).
  - exact (f_equal (fun x => d_high_water x) Hs).
  - exact (f_equal (fun x => d_pending_buf_size x) Hs).
  - exact (f_equal (fun x => d_method x) Hs).
  - exact (f_equal (fun x => tr_ltree (d_tr x)) Hs).
  - exact (f_equal (fun x => tr_dtree (d_tr x)) Hs).
  - exact (f_equal (fun x => tr_bltree (d_tr x)) Hs).
  - exact (f_equal (fun x => tr_wk (d_tr x)) Hs).
  - exact (f_equal (fun x => tr_sym_next (d_tr x)) Hs).
  - exact (f_equal (fun x => tr_sym_end (d_tr x)) Hs).
  - exact (f_equal (fun x => tr_matches (d_tr x)) Hs).
  - exact (f_equal (fun x => tr_lit_bufsize (d_tr x)) Hs).
  - exact (f_equal (fun x => tr_level (d_tr x)) Hs).
  - exact (f_equal (fun x => tr_strategy (d_tr x)) Hs).
Qed.

Lemma wsame_tune s good lazy nice chain : wsame s (tune_set s good lazy nice chain).
Proof. constructor; reflexivity. Qed.


Lemma W_frame : forall s s', W s -> core_eq s s' -> W s'.
Proof. intros s s' HW He. exact (W_transfer s s' (wsame_core_eq s s' He) HW). Qed.

Lemma W_tune : forall s good lazy nice chain, W s -> s32 nice -> W (tune_set s good lazy nice chain).
Proof. intros s good lazy nice chain HW _. exact (W_transfer _ _ (wsame_tune s good lazy nice chain) HW). Qed.

Lemma clear_hash_eq s : prm s -> wstruct s ->
  c_clear_hash s = Some (set_d_slid (set_d_head s (repeat 0 (Z.to_nat (d_hash_size s)))) 0).
Proof.
  intros (_ & _ & _ & Hhb & Hhs & _) (_ & _ & _ & _ & Hl).
  assert (Hpos : 256 <= d_hash_size s) by (rewrite Hhs; replace 256 with (2 ^ 8) by reflexivity;
    apply Z.pow_le_mono_r; lia).
  assert (Hpos2 : d_hash_size s <= 65536) by (rewrite Hhs; replace 65536 with (2 ^ 16) by reflexivity;
    apply Z.pow_le_mono_r; lia).
  unfold c_clear_hash, wr, in_range.
  rewrite Hl. unfold u32. rewrite Z.mod_small by lia.
  replace ((0 <=? d_hash_size s - 1) && (d_hash_size s - 1 <? d_hash_size s)) with true
    by (symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
  cbn [bind guard].
  rewrite Zlength_upd_Znth_any, Hl.
  replace ((1 <=? d_hash_size s) && (d_hash_size s =? d_hash_size s)) with true
    by (symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.eqb_eq]; lia).
  reflexivity.
Qed.

Lemma slide_hash_eq s : prm s -> wstruct s ->
  c_slide_hash s = Some (set_d_slid (slide_hc s) 1).
Proof.
  intros (Hwb & Hws & _ & Hhb & Hhs & _) (_ & _ & _ & Hpl & Hl).
  assert (Hpos : 256 <= d_hash_size s) by (rewrite Hhs; replace 256 with (2 ^ 8) by reflexivity;
    apply Z.pow_le_mono_r; lia).
  assert (Hw : 1 <= d_w_size s) by (rewrite Hws; replace 1 with (2 ^ 0) by reflexivity; apply Z.pow_le_mono_r; lia).
  unfold c_slide_hash. rewrite Hl, Hpl.
  replace ((1 <=? d_hash_size s) && (d_hash_size s =? d_hash_size s) && (1 <=? d_w_size s) &&
           (d_w_size s =? d_w_size s)) with true
    by (symmetry; repeat (apply andb_true_intro; split); first [apply Z.leb_le | apply Z.eqb_eq]; lia).
  reflexivity.
Qed.

Lemma sym_len_pos x : valid_sym (fst x) (snd x) -> 1 <= sym_len x.
Proof. unfold sym_len, valid_sym. intros H. destruct (fst x =? 0); lia. Qed.

Lemma blk_len_ge syms : (forall x, In x syms -> valid_sym (fst x) (snd x)) -> Zlength syms <= blk_len syms.
Proof.
  induction syms as [|x r IH]; intros Hv; [cbn; lia|].
  change (blk_len (x :: r)) with (sym_len x + blk_len r). rewrite Zlength_cons.
  pose proof (sym_len_pos x (Hv x (or_introl eq_refl))). specialize (IH (fun y Hy => Hv y (or_intror Hy))). lia.
Qed.

Lemma blk_len_zero syms : (forall x, In x syms -> valid_sym (fst x) (snd x)) -> blk_len syms <= 0 -> syms = [].
Proof.
  intros Hv H. pose proof (blk_len_ge syms Hv). destruct syms as [|x r]; [reflexivity|].
  rewrite Zlength_cons in H0. pose proof (Zlength_nonneg r). lia.
Qed.

(** In a state of [W] with nothing read beyond the blocks: no pending byte and no symbols. *)
Lemma W_empty s syms : W s -> wtrees s syms -> d_lookahead s = 0 -> d_strstart s = d_block_start s ->
  d_match_available s = 0 /\ syms = [].
Proof.
  intros (_ & _ & _ & _ & _ & Hm & _) (Tok & _ & _ & Tl0 & Tl1) Hla Hss.
  pose proof (proj1 (proj2 (proj2 (proj2 Tok)))) as Hv.
  destruct Hm as (_ & _ & Hma & _ & Hm1).
  destruct (Z.eq_dec (d_level s) 0) as [L0|L0].
  - split; [|exact (Tl0 L0)].
    destruct Hma as [E|E]; [exact E|]. destruct (Hm1 E) as (Hf & _).
    unfold fn_of in Hf. rewrite L0 in Hf. discriminate Hf.
  - specialize (Tl1 L0). pose proof (blk_len_ge syms Hv). pose proof (Zlength_nonneg syms).
    assert (E : d_match_available s = 0) by (destruct Hma; lia).
    split; [exact E|]. apply blk_len_zero; [exact Hv|lia].
Qed.

Lemma W_full : forall s,
    W s -> d_lookahead s = 0 -> d_strstart s = d_block_start s ->
    exists s1, c_clear_hash s = Some s1 /\ W (full_reset s1) /\
      api_eq s s1 /\ out_eq s s1 /\ same_prm s s1 /\ d_sym_next s1 = d_sym_next s.
Proof.
  intros s HW Hla Hss.
  pose proof HW as HW'.
  destruct HW' as (Hp & Hst & Hpos & Hwin & Hh & Hm & H0 & syms & Ht).
  destruct (W_empty s syms HW Ht Hla Hss) as [Hma Hsy]. subst syms.
  eexists. split; [exact (clear_hash_eq s Hp Hst)|].
  split; [|split; [repeat split; reflexivity|split; [repeat split; reflexivity|split; [repeat split; reflexivity|reflexivity]]]].
  assert (Hhs : 0 <= d_hash_size s) by (destruct Hp as (_ & _ & _ & _ & Hhs & _); rewrite Hhs; apply Z.pow_nonneg; lia).
  assert (Hw : 1 <= d_w_size s) by (destruct Hp as (Hwb & Hws & _); rewrite Hws;
    replace 1 with (2 ^ 0) by reflexivity; apply Z.pow_le_mono_r; lia).
  assert (Hz : forall f, f 0 = 0 -> forall h, Znth h (map f (repeat 0 (Z.to_nat (d_hash_size s)))) = 0).
  { intros f Hf h. rewrite map_repeat, Hf. destruct (Z_lt_le_dec h 0); [rewrite Znth_underflow by lia; reflexivity|].
    destruct (Z_lt_le_dec h (d_hash_size s)).
    - rewrite Znth_repeat'; [reflexivity|]. rewrite Z2Nat.id by lia. lia.
    - rewrite Znth_overflow; [reflexivity|]. rewrite Zlength_repeat; lia. }
  assert (Hz0 : forall h, Znth h (repeat 0 (Z.to_nat (d_hash_size s))) = 0).
  { intros h. rewrite <- (map_id (repeat 0 _)). apply (Hz (fun x => x)). reflexivity. }
  unfold full_reset, W.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (ex_intro _ [] _)))))))).
  - exact Hp.
  - destruct Hst as (S1 & S2 & S3 & S4 & S5). refine (conj S1 (conj S2 (conj S3 (conj S4 _)))).
    cbn. rewrite Zlength_repeat; lia.
  - destruct Hpos as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
    unfold wpos, MAX_DIST in *. cbn. rewrite Hla in *. lia.
  - unfold wwin in *. cbn. intros i Hi. apply Hwin. rewrite Hla in *. lia.
  - match goal with |- context [whash ?x] => set (s2 := x) end.
    assert (C : forall n l, chain_with s2 n l (fun v => v = 0)).
    { intros n l. unfold chain_with, s2. cbn. split; [intros v ->; left; reflexivity|].
      split; [intros h _; apply Hz0|]. intros q -> Hq. lia. }
    assert (C' : forall n l, chain_with (slide_hc s2) n l (fun v => v = 0)).
    { intros n l. unfold chain_with, slide_hc, s2. cbn. split; [intros v ->; left; reflexivity|].
      split; [intros h _; apply (Hz (slide_entry (d_w_size s))); unfold slide_entry;
        destruct (Z.geb_spec 0 (d_w_size s)); [lia|reflexivity]|]. intros q -> Hq. lia. }
    assert (EL : d_level s2 = d_level s) by reflexivity.
    assert (EM : d_matches s2 = d_matches s) by reflexivity.
    unfold whash, chain_ok in *. rewrite EL, EM.
    destruct (d_level s =? 0).
    + destruct Hh as [[E _]|[[E _]|E]].
      * left. split; [exact E|]. eexists. apply C.
      * right; left. split; [exact E|]. eexists. apply C'.
      * right; right. exact E.
    + destruct Hh as [E _]. split; [exact E|]. eexists. apply C.
  - unfold wmatch in *. cbn. destruct Hm as (M1 & M2 & M3 & M4 & M5).
    refine (conj M1 (conj M2 (conj M3 (conj M4 _)))). intros E. rewrite Hma in E. discriminate E.
  - cbn. intros L. split; [exact Hla|lia].
  - destruct Ht as (T1 & T2 & T3 & T4 & T5). unfold wtrees. cbn.
    refine (conj T1 (conj T2 (conj (Forall_nil _) (conj (fun _ => eq_refl) _)))).
    intros _. rewrite Hma. reflexivity.
Qed.

(** The fields [W] depends on, except head, prev, matches, level, strategy. *)
Record wsamex (s s' : dstate) : Prop := {
  wx_wsize : d_w_size s' = d_w_size s; wx_wbits : d_w_bits s' = d_w_bits s; wx_wmask : d_w_mask s' = d_w_mask s;
  wx_window : d_window s' = d_window s; wx_wsz : d_window_size s' = d_window_size s;
  wx_hsize : d_hash_size s' = d_hash_size s; wx_hbits : d_hash_bits s' = d_hash_bits s;
  wx_hmask : d_hash_mask s' = d_hash_mask s; wx_hshift : d_hash_shift s' = d_hash_shift s;
  wx_bs : d_block_start s' = d_block_start s; wx_ml : d_match_length s' = d_match_length s;
  wx_ma : d_match_available s' = d_match_available s; wx_ss : d_strstart s' = d_strstart s;
  wx_ms : d_match_start s' = d_match_start s; wx_la : d_lookahead s' = d_lookahead s;
  wx_pl : d_prev_length s' = d_prev_length s; wx_ins : d_insert s' = d_insert s;
  wx_hw : d_high_water s' = d_high_water s; wx_pbs : d_pending_buf_size s' = d_pending_buf_size s;
  wx_method : d_method s' = d_method s;
  wx_lt : tr_ltree (d_tr s') = tr_ltree (d_tr s); wx_dt : tr_dtree (d_tr s') = tr_dtree (d_tr s);
  wx_blt : tr_bltree (d_tr s') = tr_bltree (d_tr s); wx_wk : tr_wk (d_tr s') = tr_wk (d_tr s);
  wx_sn : tr_sym_next (d_tr s') = tr_sym_next (d_tr s); wx_se : tr_sym_end (d_tr s') = tr_sym_end (d_tr s);
  wx_lb : tr_lit_bufsize (d_tr s') = tr_lit_bufsize (d_tr s);
  wx_obl : Zlength (o_buf (tr_out (d_tr s'))) = Zlength (o_buf (tr_out (d_tr s)));
  wx_pbl : Zlength (d_pbm s') = Zlength (d_pbm s);
  wx_sym : sym_region s' = sym_region s;
  wx_prevl : Zlength (d_prev s') = Zlength (d_prev s); wx_headl : Zlength (d_head s') = Zlength (d_head s)
}.

Lemma W_rebuild s s1 : W s -> wsamex s s1 ->
  0 <= d_level s1 <= 9 -> 0 <= d_strategy s1 <= 4 -> whash s1 ->
  (d_match_available s = 1 -> fn_of s1 = 2 /\ d_strategy s1 = d_strategy s) ->
  (forall syms, wtrees s syms ->
     Forall (sym_ok s1) syms /\ (d_level s1 = 0 -> syms = []) /\
     (d_level s1 <> 0 -> blk_len syms = d_strstart s - d_block_start s - d_match_available s)) ->
  (d_level s1 = 0 -> d_lookahead s = 0 /\ 0 <= d_block_start s) ->
  W s1.
Proof.
  intros HW HX Hlv Hst Hh Hfn Hsy H0.
  destruct HW as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & syms & Ht).
  destruct (Hsy syms Ht) as (Y1 & Y2 & Y3).
  destruct HX.
  assert (H0' : d_level s1 = 0 -> d_lookahead s1 = 0 /\ 0 <= d_block_start s1) by (rewrite wx_la0, wx_bs0; exact H0).
  unfold W. refine (conj _ (conj _ (conj _ (conj _ (conj Hh (conj _ (conj H0' (ex_intro _ syms _)))))))).
  - unfold prm, d_L, d_level, d_strategy in *. rewrite wx_wsize0, wx_wbits0, wx_wmask0, wx_hsize0, wx_hbits0,
      wx_hmask0, wx_hshift0, wx_lb0, wx_pbs0, wx_obl0, wx_pbl0, wx_se0, wx_method0.
    destruct A1 as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & _ & _ & P15).
    exact (conj P1 (conj P2 (conj P3 (conj P4 (conj P5 (conj P6 (conj P7 (conj P8 (conj P9 (conj P10
      (conj P11 (conj P12 (conj Hlv (conj Hst P15)))))))))))))).
  - unfold wstruct in *. rewrite wx_window0, wx_wsz0, wx_wsize0, wx_prevl0, wx_headl0, wx_hsize0. exact A2.
  - unfold wpos, MAX_DIST in *. rewrite wx_la0, wx_ss0, wx_wsz0, wx_bs0, wx_wsize0, wx_ins0, wx_hw0. exact A3.
  - unfold wwin in *. rewrite wx_ss0, wx_la0, wx_hw0, wx_window0. exact A4.
  - unfold wmatch, MAX_DIST in *. rewrite wx_ml0, wx_pl0, wx_ma0, wx_ss0, wx_la0, wx_ms0, wx_wsize0.
    destruct A6 as (M1 & M2 & M3 & M4 & M5). refine (conj M1 (conj M2 (conj M3 (conj M4 _)))).
    intros E. destruct (Hfn E) as [F1 F2]. rewrite F1, F2. destruct (M5 E) as (_ & M6 & M7).
    exact (conj eq_refl (conj M6 M7)).
  - destruct Ht as (T1 & T2 & T3 & T4 & T5). unfold wtrees, d_L in *.
    refine (conj _ (conj _ (conj Y1 (conj Y2 _)))).
    + unfold tree_ok, sym_region, d_L, d_sym_next in *. rewrite wx_lb0, wx_obl0, wx_pbl0, wx_sn0, wx_lt0, wx_dt0,
        wx_blt0, wx_wk0. rewrite wx_sn0, wx_lb0 in wx_sym0.
      destruct T1 as (B1 & B2 & B3 & B4 & B5 & B6 & B7). rewrite B3 in wx_sym0. injection wx_sym0 as E1 E2.
      rewrite E1, E2. exact (conj B1 (conj B2 (conj B3 (conj B4 (conj B5 (conj B6 B7)))))).
    + rewrite wx_lb0. exact T2.
    + intros L. rewrite wx_ss0, wx_bs0, wx_ma0. exact (Y3 L).
Qed.

Lemma chain_zero s n l : (forall h, Znth h (d_head s) = 0) -> chain_with s n l (fun v => v = 0).
Proof.
  intros Hz. unfold chain_with. split; [intros v ->; left; reflexivity|].
  split; [intros h _; apply Hz|]. intros q -> Hq. lia.
Qed.

Lemma cfg_f_cases l : 1 <= l <= 9 -> (cfg_f l = 1 /\ l < 4) \/ (cfg_f l = 2 /\ 4 <= l).
Proof.
  intros H.
  assert (Hc : l = 1 \/ l = 2 \/ l = 3 \/ l = 4 \/ l = 5 \/ l = 6 \/ l = 7 \/ l = 8 \/ l = 9) by lia.
  destruct Hc as [->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]];
    [left|left|left|right|right|right|right|right|right]; (split; [vm_compute; reflexivity|lia]).
Qed.

Lemma cfg_f_zero : cfg_f 0 = 0.
Proof. vm_compute. reflexivity. Qed.

(** The hash step of the level change. *)
Lemma hstep_ok s : W s ->
  exists sh,
    (if (d_level s =? 0) && negb (d_matches s =? 0) then
       let* s := (if d_matches s =? 1 then c_slide_hash s else c_clear_hash s) in
       Some (set_d_matches s 0)
     else Some s) = Some sh /\
    wsamex s sh /\ d_matches sh = 0 /\ chain_ok sh /\ d_level sh = d_level s /\ d_strategy sh = d_strategy s /\
    api_eq s sh /\ out_eq s sh /\ d_w_bits sh = d_w_bits s /\ d_hash_bits sh = d_hash_bits s.
Proof.
  intros HW. pose proof HW as (Hp & Hst & _ & _ & Hh & _).
  unfold whash in Hh.
  destruct (d_level s =? 0) eqn:EL; cbn [andb negb].
  - destruct Hh as [[E Hc]|[[E Hc]|E]].
    + rewrite E. cbn [Z.eqb negb]. exists s. split; [reflexivity|].
      split; [constructor; reflexivity|]. split; [exact E|]. split; [exact Hc|].
      repeat split; reflexivity.
    + rewrite E. cbn [Z.eqb negb Pos.eqb]. rewrite (slide_hash_eq s Hp Hst). cbn [bind].
      eexists. split; [reflexivity|].
      split; [constructor; try reflexivity; unfold slide_hc; cbn; rewrite Zlength_map; reflexivity|].
      split; [reflexivity|]. split; [exact Hc|]. repeat split; reflexivity.
    + rewrite E. cbn [Z.eqb negb Pos.eqb]. rewrite (clear_hash_eq s Hp Hst). cbn [bind].
      assert (Hhs : 0 <= d_hash_size s) by (destruct Hp as (_ & _ & _ & _ & Hhs & _); rewrite Hhs; apply Z.pow_nonneg; lia).
      eexists. split; [reflexivity|].
      split; [constructor; try reflexivity; cbn; destruct Hst as (_ & _ & _ & _ & Hl); rewrite Zlength_repeat, Hl; lia|].
      split; [reflexivity|]. split.
      * exists (fun v => v = 0). apply chain_zero. intros h. cbn.
        destruct (Z_lt_le_dec h 0); [rewrite Znth_underflow by lia; reflexivity|].
        destruct (Z_lt_le_dec h (d_hash_size s)).
        -- rewrite Znth_repeat'; [reflexivity|]. rewrite Z2Nat.id by lia. lia.
        -- rewrite Znth_overflow; [reflexivity|]. rewrite Zlength_repeat; lia.
      * repeat split; reflexivity.
  - destruct Hh as [E Hc]. exists s. split; [reflexivity|].
    split; [constructor; reflexivity|]. split; [exact E|]. split; [exact Hc|]. repeat split; reflexivity.
Qed.

Lemma W_params : forall s level strategy,
    W s -> 0 <= level <= 9 -> 0 <= strategy <= 4 ->
    (cfg_f level = cfg_f (d_level s) /\ strategy = d_strategy s) \/
    (d_lookahead s = 0 /\ d_strstart s = d_block_start s) ->
    exists s1, params_tail s level strategy = Some s1 /\ W s1 /\ api_eq s s1 /\ out_eq s s1 /\
      d_level s1 = level /\ d_strategy s1 = strategy /\
      d_w_bits s1 = d_w_bits s /\ d_hash_bits s1 = d_hash_bits s /\
      d_strstart s1 = d_strstart s /\ d_lookahead s1 = d_lookahead s /\ d_block_start s1 = d_block_start s /\
      d_sym_next s1 = d_sym_next s /\ d_match_available s1 = d_match_available s /\
      d_prev_length s1 = d_prev_length s /\ d_match_length s1 = d_match_length s.
Proof.
  intros s level strategy HW Hl Hs Hcase.
  pose proof HW as (Hp & Hst & Hpos & Hwin & Hh & Hm & H0 & syms0 & Ht0).
  assert (Hold : 0 <= d_level s <= 9) by (destruct Hp as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hl0 & _); exact Hl0).
  assert (HB : d_lookahead s = 0 /\ d_strstart s = d_block_start s ->
               d_match_available s = 0 /\ forall sy, wtrees s sy -> sy = []).
  { intros [A B]. split; [exact (proj1 (W_empty s syms0 HW Ht0 A B))|].
    intros sy Hy. exact (proj2 (W_empty s sy HW Hy A B)). }
  assert (Hss0 : 0 <= d_strstart s) by (destruct Hpos as (_ & P2 & _); exact P2).
  destruct Hm as (M1 & M2 & M3 & M4 & M5).
  unfold params_tail.
  destruct (Z.eqb_spec (d_level s) level) as [Eq|Ne].
  - cbn [negb bind]. eexists. split; [reflexivity|].
    split; [|unfold api_eq, out_eq; repeat split; try reflexivity; exact Eq].
    apply (W_rebuild s _ HW).
    + constructor; reflexivity.
    + exact Hold.
    + cbn. exact Hs.
    + exact Hh.
    + intros E. destruct Hcase as [[Hc Hs']|Hb].
      * split; [|exact Hs']. destruct (M5 E) as (F & _). rewrite <- F. unfold fn_of. cbn [d_level d_strategy d_tr set_d_strategy set_d_tr api_set_strategy tr_level tr_strategy].
        rewrite Hs'. reflexivity.
      * rewrite (proj1 (HB Hb)) in E. discriminate E.
    + intros sy Hy. destruct Hy as (Y1 & Y2 & Y3 & Y4 & Y5). split; [|split; [exact Y4|exact Y5]].
      destruct Hcase as [[Hc Hs']|Hb].
      * eapply Forall_impl; [|exact Y3]. intros x Hx. unfold sym_ok in *. cbn [d_level d_strategy d_tr set_d_strategy set_d_tr api_set_strategy tr_level tr_strategy MAX_DIST d_w_size].
        rewrite Hs'. exact Hx.
      * rewrite ((proj2 (HB Hb)) sy (conj Y1 (conj Y2 (conj Y3 (conj Y4 Y5))))). constructor.
    + exact H0.
  - cbn [negb].
    destruct (hstep_ok s HW) as (sh & Eh & Hx & Hmt & Hc & Hlv & Hstr & Ha & Ho & Hwb & Hhb).
    rewrite Eh. cbn [bind].
    destruct (Znth level config_table) as [[[[g lz] nc] ch] f] eqn:Ecfg. cbn [bind].
    eexists. split; [reflexivity|].
    destruct Hx.
    assert (Hcase' : (cfg_f level = cfg_f (d_level s) /\ strategy = d_strategy s /\ 1 <= level /\ 1 <= d_level s) \/
                     (d_lookahead s = 0 /\ d_strstart s = d_block_start s)).
    { destruct Hcase as [[Hc1 Hs1]|Hb]; [left|right; exact Hb].
      destruct (Z.eq_dec level 0) as [L0|L0].
      - exfalso. subst level. rewrite cfg_f_zero in Hc1.
        destruct (Z.eq_dec (d_level s) 0) as [L1|L1]; [lia|].
        destruct (cfg_f_cases (d_level s) ltac:(lia)) as [[C _]|[C _]]; lia.
      - destruct (Z.eq_dec (d_level s) 0) as [L1|L1].
        + exfalso. rewrite L1, cfg_f_zero in Hc1.
          destruct (cfg_f_cases level ltac:(lia)) as [[C _]|[C _]]; lia.
        + repeat split; auto; lia. }
    split.
    + apply (W_rebuild s _ HW).
      * constructor; assumption.
      * exact Hl.
      * cbn. exact Hs.
      * unfold whash. cbn [d_level d_matches d_tr set_d_strategy set_d_max_chain_length set_d_nice_match
          set_d_good_match set_d_max_lazy_match set_d_level set_d_tr api_set_strategy api_set_level tr_level tr_matches].
        unfold d_matches in Hmt. rewrite Hmt.
        destruct (level =? 0); [left; split; [reflexivity|exact Hc]|split; [reflexivity|exact Hc]].
      * intros E. destruct Hcase' as [(Hc1 & Hs1 & L1 & L2)|Hb].
        -- destruct (M5 E) as (F & _).
           unfold fn_of in F |- *.
           cbn [d_level d_strategy d_tr set_d_strategy set_d_max_chain_length set_d_nice_match
             set_d_good_match set_d_max_lazy_match set_d_level set_d_tr api_set_strategy api_set_level tr_level tr_strategy].
           rewrite Hs1.
           destruct (Z.eqb_spec (d_level s) 0) as [Z0|Z0]; [lia|].
           destruct (Z.eqb_spec level 0) as [Z1|Z1]; [lia|].
           destruct (d_strategy s =? Z_HUFFMAN_ONLY); [discriminate F|].
           destruct (d_strategy s =? Z_RLE); [discriminate F|].
           split; [rewrite Hc1; exact F|reflexivity].
        -- rewrite (proj1 (HB Hb)) in E. discriminate E.
      * intros sy Hy. destruct Hy as (Y1 & Y2 & Y3 & Y4 & Y5).
        destruct Hcase' as [(Hc1 & Hs1 & L1 & L2)|Hb].
        -- split; [|split].
           ++ eapply Forall_impl; [|exact Y3]. intros x Hx. unfold sym_ok in *.
              cbn [d_level d_strategy d_tr set_d_strategy set_d_max_chain_length set_d_nice_match
                set_d_good_match set_d_max_lazy_match set_d_level set_d_tr api_set_strategy api_set_level tr_level
                tr_strategy MAX_DIST d_w_size].
              unfold MAX_DIST in Hx.
              destruct Hx as (X1 & X2 & X3). split; [exact X1|]. split.
              ** intros Hne. unfold MAX_DIST. cbn [d_w_size set_d_strategy set_d_max_chain_length set_d_nice_match
                   set_d_good_match set_d_max_lazy_match set_d_level set_d_tr]. rewrite wx_wsize0. exact (X2 Hne).
              ** intros H4 Hf. apply X3; [|rewrite <- Hs1; exact Hf].
                 destruct (cfg_f_cases level (conj L1 (proj2 Hl))) as [[C C1]|[C C1]];
                   destruct (cfg_f_cases (d_level s) (conj L2 (proj2 Hold))) as [[D D1]|[D D1]];
                   clear - C C1 D D1 Hc1 H4; lia.
           ++ cbn. intros L0. lia.
           ++ intros _. apply Y5. lia.
        -- rewrite ((proj2 (HB Hb)) sy (conj Y1 (conj Y2 (conj Y3 (conj Y4 Y5))))).
           split; [constructor|]. split; [reflexivity|]. intros _.
           destruct Hb as [A B]. rewrite (proj1 (HB (conj A B))), B. cbn. lia.
      * cbn. intros L0. destruct Hcase' as [(Hc1 & Hs1 & L1 & L2)|Hb]; [lia|].
        destruct Hb as [A B]. split; [exact A|lia].
    + unfold api_eq, out_eq in *.
      destruct Ha as (Ha1 & Ha2 & Ha3 & Ha4 & Ha5 & Ha6). destruct Ho as (Ho1 & Ho2 & Ho3).
      repeat split; cbn; try assumption; try reflexivity.
Qed.

Lemma cfg_func_eq l : 1 <= l <= 9 -> cfg_func l = Some (cfg_f l) /\ (cfg_f l = 1 \/ cfg_f l = 2).
Proof.
  intros H.
  assert (Hc : l = 1 \/ l = 2 \/ l = 3 \/ l = 4 \/ l = 5 \/ l = 6 \/ l = 7 \/ l = 8 \/ l = 9) by lia.
  destruct Hc as [->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]; (split; [vm_compute; reflexivity| vm_compute; auto]).
Qed.

(** The dispatch of the compression stage. *)
Lemma compress_dispatch : forall s z flush, prm s ->
  c_compress_func s z flush =
  if fn_of s =? 0 then c_deflate_stored s z flush
  else if fn_of s =? 1 then c_deflate_fast s z flush
  else if fn_of s =? 2 then c_deflate_slow s z flush
  else if fn_of s =? 3 then c_deflate_huff s z flush
  else c_deflate_rle s z flush.
Proof.
  intros s z flush (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hl & _).
  unfold c_compress_func at 1. unfold fn_of.
  destruct (d_level s =? 0) eqn:E0; [exact eq_refl|].
  destruct (d_strategy s =? Z_HUFFMAN_ONLY); [cbn [Z.eqb Pos.eqb]; exact eq_refl|].
  destruct (d_strategy s =? Z_RLE); [cbn [Z.eqb Pos.eqb]; exact eq_refl|].
  apply Z.eqb_neq in E0.
  destruct (cfg_func_eq (d_level s) ltac:(lia)) as [E [E1|E1]]; rewrite E; cbn [bind]; rewrite E1;
    cbn [Z.eqb Pos.eqb]; exact eq_refl.
Qed.

Lemma fn_range : forall s, prm s -> fn_of s = 0 \/ fn_of s = 1 \/ fn_of s = 2 \/ fn_of s = 3 \/ fn_of s = 4.
Proof.
  intros s (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hl & _).
  unfold fn_of. destruct (d_level s =? 0) eqn:E0; [auto|].
  destruct (d_strategy s =? Z_HUFFMAN_ONLY); [auto|]. destruct (d_strategy s =? Z_RLE); [auto|].
  apply Z.eqb_neq in E0. destruct (cfg_func_eq (d_level s) ltac:(lia)) as [_ [E1|E1]]; rewrite E1; auto.
Qed.
