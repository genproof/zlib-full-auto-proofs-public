(** * The model theory of the deflate laws, core part: the compressors, the window, the hash chains and the
    trees.c state (interface RTDLTIface.core_facts).

    Choose the invariant [W] of a live state (window / hash chains / positions / configuration / trees state and
    the symbols tallied in sym_buf; it must not depend on what [core_eq] lets change) and prove every fact of
    [core_facts W].  Lemma (i) ([Overlay.overlay_statement]) is the hypothesis for compress_block's reads of
    sym_buf at _tr_flush_block. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDLTIface.
Require Import Zlib.proof.roundtrip.RTDLTCHuffKit Zlib.proof.roundtrip.RTDLTCMisc Zlib.proof.roundtrip.RTDLTCSpecs2 Zlib.proof.roundtrip.RTDLTCFill Zlib.proof.roundtrip.RTDLTCLm Zlib.proof.roundtrip.RTDLTCTrees2 Zlib.proof.roundtrip.RTDLTCStored2 Zlib.proof.roundtrip.RTDLTCFast2 Zlib.proof.roundtrip.RTDLTCSlow2 Zlib.proof.roundtrip.RTDLTCHuff2 Zlib.proof.roundtrip.RTDLTCRle2 Zlib.proof.roundtrip.RTDLTCLive2 Zlib.proof.roundtrip.RTDLTCInit Zlib.proof.roundtrip.RTDLTCDict Zlib.proof.roundtrip.RTDLTCDict3 Zlib.proof.roundtrip.RTDLTCStillFill Zlib.proof.roundtrip.RTDLTCStillStored Zlib.proof.roundtrip.RTDLTCStillFast Zlib.proof.roundtrip.RTDLTCStillSlow Zlib.proof.roundtrip.RTDLTCStillHuff Zlib.proof.roundtrip.RTDLTCStillRle.
Import ListNotations.
Local Open Scope Z_scope.

(** Interface v2's adler_pre is exactly adler_ok. *)
Lemma adler_pre_ok : forall w a, adler_pre w a -> adler_ok w a.
Proof. intros w a H. exact H. Qed.

(** ** From the parts over [W] to the facts over [W2] *)

Lemma W_ma0 s : W s -> d_strstart s = 0 -> d_match_available s = 0.
Proof.
  intros (_ & _ & _ & _ & _ & (_ & _ & Hma & _ & Hm1) & _) H0.
  destruct Hma as [E|E]; [exact E|]. destruct (Hm1 E) as (_ & H1 & _). lia.
Qed.

Lemma W_ma0' s : W s -> d_lookahead s = 0 -> d_strstart s = d_block_start s -> d_match_available s = 0.
Proof.
  intros HW Hla Hss. pose proof HW as (_ & _ & _ & _ & _ & _ & _ & syms & Ht).
  exact (proj1 (W_empty s syms HW Ht Hla Hss)).
Qed.

Lemma extra_ma0 s : d_match_available s = 0 -> slow_extra s.
Proof. intros E E1. rewrite E in E1. discriminate E1. Qed.

Lemma fn_of_same s s' : d_level s' = d_level s -> d_strategy s' = d_strategy s -> fn_of s' = fn_of s.
Proof. intros E1 E2. unfold fn_of. rewrite E1, E2. reflexivity. Qed.

Lemma cpost_W2 s z flush s' z' bs evs :
  fn_of s <> 2 -> cpost W s z flush s' z' bs evs -> cpost W2 s z flush s' z' bs evs.
Proof.
  intros Hf (HW & Ho & Hsp & R).
  refine (conj (conj HW _) (conj Ho (conj Hsp R))).
  destruct Hsp as (_ & _ & _ & _ & _ & E1 & E2).
  intros E. exfalso. pose proof HW as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & Hm1) & _).
  destruct (Hm1 E) as (F & _). apply Hf. rewrite <- (fn_of_same s s' E1 E2). exact F.
Qed.

Lemma W2_prm s : W2 s -> prm s.
Proof. intros [H _]. exact (W_prm s H). Qed.

Lemma W2_pos s : W2 s ->
    0 <= d_lookahead s /\ 0 <= d_strstart s /\ - 1099511627776 <= d_block_start s <= d_strstart s /\
    d_strstart s + d_lookahead s <= 2 * d_w_size s.
Proof. intros [H _]. exact (W_pos s H). Qed.

Lemma W2_frame s s' : W2 s -> core_eq s s' -> W2 s'.
Proof.
  intros [H X] He. split; [exact (W_frame s s' H He)|].
  pose proof (wsame_core_eq s s' He) as HS.
  unfold slow_extra in *. rewrite (ws_ma _ _ HS), (ws_pl _ _ HS), (ws_ml _ _ HS). exact X.
Qed.

Lemma W2_tune s good lazy nice chain : W2 s -> s32 nice -> W2 (tune_set s good lazy nice chain).
Proof. intros [H X] Hn. split; [exact (W_tune s good lazy nice chain H Hn)|exact X]. Qed.

Lemma W2_init : forall level method wbits mem strategy z,
    params_ok level method wbits mem strategy = true ->
    exists s z',
      c_deflateInit2_ true true false level method wbits mem strategy true true true true true z =
        Some (Some s, z', Z_OK) /\
      W2 s /\ outok s /\
      d_status s = (if wrap_of wbits =? 2 then GZIP_STATE else INIT_STATE) /\ d_wrap s = wrap_of wbits /\
      d_gzhead s = None /\ d_gzindex s = 0 /\ d_last_flush s = -2 /\
      d_po s = 0 /\ d_pending s = 0 /\ d_bi_valid s = 0 /\
      d_strstart s = 0 /\ d_lookahead s = 0 /\ d_block_start s = 0 /\ d_sym_next s = 0 /\
      d_level s = (if level =? -1 then 6 else level) /\ d_strategy s = strategy /\
      d_w_bits s = Z.max 9 (wb_of wbits) /\ d_hash_bits s = mem + 7 /\
      z' = mkST (z_in z) (z_next_in z) (z_avail_in z) 0 (z_out z) (z_avail_out z) 0
                (if wrap_of wbits =? 2 then 0 else 1) None.
Proof.
  intros level method wbits mem strategy z Hp.
  destruct (init_ok level method wbits mem strategy z Hp) as (s & z' & E & HW & R).
  exists s, z'. split; [exact E|]. split; [|exact R]. split; [exact HW|].
  apply extra_ma0. apply (W_ma0 s HW).
  destruct R as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H.
Qed.

Lemma W2_dict : forall s z d,
    W2 s -> d_status s = INIT_STATE -> 0 <= d_wrap s <= 1 ->
    d_strstart s = 0 -> d_lookahead s = 0 -> d_block_start s = 0 -> d_sym_next s = 0 ->
    bytes d -> Zlength d <= 32768 -> 0 <= z_total_in z <= 1099511627776 -> adler_pre (d_wrap s) (z_adler z) ->
    exists s' z' k,
      c_deflateSetDictionary s z (Some d) = Some (s', z', Z_OK) /\ W2 s' /\
      api_eq s s' /\ out_eq s s' /\ same_prm s s' /\
      d_lookahead s' = 0 /\ d_strstart s' = d_block_start s' /\ (d_strstart s' = 0 <-> d = []) /\
      d_sym_next s' = 0 /\ 0 <= k <= Zlength d /\
      z' = mkST (z_in z) (z_next_in z) (z_avail_in z) (z_total_in z + k) (z_out z) (z_avail_out z)
                (z_total_out z)
                (if d_wrap s =? 1 then Zlib.proof.adler32.Model.ref_adler32 (z_adler z) d else z_adler z)
                (z_msg z).
Proof.
  intros s z d [HW _] H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.
  destruct (dict_ok fill_ok s z d HW H1 H2 H3 H4 H5 H6 H7 H8 H9 H10) as (s' & z' & k & E & HW' & R).
  exists s', z', k. split; [exact E|]. split; [|exact R]. split; [exact HW'|].
  destruct R as (_ & _ & _ & Hla & Hss & _). exact (extra_ma0 s' (W_ma0' s' HW' Hla Hss)).
Qed.

Lemma W2_full : forall s,
    W2 s -> d_lookahead s = 0 -> d_strstart s = d_block_start s ->
    exists s1, c_clear_hash s = Some s1 /\ W2 (full_reset s1) /\
      api_eq s s1 /\ out_eq s s1 /\ same_prm s s1 /\ d_sym_next s1 = d_sym_next s.
Proof.
  intros s [HW _] Hla Hss.
  destruct (W_full s HW Hla Hss) as (s1 & E & HW1 & R).
  exists s1. split; [exact E|]. split; [|exact R]. split; [exact HW1|].
  apply extra_ma0. rewrite (clear_hash_eq s (W_prm s HW) (proj1 (proj2 HW))) in E.
  injection E as <-. exact (W_ma0' s HW Hla Hss).
Qed.

Lemma W2_params : forall s level strategy,
    W2 s -> 0 <= level <= 9 -> 0 <= strategy <= 4 ->
    (cfg_f level = cfg_f (d_level s) /\ strategy = d_strategy s) \/
    (d_lookahead s = 0 /\ d_strstart s = d_block_start s) ->
    exists s1, params_tail s level strategy = Some s1 /\ W2 s1 /\ api_eq s s1 /\ out_eq s s1 /\
      d_level s1 = level /\ d_strategy s1 = strategy /\
      d_w_bits s1 = d_w_bits s /\ d_hash_bits s1 = d_hash_bits s /\
      d_strstart s1 = d_strstart s /\ d_lookahead s1 = d_lookahead s /\ d_block_start s1 = d_block_start s /\
      d_sym_next s1 = d_sym_next s.
Proof.
  intros s level strategy [HW X] Hl Hs Hc.
  destruct (W_params s level strategy HW Hl Hs Hc)
    as (s1 & E & HW1 & A & O & L & S & B & H & SS & LA & BS & SN & MA & PL & ML).
  exists s1. split; [exact E|]. split; [split; [exact HW1|]|].
  - unfold slow_extra in *. rewrite MA, PL, ML. exact X.
  - exact (conj A (conj O (conj L (conj S (conj B (conj H (conj SS (conj LA (conj BS SN))))))))).
Qed.



Lemma dispatch_stored s z flush : prm s -> fn_of s = 0 -> c_compress_func s z flush = c_deflate_stored s z flush.
Proof. intros Hp E. rewrite (compress_dispatch s z flush Hp), E. cbn [Z.eqb]. reflexivity. Qed.

Lemma core_live : fpend_spec2 ->
  forall s z s' z' bs,
    W2 s -> outok s -> quiet s -> zin_ok z -> 0 <= d_wrap s <= 2 -> adler_pre (d_wrap s) (z_adler z) ->
    d_level s = 0 ->
    stored_hdr s + 5 * ((ub s + z_avail_in z) / MAX_STORED) + ub s + z_avail_in z <= z_avail_out z ->
    c_compress_func s z Z_FINISH = Some (s', z', bs) -> bs = finish_done.
Proof.
  intros Hfp s z s' z' bs [HW _] Ho Hq Hz Hw Ha Hl Hroom Hc.
  assert (E : fn_of s = 0) by (unfold fn_of; rewrite Hl; reflexivity).
  rewrite (dispatch_stored s z Z_FINISH (W_prm s HW) E) in Hc.
  exact (live_ok2 Hfp s z s' z' bs HW Ho Hq Hz Hw (adler_pre_ok _ _ Ha) Hl Hroom Hc).
Qed.

(** ** The witness: [W] with deflate_slow's and deflate_huff's extra facts *)
Definition W3 (s : dstate) : Prop := W2 s /\ huff_extra s.

Lemma cpost_imp (Wa Wb : dstate -> Prop) s z f s' z' bs evs :
  (Wa s' -> same_prm s s' -> Wb s') -> cpost Wa s z f s' z' bs evs -> cpost Wb s z f s' z' bs evs.
Proof. intros H (A & B & C & R). exact (conj (H A C) (conj B (conj C R))). Qed.

Lemma fn_of_prm s s' : same_prm s s' -> fn_of s' = fn_of s.
Proof. intros (_ & _ & _ & _ & _ & E1 & E2). exact (fn_of_same s s' E1 E2). Qed.

Lemma slow_extra_fn s : W s -> fn_of s <> 2 -> slow_extra s.
Proof.
  intros HW Hf E. exfalso. pose proof HW as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & Hm1) & _).
  destruct (Hm1 E) as (F & _). exact (Hf F).
Qed.

Lemma huff_extra_fn s : fn_of s <> 3 -> huff_extra s.
Proof. intros Hf E. contradiction. Qed.

Lemma W_sn s : W s -> 0 <= d_sym_next s.
Proof.
  intros (_ & _ & _ & _ & _ & _ & _ & syms & (T1 & T2 & T3 & _) & _).
  unfold d_sym_next. rewrite T3. pose proof (Zlength_nonneg syms). lia.
Qed.

Lemma W3_prm s : W3 s -> prm s.
Proof. intros [H _]. exact (W2_prm s H). Qed.

Lemma W3_pos s : W3 s ->
    0 <= d_lookahead s /\ 0 <= d_strstart s /\ - 1099511627776 <= d_block_start s <= d_strstart s /\
    d_strstart s + d_lookahead s <= 2 * d_w_size s.
Proof. intros [H _]. exact (W2_pos s H). Qed.

Lemma W3_frame s s' : W3 s -> core_eq s s' -> W3 s'.
Proof.
  intros [H X] He. split; [exact (W2_frame s s' H He)|].
  pose proof (wsame_core_eq s s' He) as HS.
  unfold huff_extra in *. rewrite (fn_of_same s s' (ws_lv _ _ HS) (ws_st _ _ HS)).
  unfold d_sym_next. rewrite (ws_ss _ _ HS), (ws_bs _ _ HS), (ws_sn _ _ HS). exact X.
Qed.

Lemma W3_tune s good lazy nice chain : W3 s -> s32 nice -> W3 (tune_set s good lazy nice chain).
Proof. intros [H X] Hn. split; [exact (W2_tune s good lazy nice chain H Hn)|exact X]. Qed.

Lemma W3_init : forall level method wbits mem strategy z,
    params_ok level method wbits mem strategy = true ->
    exists s z',
      c_deflateInit2_ true true false level method wbits mem strategy true true true true true z =
        Some (Some s, z', Z_OK) /\
      W3 s /\ outok s /\
      d_status s = (if wrap_of wbits =? 2 then GZIP_STATE else INIT_STATE) /\ d_wrap s = wrap_of wbits /\
      d_gzhead s = None /\ d_gzindex s = 0 /\ d_last_flush s = -2 /\
      d_po s = 0 /\ d_pending s = 0 /\ d_bi_valid s = 0 /\
      d_strstart s = 0 /\ d_lookahead s = 0 /\ d_block_start s = 0 /\ d_sym_next s = 0 /\
      d_level s = (if level =? -1 then 6 else level) /\ d_strategy s = strategy /\
      d_w_bits s = Z.max 9 (wb_of wbits) /\ d_hash_bits s = mem + 7 /\
      z' = mkST (z_in z) (z_next_in z) (z_avail_in z) 0 (z_out z) (z_avail_out z) 0
                (if wrap_of wbits =? 2 then 0 else 1) None.
Proof.
  intros level method wbits mem strategy z Hp.
  destruct (W2_init level method wbits mem strategy z Hp) as (s & z' & E & HW & R).
  exists s, z'. split; [exact E|]. split; [|exact R]. split; [exact HW|].
  destruct R as (_ & _ & _ & _ & _ & _ & _ & _ & _ & S0 & _ & B0 & N0 & _).
  intros _. rewrite S0, B0, N0. lia.
Qed.

Lemma W3_full : forall s,
    W3 s -> d_lookahead s = 0 -> d_strstart s = d_block_start s ->
    exists s1, c_clear_hash s = Some s1 /\ W3 (full_reset s1) /\
      api_eq s s1 /\ out_eq s s1 /\ same_prm s s1 /\ d_sym_next s1 = d_sym_next s.
Proof.
  intros s [HW _] Hla Hss.
  destruct (W2_full s HW Hla Hss) as (s1 & E & HW1 & R).
  exists s1. split; [exact E|]. split; [|exact R]. split; [exact HW1|].
  intros _. pose proof (W_sn _ (proj1 HW1)) as N.
  change (3 * (0 - 0) <= d_sym_next (full_reset s1)). lia.
Qed.

Lemma fn_params s level strategy : prm s -> 0 <= level <= 9 ->
  cfg_f level = cfg_f (d_level s) -> strategy = d_strategy s ->
  forall s1, d_level s1 = level -> d_strategy s1 = strategy -> fn_of s1 = fn_of s.
Proof.
  intros Hp Hl Hc Hs s1 E1 E2.
  assert (Hold : 0 <= d_level s <= 9)
    by (destruct Hp as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _); exact X).
  unfold fn_of. rewrite E1, E2, <- Hs.
  destruct (Z.eqb_spec level 0) as [L0|L0]; destruct (Z.eqb_spec (d_level s) 0) as [M0|M0].
  - reflexivity.
  - exfalso. rewrite L0, cfg_f_zero in Hc.
    destruct (cfg_f_cases (d_level s) ltac:(lia)) as [[C _]|[C _]]; lia.
  - exfalso. rewrite M0, cfg_f_zero in Hc.
    destruct (cfg_f_cases level ltac:(lia)) as [[C _]|[C _]]; lia.
  - rewrite Hc. reflexivity.
Qed.

Lemma W3_params : forall s level strategy,
    W3 s -> 0 <= level <= 9 -> 0 <= strategy <= 4 ->
    (cfg_f level = cfg_f (d_level s) /\ strategy = d_strategy s) \/
    (d_lookahead s = 0 /\ d_strstart s = d_block_start s) ->
    exists s1, params_tail s level strategy = Some s1 /\ W3 s1 /\ api_eq s s1 /\ out_eq s s1 /\
      d_level s1 = level /\ d_strategy s1 = strategy /\
      d_w_bits s1 = d_w_bits s /\ d_hash_bits s1 = d_hash_bits s /\
      d_strstart s1 = d_strstart s /\ d_lookahead s1 = d_lookahead s /\ d_block_start s1 = d_block_start s /\
      d_sym_next s1 = d_sym_next s.
Proof.
  intros s level strategy [HW X] Hl Hs Hc.
  destruct (W2_params s level strategy HW Hl Hs Hc)
    as (s1 & E & HW1 & A & O & L & S & B & H & SS & LA & BS & SN).
  exists s1. split; [exact E|]. split; [split; [exact HW1|]|].
  - unfold huff_extra in *. rewrite SS, BS, SN.
    destruct Hc as [[Hc1 Hc2]|[Hla Hss]].
    + rewrite (fn_params s level strategy (W2_prm s HW) Hl Hc1 Hc2 s1 L S). exact X.
    + intros _. pose proof (W_sn s (proj1 HW)). rewrite Hss. lia.
  - exact (conj A (conj O (conj L (conj S (conj B (conj H (conj SS (conj LA (conj BS SN))))))))).
Qed.

Lemma core_compress3 : fill_spec -> ins_spec -> lm_spec -> tally_spec2 -> fbo_spec -> fpend_spec2 ->
  forall s z flush,
    W3 s -> outok s -> quiet s -> 0 <= flush <= 5 -> zin_ok z ->
    0 <= d_wrap s <= 2 -> adler_pre (d_wrap s) (z_adler z) ->
    exists s' z' bs evs, c_compress_func s z flush = Some (s', z', bs) /\ cpost W3 s z flush s' z' bs evs.
Proof.
  intros Hfill Hins Hlm Htal Hfbo Hfp s z flush [HW2 Hx] Ho Hq Hf Hz Hw Ha.
  pose proof (proj1 HW2) as HW.
  assert (Hpre : compress_pre s z flush)
    by exact (conj HW (conj Ho (conj Hq (conj Hf (conj Hz (conj Hw (adler_pre_ok _ _ Ha))))))).
  assert (Hpre2 : compress_pre2 s z flush)
    by exact (conj HW2 (conj Ho (conj Hq (conj Hf (conj Hz (conj Hw (adler_pre_ok _ _ Ha))))))).
  assert (Lift : forall s' z' bs evs, fn_of s <> 2 -> fn_of s <> 3 ->
            cpost W s z flush s' z' bs evs -> cpost W3 s z flush s' z' bs evs).
  { intros s' z' bs evs N2 N3. apply cpost_imp. intros HW' Hsp. rewrite <- (fn_of_prm s s' Hsp) in N2, N3.
    split; [split; [exact HW'|exact (slow_extra_fn s' HW' N2)]|exact (huff_extra_fn s' N3)]. }
  rewrite (compress_dispatch s z flush (W_prm s HW)).
  destruct (fn_range s (W_prm s HW)) as [E|[E|[E|[E|E]]]]; rewrite E; cbn [Z.eqb Pos.eqb].
  - destruct (stored_ok2 Hfp s z flush Hpre E) as (s' & z' & bs & evs & Ec & Hc).
    exists s', z', bs, evs. split; [exact Ec|]. apply Lift; [rewrite E; discriminate|rewrite E; discriminate|exact Hc].
  - destruct (fast_ok2 Hfill Hins Hlm Htal Hfbo Hfp s z flush Hpre E) as (s' & z' & bs & evs & Ec & Hc).
    exists s', z', bs, evs. split; [exact Ec|]. apply Lift; [rewrite E; discriminate|rewrite E; discriminate|exact Hc].
  - destruct (slow_ok2 Hfill Hins Hlm Htal Hfbo Hfp s z flush Hpre2 E) as (s' & z' & bs & evs & Ec & Hc).
    exists s', z', bs, evs. split; [exact Ec|]. revert Hc. apply cpost_imp. intros HW' Hsp.
    split; [exact HW'|]. apply huff_extra_fn. rewrite (fn_of_prm s s' Hsp), E. discriminate.
  - destruct (huff_okX Hfill Htal Hfbo s z flush Hpre Hx E) as (s' & z' & bs & evs & Ec & Hc & Hx').
    exists s', z', bs, evs. split; [exact Ec|]. revert Hc. apply cpost_imp. intros HW' Hsp.
    split; [|exact Hx']. split; [exact HW'|]. apply (slow_extra_fn s' HW'). rewrite (fn_of_prm s s' Hsp), E. discriminate.
  - destruct (rle_ok2 Hfill Htal Hfbo Hfp s z flush Hpre E) as (s' & z' & bs & evs & Ec & Hc).
    exists s', z', bs, evs. split; [exact Ec|]. apply Lift; [rewrite E; discriminate|rewrite E; discriminate|exact Hc].
Qed.

Lemma core_live3 : fpend_spec2 ->
  forall s z s' z' bs,
    W3 s -> outok s -> quiet s -> zin_ok z -> 0 <= d_wrap s <= 2 -> adler_pre (d_wrap s) (z_adler z) ->
    d_level s = 0 ->
    stored_hdr s + 5 * ((ub s + z_avail_in z) / MAX_STORED) + ub s + z_avail_in z <= z_avail_out z ->
    c_compress_func s z Z_FINISH = Some (s', z', bs) -> bs = finish_done.
Proof. intros Hfp s z s' z' bs [HW _]. exact (core_live Hfp s z s' z' bs HW). Qed.

(** deflateSetDictionary under the hypotheses status INIT for both wraps and strstart = 0:
    v2's cf_dict without a status hypothesis for raw streams is false (deflateStateCheck). *)
Lemma W3_dict_fix : forall s z d,
    W3 s -> 0 <= d_wrap s <= 1 -> d_status s = INIT_STATE -> d_strstart s = 0 ->
    d_lookahead s = 0 -> d_strstart s = d_block_start s ->
    bytes d -> Zlength d <= 32768 -> 0 <= z_total_in z <= 1099511627776 -> adler_pre (d_wrap s) (z_adler z) ->
    exists s' z' k,
      c_deflateSetDictionary s z (Some d) = Some (s', z', Z_OK) /\ W3 s' /\
      api_eq s s' /\ out_eq s s' /\ same_prm s s' /\
      d_lookahead s' = 0 /\ d_strstart s' = d_block_start s' /\
      (d_strstart s = 0 -> (d_strstart s' = 0 <-> d = [])) /\
      d_sym_next s' = d_sym_next s /\ 0 <= k <= Zlength d /\
      z' = mkST (z_in z) (z_next_in z) (z_avail_in z) (z_total_in z + k) (z_out z) (z_avail_out z)
                (z_total_out z)
                (if d_wrap s =? 1 then Zlib.proof.adler32.Model.ref_adler32 (z_adler z) d else z_adler z)
                (z_msg z).
Proof.
  intros s z d [HW2 _] Hw Hst Hss Hla Hbs Hb Hl Ht Ha.
  pose proof (proj1 HW2) as HW. pose proof HW as (_ & _ & _ & _ & _ & _ & _ & syms & Hwt).
  destruct (W_empty s syms HW Hwt Hla Hbs) as [_ Hsy]. subst syms.
  assert (Hsn : d_sym_next s = 0).
  { destruct Hwt as ((_ & _ & T3 & _) & _). unfold d_sym_next. rewrite T3. reflexivity. }
  assert (Hbs0 : d_block_start s = 0) by lia.
  destruct (W2_dict s z d HW2 Hst Hw Hss Hla Hbs0 Hsn Hb Hl Ht Ha)
    as (s' & z' & k & E & HW2' & A & O & P & La & Sb & Sd & Sn & K & Z).
  exists s', z', k. split; [exact E|]. split.
  { split; [exact HW2'|]. intros _. rewrite Sb. pose proof (W_sn s' (proj1 HW2')). lia. }
  repeat (split; [assumption|]). split; [intros _; exact Sd|]. split; [rewrite Sn, Hsn; reflexivity|].
  split; [exact K|exact Z].
Qed.

(** deflateSetDictionary (interface v3): strstart = block_start = lookahead = 0, any valid status on a raw
    stream (RTDLTCDict3.dict_ok3). *)
Lemma W3_dict : forall s z d,
    W3 s -> 0 <= d_wrap s <= 1 -> bad_state s = false -> (d_wrap s = 1 -> d_status s = INIT_STATE) ->
    d_strstart s = 0 -> d_lookahead s = 0 -> d_block_start s = 0 ->
    bytes d -> Zlength d <= 32768 -> 0 <= z_total_in z <= 1099511627776 -> adler_pre (d_wrap s) (z_adler z) ->
    exists s' z' k,
      c_deflateSetDictionary s z (Some d) = Some (s', z', Z_OK) /\ W3 s' /\
      api_eq s s' /\ out_eq s s' /\ same_prm s s' /\
      d_lookahead s' = 0 /\ d_strstart s' = d_block_start s' /\
      (d_strstart s' = 0 <-> d = []) /\
      d_sym_next s' = d_sym_next s /\ 0 <= k <= Zlength d /\
      z' = mkST (z_in z) (z_next_in z) (z_avail_in z) (z_total_in z + k) (z_out z) (z_avail_out z)
                (z_total_out z)
                (if d_wrap s =? 1 then Zlib.proof.adler32.Model.ref_adler32 (z_adler z) d else z_adler z)
                (z_msg z).
Proof.
  intros s z d [HW2 _] Hw Hbad Hst Hss Hla Hbs Hb Hl Ht Ha.
  pose proof (proj1 HW2) as HW. pose proof HW as (_ & _ & _ & _ & _ & _ & _ & syms & Hwt).
  destruct (W_empty s syms HW Hwt Hla ltac:(lia)) as [_ Hsy]. subst syms.
  assert (Hsn : d_sym_next s = 0).
  { destruct Hwt as ((_ & _ & T3 & _) & _). unfold d_sym_next. rewrite T3. reflexivity. }
  destruct (dict_ok3 fill_ok s z d HW Hbad Hst Hw Hss Hla Hbs Hsn Hb Hl Ht Ha)
    as (s' & z' & k & E & HW' & A & O & P & La & Sb & Sd & Sn & K & Z).
  exists s', z', k. split; [exact E|]. split.
  { split; [split; [exact HW'|exact (extra_ma0 s' (W_ma0' s' HW' La Sb))]|].
    intros _. rewrite Sb. pose proof (W_sn s' HW'). lia. }
  split; [exact A|]. split; [exact O|]. split; [exact P|]. split; [exact La|]. split; [exact Sb|].
  split; [exact Sd|]. split; [rewrite Sn, Hsn; reflexivity|]. split; [exact K|exact Z].
Qed.

(** (v3) cf_still: a compression call that reads nothing from strstart = 0 with everything in blocks leaves
    strstart at 0 (the parts in the files LTCStill...). *)
Lemma W3_still : fill_spec -> ins_spec -> lm_spec -> tally_spec2 -> fbo_spec -> fpend_spec2 ->
  forall s z flush s' z' bs,
    W3 s -> outok s -> quiet s -> 0 <= flush <= 5 -> zin_ok z ->
    0 <= d_wrap s <= 2 -> adler_pre (d_wrap s) (z_adler z) ->
    c_compress_func s z flush = Some (s', z', bs) ->
    ub s = 0 -> d_strstart s = 0 -> z_next_in z' = z_next_in z -> d_strstart s' = 0.
Proof.
  intros Hfill Hins Hlm Htal Hfbo Hfp s z flush s' z' bs [HW2 Hx] Ho Hq Hf Hz Hw Ha E Hub Hss Hn.
  pose proof (proj1 HW2) as HW.
  assert (Hpre : compress_pre s z flush)
    by exact (conj HW (conj Ho (conj Hq (conj Hf (conj Hz (conj Hw (adler_pre_ok _ _ Ha))))))).
  assert (Hpre2 : compress_pre2 s z flush)
    by exact (conj HW2 (conj Ho (conj Hq (conj Hf (conj Hz (conj Hw (adler_pre_ok _ _ Ha))))))).
  assert (Hat : still_at s).
  { destruct (W3_pos s (conj HW2 Hx)) as (P1 & P2 & P3 & P4). unfold ub in Hub. unfold still_at. lia. }
  revert E. rewrite (compress_dispatch s z flush (W_prm s HW)).
  destruct (fn_range s (W_prm s HW)) as [F|[F|[F|[F|F]]]]; rewrite F; cbn [Z.eqb Pos.eqb]; intros E.
  - exact (still_stored_ok Hfill Hfp (stored_ok2 Hfp) s z flush Hpre Hat F s' z' bs E Hn).
  - exact (still_fast_ok fill_idem_ok Hfill Hins Hlm Htal Hfbo Hfp (fast_ok2 Hfill Hins Hlm Htal Hfbo Hfp)
             s z flush Hpre Hat F s' z' bs E Hn).
  - exact (still_slow_ok fill_idem_ok Hfill Hins Hlm Htal Hfbo Hfp (slow_ok2 Hfill Hins Hlm Htal Hfbo Hfp)
             s z flush Hpre2 Hat F s' z' bs E Hn).
  - exact (still_huff_ok fill_idem_ok Hfill Htal Hfbo Hfp (huff_okX Hfill Htal Hfbo)
             s z flush Hpre Hx Hat F s' z' bs E Hn).
  - exact (still_rle_ok fill_idem_ok Hfill Htal Hfbo Hfp (rle_ok2 Hfill Htal Hfbo Hfp)
             s z flush Hpre Hat F s' z' bs E Hn).
Qed.

Theorem core_theory : Zlib.proof.huffman.Overlay.overlay_statement -> exists W, core_facts W.
Proof.
  intros Hov. exists W3.
  destruct (trees_ok2 Hov) as (Htal & Htf & Hroom).
  pose proof (fbo_ok Htf Hroom) as Hfbo. pose proof fpend2_ok as Hfp.
  pose proof fill_ok as Hfill. destruct lm_ok as [Hins Hlm].
  exact (Build_core_facts W3 W3_prm W3_pos W3_frame W3_init W3_tune W3_dict
           (core_compress3 Hfill Hins Hlm Htal Hfbo Hfp) (W3_still Hfill Hins Hlm Htal Hfbo Hfp)
           (core_live3 Hfp) W3_full W3_params).
Qed.
