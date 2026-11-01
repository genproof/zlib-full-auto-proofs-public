(** * Helpers of LTCInit.v: deflateInit2_ with accepted parameters. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTCLib.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** The state deflateInit2_ hands to deflateReset. *)
Definition s_pre (lv wb wrap mem strategy : Z) : dstate :=
  let L := Z.shiftl 1 (mem + 6) in
  let s := init_dstate wrap wb (mem + 7) L in
  let s := set_d_tr s (mkTS (tr_ltree (d_tr s)) (tr_dtree (d_tr s)) (tr_bltree (d_tr s)) 0 0 0 (tr_wk (d_tr s))
                            (tr_out (d_tr s)) 0 (u32 ((L - 1) * 3)) 0 L lv strategy 0) in
  set_d_method s (u8 8).

Lemma init_unfold level method wbits mem strategy z :
  params_ok level method wbits mem strategy = true ->
  c_deflateInit2_ true true false level method wbits mem strategy true true true true true z =
  (let* (s, z, r) := c_deflateReset (s_pre (if level =? -1 then 6 else level) (Z.max 9 (wb_of wbits))
                                           (wrap_of wbits) mem strategy) (set_z_msg z None) in
   Some (Some s, z, r)).
Proof.
  intros H.
  unfold params_ok in H.
  rewrite !andb_true_iff in H. destruct H as [[[[[[[[[[H1 H2] H3] H4] H5] H6] H7] H8] H9] H10] H11].
  unfold c_deflateInit2_. cbn [negb orb].
  unfold wb_of, wrap_of in *.
  rewrite Z.eqb_eq in H4; subst method.
  rewrite negb_true_iff, Z.ltb_ge in H1.
  rewrite Z.leb_le in H2, H3, H9, H10, H5, H6.
  change Z_DEFAULT_COMPRESSION with (-1).
  set (lv := if level =? -1 then 6 else level) in *.
  rewrite Z.leb_le in H7, H8.
  unfold MAX_MEM_LEVEL, Z_DEFLATED, Z_FIXED.
  destruct (Z.ltb_spec wbits 0).
  - destruct (Z.ltb_spec wbits (-15)); [lia|].
    rewrite orb_false_r, negb_true_iff, Z.eqb_neq in H11.
    match goal with |- context [if ?b then Some (None, _, Z_STREAM_ERROR) else _] => replace b with false end.
    2:{ symmetry. rewrite !orb_false_iff, !andb_false_iff. rewrite !Z.ltb_ge, !Z.gtb_ltb, !Z.ltb_ge.
        repeat split; try lia. }
    cbn [negb andb].
    assert (E: (if - wbits =? 8 then 9 else - wbits) = Z.max 9 (- wbits)) by (destruct (Z.eqb_spec (-wbits) 8); lia).
    rewrite E. reflexivity.
  - destruct (wbits >? 15) eqn:Hw.
    + rewrite Z.gtb_lt in Hw.
      rewrite orb_false_r, negb_true_iff, Z.eqb_neq in H11.
      match goal with |- context [if ?b then Some (None, _, Z_STREAM_ERROR) else _] => replace b with false end.
      2:{ symmetry. rewrite !orb_false_iff, !andb_false_iff. rewrite !Z.ltb_ge, !Z.gtb_ltb, !Z.ltb_ge.
          repeat split; try lia. }
      cbn [negb andb].
      assert (E: (if wbits - 16 =? 8 then 9 else wbits - 16) = Z.max 9 (wbits - 16))
        by (destruct (Z.eqb_spec (wbits - 16) 8); lia).
      rewrite E. reflexivity.
    + rewrite Z.gtb_ltb, Z.ltb_ge in Hw.
      match goal with |- context [if ?b then Some (None, _, Z_STREAM_ERROR) else _] => replace b with false end.
      2:{ symmetry. rewrite !orb_false_iff, !andb_false_iff. rewrite !Z.ltb_ge, !Z.gtb_ltb, !Z.ltb_ge.
          repeat split; try lia. }
      cbn [negb andb].
      assert (E: (if wbits =? 8 then 9 else wbits) = Z.max 9 wbits)
        by (destruct (Z.eqb_spec wbits 8); lia).
      rewrite E. reflexivity.
Qed.

(** ** deflateResetKeep on an abstract state *)
Definition rk_state (s : dstate) : dstate :=
  let s := set_d_tr s (set_data_type (d_tr s) Z_UNKNOWN) in
  let o := tr_out (d_tr s) in
  let s := set_d_tr s (set_out (d_tr s) (mkOut (o_buf o) 0 (o_bi_buf o) (o_bi_valid o) (o_bi_used o))) in
  let s := set_d_po s 0 in
  let s := set_d_status s (if d_wrap s =? 2 then GZIP_STATE else INIT_STATE) in
  set_d_last_flush s (-2).

Definition rk_strm (s : dstate) (z : strm) : strm :=
  set_z_adler (set_z_msg (set_z_total_out (set_z_total_in z 0) 0) None) (if d_wrap s =? 2 then 0 else 1).

Lemma rk_eq s z t :
  bad_state s = false -> 0 <= d_wrap s -> c_tr_init (d_trm (rk_state s)) = Some t ->
  c_deflateResetKeep s z = Some (set_d_trm (rk_state s) t, rk_strm s z, Z_OK).
Proof.
  intros Hb Hw Ht. unfold c_deflateResetKeep. rewrite Hb.
  cbn [d_wrap set_d_po set_d_tr].
  destruct (Z.ltb_spec (d_wrap s) 0); [lia|].
  cbn [bind]. unfold rk_state in Ht. cbn [d_wrap set_d_po set_d_tr set_d_status] in Ht |- *.
  rewrite Ht. reflexivity.
Qed.

(** ** _tr_init on zero trees *)
Definition LT1 : tree :=
  mkTree (upd_Znth END_BLOCK (repeat 0 (Z.to_nat HEAP_SIZE)) 1) (repeat 0 (Z.to_nat HEAP_SIZE)).

Definition ib_state (t : tstate) : tstate :=
  let t := set_out t (mkOut (o_buf (tr_out t)) (o_pending (tr_out t)) 0 0 0) in
  let t := set_ltree t (zero_tree HEAP_SIZE) in
  let t := set_dtree t (zero_tree (2 * D_CODES + 1)) in
  let t := set_bltree t (zero_tree (2 * BL_CODES + 1)) in
  let t := set_ltree t LT1 in
  let t := set_wk t (w_set_static_len (w_set_opt_len (tr_wk t) 0) 0) in
  set_matches (set_sym_next t 0) 0.

Lemma zfc_l : c_zero_fc (Z.to_nat L_CODES) (zero_tree HEAP_SIZE) 0 L_CODES = Some (zero_tree HEAP_SIZE).
Proof. vm_compute. reflexivity. Qed.
Lemma zfc_d : c_zero_fc (Z.to_nat D_CODES) (zero_tree (2 * D_CODES + 1)) 0 D_CODES = Some (zero_tree (2 * D_CODES + 1)).
Proof. vm_compute. reflexivity. Qed.
Lemma zfc_bl : c_zero_fc (Z.to_nat BL_CODES) (zero_tree (2 * BL_CODES + 1)) 0 BL_CODES = Some (zero_tree (2 * BL_CODES + 1)).
Proof. vm_compute. reflexivity. Qed.
Lemma sfc_lt1 : c_set_fc (zero_tree HEAP_SIZE) END_BLOCK 1 = Some LT1.
Proof. vm_compute. reflexivity. Qed.

Lemma tr_init_eq t m :
  tr_ltree t = zero_tree HEAP_SIZE -> tr_dtree t = zero_tree (2 * D_CODES + 1) ->
  tr_bltree t = zero_tree (2 * BL_CODES + 1) ->
  c_tr_init (t, m) = Some (ib_state t, m).
Proof.
  intros H1 H2 H3. unfold c_tr_init, c_init_block.
  cbn [set_out tr_ltree tr_dtree tr_bltree set_ltree set_dtree set_bltree].
  rewrite H1, zfc_l. cbn [bind]. rewrite H2, zfc_d. cbn [bind]. rewrite H3, zfc_bl. cbn [bind].
  rewrite sfc_lt1. reflexivity.
Qed.

(** ** lm_init *)
Definition cfg_good (l : Z) : Z := let '(g, _, _, _, _) := Znth l config_table in g.
Definition cfg_lazy (l : Z) : Z := let '(_, g, _, _, _) := Znth l config_table in g.
Definition cfg_nice (l : Z) : Z := let '(_, _, g, _, _) := Znth l config_table in g.
Definition cfg_chain (l : Z) : Z := let '(_, _, _, g, _) := Znth l config_table in g.

Definition lm_state (s : dstate) : dstate :=
  let s := set_d_window_size s (u64 (2 * d_w_size s)) in
  let s := set_d_slid (set_d_head s (repeat 0 (Z.to_nat (d_hash_size s)))) 0 in
  let l := d_level s in
  let s := set_d_max_lazy_match s (cfg_lazy l) in
  let s := set_d_good_match s (cfg_good l) in
  let s := set_d_nice_match s (cfg_nice l) in
  let s := set_d_max_chain_length s (cfg_chain l) in
  let s := set_d_strstart s 0 in
  let s := set_d_block_start s 0 in
  let s := set_d_lookahead s 0 in
  let s := set_d_insert s 0 in
  let s := set_d_match_length s (MIN_MATCH - 1) in
  let s := set_d_prev_length s (MIN_MATCH - 1) in
  let s := set_d_match_available s 0 in
  set_d_ins_h s 0.

Lemma lm_eq s :
  Zlength (d_head s) = d_hash_size s -> 1 <= d_hash_size s <= 65536 -> 0 <= d_level s <= 9 ->
  c_lm_init s = Some (lm_state s).
Proof.
  intros Hh Hs Hl. unfold c_lm_init, c_clear_hash, lm_state.
  cbn [d_head d_hash_size set_d_window_size d_w_size].
  unfold wr, in_range. rewrite Hh.
  replace (u32 (d_hash_size s - 1)) with (d_hash_size s - 1)
    by (unfold u32; rewrite Z.mod_small; lia).
  replace ((0 <=? d_hash_size s - 1) && (d_hash_size s - 1 <? d_hash_size s)) with true
    by (symmetry; rewrite andb_true_iff, Z.leb_le, Z.ltb_lt; lia).
  cbn [bind].
  rewrite upd_Znth_Zlength by lia. rewrite Hh, Z.eqb_refl.
  replace (1 <=? d_hash_size s) with true by (symmetry; apply Z.leb_le; lia).
  cbn [andb guard bind].
  change (d_level (set_d_slid (set_d_head (set_d_window_size s (u64 (2 * d_w_size s)))
                                          (repeat 0 (Z.to_nat (d_hash_size s)))) 0)) with (d_level s).
  replace ((0 <=? d_level s) && (d_level s <? 10)) with true
    by (symmetry; rewrite andb_true_iff, Z.leb_le, Z.ltb_lt; lia).
  cbn [guard bind].
  unfold cfg_lazy, cfg_good, cfg_nice, cfg_chain.
  destruct (Znth (d_level s) config_table) as [[[[a b] c] d] e]. reflexivity.
Qed.

(** ** deflateReset *)
Definition fin_state (s : dstate) : dstate :=
  let s := rk_state s in lm_state (set_d_trm s (ib_state (d_tr s), d_pbm s)).

Lemma reset_eq s z :
  bad_state s = false -> 0 <= d_wrap s ->
  tr_ltree (d_tr s) = zero_tree HEAP_SIZE -> tr_dtree (d_tr s) = zero_tree (2 * D_CODES + 1) ->
  tr_bltree (d_tr s) = zero_tree (2 * BL_CODES + 1) ->
  Zlength (d_head s) = d_hash_size s -> 1 <= d_hash_size s <= 65536 -> 0 <= d_level s <= 9 ->
  c_deflateReset s z = Some (fin_state s, rk_strm s z, Z_OK).
Proof.
  intros Hb Hw H1 H2 H3 Hh Hs Hl.
  unfold c_deflateReset.
  rewrite (rk_eq s z (ib_state (d_tr (rk_state s)), d_pbm (rk_state s))); auto.
  2:{ apply tr_init_eq; assumption. }
  cbn [bind]. rewrite Z.eqb_refl.
  rewrite lm_eq. reflexivity.
  all: unfold rk_state; cbn [d_head d_hash_size d_level set_d_trm set_d_tr set_d_pbm set_d_po set_d_status
                             set_d_last_flush fst snd ib_state set_matches set_sym_next set_wk set_ltree set_dtree
                             set_bltree set_out set_data_type tr_level d_tr]; auto.
Qed.

Lemma init_eq level method wbits mem strategy z :
  params_ok level method wbits mem strategy = true ->
  c_deflateInit2_ true true false level method wbits mem strategy true true true true true z =
  Some (Some (fin_state (s_pre (if level =? -1 then 6 else level) (Z.max 9 (wb_of wbits)) (wrap_of wbits) mem strategy)),
        rk_strm (s_pre (if level =? -1 then 6 else level) (Z.max 9 (wb_of wbits)) (wrap_of wbits) mem strategy)
                (set_z_msg z None), Z_OK).
Proof.
  intros H. rewrite (init_unfold _ _ _ _ _ _ H).
  pose proof H as H'.
  unfold params_ok in H'.
  rewrite !andb_true_iff in H'. destruct H' as [[[[[[[[[[H1 H2] H3] H4] H5] H6] H7] H8] H9] H10] H11].
  rewrite Z.leb_le in H2, H3, H7, H8.
  rewrite reset_eq; [reflexivity|..]; try reflexivity.
  - unfold wrap_of. cbn. destruct (wbits <? 0); [lia|]. destruct (wbits >? 15); lia.
  - change (d_head _) with (repeat 0 (Z.to_nat (Z.shiftl 1 (mem + 7)))).
    change (d_hash_size _) with (Z.shiftl 1 (mem + 7)).
    rewrite Zlength_repeat; [lia|]. rewrite Z.shiftl_1_l. apply Z.pow_nonneg; lia.
  - change (d_hash_size _) with (Z.shiftl 1 (mem + 7)).
    rewrite Z.shiftl_1_l. split; [assert (0 < 2 ^ (mem + 7)) by (apply Z.pow_pos_nonneg; lia); lia|].
    change 65536 with (2 ^ 16). apply Z.pow_le_mono_r; lia.
  - change (d_level _) with (if level =? -1 then 6 else level). lia.
Qed.

(** ** The state deflateInit2_ makes, with the powers of two abstracted *)
Definition sG (lv wb wrap hb strategy w hs L : Z) : dstate :=
  mkDS (if wrap =? 2 then GZIP_STATE else INIT_STATE) 0 wrap None 0 (u8 8) (-2)
       w wb (u32 (w - 1))
       (mkMB (repeat 0 (Z.to_nat (2 * w))) (repeat false (Z.to_nat (2 * w)))) (u64 (2 * w))
       (repeat 0 (Z.to_nat w)) (repeat 0 (Z.to_nat hs)) 0 hs hb (u32 (hs - 1)) ((hb + MIN_MATCH - 1) / MIN_MATCH)
       0 (MIN_MATCH - 1) 0 0 0 0 0 (MIN_MATCH - 1) (cfg_chain lv) (cfg_lazy lv) (cfg_good lv) (cfg_nice lv)
       0 0 0 (u64 (L * 4))
       (mkTS LT1 (zero_tree (2 * D_CODES + 1)) (zero_tree (2 * BL_CODES + 1)) 0 0 0
             (w_set_static_len (w_set_opt_len zero_work 0) 0)
             (mkOut (repeat 0 (Z.to_nat (L * LIT_BUFS))) 0 0 0 0) 0 (u32 ((L - 1) * 3)) 0 L lv strategy Z_UNKNOWN)
       (repeat false (Z.to_nat (L * LIT_BUFS))).

Lemma fin_eq lv wb wrap mem strategy :
  fin_state (s_pre lv wb wrap mem strategy) =
  sG lv wb wrap (mem + 7) strategy (Z.shiftl 1 wb) (Z.shiftl 1 (mem + 7)) (Z.shiftl 1 (mem + 6)).
Proof. reflexivity. Qed.

Lemma LT1_facts :
  Zlength (fc LT1) = HEAP_SIZE /\ Zlength (dl LT1) = HEAP_SIZE /\
  (forall n, 0 <= n < HEAP_SIZE -> 0 <= Znth n (fc LT1) < 65536) /\
  forall c, 0 <= c < L_CODES -> Znth c (fc LT1) = lfreq [] c.
Proof.
  unfold LT1; cbn [fc dl].
  assert (HL : Zlength (repeat 0 (Z.to_nat HEAP_SIZE)) = HEAP_SIZE) by (rewrite Zlength_repeat; try reflexivity; unfold HEAP_SIZE; lia).
  split; [rewrite upd_Znth_Zlength; [exact HL | rewrite HL; unfold END_BLOCK, HEAP_SIZE; lia]|].
  split; [exact HL|].
  assert (HZ : forall n, 0 <= n < HEAP_SIZE ->
            Znth n (upd_Znth END_BLOCK (repeat 0 (Z.to_nat HEAP_SIZE)) 1) = if n =? END_BLOCK then 1 else 0).
  { intros n Hn. destruct (Z.eqb_spec n END_BLOCK).
    - subst. rewrite upd_Znth_same; [reflexivity|]. rewrite HL. unfold END_BLOCK, HEAP_SIZE; lia.
    - rewrite upd_Znth_diff; [|rewrite HL; unfold END_BLOCK, HEAP_SIZE in *; lia..|auto].
      apply Znth_repeat_inrange. lia. }
  split.
  - intros n Hn. rewrite HZ by lia. destruct (n =? END_BLOCK); lia.
  - intros c Hc. rewrite HZ by (unfold L_CODES, HEAP_SIZE in *; lia). unfold lfreq. cbn [filter].
    rewrite Zlength_nil. destruct (c =? END_BLOCK); reflexivity.
Qed.

Lemma zero_tree_facts n :
  0 <= n ->
  Zlength (fc (zero_tree n)) = n /\ Zlength (dl (zero_tree n)) = n /\
  forall i, Znth i (fc (zero_tree n)) = 0.
Proof.
  intros Hn. unfold zero_tree; cbn [fc dl].
  rewrite !Zlength_repeat by lia. split; [|split]; auto.
  intros i. apply (@Znth_repeat Z 0).
Qed.

Lemma pow2_bounds k : 0 <= k -> 0 < 2 ^ k.
Proof. intros; apply Z.pow_pos_nonneg; lia. Qed.

Section Facts.
Variables lv wb wrap hb strategy w hs L : Z.
Hypotheses (Hlv : 0 <= lv <= 9) (Hwb : 9 <= wb <= 15) (Hwrap : 0 <= wrap <= 2) (Hhb : 8 <= hb <= 16)
           (Hst : 0 <= strategy <= 4) (Hw : w = 2 ^ wb) (Hhs : hs = 2 ^ hb) (HL : L = 2 ^ (hb - 1)).

Let s := sG lv wb wrap hb strategy w hs L.

Lemma w_bounds : 512 <= w <= 32768.
Proof.
  subst w. split.
  - change 512 with (2 ^ 9). apply Z.pow_le_mono_r; lia.
  - change 32768 with (2 ^ 15). apply Z.pow_le_mono_r; lia.
Qed.
Lemma hs_bounds : 256 <= hs <= 65536.
Proof.
  subst hs. split.
  - change 256 with (2 ^ 8). apply Z.pow_le_mono_r; lia.
  - change 65536 with (2 ^ 16). apply Z.pow_le_mono_r; lia.
Qed.
Lemma L_bounds : 128 <= L <= 32768 /\ hs = 2 * L.
Proof.
  subst L hs. split; [split|].
  - change 128 with (2 ^ 7). apply Z.pow_le_mono_r; lia.
  - change 32768 with (2 ^ 15). apply Z.pow_le_mono_r; lia.
  - replace hb with (Z.succ (hb - 1)) at 1 by lia. rewrite Z.pow_succ_r by lia. lia.
Qed.

Lemma sG_prm : prm s.
Proof.
  pose proof w_bounds. pose proof hs_bounds. pose proof L_bounds.
  unfold prm, s, sG, d_L, d_level, d_strategy; cbn - [Z.pow Z.div Z.modulo].
  unfold u32, u64, u8, MIN_MATCH, LIT_BUFS.
  rewrite !Zlength_repeat by lia.
  repeat split; try lia.
  - rewrite Z.mod_small; lia.
  - rewrite Z.mod_small; lia.
  - f_equal; lia.
  - rewrite Z.mod_small; lia.
  - rewrite Z.mod_small; lia.
Qed.

Lemma sG_tree_ok : tree_ok (d_tr s) (d_pbm s) [].
Proof.
  pose proof L_bounds.
  unfold tree_ok, s, sG; cbn [d_tr d_pbm tr_out o_buf tr_sym_next tr_lit_bufsize tr_ltree tr_dtree tr_bltree tr_wk].
  unfold LIT_BUFS. rewrite !Zlength_repeat by lia. rewrite Zlength_nil.
  replace (L + 3 * 0) with L by lia. rewrite !sublist_nil.
  destruct LT1_facts as (A1 & A2 & A3 & A4).
  destruct (zero_tree_facts (2 * D_CODES + 1)) as (B1 & B2 & B3); [unfold D_CODES; lia|].
  destruct (zero_tree_facts (2 * BL_CODES + 1)) as (C1 & C2 & C3); [unfold BL_CODES; lia|].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [intros x []|]. split; [reflexivity|].
  split; [reflexivity|].
  split; [split; [exact A1|split; [exact A2|split; [exact A3|exact A4]]]|].
  split; [split; [exact B1|split; [exact B2|split]]|].
  { intros n _. rewrite B3. lia. }
  { intros c _. rewrite B3. reflexivity. }
  split; [split; [exact C1|split; [exact C2|split]]|].
  { intros n _. rewrite C3. lia. }
  { intros c _. rewrite C3. reflexivity. }
  vm_compute. repeat split; reflexivity.
Qed.

Lemma sG_W : W s.
Proof.
  pose proof w_bounds. pose proof hs_bounds. pose proof L_bounds.
  unfold W.
  split; [exact sG_prm|].
  split.
  { unfold wstruct, s, sG; cbn [d_window d_w_size d_window_size d_prev d_head d_hash_size mb_val mb_def].
    rewrite !Zlength_repeat by lia. unfold u64. rewrite Z.mod_small by lia.
    split; [lia|]. split; [|split; [reflexivity|split; reflexivity]].
    unfold mb_ok; cbn [mb_val mb_def]. rewrite !Zlength_repeat by lia. split; [reflexivity|].
    intros i Hi. rewrite Znth_repeat_inrange by (try rewrite Zlength_repeat in Hi by lia; lia). discriminate. }
  split.
  { unfold wpos, s, sG; cbn [d_lookahead d_strstart d_window_size d_block_start d_insert d_w_size d_high_water].
    unfold u64. rewrite Z.mod_small by lia. lia. }
  split.
  { unfold wwin, s, sG; cbn [d_lookahead d_strstart d_high_water]. intros i Hi. lia. }
  split.
  { assert (Hc : chain_ok s).
    { exists (fun v => v = 0). unfold chain_with. split; [|split].
      - intros v Hv; left; exact Hv.
      - intros h Hh. unfold s, sG in *; cbn [d_head d_hash_size] in *. apply Znth_repeat_inrange. lia.
      - intros q Hq Hq'. lia. }
    unfold whash. unfold d_matches at 1 2. unfold s at 1 2 3, sG at 1 2 3. cbn [d_tr tr_matches].
    destruct (d_level _ =? 0); [left|]; split; auto. }
  split.
  { unfold wmatch, s, sG; cbn [d_match_length d_prev_length d_match_available]. unfold MIN_MATCH, MAX_MATCH.
    split; [lia|]. split; [lia|]. split; [left; reflexivity|]. split; [intros _; lia|].
    intros Hc; discriminate. }
  split.
  { unfold s, sG; cbn [d_lookahead d_block_start]. intros _; lia. }
  exists [].
  unfold wtrees. split; [exact sG_tree_ok|].
  split; [unfold d_L, s, sG; cbn [d_tr tr_lit_bufsize]; rewrite Zlength_nil; lia|].
  split; [constructor|]. split; [reflexivity|].
  intros _. unfold s, sG; cbn [d_strstart d_block_start d_match_available]. reflexivity.
Qed.

Lemma sG_outok : outok s.
Proof.
  pose proof L_bounds.
  unfold outok, d_pb, s, sG, d_pending, d_pending_buf_size;
    cbn [d_tr d_pbm tr_out o_buf o_pending d_po o_bi_valid o_bi_buf].
  unfold LIT_BUFS, u64. rewrite Z.mod_small by lia.
  split.
  { unfold mb_ok; cbn [mb_val mb_def]. rewrite !Zlength_repeat by lia. split; [reflexivity|].
    intros i Hi. rewrite Znth_repeat_inrange by (try rewrite Zlength_repeat in Hi by lia; lia). discriminate. }
  split.
  { unfold bits_ok; cbn [o_bi_valid o_bi_buf o_pending]. rewrite Z.pow_0_r. lia. }
  split; [lia|]. split; [lia|]. split; [|intros _; reflexivity].
  unfold mb_defined; cbn [mb_val]. rewrite Zlength_repeat by lia. split; [lia|]. split; [lia|]. intros; lia.
Qed.

End Facts.

Lemma params_bounds level method wbits mem strategy :
  params_ok level method wbits mem strategy = true ->
  0 <= (if level =? -1 then 6 else level) <= 9 /\ 9 <= Z.max 9 (wb_of wbits) <= 15 /\
  0 <= wrap_of wbits <= 2 /\ 1 <= mem <= 9 /\ 0 <= strategy <= 4.
Proof.
  intros H. unfold params_ok in H.
  rewrite !andb_true_iff in H. destruct H as [[[[[[[[[[H1 H2] H3] H4] H5] H6] H7] H8] H9] H10] H11].
  rewrite Z.leb_le in H2, H3, H5, H6, H7, H8, H9, H10.
  split; [lia|]. split; [lia|]. split; [unfold wrap_of; destruct (wbits <? 0); [lia|]; destruct (wbits >? 15); lia|].
  lia.
Qed.
