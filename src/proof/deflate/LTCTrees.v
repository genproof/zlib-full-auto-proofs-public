(** * Core part of the deflate law theory: the _tr_tally macros and _tr_flush_block
    Statement: LTCSpecs.v; invariant: LTCW.v; shared lemmas: LTCLib.v. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTCLib.
Require Import Zlib.proof.deflate.LTCTrKit Zlib.proof.deflate.LTCTrBuild Zlib.proof.deflate.LTCTrPrep
  Zlib.proof.deflate.LTCTrComp Zlib.proof.deflate.LTCTrSend Zlib.proof.deflate.LTCTrStored
  Zlib.proof.deflate.LTCTrBytes Zlib.proof.deflate.LTCTrTally.
Require Zlib.proof.huffman.FlushStatic Zlib.proof.huffman.DynSum Zlib.proof.huffman.FlushDyn
  Zlib.proof.huffman.TreeDD Zlib.proof.huffman.RepairBound Zlib.proof.huffman.BlockStored.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** Small checked-run lemmas *)

Lemma bind_some {A B} (a : A) (f : A -> option B) : bind (Some a) f = f a.
Proof. reflexivity. Qed.

Lemma c_set_fc_some t i v : 0 <= i < Zlength (fc t) -> c_set_fc t i v = Some (set_fc t i v).
Proof.
  intros H. unfold c_set_fc, wr, in_range.
  replace ((0 <=? i) && (i <? Zlength (fc t))) with true by (symmetry; apply andb_true_iff; lia).
  reflexivity.
Qed.

Lemma zero_fc_facts : forall fuel t n hi,
  Zlength (fc (zero_fc fuel t n hi)) = Zlength (fc t) /\ dl (zero_fc fuel t n hi) = dl t /\
  forall i, Znth i (fc (zero_fc fuel t n hi)) =
            if (n <=? i) && (i <? Z.min hi (n + Z.of_nat fuel)) && (0 <=? i) && (i <? Zlength (fc t))
            then 0 else Znth i (fc t).
Proof.
  induction fuel as [|f IH]; intros t n hi; cbn [zero_fc].
  - split; [reflexivity|]. split; [reflexivity|]. intros i.
    destruct (Z.leb_spec n i), (Z.ltb_spec i (Z.min hi (n + Z.of_nat 0))); cbn [andb]; auto; lia.
  - destruct (Z.ltb_spec n hi) as [Hn|Hn].
    + destruct (IH (set_fc t n 0) (n + 1) hi) as [L1 [D1 F1]].
      cbn [fc dl set_fc] in L1, D1. rewrite Zlength_upd_Znth_any in L1.
      split; [exact L1|]. split; [exact D1|]. intros i. rewrite F1. cbn [fc set_fc].
      rewrite Zlength_upd_Znth_any.
      destruct (Z.eq_dec i n) as [->|Hi].
      * destruct (Z_le_gt_dec 0 n); [destruct (Z_lt_ge_dec n (Zlength (fc t)))|].
        -- rewrite upd_Znth_same by lia.
           replace (n + 1 <=? n) with false by (symmetry; apply Z.leb_gt; lia). cbn [andb].
           replace ((n <=? n) && (n <? Z.min hi (n + Z.of_nat (S f))) && (0 <=? n) && (n <? Zlength (fc t)))
             with true by (symmetry; repeat rewrite andb_true_iff; rewrite ?Z.leb_le, ?Z.ltb_lt; lia). reflexivity.
        -- rewrite upd_Znth_out_of_range by lia.
           replace ((n <=? n) && (n <? Z.min hi (n + Z.of_nat (S f))) && (0 <=? n) && (n <? Zlength (fc t)))
             with false by (symmetry; repeat rewrite andb_false_iff; rewrite ?Z.leb_gt, ?Z.ltb_ge; lia).
           replace (n + 1 <=? n) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
        -- rewrite upd_Znth_out_of_range by lia.
           replace ((n <=? n) && (n <? Z.min hi (n + Z.of_nat (S f))) && (0 <=? n) && (n <? Zlength (fc t)))
             with false by (symmetry; repeat rewrite andb_false_iff; rewrite ?Z.leb_gt, ?Z.ltb_ge; lia).
           replace (n + 1 <=? n) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
      * rewrite Znth_upd_Znth_other by auto.
        destruct (Z.leb_spec (n + 1) i), (Z.ltb_spec i (Z.min hi (n + 1 + Z.of_nat f))),
                 (Z.leb_spec n i), (Z.ltb_spec i (Z.min hi (n + Z.of_nat (S f)))),
                 (Z.leb_spec 0 i), (Z.ltb_spec i (Zlength (fc t))); cbn [andb]; auto; lia.
    + split; [reflexivity|]. split; [reflexivity|]. intros i.
      destruct (Z.leb_spec n i), (Z.ltb_spec i (Z.min hi (n + Z.of_nat (S f)))); cbn [andb]; auto; lia.
Qed.

Lemma c_zero_fc_some : forall fuel t n hi,
  0 <= n -> hi <= Zlength (fc t) -> hi - n <= Z.of_nat fuel ->
  c_zero_fc fuel t n hi = Some (zero_fc fuel t n hi).
Proof.
  induction fuel as [|f IH]; intros t n hi H0 H1 H2; cbn [c_zero_fc zero_fc].
  - replace (n <? hi) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
  - destruct (Z.ltb_spec n hi) as [Hn|Hn]; [|reflexivity].
    rewrite c_set_fc_some by lia. rewrite bind_some.
    apply IH; cbn [fc set_fc]; rewrite ?Zlength_upd_Znth_any; lia.
Qed.

Lemma c_init_block_some s :
  L_CODES <= Zlength (fc (tr_ltree s)) -> D_CODES <= Zlength (fc (tr_dtree s)) ->
  BL_CODES <= Zlength (fc (tr_bltree s)) ->
  c_init_block s = Some (init_block s).
Proof.
  intros H1 H2 H3. unfold c_init_block, init_block.
  rewrite c_zero_fc_some by (unfold L_CODES in *; lia). rewrite bind_some.
  rewrite c_zero_fc_some by (cbn [tr_dtree set_ltree]; unfold D_CODES in *; lia). rewrite bind_some.
  rewrite c_zero_fc_some by (cbn [tr_bltree set_dtree set_ltree]; unfold BL_CODES in *; lia). rewrite bind_some.
  destruct (zero_fc_facts (Z.to_nat L_CODES) (tr_ltree s) 0 L_CODES) as [L1 _].
  rewrite c_set_fc_some by (cbn [tr_ltree set_bltree set_dtree set_ltree]; rewrite L1;
                            unfold END_BLOCK, L_CODES in *; lia).
  reflexivity.
Qed.

Lemma c_put_byte_some o m c : 0 <= o_pending o < Zlength (o_buf o) ->
  c_put_byte (o, m) c = Some (put_byte o c, upd_Znth (o_pending o) m true).
Proof.
  intros H. unfold c_put_byte, wr, in_range.
  replace ((0 <=? o_pending o) && (o_pending o <? Zlength (o_buf o))) with true
    by (symmetry; apply andb_true_iff; lia).
  reflexivity.
Qed.

Lemma c_put_short_some o m w : 0 <= o_pending o -> o_pending o + 2 <= Zlength (o_buf o) ->
  exists m', c_put_short (o, m) w = Some (put_short o w, m').
Proof.
  intros H1 H2. unfold c_put_short. rewrite c_put_byte_some by lia. rewrite bind_some.
  rewrite c_put_byte_some by (unfold put_byte; cbn [o_pending o_buf]; rewrite Zlength_upd_Znth_any; lia).
  eexists. reflexivity.
Qed.

Lemma c_bi_windup_some o m :
  bits_ok o -> o_pending o + (o_bi_valid o + 7) / 8 <= Zlength (o_buf o) ->
  exists m', c_bi_windup (o, m) = Some (bi_windup o, m').
Proof.
  intros [Hv [Hb Hp]] H. unfold c_bi_windup, bi_windup.
  replace ((0 <=? o_bi_valid o) && (o_bi_valid o <=? 16)) with true by (symmetry; apply andb_true_iff; lia).
  cbv beta iota zeta delta [guard]. rewrite bind_some.
  destruct (Z.gtb_spec (o_bi_valid o) 8) as [E|E].
  - assert ((o_bi_valid o + 7) / 8 = 2) by (symmetry; apply Z.div_unique with (o_bi_valid o + 7 - 16); lia).
    destruct (c_put_short_some o m (o_bi_buf o)) as [m' Hm]; [lia|lia|].
    rewrite Hm, bind_some. eexists. reflexivity.
  - destruct (Z.gtb_spec (o_bi_valid o) 0) as [E0|E0].
    + assert ((o_bi_valid o + 7) / 8 = 1) by (symmetry; apply Z.div_unique with (o_bi_valid o + 7 - 8); lia).
      rewrite c_put_byte_some by lia. rewrite bind_some. eexists. reflexivity.
    + rewrite bind_some. eexists. reflexivity.
Qed.

(** send_bits without a flush of bi_buf. *)
Lemma c_send_bits_noflush o m v l :
  0 <= o_bi_valid o -> 0 <= l -> o_bi_valid o + l <= 16 ->
  c_send_bits (o, m) v l = Some (send_bits o v l, m).
Proof.
  intros H1 H2 H3. unfold c_send_bits, send_bits.
  replace ((0 <=? o_bi_valid o) && (o_bi_valid o <=? Buf_size)) with true
    by (symmetry; apply andb_true_iff; unfold Buf_size; lia).
  cbv beta iota zeta delta [guard]. rewrite bind_some.
  replace (o_bi_valid o >? Buf_size - l) with false by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; unfold Buf_size; lia).
  reflexivity.
Qed.


(** ** The state after init_block *)

Definition tr_sizes (s : tstate) : Prop :=
  Zlength (fc (tr_ltree s)) = HEAP_SIZE /\ Zlength (dl (tr_ltree s)) = HEAP_SIZE /\
  (forall n, 0 <= n < HEAP_SIZE -> 0 <= Znth n (fc (tr_ltree s)) < 65536) /\
  Zlength (fc (tr_dtree s)) = 2 * D_CODES + 1 /\ Zlength (dl (tr_dtree s)) = 2 * D_CODES + 1 /\
  (forall n, 0 <= n < 2 * D_CODES + 1 -> 0 <= Znth n (fc (tr_dtree s)) < 65536) /\
  Zlength (fc (tr_bltree s)) = 2 * BL_CODES + 1 /\ Zlength (dl (tr_bltree s)) = 2 * BL_CODES + 1 /\
  (forall n, 0 <= n < 2 * BL_CODES + 1 -> 0 <= Znth n (fc (tr_bltree s)) < 65536) /\
  Zlength (w_heap (tr_wk s)) = HEAP_SIZE /\ Zlength (w_depth (tr_wk s)) = HEAP_SIZE /\
  Zlength (w_bl_count (tr_wk s)) = MAX_BITS + 1.

Lemma zero_fc_all fuel t hi i :
  Z.of_nat fuel = hi -> hi <= Zlength (fc t) ->
  Znth i (fc (zero_fc fuel t 0 hi)) = if (0 <=? i) && (i <? hi) then 0 else Znth i (fc t).
Proof.
  intros E H. destruct (zero_fc_facts fuel t 0 hi) as [_ [_ F]]. rewrite F.
  destruct (Z.leb_spec 0 i), (Z.ltb_spec i hi), (Z.ltb_spec i (Z.min hi (0 + Z.of_nat fuel))),
           (Z.ltb_spec i (Zlength (fc t))); cbn [andb]; auto; lia.
Qed.

Lemma tree_ok_init s o m : tr_sizes s ->
  Zlength (o_buf o) = 4 * tr_lit_bufsize s -> Zlength m = 4 * tr_lit_bufsize s ->
  tree_ok (set_out (init_block s) o) m [].
Proof.
  intros (Hl1 & Hl2 & Hl3 & Hd1 & Hd2 & Hd3 & Hb1 & Hb2 & Hb3 & Hw1 & Hw2 & Hw3) Ho Hm.
  destruct (zero_fc_facts (Z.to_nat L_CODES) (tr_ltree s) 0 L_CODES) as [ZL1 [ZL2 _]].
  destruct (zero_fc_facts (Z.to_nat D_CODES) (tr_dtree s) 0 D_CODES) as [ZD1 [ZD2 _]].
  destruct (zero_fc_facts (Z.to_nat BL_CODES) (tr_bltree s) 0 BL_CODES) as [ZB1 [ZB2 _]].
  assert (ZL := fun i => zero_fc_all (Z.to_nat L_CODES) (tr_ltree s) L_CODES i eq_refl
                           ltac:(rewrite Hl1; unfold L_CODES, HEAP_SIZE; lia)).
  assert (ZD := fun i => zero_fc_all (Z.to_nat D_CODES) (tr_dtree s) D_CODES i eq_refl
                           ltac:(rewrite Hd1; unfold D_CODES; lia)).
  assert (ZB := fun i => zero_fc_all (Z.to_nat BL_CODES) (tr_bltree s) BL_CODES i eq_refl
                           ltac:(rewrite Hb1; unfold BL_CODES; lia)).
  unfold tree_ok, init_block.
  cbn [tr_lit_bufsize tr_out tr_sym_next tr_ltree tr_dtree tr_bltree tr_wk set_out set_matches set_sym_next
       set_wk set_ltree set_dtree set_bltree fc dl set_fc w_heap w_depth w_bl_count w_opt_len w_static_len
       w_set_opt_len w_set_static_len].
  rewrite Zlength_nil. rewrite Z.mul_0_r, Z.add_0_r, !sublist_nil.
  split; [exact Ho|]. split; [exact Hm|]. split; [reflexivity|].
  split; [intros x []|]. split; [reflexivity|]. split; [reflexivity|].
  split.
  { rewrite Zlength_upd_Znth_any. split; [congruence|]. split; [congruence|]. split.
    - intros k Hk. destruct (Z.eq_dec k END_BLOCK) as [->|Hne].
      + rewrite upd_Znth_same by (rewrite ZL1, Hl1; unfold END_BLOCK, HEAP_SIZE; lia). lia.
      + rewrite Znth_upd_Znth_other by auto. rewrite ZL.
        destruct ((0 <=? k) && (k <? L_CODES)); [lia|]. apply Hl3; lia.
    - intros c Hc. unfold lfreq. cbn [filter]. rewrite Zlength_nil.
      destruct (Z.eq_dec c END_BLOCK) as [->|Hne].
      + rewrite upd_Znth_same by (rewrite ZL1, Hl1; unfold END_BLOCK, HEAP_SIZE; lia). reflexivity.
      + rewrite Znth_upd_Znth_other by auto. rewrite ZL.
        replace ((0 <=? c) && (c <? L_CODES)) with true by (symmetry; apply andb_true_iff; rewrite Z.leb_le, Z.ltb_lt; lia).
        replace (c =? END_BLOCK) with false by (symmetry; apply Z.eqb_neq; auto). reflexivity. }
  split.
  { split; [congruence|]. split; [congruence|]. split.
    - intros k Hk. rewrite ZD. destruct ((0 <=? k) && (k <? D_CODES)); [lia|]. apply Hd3; lia.
    - intros c Hc. unfold dfreq. cbn [filter]. rewrite Zlength_nil. rewrite ZD.
      replace ((0 <=? c) && (c <? D_CODES)) with true by (symmetry; apply andb_true_iff; rewrite Z.leb_le, Z.ltb_lt; lia).
      reflexivity. }
  split.
  { split; [congruence|]. split; [congruence|]. split.
    - intros k Hk. rewrite ZB. destruct ((0 <=? k) && (k <? BL_CODES)); [lia|]. apply Hb3; lia.
    - intros c Hc. rewrite ZB.
      replace ((0 <=? c) && (c <? BL_CODES)) with true by (symmetry; apply andb_true_iff; rewrite Z.leb_le, Z.ltb_lt; lia).
      reflexivity. }
  repeat split; assumption.
Qed.

Lemma init_block_set_out s o : init_block (set_out s o) = set_out (init_block s) o.
Proof. reflexivity. Qed.
Lemma set_out_set_out s o o' : set_out (set_out s o) o' = set_out s o'.
Proof. reflexivity. Qed.
Lemma tr_out_set_out s o : tr_out (set_out s o) = o.
Proof. reflexivity. Qed.
Lemma tr_cfg_set_out_init s o : tr_cfg (set_out (init_block s) o) = tr_cfg s.
Proof. reflexivity. Qed.
Lemma tr_matches_set_out_init s o : tr_matches (set_out (init_block s) o) = 0.
Proof. reflexivity. Qed.


(** ** compress_block at the end of a Huffman block *)
Lemma comp_tail L syms o m lcodes llens dcodes dlens :
  (forall x, In x syms -> valid_sym (fst x) (snd x)) ->
  overlay_ok L syms (o, lcodes, llens, dcodes, dlens) ->
  Zlength syms <= L - 1 -> Zlength m = 4 * L ->
  (forall i, 0 <= i < 3 * Zlength syms -> Znth (L + i) m = true) ->
  L_CODES <= Zlength lcodes -> L_CODES <= Zlength llens ->
  D_CODES <= Zlength dcodes -> D_CODES <= Zlength dlens ->
  exists m',
    c_compress_block (o, m) L (3 * Zlength syms) lcodes llens dcodes dlens =
      Some (compress_block o L (3 * Zlength syms) lcodes llens dcodes dlens, m') /\
    let o' := compress_block o L (3 * Zlength syms) lcodes llens dcodes dlens in
    bits_ok o' /\ bitpos o' <= 8 * (L + 3 * Zlength syms) + 15 /\ Zlength (o_buf o') = 4 * L.
Proof.
  intros Hv Hov Hn Hm Hmask H1 H2 H3 H4.
  destruct (comp_some L syms o m lcodes llens dcodes dlens Hv Hov Hn Hm Hmask H1 H2 H3 H4) as [m' Hc].
  exists m'. split; [exact Hc|]. cbv zeta.
  destruct (overlay_compress L syms o lcodes llens dcodes dlens Hv Hov) as [E _]. rewrite E.
  destruct Hov as [Hok [Hlen [Hsy [Hcodes [Hend Hbits]]]]].
  destruct (compress_sep_spec syms o lcodes llens dcodes dlens Hok
              ltac:(intros x Hx; split; [apply Hv, Hx|apply Hcodes, Hx])) as [[W1 [Ok1 _]] [B1 _]].
  set (o1 := compress_sep o lcodes llens dcodes dlens syms) in *.
  assert (Hb := Hbits (length syms) (le_n _)). rewrite firstn_all in Hb. fold o1 in Hb.
  rewrite <- Zlength_correct in Hb.
  destruct (send_code_spec o1 END_BLOCK lcodes llens Ok1 Hend) as [B2 [_ [Ok2 [_ W2]]]].
  destruct Hend as [Hl _].
  split; [exact Ok2|]. split; [lia|].
  destruct W2 as [_ [W2 _]]. destruct W1 as [_ [W1 _]]. congruence.
Qed.

(** find_max_blindex stays in [2, i]. *)
Lemma fmb_range : forall fuel bl i, 2 <= i -> 2 <= find_max_blindex fuel bl i <= i.
Proof.
  induction fuel as [|f IH]; intros bl i Hi; cbn [find_max_blindex]; [lia|].
  destruct (i >=? 3) eqn:E; [|lia].
  apply Z.geb_le in E.
  destruct (negb _); [lia|]. specialize (IH bl (i - 1) ltac:(lia)). lia.
Qed.

(** The input length of a block of valid symbols is at least its number of symbols. *)
Lemma blk_len_ge syms : (forall x, In x syms -> valid_sym (fst x) (snd x)) -> Zlength syms <= blk_len syms.
Proof.
  induction syms as [|[d c] r IH]; intros Hv.
  - unfold blk_len. simpl. rewrite Zlength_nil. lia.
  - unfold blk_len in *. cbn [map HuffAbs.sumZ]. rewrite Zlength_cons.
    assert (IH' := IH ltac:(intros; apply Hv; right; auto)).
    destruct (Hv (d, c) (or_introl eq_refl)) as [Hc Hd]. cbn [fst snd] in Hc, Hd.
    assert (1 <= sym_len (d, c)) by (unfold sym_len; cbn [fst snd]; destruct (d =? 0); lia). lia.
Qed.

(** The static size of a block: at most 31 bits per symbol and the 7-bit END_BLOCK. *)
Lemma stat_data_le syms : (forall x, In x syms -> valid_sym (fst x) (snd x)) ->
  cost_sum static_ltree_len static_dtree_len syms + Znth END_BLOCK static_ltree_len <= 31 * Zlength syms + 7.
Proof.
  intros Hv.
  assert (H := FlushStatic.cost_sum_le static_ltree_len static_dtree_len syms 31
                 ltac:(intros x Hx; apply (FlushStatic.static_sym (fst x) (snd x) (Hv x Hx)))).
  rewrite Zlength_correct. replace (Znth END_BLOCK static_ltree_len) with 7 by reflexivity. lia.
Qed.


(** ** The stored block's output *)
Lemma stored_out o b sl last : bits_ok o -> 0 <= last <= 1 -> 0 <= sl <= Zlength b ->
  o_pending o + (o_bi_valid o + 3 + 7) / 8 + 4 + sl <= Zlength (o_buf o) ->
  let o' := tr_stored_block o b sl last in
  bits_ok o' /\ o_bi_valid o' = 0 /\ o_pending o' = o_pending o + (o_bi_valid o + 3 + 7) / 8 + 4 + sl /\
  Zlength (o_buf o') = Zlength (o_buf o).
Proof.
  intros Hok Hl Hs Hfit o'.
  destruct (BlockStored.stored_block_bitpos o b sl last Hok Hl ltac:(lia)) as [B V].
  fold o' in B, V.
  assert (Hval3 : 0 <= Z.shiftl STORED_BLOCK 1 + last < 2 ^ 3) by (unfold STORED_BLOCK; simpl; lia).
  destruct (send_bits_spec o (Z.shiftl STORED_BLOCK 1 + last) 3 Hok ltac:(lia) Hval3) as [S1 [_ [S3 [_ [_ [SL _]]]]]].
  set (o1 := send_bits o (Z.shiftl STORED_BLOCK 1 + last) 3) in *.
  destruct (bi_windup_spec o1 S3) as [P2 [V2 [BB2 [_ [_ [L2 _]]]]]].
  set (o2 := bi_windup o1) in *.
  destruct (put_short_spec o2 (u16 sl)) as [Q1 [QB [_ [_ [QL _]]]]].
  set (o3 := put_short o2 (u16 sl)) in *.
  destruct (put_short_spec o3 (u16 (Z.lnot sl))) as [R1 [RB [_ [_ [RL _]]]]].
  set (o4 := put_short o3 (u16 (Z.lnot sl))) in *.
  assert (Ho' : o' = mkOut (if negb (sl =? 0) then copy_bytes (o_buf o4) (o_pending o4) (sublist 0 sl b) else o_buf o4)
                           (o_pending o4 + sl) (o_bi_buf o4) (o_bi_valid o4) (o_bi_used o4)) by reflexivity.
  destruct Hok as [Hv [Hb Hp]].
  assert (Hpend : o_pending o' = o_pending o + (o_bi_valid o + 3 + 7) / 8 + 4 + sl).
  { unfold bitpos in B, S1. rewrite V in B.
    replace (8 * o_pending o + o_bi_valid o + 3 + 7) with ((o_bi_valid o + 3 + 7) + o_pending o * 8) in B by lia.
    rewrite Z.div_add in B by lia. lia. }
  split; [|split; [exact V|split; [exact Hpend|]]].
  - unfold bits_ok. rewrite V. rewrite Ho'. cbn [o_bi_buf o_pending]. rewrite RB, QB, BB2.
    split; [lia|]. split; [simpl; lia|]. rewrite R1, Q1. rewrite Ho' in Hpend. cbn [o_pending] in Hpend. rewrite R1, Q1 in Hpend.
    assert (0 <= (o_bi_valid o + 3 + 7) / 8) by (apply Z.div_pos; lia). lia.
  - rewrite Ho'. cbn [o_buf]. assert (E4 : Zlength (o_buf o4) = Zlength (o_buf o)) by congruence.
    destruct (negb (sl =? 0)); [|exact E4].
    unfold copy_bytes. rewrite Zlength_sublist by lia.
    assert (Hp4 : o_pending o4 = o_pending o + (o_bi_valid o + 3 + 7) / 8 + 4).
    { rewrite Ho' in Hpend. cbn [o_pending] in Hpend. lia. }
    assert (0 <= (o_bi_valid o + 3 + 7) / 8) by (apply Z.div_pos; lia).
    rewrite !Zlength_app, !Zlength_sublist; rewrite ?Zlength_sublist; try lia.
Qed.


(** ** The three kinds of block *)

(** The output at the end of the block, before the final bi_windup. *)
Definition out_fin (L : Z) (o : outbuf) (m : list bool) : Prop :=
  bits_ok o /\ o_pending o + (o_bi_valid o + 7) / 8 <= 4 * L /\ Zlength (o_buf o) = 4 * L /\ Zlength m = 4 * L.

Lemma mask_syms t m syms : tree_ok t m syms ->
  forall i, 0 <= i < 3 * Zlength syms -> Znth (tr_lit_bufsize t + i) m = true.
Proof.
  intros (H1 & H2 & H3 & H4 & H5 & H6 & _) i Hi.
  assert (E := f_equal (Znth i) H6).
  rewrite Znth_sublist in E by (pose proof (Zlength_nonneg syms); pose proof (Zlength_nonneg m); lia).
  rewrite Znth_repeat' in E by lia.
  replace (i + tr_lit_bufsize t) with (tr_lit_bufsize t + i) in E by lia. exact E.
Qed.

Lemma mask_after_true m m' lo hi i : mask_after m m' lo hi -> 0 <= i < Zlength m -> Znth i m = true -> Znth i m' = true.
Proof.
  intros [_ [_ H]] Hi E. rewrite H by lia. destruct ((lo <=? i) && (i <? hi)); auto.
Qed.

(** The end of a Huffman block: from the bit position bound to [out_fin]. *)
Lemma out_fin_of L n o m : bits_ok o -> bitpos o <= 8 * (L + 3 * n) + 15 -> n <= L - 1 ->
  Zlength (o_buf o) = 4 * L -> Zlength m = 4 * L -> out_fin L o m.
Proof.
  intros [Hv [Hb Hp]] Hbp Hn Hl Hm. unfold bitpos in Hbp.
  split; [split; [lia|split; [lia|lia]]|]. split; [|split; [exact Hl|exact Hm]].
  assert (E : o_pending o + (o_bi_valid o + 7) / 8 = (o_bi_valid o + 7 + o_pending o * 8) / 8)
    by (rewrite Z.div_add by lia; lia).
  rewrite E. apply Z.div_le_upper_bound; lia.
Qed.

Lemma stat_run t m syms s last :
  flush_pre t syms -> tree_ok t m syms -> 0 <= last <= 1 ->
  tr_out s = tr_out t -> tr_lit_bufsize s = tr_lit_bufsize t -> tr_sym_next s = tr_sym_next t ->
  exists o3 m3,
    (let* _ := guard (last <=? 2147483645) in
     let* om := c_send_bits (tr_out s, m) (Z.shiftl STATIC_TREES 1 + last) 3 in
     let* om := c_compress_block om (tr_lit_bufsize s) (tr_sym_next s)
                  static_ltree_code static_ltree_len static_dtree_code static_dtree_len in
     Some (om, BK_static)) = Some ((o3, m3), BK_static) /\ out_fin (tr_lit_bufsize t) o3 m3.
Proof.
  intros Hfp Htr Hlast Eo EL En.
  pose proof Hfp as [HL [Hok [Hp0 [Hbv Hob]]] [Hsn [Hn [Hval Hsy]]] _ _ _ _].
  assert (H128 : 128 <= tr_lit_bufsize t).
  { destruct HL as [ml [Hml E]]. rewrite E. change 128 with (2 ^ 7). apply Z.pow_le_mono_r; lia. }
  replace (last <=? 2147483645) with true by (symmetry; apply Z.leb_le; lia).
  cbv beta iota delta [guard]. rewrite bind_some.
  rewrite Eo, EL, En, Hsn.
  destruct Hok as [Hv0 [Hb0 Hpp]].
  rewrite c_send_bits_noflush by lia. rewrite bind_some.
  assert (Hov := FlushStatic.static_overlay (tr_lit_bufsize t) syms (tr_out t) last
                   (conj Hv0 (conj Hb0 Hpp)) Hp0 Hbv Hob H128 Hn Hval Hsy Hlast).
  destruct Htr as (T1 & T2 & Htr).
  destruct (comp_tail (tr_lit_bufsize t) syms _ m _ _ _ _ Hval Hov Hn ltac:(lia)
              (mask_syms t m syms (conj T1 (conj T2 Htr)))
              ltac:(vm_compute; congruence) ltac:(vm_compute; congruence)
              ltac:(vm_compute; congruence) ltac:(vm_compute; congruence)) as [m' [Hc [Ok [Bp Len]]]].
  rewrite Hc, bind_some. eexists _, _. split; [reflexivity|].
  assert (A := capp _ _ Hc). destruct A as [_ [Lm _]].
  apply out_fin_of with (n := Zlength syms); auto; lia.
Qed.

Lemma dyn_run t m syms s last mbi :
  flush_pre t syms -> tree_ok t m syms -> 0 <= last <= 1 ->
  tr_out s = tr_out t -> tr_lit_bufsize s = tr_lit_bufsize t -> tr_sym_next s = tr_sym_next t -> tr_sizes s ->
  END_BLOCK <= tr_lmax s < L_CODES -> 0 <= tr_dmax s < D_CODES -> 2 <= mbi <= BL_CODES - 1 ->
  (forall i, 0 <= i <= tr_lmax s -> 0 <= Znth i (dl (tr_ltree s)) <= 15) ->
  (forall i, 0 <= i <= tr_dmax s -> 0 <= Znth i (dl (tr_dtree s)) <= 15) ->
  (forall i, 0 <= i < BL_CODES -> 0 <= Znth i (dl (tr_bltree s)) <= 7) ->
  overlay_ok (tr_lit_bufsize t) syms
    (send_all_trees (send_bits (tr_out s) (Z.shiftl DYN_TREES 1 + last) 3)
       (tr_ltree s) (tr_dtree s) (tr_bltree s) (tr_lmax s + 1) (tr_dmax s + 1) (mbi + 1),
     fc (tr_ltree s), dl (tr_ltree s), fc (tr_dtree s), dl (tr_dtree s)) ->
  exists o3 m3,
    (let* _ := guard (last <=? 2147483643) in
     let* om := c_send_bits (tr_out s, m) (Z.shiftl DYN_TREES 1 + last) 3 in
     let* om := c_send_all_trees om (tr_ltree s) (tr_dtree s) (tr_bltree s)
                  (tr_lmax s + 1) (tr_dmax s + 1) (mbi + 1) in
     let* om := c_compress_block om (tr_lit_bufsize s) (tr_sym_next s)
                  (fc (tr_ltree s)) (dl (tr_ltree s)) (fc (tr_dtree s)) (dl (tr_dtree s)) in
     Some (om, BK_dynamic)) = Some ((o3, m3), BK_dynamic) /\ out_fin (tr_lit_bufsize t) o3 m3.
Proof.
  intros Hfp Htr Hlast Eo EL En Hsz Hlm Hdm Hmbi Hll Hdl Hbl Hov.
  pose proof Hfp as [HL [Hok [Hp0 [Hbv Hob]]] [Hsn [Hn [Hval Hsy]]] _ _ _ _].
  destruct Hsz as (Hl1 & Hl2 & Hl3 & Hd1 & Hd2 & Hd3 & Hb1 & Hb2 & Hb3 & _).
  replace (last <=? 2147483643) with true by (symmetry; apply Z.leb_le; lia).
  cbv beta iota delta [guard]. rewrite bind_some.
  rewrite EL, En, Hsn.
  rewrite Eo in Hov |- *.
  set (o1 := send_bits (tr_out t) (Z.shiftl DYN_TREES 1 + last) 3) in *.
  assert (Hval3 : 0 <= Z.shiftl DYN_TREES 1 + last < 2 ^ 3) by (unfold DYN_TREES; simpl; lia).
  destruct (send_bits_spec (tr_out t) (Z.shiftl DYN_TREES 1 + last) 3 Hok ltac:(lia) Hval3)
    as [_ [_ [Ok1 [_ [_ [L1 _]]]]]].
  fold o1 in Ok1, L1.
  destruct Hok as [Hv0 [Hb0 Hpp]].
  rewrite c_send_bits_noflush by lia. rewrite bind_some. fold o1.
  set (o2 := send_all_trees o1 (tr_ltree s) (tr_dtree s) (tr_bltree s) (tr_lmax s + 1) (tr_dmax s + 1) (mbi + 1)) in *.
  pose proof Htr as (T1 & T2 & _).
  assert (Hp2 : o_pending o2 <= Zlength (o_buf o1)).
  { destruct Hov as [Ok2 [Len2 [_ [_ [_ Hb]]]]].
    assert (B0 := Hb O ltac:(lia)). cbn [firstn compress_sep] in B0. unfold bitpos in B0.
    destruct Ok2 as [V2 _]. rewrite L1, Hob. pose proof (Zlength_nonneg syms). lia. }
  destruct (send_some o1 m (tr_ltree s) (tr_dtree s) (tr_bltree s) (tr_lmax s + 1) (tr_dmax s + 1) (mbi + 1)
              Ok1 ltac:(rewrite L1; lia) ltac:(unfold END_BLOCK, L_CODES in *; lia)
              ltac:(unfold D_CODES in *; lia) ltac:(unfold BL_CODES in *; lia)
              ltac:(rewrite Hl2; unfold HEAP_SIZE, L_CODES in *; lia) ltac:(rewrite Hd2; unfold D_CODES in *; lia)
              ltac:(intros i Hi; apply Hll; lia) ltac:(intros i Hi; apply Hdl; lia)
              Hb1 Hb2 Hbl Hp2) as [m2 Hs2].
  rewrite Hs2, bind_some. fold o2.
  assert (A2 := capp _ _ Hs2). destruct A2 as [_ [Lm2 _]].
  assert (Hmask : forall i, 0 <= i < 3 * Zlength syms -> Znth (tr_lit_bufsize t + i) m2 = true).
  { intros i Hi. apply (mask_after_true m m2 _ _ _ (capp _ _ Hs2)); [|apply (mask_syms t m syms Htr); lia].
    pose proof (Zlength_nonneg syms). lia. }
  destruct (comp_tail (tr_lit_bufsize t) syms o2 m2 _ _ _ _ Hval Hov Hn ltac:(lia) Hmask
              ltac:(rewrite Hl1; unfold HEAP_SIZE, L_CODES; lia) ltac:(rewrite Hl2; unfold HEAP_SIZE, L_CODES; lia)
              ltac:(rewrite Hd1; unfold D_CODES; lia) ltac:(rewrite Hd2; unfold D_CODES; lia))
    as [m' [Hc [Ok [Bp Len]]]].
  rewrite Hc, bind_some. eexists _, _. split; [reflexivity|].
  assert (A := capp _ _ Hc). destruct A as [_ [Lm _]].
  apply out_fin_of with (n := Zlength syms); auto; lia.
Qed.

Lemma stored_run t m syms s b sl last :
  flush_pre t syms -> tree_ok t m syms -> 0 <= last <= 1 ->
  tr_out s = tr_out t -> 0 < sl -> Zlength b = sl ->
  (o_bi_valid (tr_out t) + 3 + 7) / 8 + 4 + sl <= 4 * tr_lit_bufsize t ->
  exists o3 m3,
    (let* _ := guard (0 <? Zlength b) in
     let* om := c_tr_stored_block (tr_out s, m) b sl last in Some (om, BK_stored)) =
      Some ((o3, m3), BK_stored) /\ out_fin (tr_lit_bufsize t) o3 m3 /\ o_bi_valid o3 = 0.
Proof.
  intros Hfp Htr Hlast Eo Hsl Hb Hfit.
  pose proof Hfp as [HL [Hok [Hp0 [Hbv Hob]]] _ _ _ _ _].
  pose proof Htr as (T1 & T2 & _).
  replace (0 <? Zlength b) with true by (symmetry; apply Z.ltb_lt; lia).
  cbv beta iota delta [guard]. rewrite bind_some. rewrite Eo.
  destruct (stored_some (tr_out t) m b sl last Hok ltac:(lia) Hlast ltac:(lia) ltac:(lia)) as [m' Hc].
  rewrite Hc, bind_some. eexists _, _. split; [reflexivity|].
  destruct (stored_out (tr_out t) b sl last Hok Hlast ltac:(lia) ltac:(lia)) as [Ok [V [P Len]]].
  assert (A := capp _ _ Hc). destruct A as [_ [Lm _]].
  split; [|exact V].
  split; [exact Ok|]. split; [rewrite V, P; change ((0 + 7) / 8) with 0; lia|]. split; lia.
Qed.


(** ** The conclusions of trflush_spec from a run *)
Lemma fin_props t m syms buf sl last s' o4 M' kind :
  flush_pre t syms -> tree_ok t m syms -> mb_ok (mkMB (o_buf (tr_out t)) m) ->
  (forall b, buf = Some b -> bytes b) ->
  c_tr_flush_block (t, m) buf sl last = Some ((set_out (init_block s') o4, M'), kind) ->
  tr_sizes s' -> tr_cfg s' = tr_cfg t ->
  bits_ok o4 -> (last = 1 -> o_bi_valid o4 = 0) -> o_pending o4 <= 4 * tr_lit_bufsize t ->
  Zlength (o_buf o4) = 4 * tr_lit_bufsize t ->
  exists t' m' kind,
    c_tr_flush_block (t, m) buf sl last = Some ((t', m'), kind) /\
    (t', kind) = tr_flush_block t buf sl last /\
    tree_ok t' m' [] /\ tr_cfg t' = tr_cfg t /\ tr_matches t' = 0 /\
    bits_ok (tr_out t') /\ (last = 1 -> o_bi_valid (tr_out t') = 0) /\
    pb_grow (tr_out t) m (tr_out t') m' /\
    mb_defined (mkMB (o_buf (tr_out t')) m') 0 (o_pending (tr_out t')).
Proof.
  intros Hfp Htr Hmb Hbytes Hrun Hsz Hcfg Hok Hlast Hp4 Hl4.
  pose proof Hfp as [_ [_ [Hp0 _]] _ _ _ _ _].
  pose proof Htr as (T1 & T2 & _).
  assert (HL : tr_lit_bufsize s' = tr_lit_bufsize t) by (unfold tr_cfg in Hcfg; congruence).
  pose proof (c_tr_flush_block_mask _ _ _ _ _ _ _ _ Hrun) as MA.
  rewrite tr_out_set_out, Hp0 in MA.
  destruct (bytes_some _ _ _ _ _ _ _ _ Hrun Hbytes) as [BL [BF BB]].
  rewrite tr_out_set_out in BL, BF, BB. rewrite Hp0 in BF, BB.
  pose proof MA as [_ [MAL MAP]].
  exists (set_out (init_block s') o4), M', kind.
  split; [exact Hrun|].
  split; [exact (crel_tr_flush_block t m buf sl last _ Hrun)|].
  split; [apply tree_ok_init; [exact Hsz|congruence|congruence]|].
  split; [rewrite tr_cfg_set_out_init; exact Hcfg|].
  split; [apply tr_matches_set_out_init|].
  rewrite tr_out_set_out.
  split; [exact Hok|]. split; [exact Hlast|].
  split.
  - split; [congruence|]. split; [congruence|]. split.
    + intros i Hi. destruct (Z_le_gt_dec 0 i); [destruct (Z_lt_ge_dec i (Zlength m))|].
      * apply (mask_after_true m M' 0 (o_pending o4)); auto.
      * rewrite Znth_overflow in Hi by lia. discriminate.
      * rewrite Znth_underflow in Hi by lia. discriminate.
    + intros [Hm1 Hm2]. split; [cbn [mb_def mb_val] in *; congruence|].
      cbn [mb_def mb_val] in *. intros i Hi HM.
      destruct (Z_lt_ge_dec i (o_pending o4)) as [Hlt|Hge].
      * apply BB. lia.
      * rewrite BF by lia. rewrite MAP in HM by lia.
        replace ((0 <=? i) && (i <? o_pending o4)) with false in HM
          by (symmetry; apply andb_false_iff; right; apply Z.ltb_ge; lia).
        apply Hm2; [lia|exact HM].
  - split; [lia|]. split; [cbn [mb_val]; lia|]. intros i Hi. cbn [mb_def].
    rewrite MAP by (destruct Hok as [_ [_ ?]]; lia).
    replace ((0 <=? i) && (i <? o_pending o4)) with true
      by (symmetry; apply andb_true_iff; rewrite Z.leb_le, Z.ltb_lt; lia). reflexivity.
Qed.


Lemma flush_run : overlay_statement -> forall t m syms buf sl last,
  flush_pre t syms -> tree_ok t m syms -> 0 < tr_level t -> 0 <= last <= 1 ->
  mb_ok (mkMB (o_buf (tr_out t)) m) -> sl = blk_len syms ->
  match buf with Some b => Zlength b = sl /\ bytes b /\ sl <= 65535 | None => True end ->
  exists s' o4 M' kind,
    c_tr_flush_block (t, m) buf sl last = Some ((set_out (init_block s') o4, M'), kind) /\
    tr_sizes s' /\ tr_cfg s' = tr_cfg t /\
    bits_ok o4 /\ (last = 1 -> o_bi_valid o4 = 0) /\ o_pending o4 <= 4 * tr_lit_bufsize t /\
    Zlength (o_buf o4) = 4 * tr_lit_bufsize t /\ bitpos o4 <= 8 * (4 * tr_lit_bufsize t).
Proof.
  intros Hov t m syms buf sl last Hfp Htr Hlev Hlast Hmb Hsl Hbuf.
  pose proof Hfp as [HL [Hok [Hp0 [Hbv Hob]]] [Hsn [Hn [Hval Hsy]]] _ _ _ _].
  pose proof Htr as (T1 & T2 & _).
  assert (H128 : 128 <= tr_lit_bufsize t <= 32768).
  { destruct HL as [ml [Hml E]]. rewrite E. change 128 with (2 ^ 7). change 32768 with (2 ^ 15).
    split; apply Z.pow_le_mono_r; lia. }
  assert (Hbytes : forall b, buf = Some b -> bytes b) by (intros b ->; tauto).
  destruct (prep_some bt_some t syms sl Hfp Hlev) as [Hprep Hfacts].
  destruct (flush_prep t sl) as [[[s' olb] slb] mbi] eqn:Efp.
  cbn [fst] in Hfacts.
  destruct Hfacts as (Hcfg & Hout & Hsn' & Hmt & Hsz).
  assert (HLs : tr_lit_bufsize s' = tr_lit_bufsize t) by (unfold tr_cfg in Hcfg; congruence).
  destruct (DynSum.dyn_sum_holds FlushDyn.dyn_prep (TreeDD.tree_dd RepairBound.repair15_bound) t syms sl Hfp Hlev)
    as (s2 & olb2 & slb2 & mbi2 & ll & dl0 & dd & dd0 & Hh & E & DS).
  pose proof (DynSum.ds_prep _ _ _ _ _ _ _ _ _ _ _ _ _ DS) as Ep. rewrite Efp in Ep.
  inversion Ep; subst s2 olb2 slb2 mbi2; clear Ep.
  (* the dynamic-tree facts *)
  pose proof (FlushDyn.dyn_prep t syms sl Hfp Hlev) as DP. rewrite Efp in DP.
  destruct DP as (Sl & Fl & ordl & Rl & lt0 & wl & Sd & Fd & ordd & Rd & dt0 & wd & blt & Sb & Fb & ordb & Rb & wb &
                  BL & BD & BB & _ & _ & _ & _ & _ & _ & Hmbi & _).
  assert (Hmbi' : 2 <= mbi <= BL_CODES - 1) by (rewrite Hmbi; apply fmb_range; unfold BL_CODES; lia).
  assert (Hbl7 : forall i, 0 <= i < BL_CODES -> 0 <= Znth i (dl (tr_bltree s')) <= 7).
  { intros i Hi. destruct (in_dec Z.eq_dec i Sb) as [Hin|Hin].
    - pose proof (bt_len_in _ _ _ _ _ _ _ _ _ _ BB i Hin) as H. cbn in H. unfold MAX_BL_BITS in H. lia.
    - rewrite (bt_len_out _ _ _ _ _ _ _ _ _ _ BB i ltac:(cbn [sd_elems static_bl_desc]; unfold BL_CODES in *; lia) Hin). lia. }
  pose proof (DynSum.ds_lmax _ _ _ _ _ _ _ _ _ _ _ _ _ DS) as [Hlm _].
  pose proof (DynSum.ds_dmax _ _ _ _ _ _ _ _ _ _ _ _ _ DS) as [Hdm _].
  pose proof (DynSum.ds_guard _ _ _ _ _ _ _ _ _ _ _ _ _ DS) as [Gl Gd].
  pose proof (DynSum.ds_llen _ _ _ _ _ _ _ _ _ _ _ _ _ DS) as Hllen.
  pose proof (DynSum.ds_dlen _ _ _ _ _ _ _ _ _ _ _ _ _ DS) as Hdlen.
  pose proof (DynSum.ds_lists _ _ _ _ _ _ _ _ _ _ _ _ _ DS) as (Lll & Ldl0 & _ & _).
  assert (Hll : forall i, 0 <= i <= tr_lmax s' -> 0 <= Znth i (dl (tr_ltree s')) <= 15).
  { intros i Hi. rewrite Gl, Znth_upd_Znth_other by lia. apply Hllen. unfold L_CODES in *; lia. }
  assert (Hdl : forall i, 0 <= i <= tr_dmax s' -> 0 <= Znth i (dl (tr_dtree s')) <= 15).
  { intros i Hi. rewrite Gd, Znth_upd_Znth_other by lia. apply Hdlen. unfold D_CODES in *; lia. }
  assert (Hsz' : tr_sizes s') by exact Hsz.
  assert (DYN : forall b0, buf = b0 ->
            flush_call t buf sl last =
              Some (send_all_trees (send_bits (tr_out s') (Z.shiftl DYN_TREES 1 + last) 3)
                      (tr_ltree s') (tr_dtree s') (tr_bltree s') (tr_lmax s' + 1) (tr_dmax s' + 1) (mbi + 1),
                    fc (tr_ltree s'), dl (tr_ltree s'), fc (tr_dtree s'), dl (tr_dtree s')) ->
            exists o3 m3,
              (let* _ := guard (last <=? 2147483643) in
               let* om := c_send_bits (tr_out s', m) (Z.shiftl DYN_TREES 1 + last) 3 in
               let* om := c_send_all_trees om (tr_ltree s') (tr_dtree s') (tr_bltree s')
                            (tr_lmax s' + 1) (tr_dmax s' + 1) (mbi + 1) in
               let* om := c_compress_block om (tr_lit_bufsize s') (tr_sym_next s')
                            (fc (tr_ltree s')) (dl (tr_ltree s')) (fc (tr_dtree s')) (dl (tr_dtree s')) in
               Some (om, BK_dynamic)) = Some ((o3, m3), BK_dynamic) /\ out_fin (tr_lit_bufsize t) o3 m3).
  { intros b0 _ Hcall. apply dyn_run with (syms := syms); auto.
    apply (Hov t syms buf sl last Hfp Hlast _ Hcall). }
  assert (STAT := stat_run t m syms s' last Hfp Htr Hlast Hout HLs Hsn').
  (* the run *)
  assert (RUN : exists o4 M' kind,
             c_tr_flush_block (t, m) buf sl last = Some ((set_out (init_block s') o4, M'), kind) /\
             bits_ok o4 /\ (last = 1 -> o_bi_valid o4 = 0) /\ o_pending o4 <= 4 * tr_lit_bufsize t /\
             Zlength (o_buf o4) = 4 * tr_lit_bufsize t /\ bitpos o4 <= 8 * (4 * tr_lit_bufsize t)).
  { rewrite c_tr_flush_block_prep, Hprep, bind_some. cbv beta iota.
    match goal with |- exists _ _ _, bind ?X _ = _ /\ _ =>
      assert (MID : exists o3 m3 kind, X = Some ((o3, m3), kind) /\ out_fin (tr_lit_bufsize t) o3 m3) end.
    { pose proof (blk_len_ge syms Hval) as Hge. rewrite <- Hsl in Hge.
      pose proof (Zlength_nonneg syms) as Hn0.
      destruct buf as [b|].
      - destruct Hbuf as (Hbl & Hbb & Hs65).
        destruct (u64 (sl + 4) <=? olb) eqn:Es.
        + (* a stored block *)
          assert (Hu : u64 (sl + 4) = sl + 4) by (unfold u64; apply Z.mod_small; lia).
          rewrite Hu in Es. apply Z.leb_le in Es.
          pose proof (DynSum.ds_lenb _ _ _ _ _ _ _ _ _ _ _ _ _ DS) as [Eslb Eolb].
          pose proof (DynSum.ds_cost_stat _ _ _ _ _ _ _ _ _ _ _ _ _ DS) as Ecs.
          pose proof (stat_data_le syms Hval) as Hsd.
          assert (Hle : olb <= slb).
          { rewrite Eolb. destruct (slb <=? _) eqn:Eb; cbn [orb]; [lia|].
            apply Z.leb_gt in Eb. destruct (tr_strategy t =? Z_FIXED); lia. }
          assert (Hsd' : DynSum.stat_data syms <= 31 * Zlength syms + 7) by (rewrite <- Ecs; exact Hsd).
          destruct Hok as [Hv0 _].
          assert (Hpos : 0 < sl) by (clear - Es Hle Eslb Hsd' Hge Hn0; subst slb; Z.to_euclidean_division_equations; lia).
          assert (Hfit : (o_bi_valid (tr_out t) + 3 + 7) / 8 + 4 + sl <= 4 * tr_lit_bufsize t)
            by (clear - Es Hle Eslb Hsd' Hge Hn0 Hv0 Hbv Hn H128; subst slb; Z.to_euclidean_division_equations; lia).
          destruct (stored_run t m syms s' b sl last Hfp Htr Hlast Hout Hpos Hbl Hfit)
            as (o3 & m3 & R & F & _).
          exists o3, m3, BK_stored. split; [exact R|exact F].
        + destruct (slb =? olb) eqn:Est.
          * destruct STAT as (o3 & m3 & R & F). exists o3, m3, BK_static. split; [exact R|exact F].
          * destruct (DYN (Some b) eq_refl) as (o3 & m3 & R & F).
            { unfold flush_call. rewrite Efp. cbv beta iota zeta. rewrite Es, Est. reflexivity. }
            exists o3, m3, BK_dynamic. split; [exact R|exact F].
      - destruct (slb =? olb) eqn:Est.
        * destruct STAT as (o3 & m3 & R & F). exists o3, m3, BK_static. split; [exact R|exact F].
        * destruct (DYN None eq_refl) as (o3 & m3 & R & F).
          { unfold flush_call. rewrite Efp. cbv beta iota zeta. rewrite Est. reflexivity. }
          exists o3, m3, BK_dynamic. split; [exact R|exact F]. }
    destruct MID as (o3 & m3 & kind & EM & Fin). rewrite EM, bind_some. cbv beta iota.
    destruct Hsz as (Hl1 & _ & _ & Hd1 & _ & _ & Hb1 & _).
    rewrite c_init_block_some
      by (cbn [tr_ltree tr_dtree tr_bltree set_out]; unfold HEAP_SIZE, L_CODES, D_CODES, BL_CODES in *; lia).
    rewrite bind_some.
    destruct Fin as (Ok3 & P3 & L3 & M3).
    assert (0 <= (o_bi_valid o3 + 7) / 8) by (destruct Ok3 as [? _]; apply Z.div_pos; lia).
    destruct (Z.eqb_spec last 0) as [E0|E0].
    - cbn [negb]. rewrite bind_some. cbv beta iota.
      exists o3, m3, kind. split; [reflexivity|]. split; [exact Ok3|]. split; [intros; lia|]. split; [lia|].
      split; [lia|]. unfold bitpos. destruct Ok3 as [Hv3 _]. clear - P3 Hv3. Z.to_euclidean_division_equations; lia.
    - cbn [negb]. change (tr_out (init_block (set_out s' o3))) with o3.
      destruct (c_bi_windup_some o3 m3 Ok3 ltac:(lia)) as [m4 Hw]. rewrite Hw, bind_some. cbv beta iota.
      exists (bi_windup o3), m4, kind. split; [reflexivity|].
      destruct (BlockStored.windup_bitpos o3 Ok3) as [_ Ok4].
      destruct (bi_windup_spec o3 Ok3) as (W1 & W2 & _ & _ & _ & W6 & _).
      split; [exact Ok4|]. split; [intros; exact W2|]. split; [lia|]. split; [lia|].
      unfold bitpos. rewrite W2. lia. }
  destruct RUN as (o4 & M' & kind & Hrun & Ok4 & V4 & P4 & L4 & B4).
  exists s', o4, M', kind. repeat (split; [eassumption|]). exact B4.
Qed.

Lemma trflush_ok : overlay_statement -> trflush_spec.
Proof.
  intros Hov t m syms buf sl last Hfp Htr Hlev Hlast Hmb Hsl Hbuf.
  destruct (flush_run Hov t m syms buf sl last Hfp Htr Hlev Hlast Hmb Hsl Hbuf)
    as (s' & o4 & M' & kind & Hrun & Hsz & Hcfg & Ok4 & V4 & P4 & L4 & _).
  assert (Hbytes : forall b, buf = Some b -> bytes b) by (intros b ->; tauto).
  eapply fin_props; eauto.
Qed.

(* trees_ok (with the false tally_spec) is not provable; see LTCTrees2.trees_ok2. *)
