(** * _tr_flush_block with level > 0: what flush_prep computes (raw facts)

    [dyn_prep]: from [flush_pre], the three build_tree calls of flush_prep (literal/length, distance, bit length)
    satisfy [BtSpec.bt_facts] (via [BuildThm.build_tree_correct], discharging [bt_req]); scan_tree stored the
    guards 0xffff at max_code + 1 and counted the run-length symbols of both length tables into the bit-length
    frequencies; max_blindex is find_max_blindex's; opt_len / static_len are the build_tree results plus the
    header bits of build_bl_tree; the output, lit_bufsize, sym_next and strategy are untouched. *)

From Coq Require Import ZArith List Lia Bool Permutation.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.huffman.Model Zlib.proof.huffman.HuffAbs Zlib.proof.huffman.Heap
               Zlib.proof.huffman.Bits Zlib.proof.huffman.Overlay Zlib.proof.huffman.BuildPre
               Zlib.proof.huffman.Repair Zlib.proof.huffman.BtSpec Zlib.proof.huffman.BuildThm.
Require Zlib.proof.huffman.Header.
Require Zlib.proof.huffman.Cert Zlib.proof.huffman.FlushStream Zlib.proof.huffman.FlushHdr.
Module Hd := Zlib.proof.huffman.Header.
Import ListNotations.
Local Open Scope Z_scope.


(** ** Helpers *)

Lemma lfreq_sum : forall syms, (forall x, In x syms -> valid_sym (fst x) (snd x)) ->
  sumZ (map (fun x => lfreq syms x) (zseq 0 (Z.to_nat L_CODES))) = Zlength syms + 1.
Proof.
  intros syms Hv.
  assert (Hb : forall x, In x syms -> 0 <= lcode_of x < 286).
  { intros x Hx. destruct (FlushStream.lcode_range x (Hv x Hx)) as [A _]. unfold L_CODES in A. lia. }
  assert (Hk := Cert.sum_by_key lcode_of (fun _ => 1) 286 syms Hb). rewrite Cert.hsum_ones in Hk.
  rewrite Cert.zsum_rs in Hk. change (Z.to_nat 286) with 286%nat in Hk.
  change (sumZ (map (fun x => lfreq syms x) (zseq 0 (Z.to_nat L_CODES)))) with (Cert.rs 0 286 (lfreq syms)).
  rewrite (Cert.rs_ext _ 0 (lfreq syms) (fun j => 1 * Zlength (filter (fun x => lcode_of x =? j) syms) + (if j =? 256 then 1 else 0)))
    by (intros j Hj; unfold lfreq, END_BLOCK; lia).
  rewrite Cert.rs_add, Cert.rs_ind by (simpl; lia). lia.
Qed.

Definition dkey (x : Z * Z) : Z := if fst x =? 0 then 30 else d_code (fst x - 1).

Lemma dfreq_sum : forall syms, (forall x, In x syms -> valid_sym (fst x) (snd x)) ->
  sumZ (map (fun x => dfreq syms x) (zseq 0 (Z.to_nat D_CODES))) <= Zlength syms.
Proof.
  intros syms Hv.
  assert (Hb : forall x, In x syms -> 0 <= dkey x < 31).
  { intros [d lc] Hx. specialize (Hv _ Hx). destruct Hv as [Hl Hd]. unfold dkey; simpl in *.
    destruct (Z.eqb_spec d 0); [lia|]. destruct (dist_code_facts (d - 1) ltac:(lia)) as [A _]. lia. }
  assert (Hk := Cert.sum_by_key dkey (fun _ => 1) 31 syms Hb). rewrite Cert.hsum_ones in Hk.
  rewrite Cert.zsum_rs in Hk. change (Z.to_nat 31) with (S 30) in Hk. rewrite Cert.rs_snoc in Hk.
  change (sumZ (map (fun x => dfreq syms x) (zseq 0 (Z.to_nat D_CODES)))) with (Cert.rs 0 30 (dfreq syms)).
  rewrite (Cert.rs_ext _ 0 (dfreq syms) (fun j => 1 * Zlength (filter (fun x => dkey x =? j) syms))).
  - assert (H0 := Zlength_nonneg (filter (fun x => dkey x =? 0 + Z.of_nat 30) syms)). lia.
  - intros d Hd. rewrite Z.mul_1_l. unfold dfreq. f_equal. apply filter_ext_in. intros x Hx. unfold dkey.
    destruct (fst x =? 0); cbn [negb andb]; [|reflexivity].
    symmetry. apply Z.eqb_neq. lia.
Qed.

Definition tabs_ok (sd : stat_desc) (n : Z) : bool :=
  (0 <=? xbits sd n) && (xbits sd n <=? 16) &&
  match sd_stree sd with Some st => (0 <=? Znth n st) && (Znth n st <=? 16) | None => true end.

Lemma tabs_ok_spec : forall sd N, forallb (tabs_ok sd) (zseq 0 (Z.to_nat N)) = true ->
  (forall n, 0 <= n < N -> 0 <= xbits sd n <= 16) /\
  (forall st, sd_stree sd = Some st -> forall n, 0 <= n < N -> 0 <= Znth n st <= 16).
Proof.
  intros sd N H. split; [intros n Hn|intros st Est n Hn];
    assert (E := proj1 (forallb_forall _ _) H n ltac:(apply in_zseq; lia)); unfold tabs_ok in E;
    [|rewrite Est in E]; repeat rewrite andb_true_iff in E; rewrite ?Z.leb_le in E; lia.
Qed.

Lemma tabs_l : forallb (tabs_ok static_l_desc) (zseq 0 (Z.to_nat HEAP_SIZE)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma tabs_d : forallb (tabs_ok static_d_desc) (zseq 0 (Z.to_nat (2 * D_CODES + 1))) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma tabs_bl : forallb (tabs_ok static_bl_desc) (zseq 0 (Z.to_nat (2 * BL_CODES + 1))) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma cnt_le_length : forall s l, Hd.cnt s l <= Z.of_nat (length l).
Proof. intros. unfold Hd.cnt. assert (H := filter_length_le (fun q => fst q =? s) l). lia. Qed.

Lemma cnt_out : forall s l, Hd.syms_ok l -> ~ (0 <= s < 19) -> Hd.cnt s l = 0.
Proof.
  intros s l Hok Hs. unfold Hd.cnt. rewrite Cert.filter_false; [reflexivity|].
  intros q Hq. apply Z.eqb_neq. intros E. apply Hs. rewrite <- E. apply (Hok q Hq).
Qed.

Lemma no_wrap_of : forall blf l, Zlength blf = 2 * BL_CODES + 1 -> Hd.syms_ok l ->
  (forall s, 0 <= s < 2 * BL_CODES + 1 -> 0 <= Znth s blf < 65536) ->
  (forall s, 0 <= s < BL_CODES -> Znth s blf + Z.of_nat (length l) < 65536) -> Hd.no_wrap blf l.
Proof.
  intros blf l HL Hok Hr Hs. unfold BL_CODES in *. split.
  - intros q Hq. rewrite HL. destruct (Hok q Hq). lia.
  - intros s Hs'. rewrite HL in Hs'. split; [apply Hr; lia|].
    destruct (Z_lt_dec s 19).
    + specialize (Hs s ltac:(lia)). pose proof (cnt_le_length s l). lia.
    + rewrite cnt_out by (auto; lia). specialize (Hr s ltac:(lia)). lia.
Qed.

(** Lengths of a built tree on 0..max_code. *)
Lemma bt_lens : forall sd t w S F order R t' mc w', bt_facts sd t w S F order R t' mc w' ->
  sd_maxlen sd <= 15 ->
  0 <= mc < sd_elems sd /\ forall i, 0 <= i <= mc -> 0 <= Znth i (dl t') <= 15.
Proof.
  intros sd t w S F order R t' mc w' B Hm.
  destruct (bt_S _ _ _ _ _ _ _ _ _ _ B) as [_ [_ [HS _]]]. destruct (bt_mc _ _ _ _ _ _ _ _ _ _ B) as [Hin _].
  specialize (HS mc Hin). split; [lia|].
  intros i Hi. destruct (in_dec Z.eq_dec i S) as [Hi'|Hi'].
  - specialize (bt_len_in _ _ _ _ _ _ _ _ _ _ B i Hi'). lia.
  - rewrite (bt_len_out _ _ _ _ _ _ _ _ _ _ B i ltac:(lia) Hi'). lia.
Qed.

Definition dyn_prep_statement : Prop := forall s syms stored_len, flush_pre s syms -> 0 < tr_level s ->
  let '(s', olb, slb, mbi) := flush_prep s stored_len in
  exists Sl Fl ordl Rl lt0 wl Sd Fd ordd Rd dt0 wd blt Sb Fb ordb Rb wb,
    bt_facts static_l_desc (tr_ltree s) (tr_wk s) Sl Fl ordl Rl lt0 (tr_lmax s') wl /\
    bt_facts static_d_desc (tr_dtree s) wl Sd Fd ordd Rd dt0 (tr_dmax s') wd /\
    bt_facts static_bl_desc blt wd Sb Fb ordb Rb (tr_bltree s') (tr_blmax s') wb /\
    tr_ltree s' = set_dl lt0 (tr_lmax s' + 1) 65535 /\
    tr_dtree s' = set_dl dt0 (tr_dmax s' + 1) 65535 /\
    dl blt = dl (tr_bltree s) /\ Zlength (fc blt) = 2 * BL_CODES + 1 /\
    (forall n, 0 <= n < 2 * BL_CODES + 1 -> 0 <= Znth n (fc blt) < 65536) /\
    (forall c, 0 <= c < BL_CODES -> Znth c (fc blt) =
       Hd.cnt c (Hd.tree_syms (dl (tr_ltree s')) (tr_lmax s')) +
       Hd.cnt c (Hd.tree_syms (dl (tr_dtree s')) (tr_dmax s'))) /\
    mbi = find_max_blindex 20 (tr_bltree s') (BL_CODES - 1) /\
    w_opt_len (tr_wk s') = u64 (w_opt_len wb + (3 * (mbi + 1) + 5 + 5 + 4)) /\
    w_static_len (tr_wk s') = w_static_len wb /\
    slb = Z.shiftr (u64 (w_static_len (tr_wk s') + 3 + 7)) 3 /\
    olb = (if (slb <=? Z.shiftr (u64 (w_opt_len (tr_wk s') + 3 + 7)) 3) || (tr_strategy s =? Z_FIXED)
           then slb else Z.shiftr (u64 (w_opt_len (tr_wk s') + 3 + 7)) 3) /\
    tr_out s' = tr_out s /\ tr_lit_bufsize s' = tr_lit_bufsize s /\ tr_sym_next s' = tr_sym_next s /\
    tr_strategy s' = tr_strategy s.

Theorem dyn_prep : dyn_prep_statement.
Proof.
  intros s syms stored_len Hfp Hlev.
  destruct Hfp as [HL [Hok [Hp0 [Hbv Hob]]] [Hsn [Hsl [Hval Hsy]]] [Hl1 [Hl2 [Hl3 Hl4]]] [Hd1 [Hd2 [Hd3 Hd4]]]
                  [Hb1 [Hb2 [Hb3 Hb4]]] [Hw1 [Hw2 [Hw3 [Hw4 Hw5]]]]].
  assert (HLB : tr_lit_bufsize s <= 32768).
  { destruct HL as [ml [Hml E]]. rewrite E. change 32768 with (2 ^ 15). apply Z.pow_le_mono_r; lia. }
  pose proof (Zlength_nonneg syms) as Hn0.
  unfold flush_prep. replace (tr_level s >? 0) with true by (symmetry; apply Z.gtb_lt; lia).
  set (s0 := if tr_data_type s =? Z_UNKNOWN then set_data_type s (detect_data_type (fc (tr_ltree s))) else s).
  assert (E0 : tr_ltree s0 = tr_ltree s /\ tr_dtree s0 = tr_dtree s /\ tr_bltree s0 = tr_bltree s /\
               tr_wk s0 = tr_wk s /\ tr_out s0 = tr_out s /\ tr_lit_bufsize s0 = tr_lit_bufsize s /\
               tr_sym_next s0 = tr_sym_next s /\ tr_strategy s0 = tr_strategy s)
    by (unfold s0; destruct (tr_data_type s =? Z_UNKNOWN); repeat split).
  clearbody s0. destruct E0 as [E1 [E2 [E3 [E4 [E5 [E6 [E7 E8]]]]]]].
  rewrite E1, E4.
  (* the literal/length tree *)
  assert (RL : bt_req static_l_desc (tr_ltree s) (tr_wk s)).
  { constructor.
    - cbn; unfold L_CODES, D_CODES, BL_CODES, MAX_BITS, MAX_BL_BITS; cbn; lia.
    - cbn. unfold HEAP_SIZE in *. lia.
    - rewrite Hw1, Hw2, Hw4, Hw5. unfold HEAP_SIZE. lia.
    - rewrite Hl1. exact Hl3.
    - split.
      + intros x Hx. cbn in Hx. apply Hl3. unfold HEAP_SIZE, L_CODES in *. lia.
      + cbn [sd_elems static_l_desc].
        rewrite (map_ext_in _ (fun x => lfreq syms x)) by (intros x Hx; apply in_zseq in Hx; apply Hl4; lia).
        rewrite lfreq_sum by exact Hval. lia.
    - rewrite Hl2. exact (tabs_ok_spec _ _ tabs_l). }
  assert (BL := build_tree_correct _ _ _ RL).
  destruct (build_tree static_l_desc (tr_ltree s) (tr_wk s)) as [[lt lmax] w1] eqn:EL.
  destruct BL as [Sl [Fl [ordl [Rl BL]]]].
  cbn [tr_dtree tr_wk set_wk set_lmax set_ltree]. rewrite E2.
  destruct (bt_lens _ _ _ _ _ _ _ _ _ _ BL ltac:(simpl; unfold MAX_BITS; lia)) as [Hlm Hll].
  cbn [sd_elems static_l_desc] in Hlm. unfold L_CODES in Hlm.
  (* the distance tree *)
  assert (RD : bt_req static_d_desc (tr_dtree s) w1).
  { destruct (bt_sizes _ _ _ _ _ _ _ _ _ _ BL) as [_ [_ [W1 [W2 _]]]].
    assert (O1 := bt_opt _ _ _ _ _ _ _ _ _ _ BL). assert (O2 := bt_static _ _ _ _ _ _ _ _ _ _ BL).
    cbn [sd_stree static_l_desc] in O2.
    constructor.
    - cbn; unfold L_CODES, D_CODES, BL_CODES, MAX_BITS, MAX_BL_BITS; cbn; lia.
    - cbn. unfold HEAP_SIZE, D_CODES in *. lia.
    - rewrite W1, W2, O1, O2. unfold u64. repeat split; try lia; apply Z.mod_pos_bound; lia.
    - rewrite Hd1. exact Hd3.
    - split.
      + intros x Hx. cbn in Hx. apply Hd3. unfold D_CODES in *. lia.
      + cbn [sd_elems static_d_desc].
        rewrite (map_ext_in _ (fun x => dfreq syms x)) by (intros x Hx; apply in_zseq in Hx; apply Hd4; lia).
        assert (H := dfreq_sum syms Hval). lia.
    - rewrite Hd2. exact (tabs_ok_spec _ _ tabs_d). }
  assert (BD := build_tree_correct _ _ _ RD).
  destruct (build_tree static_d_desc (tr_dtree s) w1) as [[dt dmax] w2] eqn:ED.
  destruct BD as [Sd [Fd [ordd [Rd BD]]]].
  destruct (bt_lens _ _ _ _ _ _ _ _ _ _ BD ltac:(simpl; unfold MAX_BITS; lia)) as [Hdm Hdl].
  cbn [sd_elems static_d_desc] in Hdm. unfold D_CODES in Hdm.
  unfold build_bl_tree. cbn [tr_ltree tr_dtree tr_bltree tr_lmax tr_dmax tr_wk set_wk set_dmax set_dtree set_lmax set_ltree].
  rewrite E3.
  (* the two streams *)
  set (l1 := Hd.tree_syms (dl (set_dl lt (lmax + 1) 65535)) lmax).
  set (l2 := Hd.tree_syms (dl (set_dl dt (dmax + 1) 65535)) dmax).
  assert (K1 : Hd.syms_ok l1 /\ Z.of_nat (length l1) <= lmax + 1).
  { split; [|apply FlushHdr.tree_syms_length; lia].
    apply Hd.tree_syms_ok; [lia|]. intros i Hi. cbn [dl set_dl]. rewrite Hd.Znth_upd_other by lia. auto. }
  assert (K2 : Hd.syms_ok l2 /\ Z.of_nat (length l2) <= dmax + 1).
  { split; [|apply FlushHdr.tree_syms_length; lia].
    apply Hd.tree_syms_ok; [lia|]. intros i Hi. cbn [dl set_dl]. rewrite Hd.Znth_upd_other by lia. auto. }
  destruct K1 as [K1a K1b]. destruct K2 as [K2a K2b].
  assert (NW1 : Hd.no_wrap (fc (tr_bltree s)) l1).
  { apply no_wrap_of; auto. intros c Hc. rewrite Hb4 by lia. lia. }
  destruct (Hd.scan_tree_counts lt lmax (tr_bltree s) ltac:(lia) NW1) as [S1a [S1b [S1c S1d]]].
  destruct (scan_tree lt lmax (tr_bltree s)) as [lt' bl1] eqn:ES1. cbn [fst snd] in S1a, S1b, S1c, S1d. subst lt'. fold l1 in S1d.
  assert (NW2 : Hd.no_wrap (fc bl1) l2).
  { apply no_wrap_of; auto; [lia| |].
    - intros n Hn. rewrite S1d by lia. destruct (Z_lt_dec n 19).
      + rewrite Hb4 by (unfold BL_CODES; lia). pose proof (cnt_le_length n l1). pose proof (Hd.cnt_nonneg n l1). lia.
      + rewrite (cnt_out n l1 K1a) by lia. specialize (Hb3 n Hn). lia.
    - intros c Hc. rewrite S1d by (unfold BL_CODES in *; lia). rewrite Hb4 by lia.
      pose proof (cnt_le_length c l1). lia. }
  destruct (Hd.scan_tree_counts dt dmax bl1 ltac:(lia) NW2) as [S2a [S2b [S2c S2d]]].
  destruct (scan_tree dt dmax bl1) as [dt' bl2] eqn:ES2. cbn [fst snd] in S2a, S2b, S2c, S2d. subst dt'. fold l2 in S2d.
  assert (HZ : Zlength (fc bl2) = 2 * BL_CODES + 1) by lia.
  assert (HF : forall n, 0 <= n < 2 * BL_CODES + 1 ->
                 Znth n (fc bl2) = Znth n (fc (tr_bltree s)) + Hd.cnt n l1 + Hd.cnt n l2).
  { intros n Hn. rewrite S2d by lia. rewrite S1d by lia. lia. }
  assert (HR : forall n, 0 <= n < 2 * BL_CODES + 1 -> 0 <= Znth n (fc bl2) < 65536).
  { intros n Hn. rewrite HF by lia. destruct (Z_lt_dec n 19).
    - rewrite Hb4 by (unfold BL_CODES; lia).
      pose proof (cnt_le_length n l1). pose proof (Hd.cnt_nonneg n l1).
      pose proof (cnt_le_length n l2). pose proof (Hd.cnt_nonneg n l2). lia.
    - rewrite (cnt_out n l1 K1a), (cnt_out n l2 K2a) by lia. specialize (Hb3 n Hn). lia. }
  (* the bit length tree *)
  assert (RB : bt_req static_bl_desc bl2 w2).
  { destruct (bt_sizes _ _ _ _ _ _ _ _ _ _ BD) as [_ [_ [W1 [W2 _]]]].
    assert (O1 := bt_opt _ _ _ _ _ _ _ _ _ _ BD). assert (O2 := bt_static _ _ _ _ _ _ _ _ _ _ BD).
    cbn [sd_stree static_d_desc] in O2.
    constructor.
    - cbn; unfold L_CODES, D_CODES, BL_CODES, MAX_BITS, MAX_BL_BITS; cbn; lia.
    - rewrite HZ, S2b, S1b, Hb2. cbn. unfold HEAP_SIZE. lia.
    - rewrite W1, W2, O1, O2. unfold u64. repeat split; try lia; apply Z.mod_pos_bound; lia.
    - rewrite HZ. exact HR.
    - split.
      + intros x Hx. cbn in Hx. apply HR. unfold BL_CODES in *. lia.
      + cbn [sd_elems static_bl_desc].
        rewrite (map_ext_in _ (fun x => Hd.cnt x l1 + Hd.cnt x l2)).
        2:{ intros x Hx. apply in_zseq in Hx. cbn in Hx. rewrite HF by (unfold BL_CODES; lia).
            rewrite Hb4 by (unfold BL_CODES; lia). lia. }
        rewrite Cert.hsum_map_add. change (Z.to_nat BL_CODES) with 19%nat.
        rewrite !FlushStream.sum_cnt_length by (intros q Hq; first [apply (K1a q Hq) | apply (K2a q Hq)]).
        lia.
    - rewrite S2b, S1b, Hb2. exact (tabs_ok_spec _ _ tabs_bl). }
  assert (BB := build_tree_correct _ _ _ RB).
  destruct (build_tree static_bl_desc bl2 w2) as [[bl3 blmax] w3] eqn:EB.
  destruct BB as [Sb [Fb [ordb [Rb BB]]]].
  cbn beta iota.
  exists Sl, Fl, ordl, Rl, lt, w1, Sd, Fd, ordd, Rd, dt, w2, bl2, Sb, Fb, ordb, Rb, w3.
  cbn [tr_ltree tr_dtree tr_bltree tr_lmax tr_dmax tr_blmax tr_wk tr_out tr_lit_bufsize tr_sym_next tr_strategy
       set_wk set_blmax set_bltree set_dtree set_ltree set_dmax set_lmax w_opt_len w_static_len w_set_opt_len].
  rewrite E5, E6, E7, E8.
  split; [exact BL|]. split; [exact BD|]. split; [exact BB|].
  split; [reflexivity|]. split; [reflexivity|].
  split; [congruence|]. split; [exact HZ|]. split; [exact HR|].
  split.
  { intros c Hc. rewrite HF by (unfold BL_CODES in *; lia). rewrite Hb4 by lia. reflexivity. }
  repeat split.
Qed.
