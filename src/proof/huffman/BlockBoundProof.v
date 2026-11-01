(** * Lemma (ii), proved from lemma (i): [BlockBound.block_bound_statement]

    The block written by _tr_flush_block at memLevel 8 (lit_bufsize 16384), from [DynSum.dyn_sum] (level > 0) and
    the stored-block / bi_windup bit counts of [BlockStored]:
    - stored block: [BlockStored.stored_block_bitpos], [Bound.acct_stored];
    - static or dynamic block with [buf <> NULL]: the decision [u64 (stored_len + 4) > opt_lenb] and
      [Bound.acct_not_stored] (the bits of compress_block over the overlaid buffer are those of the separate run by
      [Overlay.overlay_compress], given lemma (i));
    - [buf = NULL]: [Bound.null_block_bound], with the Huffman depths optimal against the reference code [Bound.r1]
      ([ds_dd_opt]) and Delta = X + E <= 632 * 16386 / 540 + 64 <= 21600 ([ds_dd_repair], [ds_E]);
    - the final bi_windup of the last block rounds up to a byte ([BlockStored.round8_le]). *)

From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.huffman.Model Zlib.proof.huffman.HuffAbs Zlib.proof.huffman.Bits
               Zlib.proof.huffman.Overlay Zlib.proof.huffman.BlockBound Zlib.proof.huffman.Header
               Zlib.proof.huffman.BlockFacts Zlib.proof.huffman.BlockStored Zlib.proof.huffman.Bound
               Zlib.proof.huffman.FlushStatic Zlib.proof.huffman.DynSum.
Import ListNotations.
Local Open Scope Z_scope.

(** Regrouping: the bits of a block's symbols plus END_BLOCK, under any code lengths, as a sum over the codes of
    frequency times (length + extra bits). *)
Lemma cr_sumZ_add : forall {A} (f g : A -> Z) l,
  HuffAbs.sumZ (map (fun x => f x + g x) l) = HuffAbs.sumZ (map f l) + HuffAbs.sumZ (map g l).
Proof. intros A f g l. induction l as [|a l IH]; simpl; lia. Qed.

Lemma cr_sumZ_ext : forall {A} (f g : A -> Z) l, (forall x, In x l -> f x = g x) ->
  HuffAbs.sumZ (map f l) = HuffAbs.sumZ (map g l).
Proof. intros A f g l H. rewrite (map_ext_in f g l H). reflexivity. Qed.

Lemma cr_sumZ_zero : forall {A} (l : list A), HuffAbs.sumZ (map (fun _ => 0) l) = 0.
Proof. intros A l. induction l; simpl; lia. Qed.

Lemma cr_ind_out : forall (h : Z -> Z) x n a, ~ (a <= x < a + Z.of_nat n) ->
  HuffAbs.sumZ (map (fun s => if x =? s then h s else 0) (Heap.zseq a n)) = 0.
Proof.
  intros h x n. induction n as [|n IH]; intros a Ha; simpl; [reflexivity|].
  destruct (Z.eqb_spec x a); [lia|]. rewrite IH; lia.
Qed.

Lemma cr_ind_in : forall (h : Z -> Z) x n a, a <= x < a + Z.of_nat n ->
  HuffAbs.sumZ (map (fun s => if x =? s then h s else 0) (Heap.zseq a n)) = h x.
Proof.
  intros h x n. induction n as [|n IH]; intros a Ha; simpl; [lia|].
  destruct (Z.eqb_spec x a).
  - subst. rewrite cr_ind_out; lia.
  - rewrite IH; lia.
Qed.

Lemma cr_zsum_ind : forall (h : Z -> Z) x n, 0 <= x < n ->
  zsum n (fun c => if x =? c then h c else 0) = h x.
Proof. intros h x n Hx. unfold zsum. apply cr_ind_in. lia. Qed.

Lemma cr_zsum_add : forall n (f g : Z -> Z), zsum n (fun c => f c + g c) = zsum n f + zsum n g.
Proof. intros. unfold zsum. apply cr_sumZ_add. Qed.

Lemma cr_zsum_ext : forall n (f g : Z -> Z), (forall c, f c = g c) -> zsum n f = zsum n g.
Proof. intros. unfold zsum. apply cr_sumZ_ext. auto. Qed.

Lemma cr_sym_cost : forall llens dlens d l, valid_sym d l ->
  sym_cost llens dlens d l =
  (Znth (lcode_of (d, l)) llens + xl (lcode_of (d, l))) +
  (if d =? 0 then 0 else Znth (d_code (d - 1)) dlens + xd (d_code (d - 1))).
Proof.
  intros llens dlens d l [Hl Hd]. unfold sym_cost, lcode_of, xl, xd; simpl.
  destruct (Z.eqb_spec d 0).
  - destruct (Z.leb_spec 257 l); lia.
  - destruct (length_code_facts l Hl) as [A _]. unfold LITERALS.
    destruct (Z.leb_spec 257 (Znth l length_code_tab + 256 + 1)); [|lia].
    replace (Znth l length_code_tab + 256 + 1 - 257) with (Znth l length_code_tab) by lia.
    replace (Znth l length_code_tab + 256 + 1) with (Znth l length_code_tab + 257) by lia. lia.
Qed.

Lemma cost_regroup : forall (llens dlens : list Z) (syms : list (Z * Z)),
  (forall x, In x syms -> valid_sym (fst x) (snd x)) ->
  cost_sum llens dlens syms + Znth END_BLOCK llens =
  zsum L_CODES (fun c => lfreq syms c * (Znth c llens + xl c)) +
  zsum D_CODES (fun d => dfreq syms d * (Znth d dlens + xd d)).
Proof.
  intros llens dlens syms. induction syms as [|[d l] syms IH]; intros Hv.
  - simpl cost_sum. unfold lfreq, dfreq. simpl filter. rewrite !Zlength_nil.
    rewrite (cr_zsum_ext D_CODES _ (fun _ => 0)) by (intros; lia).
    rewrite (cr_zsum_ext L_CODES _ (fun c => if END_BLOCK =? c then Znth c llens + xl c else 0)).
    + rewrite cr_zsum_ind by (unfold END_BLOCK, L_CODES; lia).
      unfold zsum. rewrite cr_sumZ_zero. unfold xl, END_BLOCK. simpl. lia.
    + intros c. destruct (Z.eqb_spec c END_BLOCK), (Z.eqb_spec END_BLOCK c); try lia.
  - assert (Hs : valid_sym d l) by exact (Hv (d, l) (in_eq _ _)).
    assert (Hv' : forall x, In x syms -> valid_sym (fst x) (snd x)) by (intros; apply Hv; right; auto).
    specialize (IH Hv'). cbn [cost_sum]. rewrite cr_sym_cost by auto.
    assert (HL : 0 <= lcode_of (d, l) < L_CODES).
    { destruct Hs as [Hl Hd]. unfold lcode_of; simpl. destruct (Z.eqb_spec d 0).
      - unfold L_CODES. lia.
      - destruct (length_code_facts l Hl) as [A _]. unfold L_CODES, LITERALS. lia. }
    rewrite (cr_zsum_ext L_CODES (fun c => lfreq ((d, l) :: syms) c * (Znth c llens + xl c))
               (fun c => (if lcode_of (d, l) =? c then Znth c llens + xl c else 0) +
                         lfreq syms c * (Znth c llens + xl c))).
    2:{ intros c. unfold lfreq. cbn [filter]. destruct (lcode_of (d, l) =? c); [rewrite Zlength_cons|]; lia. }
    rewrite (cr_zsum_ext D_CODES (fun c => dfreq ((d, l) :: syms) c * (Znth c dlens + xd c))
               (fun c => (if negb (d =? 0) && (d_code (d - 1) =? c) then Znth c dlens + xd c else 0) +
                         dfreq syms c * (Znth c dlens + xd c))).
    2:{ intros c. unfold dfreq. cbn [filter fst].
        destruct (negb (d =? 0) && (d_code (d - 1) =? c)); [rewrite Zlength_cons|]; lia. }
    rewrite !cr_zsum_add. rewrite cr_zsum_ind by exact HL.
    destruct (Z.eqb_spec d 0) as [E|E]; simpl negb; cbn [andb].
    + unfold zsum at 2. rewrite cr_sumZ_zero. lia.
    + destruct Hs as [Hl Hd]. destruct (dist_code_facts (d - 1) ltac:(lia)) as [A _].
      rewrite cr_zsum_ind by (unfold D_CODES; lia). lia.
Qed.

(** ** Small facts *)

Lemma zsum_le : forall n (f g : Z -> Z), (forall i, 0 <= i < n -> f i <= g i) -> zsum n f <= zsum n g.
Proof.
  intros n f g H. unfold zsum. apply sumZ_le. intros i Hi. apply Heap.in_zseq in Hi. apply H.
  destruct (Z_lt_le_dec n 0); [replace (Z.to_nat n) with O in Hi by lia; simpl in Hi; lia|].
  rewrite Z2Nat.id in Hi by lia. lia.
Qed.

Lemma zsum_add : forall n (f g : Z -> Z), zsum n (fun i => f i + g i) = zsum n f + zsum n g.
Proof. intros. unfold zsum. apply FlushTree.sumZ_map_add'. Qed.

Lemma zsum_ext : forall n (f g : Z -> Z), (forall i, 0 <= i < n -> f i = g i) -> zsum n f = zsum n g.
Proof. intros n f g H. apply Z.le_antisymm; apply zsum_le; intros i Hi; rewrite H by lia; lia. Qed.

Lemma blk_bits_cost : forall llens dlens syms, blk_bits llens dlens syms = cost_sum llens dlens syms.
Proof.
  intros llens dlens syms. induction syms as [|[d l] r IH]; [reflexivity|].
  unfold blk_bits in *. cbn [map sumZl cost_sum fst snd]. rewrite IH. f_equal.
  unfold sym_bits, sym_cost. destruct (d =? 0); [reflexivity|]. unfold LITERALS. replace (Znth l length_code_tab + 256 + 1) with (Znth l length_code_tab + 257) by lia. reflexivity.
Qed.

Lemma blk_bytes_len : forall syms, blk_bytes syms = blk_len syms.
Proof.
  intros syms. induction syms as [|[d l] r IH]; [reflexivity|].
  unfold blk_bytes, blk_len in *. cbn [map sumZl HuffAbs.sumZ fst snd]. rewrite IH. reflexivity.
Qed.

Lemma blk_len_nonneg : forall syms, (forall x, In x syms -> valid_sym (fst x) (snd x)) -> 0 <= blk_len syms.
Proof.
  intros syms H. unfold blk_len. apply sumZ_nonneg. intros [d l] Hx. specialize (H _ Hx).
  unfold sym_len, valid_sym in *; simpl in *. destruct (d =? 0); lia.
Qed.

Lemma windup_bitpos' : forall o, 0 <= o_bi_valid o <= 16 ->
  Bits.bitpos (bi_windup o) = 8 * ((Bits.bitpos o + 7) / 8) /\ o_bi_valid (bi_windup o) = 0.
Proof.
  intros o Hv. unfold bi_windup, Bits.bitpos.
  destruct (Z.gtb_spec (o_bi_valid o) 8) as [E|E]; [|destruct (Z.gtb_spec (o_bi_valid o) 0) as [E0|E0]];
    cbn [o_pending o_bi_valid put_short put_byte]; split; auto.
  - replace (8 * o_pending o + o_bi_valid o + 7) with ((o_bi_valid o + 7 - 16) + (o_pending o + 2) * 8) by lia.
    rewrite Z.div_add by lia. rewrite (Z.div_small (o_bi_valid o + 7 - 16)) by lia. lia.
  - replace (8 * o_pending o + o_bi_valid o + 7) with ((o_bi_valid o + 7 - 8) + (o_pending o + 1) * 8) by lia.
    rewrite Z.div_add by lia. rewrite (Z.div_small (o_bi_valid o + 7 - 8)) by lia. lia.
  - replace (8 * o_pending o + o_bi_valid o + 7) with (7 + o_pending o * 8) by lia.
    rewrite Z.div_add by lia. change (7 / 8) with 0. lia.
Qed.

(** The end of _tr_flush_block: init_block keeps the output, the last block is padded to a byte. *)
Lemma finish : forall s1 (p : outbuf * block_kind) last T M,
  0 <= o_bi_valid (fst p) <= 16 -> 8 * T + Bits.bitpos (fst p) <= 8 * M ->
  8 * T + Bits.bitpos (tr_out (fst (let '(o, kind) := p in
                                let s := init_block (set_out s1 o) in
                                let s := if negb (last =? 0) then set_out s (bi_windup (tr_out s)) else s in
                                (s, kind)))) <= 8 * M.
Proof.
  intros s1 [o kind] last T M Hv Hb. cbn [fst] in *.
  assert (Hi : tr_out (init_block (set_out s1 o)) = o) by reflexivity.
  destruct (negb (last =? 0)); cbn [fst]; [|rewrite Hi; exact Hb].
  change (tr_out (set_out (init_block (set_out s1 o)) (bi_windup (tr_out (init_block (set_out s1 o))))))
    with (bi_windup (tr_out (init_block (set_out s1 o)))).
  rewrite Hi. destruct (windup_bitpos' o Hv) as [-> _].
  replace (8 * T + 8 * ((Bits.bitpos o + 7) / 8)) with (8 * ((8 * T + Bits.bitpos o + 7) / 8)).
  - apply round8_le. exact Hb.
  - replace (8 * T + Bits.bitpos o + 7) with ((Bits.bitpos o + 7) + T * 8) by lia. rewrite Z.div_add by lia. lia.
Qed.

(** A stored block. *)
Lemma stored_case : forall o b B last T A,
  bits_ok o -> 0 <= last <= 1 -> 0 <= B -> 0 <= T -> 8 * T + Bits.bitpos o <= 8 * A ->
  0 <= o_bi_valid (tr_stored_block o b B last) <= 16 /\
  8 * T + Bits.bitpos (tr_stored_block o b B last) <= 8 * (A + B + 5).
Proof.
  intros o b B last T A Hok Hl HB HT Hb.
  destruct (stored_block_bitpos o b B last Hok Hl HB) as [E V]. rewrite V. split; [lia|]. rewrite E.
  assert (Hbo : 0 <= Bits.bitpos o) by (destruct Hok as [? [? ?]]; unfold Bits.bitpos; lia).
  pose proof (acct_stored (8 * T + Bits.bitpos o) A B ltac:(lia) HB) as H.
  replace (8 * T + Bits.bitpos o + 3 + 7) with ((Bits.bitpos o + 3 + 7) + T * 8) in H by lia.
  rewrite Z.div_add in H by lia. lia.
Qed.

(** The compress_block call, given lemma (i): the bits of the symbols and of END_BLOCK. *)
Lemma call_bits : forall L syms o lc ll dc dl,
  (forall x, In x syms -> valid_sym (fst x) (snd x)) ->
  overlay_ok L syms (o, lc, ll, dc, dl) ->
  0 <= o_bi_valid (compress_block o L (3 * Zlength syms) lc ll dc dl) <= 16 /\
  Bits.bitpos (compress_block o L (3 * Zlength syms) lc ll dc dl) =
    Bits.bitpos o + cost_sum ll dl syms + Znth END_BLOCK ll.
Proof.
  intros L syms o lc ll dc dl Hv Hov.
  destruct (overlay_compress L syms o lc ll dc dl Hv Hov) as [Ec _]. rewrite Ec.
  destruct Hov as [Hok [_ [_ [Hcodes [Hend _]]]]].
  destruct (compress_sep_spec syms o lc ll dc dl Hok (fun x Hx => conj (Hv x Hx) (Hcodes x Hx)))
    as [[_ [Ok1 _]] [B1 _]].
  destruct (send_code_spec (compress_sep o lc ll dc dl syms) END_BLOCK lc ll Ok1 Hend) as [B2 [_ [Ok2 _]]].
  destruct Ok2 as [V2 _]. split; [exact V2|]. rewrite B2, B1. lia.
Qed.

(** ** The reference code R1 in the form of [ds_dd_opt] *)

Lemma forallb_zseq' : forall f a n, forallb f (Heap.zseq a n) = true ->
  forall i, a <= i < a + Z.of_nat n -> f i = true.
Proof.
  intros f a n H i Hi. rewrite forallb_forall in H. apply H. apply Heap.in_zseq. exact Hi.
Qed.

Lemma r1_ll_range30 : forall c, 0 <= c < L_CODES -> 1 <= Znth c r1_ll <= 30.
Proof.
  intros c Hc.
  assert (H := forallb_zseq' (fun c => (1 <=? Znth c r1_ll) && (Znth c r1_ll <=? 30)) 0 286
                 ltac:(vm_compute; reflexivity) c ltac:(unfold L_CODES in Hc; lia)).
  apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1, H2. lia.
Qed.

Lemma r1_dl_5 : forall d, 0 <= d < D_CODES -> Znth d r1_dl = 5.
Proof.
  intros d Hd.
  assert (H := forallb_zseq' (fun d => Znth d r1_dl =? 5) 0 30
                 ltac:(vm_compute; reflexivity) d ltac:(unfold D_CODES in Hd; lia)).
  apply Z.eqb_eq in H. exact H.
Qed.

Lemma r1_ll_kraft30 : zsum L_CODES (fun c => 2 ^ (30 - Znth c r1_ll)) <= 2 ^ 30.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

Lemma r1_dl_kraft30 : zsum D_CODES (fun _ => 2 ^ (30 - 5)) <= 2 ^ 30.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

Lemma lfreq_nonneg : forall syms c, 0 <= lfreq syms c.
Proof. intros. unfold lfreq. pose proof (Zlength_nonneg (filter (fun s => lcode_of s =? c) syms)). destruct (c =? END_BLOCK); lia. Qed.

Lemma dfreq_nonneg : forall syms d, 0 <= dfreq syms d.
Proof. intros. unfold dfreq. apply Zlength_nonneg. Qed.

(** The data of a block with [buf = NULL] under the Huffman lengths: at most R1's cost plus the repair overhead
    and the forced-node terms. *)
Lemma null_data : forall s syms B s' olb slb mbi ll dl0 dd dd0 Hh E,
  dyn_sum s syms B s' olb slb mbi ll dl0 dd dd0 Hh E ->
  (forall x, In x syms -> valid_sym (fst x) (snd x)) -> syms <> [] -> tr_lit_bufsize s = 16384 ->
  dyn_data syms ll dl0 + E <= blk_bits r1_ll r1_dl syms + Znth END_BLOCK r1_ll + 4 + 21600.
Proof.
  intros s syms B s' olb slb mbi ll dl0 dd dd0 Hh E D Hv Hne HL.
  pose proof (ds_dd_repair _ _ _ _ _ _ _ _ _ _ _ _ _ D) as Hrep. rewrite HL in Hrep.
  pose proof (ds_E _ _ _ _ _ _ _ _ _ _ _ _ _ D) as [HE _].
  destruct (ds_dd_opt _ _ _ _ _ _ _ _ _ _ _ _ _ D (fun c => Znth c r1_ll) (fun _ => 5)
              r1_ll_range30 ltac:(intros; lia) r1_ll_kraft30 r1_dl_kraft30 Hne) as [Ol Od].
  rewrite blk_bits_cost, (cost_regroup r1_ll r1_dl syms Hv).
  rewrite (zsum_ext D_CODES (fun d => dfreq syms d * (Znth d r1_dl + xd d)) (fun d => dfreq syms d * 5 + dfreq syms d * xd d))
    by (intros d Hd; rewrite r1_dl_5 by exact Hd; ring).
  rewrite (zsum_ext L_CODES (fun c => lfreq syms c * (Znth c r1_ll + xl c)) (fun c => lfreq syms c * Znth c r1_ll + lfreq syms c * xl c))
    by (intros; ring).
  rewrite !zsum_add.
  unfold dyn_data.
  assert (Hl : zsum L_CODES (fun c => lfreq syms c * (Znth c ll + xl c)) <=
               zsum L_CODES (fun c => (lfreq syms c * Znth c dd + lfreq syms c * Z.max 0 (Znth c ll - Znth c dd)) + lfreq syms c * xl c)).
  { apply zsum_le. intros c _. pose proof (lfreq_nonneg syms c).
    assert (Znth c ll <= Znth c dd + Z.max 0 (Znth c ll - Znth c dd)) by lia. nia. }
  assert (Hd : zsum D_CODES (fun d => dfreq syms d * (Znth d dl0 + xd d)) <=
               zsum D_CODES (fun d => (dfreq syms d * Znth d dd0 + dfreq syms d * Z.max 0 (Znth d dl0 - Znth d dd0)) + dfreq syms d * xd d)).
  { apply zsum_le. intros d _. pose proof (dfreq_nonneg syms d).
    assert (Znth d dl0 <= Znth d dd0 + Z.max 0 (Znth d dl0 - Znth d dd0)) by lia. nia. }
  rewrite !zsum_add in Hl, Hd. cbv beta in Ol, Od. lia.
Qed.

Lemma div8_lt : forall x y, x / 8 < y -> x < 8 * y.
Proof.
  intros x y H. destruct (Z_lt_le_dec x (8 * y)) as [?|Hc]; [lia|].
  assert (y <= x / 8) by (apply Z.div_le_lower_bound; lia). lia.
Qed.

Lemma div8_le : forall x y, x / 8 <= y / 8 -> x <= y + 7.
Proof.
  intros x y H. pose proof (Z.mul_succ_div_gt x 8 ltac:(lia)). pose proof (Z.mul_div_le y 8 ltac:(lia)). lia.
Qed.

Theorem block_bound_proof : dyn_sum_statement -> overlay_statement -> block_bound_statement.
Proof.
  intros Hds Hov s syms buf B last T A Hpre Hlast HL HB Hbuf HT Hb.
  pose proof Hpre as [_ [Hok [Hp0 [Hv7 _]]] [Hsn [Hsl [Hval _]]] _ _ _ _].
  assert (HB0 : 0 <= B) by (rewrite HB; apply blk_len_nonneg; exact Hval).
  rewrite tr_flush_block_prep.
  destruct (Z_lt_le_dec 0 (tr_level s)) as [Hlev|Hlev].
  - destruct (Hds s syms B Hpre Hlev) as (s' & olb & slb & mbi & ll & dl0 & dd & dd0 & Hh & E & D).
    pose proof (ds_prep _ _ _ _ _ _ _ _ _ _ _ _ _ D) as Hp.
    pose proof (ds_keep _ _ _ _ _ _ _ _ _ _ _ _ _ D) as [Ko [KL [Ks Kst]]].
    assert (Hcall := Hov s syms buf B last Hpre Hlast). unfold flush_call in Hcall. rewrite Hp in Hcall.
    rewrite Hp. cbv beta iota zeta in Hcall. cbv beta iota.
    set (os := send_bits (tr_out s') (Z.shiftl STATIC_TREES 1 + last) 3) in *.
    set (od := send_all_trees (send_bits (tr_out s') (Z.shiftl DYN_TREES 1 + last) 3) (tr_ltree s') (tr_dtree s')
                 (tr_bltree s') (tr_lmax s' + 1) (tr_dmax s' + 1) (mbi + 1)) in *.
    rewrite KL, Ks, Hsn.
    assert (Hv3 : forall t, 0 <= t <= 2 -> 0 <= Z.shiftl t 1 + last < 2 ^ 3).
    { intros t Ht. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2. change (2 ^ 3) with 8. lia. }
    assert (Bos : Bits.bitpos os = Bits.bitpos (tr_out s) + 3).
    { unfold os. rewrite Ko.
      destruct (send_bits_spec (tr_out s) (Z.shiftl STATIC_TREES 1 + last) 3 Hok ltac:(lia)
                  (Hv3 STATIC_TREES ltac:(unfold STATIC_TREES; lia))) as [Hx _]. exact Hx. }
    assert (Bod : Bits.bitpos od = Bits.bitpos (tr_out s) + 3 + Hh).
    { unfold od. rewrite Ko.
      destruct (send_bits_spec (tr_out s) (Z.shiftl DYN_TREES 1 + last) 3 Hok ltac:(lia)
                  (Hv3 DYN_TREES ltac:(unfold DYN_TREES; lia))) as [Hx [_ [Ok1 _]]].
      destruct (ds_hdr _ _ _ _ _ _ _ _ _ _ _ _ _ D _ Ok1) as [_ [Hy _]]. unfold Header.bitpos in Hy. unfold Bits.bitpos in *. lia. }
    assert (Sb : overlay_ok (tr_lit_bufsize s) syms (os, static_ltree_code, static_ltree_len, static_dtree_code, static_dtree_len) ->
                 0 <= o_bi_valid (compress_block os (tr_lit_bufsize s) (3 * Zlength syms) static_ltree_code
                                    static_ltree_len static_dtree_code static_dtree_len) <= 16 /\
                 Bits.bitpos (compress_block os (tr_lit_bufsize s) (3 * Zlength syms) static_ltree_code
                                static_ltree_len static_dtree_code static_dtree_len) =
                   Bits.bitpos (tr_out s) + 3 + stat_data syms).
    { intros Hx. destruct (call_bits _ _ _ _ _ _ _ Hval Hx) as [V1 B1]. split; [exact V1|]. rewrite B1, Bos.
      pose proof (ds_cost_stat _ _ _ _ _ _ _ _ _ _ _ _ _ D). lia. }
    assert (Db : overlay_ok (tr_lit_bufsize s) syms (od, fc (tr_ltree s'), dl (tr_ltree s'), fc (tr_dtree s'), dl (tr_dtree s')) ->
                 0 <= o_bi_valid (compress_block od (tr_lit_bufsize s) (3 * Zlength syms) (fc (tr_ltree s'))
                                    (dl (tr_ltree s')) (fc (tr_dtree s')) (dl (tr_dtree s'))) <= 16 /\
                 Bits.bitpos (compress_block od (tr_lit_bufsize s) (3 * Zlength syms) (fc (tr_ltree s'))
                                (dl (tr_ltree s')) (fc (tr_dtree s')) (dl (tr_dtree s'))) =
                   Bits.bitpos (tr_out s) + 3 + Hh + dyn_data syms ll dl0).
    { intros Hx. destruct (call_bits _ _ _ _ _ _ _ Hval Hx) as [V1 B1]. split; [exact V1|]. rewrite B1, Bod.
      pose proof (ds_cost_guard _ _ _ _ _ _ _ _ _ _ _ _ _ D (length syms)) as G. rewrite firstn_all in G. rewrite G.
      destruct (ds_guard _ _ _ _ _ _ _ _ _ _ _ _ _ D) as [G1 _]. rewrite G1.
      destruct (ds_lmax _ _ _ _ _ _ _ _ _ _ _ _ _ D) as [Hm _].
      rewrite Znth_upd_Znth_other by (unfold END_BLOCK in *; lia).
      pose proof (ds_cost_dyn _ _ _ _ _ _ _ _ _ _ _ _ _ D). lia. }
    destruct (ds_lenb _ _ _ _ _ _ _ _ _ _ _ _ _ D) as [Hslb Holb].
    pose proof (ds_E _ _ _ _ _ _ _ _ _ _ _ _ _ D) as [HE _].
    pose proof (ds_H _ _ _ _ _ _ _ _ _ _ _ _ _ D) as HH.
    destruct buf as [b|].
    + destruct Hbuf as [HB1 HB2].
      assert (Hu : u64 (B + 4) = B + 4) by (unfold u64; apply Z.mod_small; lia).
      rewrite Hu in Hcall |- *.
      destruct (Z.leb_spec (B + 4) olb) as [Hst|Hst].
      * rewrite Ko. destruct (stored_case (tr_out s) b B last T A Hok Hlast HB0 HT Hb) as [V1 B1].
        exact (finish s' (tr_stored_block (tr_out s) b B last, BK_stored) last T (A + B + 5) V1 B1).
      * destruct (Z.eqb_spec slb olb) as [Heq|Hne].
        -- destruct (Sb (Hcall _ eq_refl)) as [V1 B1].
           refine (finish s' (_, BK_static) last T (A + B + 5) V1 _). cbn [fst]. rewrite B1.
           assert (stat_data syms + 10 < 8 * (B + 4)) by (apply div8_lt; lia). lia.
        -- destruct (Db (Hcall _ eq_refl)) as [V1 B1].
           refine (finish s' (_, BK_dynamic) last T (A + B + 5) V1 _). cbn [fst]. rewrite B1.
           destruct ((slb <=? (Hh + dyn_data syms ll dl0 + E + 10) / 8) || (tr_strategy s =? Z_FIXED)); [lia|].
           assert (Hh + dyn_data syms ll dl0 + E + 10 < 8 * (B + 4)) by (apply div8_lt; lia). lia.
    + destruct Hbuf as [HBn [_ Hfix]].
      assert (Hne : syms <> []) by (intros ->; cbv in HB; lia).
      pose proof (null_data _ _ _ _ _ _ _ _ _ _ _ _ _ D Hval Hne HL) as Hnd.
      assert (Hf : Forall (fun x => 0 <= snd x < 256) syms)
        by (apply Forall_forall; intros x Hx; destruct (Hval x Hx); lia).
      assert (Hn : Zlength syms <= 16383) by lia.
      assert (Hby : 32507 <= blk_bytes syms) by (rewrite blk_bytes_len, <- HB; lia).
      destruct (Z.eqb_spec slb olb) as [Heq|Hne'].
      * destruct (Sb (Hcall _ eq_refl)) as [V1 B1].
        refine (finish s' (_, BK_static) last T (A + B + 5) V1 _). cbn [fst]. rewrite B1.
        assert (Hs : stat_data syms <= Hh + (dyn_data syms ll dl0 + E) + 7).
        { assert (Hle : (stat_data syms + 10) / 8 <= (Hh + dyn_data syms ll dl0 + E + 10) / 8).
          { rewrite <- Hslb. destruct (Z.eqb_spec (tr_strategy s) Z_FIXED) as [|_]; [contradiction|].
            rewrite orb_false_r in Holb.
            destruct (Z.leb_spec slb ((Hh + dyn_data syms ll dl0 + E + 10) / 8)); lia. }
          apply div8_le in Hle. lia. }
        pose proof (null_block_bound syms Hh (dyn_data syms ll dl0 + E) 21600 (stat_data syms) Hf Hn Hby
                      ltac:(lia) Hnd Hs ltac:(lia)).
        rewrite blk_bytes_len, <- HB in *. lia.
      * destruct (Db (Hcall _ eq_refl)) as [V1 B1].
        refine (finish s' (_, BK_dynamic) last T (A + B + 5) V1 _). cbn [fst]. rewrite B1.
        pose proof (null_block_bound syms Hh (dyn_data syms ll dl0 + E) 21600 (Hh + dyn_data syms ll dl0) Hf Hn Hby
                      ltac:(lia) Hnd ltac:(lia) ltac:(lia)).
        rewrite blk_bytes_len, <- HB in *. lia.
  - assert (Hp : flush_prep s B = (s, u64 (B + 5), u64 (B + 5), 0)).
    { unfold flush_prep. destruct (Z.gtb_spec (tr_level s) 0); [lia|reflexivity]. }
    rewrite Hp. destruct buf as [b|]; [|lia].
    destruct Hbuf as [HB1 HB2].
    assert (Hu : forall x, 0 <= x < 18446744073709551616 -> u64 x = x) by (intros; unfold u64; apply Z.mod_small; lia).
    rewrite (Hu (B + 4)) by lia. rewrite (Hu (B + 5)) by lia.
    destruct (Z.leb_spec (B + 4) (B + 5)); [|lia].
    destruct (stored_case (tr_out s) b B last T A Hok Hlast HB0 HT Hb) as [V1 B1].
    exact (finish s (tr_stored_block (tr_out s) b B last, BK_stored) last T (A + B + 5) V1 B1).
Qed.
