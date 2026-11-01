(** * Bit output of the trees.c model: accounting of send_bits and friends, symbol costs, and the overlay
    non-interference of compress_block (the symbols it reads are not overwritten when the output stays below them).

    [bitpos o = 8 * pending + bi_valid] is the number of bits written since pending was 0 (bits in pending_buf plus
    bits in bi_buf).  Every writer only writes bytes at indices in [pending, pending'), so the bytes at or above the
    final [pending] are untouched; compress_block's loop over the overlaid buffer then computes exactly what the
    loop over a separate symbol list computes ([compress_sep]) as long as the output position stays at or below the
    next unread symbol. *)

From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.huffman.Model.
Import ListNotations.
Local Open Scope Z_scope.

(** ** General list facts *)

Lemma Zlength_upd_Znth_any : forall {A} i (l : list A) x, Zlength (upd_Znth i l x) = Zlength l.
Proof.
  intros. destruct (Z_le_gt_dec 0 i); destruct (Z_lt_ge_dec i (Zlength l)).
  - rewrite upd_Znth_Zlength; auto; lia.
  - rewrite upd_Znth_out_of_range; auto; lia.
  - rewrite upd_Znth_out_of_range; auto; lia.
  - rewrite upd_Znth_out_of_range; auto; lia.
Qed.

Lemma Znth_upd_Znth_other : forall i j (l : list Z) x, i <> j -> Znth j (upd_Znth i l x) = Znth j l.
Proof.
  intros i j l x Hij.
  destruct (Z_le_gt_dec 0 i); [destruct (Z_lt_ge_dec i (Zlength l))|].
  - destruct (Z_lt_ge_dec j 0) as [Hj|Hj]; [rewrite !Znth_underflow by lia; reflexivity|].
    destruct (Z_lt_ge_dec j (Zlength l)) as [Hj'|Hj'].
    + apply upd_Znth_diff; lia.
    + rewrite !Znth_overflow; auto; rewrite ?upd_Znth_Zlength; lia.
  - rewrite upd_Znth_out_of_range; auto; lia.
  - rewrite upd_Znth_out_of_range; auto; lia.
Qed.

Lemma lor_bound : forall a b n, 0 <= n -> 0 <= a < 2 ^ n -> 0 <= b < 2 ^ n -> 0 <= Z.lor a b < 2 ^ n.
Proof.
  intros a b n Hn Ha Hb. split; [apply Z.lor_nonneg; lia|].
  destruct (Z.eq_dec (Z.lor a b) 0) as [E|E]; [rewrite E; apply Z.pow_pos_nonneg; lia|].
  assert (Hpos : 0 < Z.lor a b) by (assert (0 <= Z.lor a b) by (apply Z.lor_nonneg; lia); lia).
  assert (Hn1 : 1 <= n).
  { destruct (Z.eq_dec n 0) as [->|]; [|lia]. simpl in Ha, Hb.
    assert (a = 0) by lia. assert (b = 0) by lia. subst. simpl in E. congruence. }
  assert (Hla : Z.log2 a < n).
  { destruct (Z.eq_dec a 0) as [->|]; [simpl; lia|]. apply Z.log2_lt_pow2; lia. }
  assert (Hlb : Z.log2 b < n).
  { destruct (Z.eq_dec b 0) as [->|]; [simpl; lia|]. apply Z.log2_lt_pow2; lia. }
  apply Z.log2_lt_pow2; auto. rewrite Z.log2_lor by lia. lia.
Qed.

Lemma u16_id : forall x, 0 <= x < 65536 -> u16 x = x.
Proof. intros; unfold u16; apply Z.mod_small; lia. Qed.

(** ** Output states and the bit position *)

Lemma set_bits_pending : forall o bb bv, o_pending (set_bits o bb bv) = o_pending o. Proof. reflexivity. Qed.
Lemma set_bits_buf : forall o bb bv, o_buf (set_bits o bb bv) = o_buf o. Proof. reflexivity. Qed.
Lemma set_bits_bi_buf : forall o bb bv, o_bi_buf (set_bits o bb bv) = bb. Proof. reflexivity. Qed.
Lemma set_bits_bi_valid : forall o bb bv, o_bi_valid (set_bits o bb bv) = bv. Proof. reflexivity. Qed.
Lemma set_bits_used : forall o bb bv, o_bi_used (set_bits o bb bv) = o_bi_used o. Proof. reflexivity. Qed.
Ltac proj := cbn [o_pending o_bi_buf o_bi_valid o_bi_used o_buf] in *;
  rewrite ?set_bits_pending, ?set_bits_buf, ?set_bits_bi_buf, ?set_bits_bi_valid, ?set_bits_used in *.

Definition bitpos (o : outbuf) : Z := 8 * o_pending o + o_bi_valid o.

(** The invariant zlib keeps between writes: 0..16 valid bits, no garbage above them. *)
Definition bits_ok (o : outbuf) : Prop :=
  0 <= o_bi_valid o <= 16 /\ 0 <= o_bi_buf o < 2 ^ o_bi_valid o /\ 0 <= o_pending o.

(** A write from [o] to [o']: pending grows, the buffer length and bi_used are kept, and only the bytes in
    [pending, pending') change. *)
Definition writes (o o' : outbuf) : Prop :=
  o_pending o <= o_pending o' /\ Zlength (o_buf o') = Zlength (o_buf o) /\ o_bi_used o' = o_bi_used o /\
  forall i, i < o_pending o \/ o_pending o' <= i -> Znth i (o_buf o') = Znth i (o_buf o).

Lemma writes_refl : forall o, writes o o.
Proof. intros; repeat split; auto; lia. Qed.

Lemma writes_trans : forall o1 o2 o3, writes o1 o2 -> writes o2 o3 -> writes o1 o3.
Proof.
  intros o1 o2 o3 [P1 [L1 [U1 B1]]] [P2 [L2 [U2 B2]]].
  split; [lia|]. split; [congruence|]. split; [congruence|].
  intros i Hi. rewrite B2 by lia. apply B1; lia.
Qed.

(** ** put_byte, put_short *)

Lemma put_byte_spec : forall o c,
  let o' := put_byte o c in
  o_pending o' = o_pending o + 1 /\ o_bi_buf o' = o_bi_buf o /\ o_bi_valid o' = o_bi_valid o /\ writes o o'.
Proof.
  intros o c o'. unfold o', put_byte, writes; simpl.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [lia|]. split; [apply Zlength_upd_Znth_any|]. split; [reflexivity|].
  intros i Hi. apply Znth_upd_Znth_other. lia.
Qed.

Lemma put_short_spec : forall o w,
  let o' := put_short o w in
  o_pending o' = o_pending o + 2 /\ o_bi_buf o' = o_bi_buf o /\ o_bi_valid o' = o_bi_valid o /\ writes o o'.
Proof.
  intros o w o'. unfold o', put_short.
  destruct (put_byte_spec o (Z.land w 255)) as [P1 [B1 [V1 W1]]].
  destruct (put_byte_spec (put_byte o (Z.land w 255)) (Z.shiftr (u16 w) 8)) as [P2 [B2 [V2 W2]]].
  split; [lia|]. split; [congruence|]. split; [congruence|]. eapply writes_trans; eauto.
Qed.

Lemma set_bits_writes : forall o bb bv, writes o (set_bits o bb bv).
Proof. intros; unfold set_bits, writes; simpl. repeat split; auto; lia. Qed.

(** ** send_bits *)

Lemma send_bits_spec : forall o value length,
  bits_ok o -> 1 <= length <= 16 -> 0 <= value < 2 ^ length ->
  let o' := send_bits o value length in
  bitpos o' = bitpos o + length /\ 1 <= o_bi_valid o' <= 16 /\ bits_ok o' /\
  (o_pending o' = o_pending o \/ o_pending o' = o_pending o + 2) /\ writes o o'.
Proof.
  intros o value length [Hv [Hb Hp]] Hl Hval o'.
  assert (H16 : 2 ^ length <= 2 ^ 16) by (apply Z.pow_le_mono_r; lia).
  assert (Hu : u16 value = value) by (apply u16_id; change (2 ^ 16) with 65536 in H16; lia).
  unfold o', send_bits, Buf_size. rewrite Hu.
  destruct (Z.gtb_spec (o_bi_valid o) (16 - length)) as [Hc|Hc].
  - (* the buffer overflows: two bytes out *)
    set (bb := u16 (Z.lor (o_bi_buf o) (Z.shiftl value (o_bi_valid o)))).
    destruct (put_short_spec (set_bits o bb (o_bi_valid o)) bb) as [P [B [V W]]].
    proj.
    assert (Hsh : 0 <= Z.shiftr value (16 - o_bi_valid o) < 2 ^ (o_bi_valid o + length - 16)).
    { rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; [lia|apply Z.pow_pos_nonneg; lia]|].
      apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia|].
      rewrite <- Z.pow_add_r by lia. replace (16 - o_bi_valid o + (o_bi_valid o + length - 16)) with length
        by lia. lia. }
    split; [unfold bitpos; proj; lia|]. split; [proj; lia|].
    split; [unfold bits_ok; proj; repeat split; try lia|].
    split; [right; proj; lia|].
    eapply writes_trans; [apply set_bits_writes|]. eapply writes_trans; [exact W|]. apply set_bits_writes.
  - (* the bits fit *)
    assert (Hsh : 0 <= Z.shiftl value (o_bi_valid o) < 2 ^ (o_bi_valid o + length)).
    { rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.pow_add_r by lia.
      assert (0 < 2 ^ o_bi_valid o) by (apply Z.pow_pos_nonneg; lia).
      split; [apply Z.mul_nonneg_nonneg; lia|].
      rewrite (Z.mul_comm (2 ^ o_bi_valid o)). apply Z.mul_lt_mono_pos_r; lia. }
    assert (Hbb : 0 <= o_bi_buf o < 2 ^ (o_bi_valid o + length)).
    { split; [lia|]. eapply Z.lt_le_trans; [apply Hb|]. apply Z.pow_le_mono_r; lia. }
    assert (Hlor := lor_bound _ _ (o_bi_valid o + length) ltac:(lia) Hbb Hsh).
    assert (H16' : 2 ^ (o_bi_valid o + length) <= 65536)
      by (change 65536 with (2 ^ 16); apply Z.pow_le_mono_r; lia).
    rewrite u16_id by lia.
    split; [unfold bitpos; proj; lia|]. split; [proj; lia|].
    split; [unfold bits_ok; proj; repeat split; lia|]. split; [left; proj; reflexivity|].
    apply set_bits_writes.
Qed.

Corollary send_bits_pending : forall o value length,
  bits_ok o -> 1 <= length <= 16 -> 0 <= value < 2 ^ length ->
  let o' := send_bits o value length in
  8 * o_pending o' + 1 <= bitpos o' /\ (Z.even (o_pending o) = true -> Z.even (o_pending o') = true).
Proof.
  intros o value length H1 H2 H3 o'.
  destruct (send_bits_spec o value length H1 H2 H3) as [Hbp [Hv [_ [Hp _]]]]. fold o' in Hbp, Hv, Hp.
  split; [unfold bitpos; lia|]. intros He. destruct Hp as [-> | ->]; auto.
  rewrite Z.even_add. rewrite He. reflexivity.
Qed.

(** ** send_code *)

Definition code_ok (codes lens : list Z) (c : Z) : Prop :=
  1 <= Znth c lens <= 15 /\ 0 <= Znth c codes < 2 ^ Znth c lens.

Lemma send_code_spec : forall o c codes lens,
  bits_ok o -> code_ok codes lens c ->
  let o' := send_code o c codes lens in
  bitpos o' = bitpos o + Znth c lens /\ 1 <= o_bi_valid o' <= 16 /\ bits_ok o' /\
  (o_pending o' = o_pending o \/ o_pending o' = o_pending o + 2) /\ writes o o'.
Proof.
  intros o c codes lens Ho [Hl Hc] o'. unfold o', send_code.
  apply send_bits_spec; auto; lia.
Qed.

(** ** bi_flush, bi_windup *)

Lemma bi_flush_spec : forall o, bits_ok o ->
  let o' := bi_flush o in
  bitpos o' = bitpos o /\ bits_ok o' /\ o_bi_valid o' <= 7 /\ writes o o'.
Proof.
  intros o [Hv [Hb Hp]] o'. unfold o', bi_flush.
  destruct (Z.eqb_spec (o_bi_valid o) 16) as [E|E].
  - destruct (put_short_spec o (o_bi_buf o)) as [P [B [V W]]].
    unfold set_bits, bitpos, bits_ok. proj.
    split; [lia|]. split; [proj; repeat split; lia|]. split; [lia|].
    eapply writes_trans; [exact W|]. apply set_bits_writes.
  - destruct (Z.geb_spec (o_bi_valid o) 8) as [E8|E8].
    + destruct (put_byte_spec o (o_bi_buf o)) as [P [B [V W]]].
      unfold set_bits, bitpos, bits_ok. proj. rewrite B, V.
      assert (Hsh : 0 <= Z.shiftr (o_bi_buf o) 8 < 2 ^ (o_bi_valid o - 8)).
      { rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|].
        assert (E2 : 2 ^ o_bi_valid o = 2 ^ (o_bi_valid o - 8) * 2 ^ 8)
          by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
        change (2 ^ 8) with 256 in *.
        apply Z.div_lt_upper_bound; lia. }
      split; [lia|]. split; [repeat split; lia|]. split; [lia|].
      eapply writes_trans; [exact W|]. apply set_bits_writes.
    + unfold bitpos, bits_ok. split; [reflexivity|]. split; [repeat split; lia|]. split; [lia|].
      apply writes_refl.
Qed.

Lemma bi_windup_spec : forall o, bits_ok o ->
  let o' := bi_windup o in
  o_pending o' = o_pending o + (o_bi_valid o + 7) / 8 /\ o_bi_valid o' = 0 /\ o_bi_buf o' = 0 /\
  o_bi_used o' = Z.land (o_bi_valid o - 1) 7 + 1 /\
  o_pending o <= o_pending o' /\ Zlength (o_buf o') = Zlength (o_buf o) /\
  (forall i, i < o_pending o \/ o_pending o' <= i -> Znth i (o_buf o') = Znth i (o_buf o)).
Proof.
  intros o [Hv [Hb Hp]] o'. unfold o', bi_windup.
  destruct (Z.gtb_spec (o_bi_valid o) 8) as [E|E].
  - destruct (put_short_spec o (o_bi_buf o)) as [P [B [V [W1 [W2 [W3 W4]]]]]].
    proj. rewrite P in W4. rewrite P, V.
    split; [assert ((o_bi_valid o + 7) / 8 = 2) by (symmetry; apply Z.div_unique with (o_bi_valid o + 7 - 16); lia); lia|].
    repeat split; auto; lia.
  - destruct (Z.gtb_spec (o_bi_valid o) 0) as [E0|E0].
    + destruct (put_byte_spec o (o_bi_buf o)) as [P [B [V [W1 [W2 [W3 W4]]]]]].
      proj. rewrite P in W4. rewrite P, V.
      split; [assert ((o_bi_valid o + 7) / 8 = 1) by (symmetry; apply Z.div_unique with (o_bi_valid o + 7 - 8); lia); lia|].
      repeat split; auto; lia.
    + proj. assert (o_bi_valid o = 0) by lia.
      split; [rewrite H; change ((0 + 7) / 8) with 0; lia|]. repeat split; auto; lia.
Qed.

(** ** Table facts (finite checks) *)

Fixpoint check_from (f : Z -> bool) (d : Z) (n : nat) : bool :=
  match n with O => true | S m => f d && check_from f (d + 1) m end.

Lemma check_from_spec : forall f n d, check_from f d n = true -> forall e, d <= e < d + Z.of_nat n -> f e = true.
Proof.
  intros f n; induction n as [|n IH]; simpl; intros d H e He; [lia|].
  apply andb_true_iff in H. destruct H as [H1 H2].
  destruct (Z.eq_dec e d) as [->|Hne]; auto. apply (IH (d + 1)); auto. lia.
Qed.

Definition len_entry_ok (lc : Z) : bool :=
  let code := Znth lc length_code_tab in
  let x := Znth code extra_lbits in
  (0 <=? code) && (code <=? 28) && (0 <=? x) && (x <=? 5) &&
  ((x =? 0) || ((0 <=? lc - Znth code base_length_tab) && (lc - Znth code base_length_tab <? 2 ^ x))).

Definition dist_entry_ok (d : Z) : bool :=
  let code := d_code d in
  let x := Znth code extra_dbits in
  (0 <=? code) && (code <=? 29) && (0 <=? x) && (x <=? 13) &&
  ((x =? 0) || ((0 <=? d - Znth code base_dist_tab) && (d - Znth code base_dist_tab <? 2 ^ x))).

Lemma len_entries_ok : check_from len_entry_ok 0 (Z.to_nat 256) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma dist_entries_ok : check_from dist_entry_ok 0 (Z.to_nat 32768) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma length_code_facts : forall lc, 0 <= lc <= 255 ->
  let code := Znth lc length_code_tab in
  let x := Znth code extra_lbits in
  0 <= code <= 28 /\ 0 <= x <= 5 /\ (x <> 0 -> 0 <= lc - Znth code base_length_tab < 2 ^ x).
Proof.
  intros lc Hlc code x.
  assert (H := check_from_spec _ _ _ len_entries_ok lc ltac:(rewrite Z2Nat.id; lia)).
  unfold len_entry_ok in H. fold code x in H.
  repeat rewrite andb_true_iff in H. rewrite orb_true_iff, andb_true_iff, Z.eqb_eq in H.
  rewrite !Z.leb_le, Z.ltb_lt in H. lia.
Qed.

Lemma dist_code_facts : forall d, 0 <= d <= 32767 ->
  let code := d_code d in
  let x := Znth code extra_dbits in
  0 <= code <= 29 /\ 0 <= x <= 13 /\ (x <> 0 -> 0 <= d - Znth code base_dist_tab < 2 ^ x).
Proof.
  intros d Hd code x.
  assert (H := check_from_spec _ _ _ dist_entries_ok d ltac:(rewrite Z2Nat.id; lia)).
  unfold dist_entry_ok in H. fold code x in H.
  repeat rewrite andb_true_iff in H. rewrite orb_true_iff, andb_true_iff, Z.eqb_eq in H.
  rewrite !Z.leb_le, Z.ltb_lt in H. lia.
Qed.

(** ** One symbol *)

(** The bits one symbol costs: its literal code, or the length code, the extra length bits, the distance code
    and the extra distance bits. *)
Definition sym_cost (llens dlens : list Z) (dist lc : Z) : Z :=
  if dist =? 0 then Znth lc llens
  else Znth (Znth lc length_code_tab + 257) llens + Znth (Znth lc length_code_tab) extra_lbits +
       Znth (d_code (dist - 1)) dlens + Znth (d_code (dist - 1)) extra_dbits.

Definition valid_sym (dist lc : Z) : Prop := 0 <= lc <= 255 /\ 0 <= dist <= 32768.

(** The codes a symbol uses are proper codes (length 1..15, value below 2^length). *)
Definition sym_codes_ok (lcodes llens dcodes dlens : list Z) (dist lc : Z) : Prop :=
  if dist =? 0 then code_ok lcodes llens lc
  else code_ok lcodes llens (Znth lc length_code_tab + 257) /\ code_ok dcodes dlens (d_code (dist - 1)).

(** A sequence of writes that keeps the invariants. *)
Definition step_ok (o o' : outbuf) : Prop :=
  writes o o' /\ bits_ok o' /\ (Z.even (o_pending o) = true -> Z.even (o_pending o') = true).

Lemma step_ok_trans : forall o1 o2 o3, step_ok o1 o2 -> step_ok o2 o3 -> step_ok o1 o3.
Proof.
  intros o1 o2 o3 [W1 [B1 E1]] [W2 [B2 E2]]. split; [eapply writes_trans; eauto|]. split; auto.
Qed.

Lemma send_bits_step : forall o value length,
  bits_ok o -> 1 <= length <= 16 -> 0 <= value < 2 ^ length ->
  step_ok o (send_bits o value length) /\ bitpos (send_bits o value length) = bitpos o + length /\
  1 <= o_bi_valid (send_bits o value length).
Proof.
  intros o value length H1 H2 H3.
  destruct (send_bits_spec o value length H1 H2 H3) as [Hb [Hv [Hok [Hp W]]]].
  split; [|split; [exact Hb|lia]].
  split; [exact W|]. split; [exact Hok|].
  intros He. destruct Hp as [-> | ->]; auto. rewrite Z.even_add, He. reflexivity.
Qed.

Lemma send_symbol_spec : forall o lcodes llens dcodes dlens dist lc,
  bits_ok o -> valid_sym dist lc -> sym_codes_ok lcodes llens dcodes dlens dist lc ->
  let o' := send_symbol o lcodes llens dcodes dlens dist lc in
  step_ok o o' /\ bitpos o' = bitpos o + sym_cost llens dlens dist lc /\ 1 <= o_bi_valid o'.
Proof.
  intros o lcodes llens dcodes dlens dist lc Ho [Hlc Hd] Hc o'.
  unfold o', send_symbol, sym_cost, sym_codes_ok, LITERALS in *.
  destruct (Z.eqb_spec dist 0) as [Hd0|Hd0].
  - destruct Hc as [Hl Hcv]. unfold send_code. apply send_bits_step; auto; lia.
  - destruct Hc as [[Hl1 Hc1] [Hl2 Hc2]].
    destruct (length_code_facts lc Hlc) as [Hcode [Hx Hext]].
    destruct (dist_code_facts (dist - 1) ltac:(lia)) as [Hdcode [Hdx Hdext]].
    set (code := Znth lc length_code_tab) in *.
    set (dcode := d_code (dist - 1)) in *.
    replace (code + 256 + 1) with (code + 257) by lia.
    unfold send_code.
    destruct (send_bits_step o (Znth (code + 257) lcodes) (Znth (code + 257) llens)) as [S1 [B1 V1]];
      auto; try lia.
    set (o1 := send_bits o (Znth (code + 257) lcodes) (Znth (code + 257) llens)) in *.
    assert (Ho1 : bits_ok o1) by (destruct S1 as [_ [H _]]; exact H).
    (* extra length bits *)
    assert (X1 : step_ok o1 (if negb (Znth code extra_lbits =? 0)
                             then send_bits o1 (lc - Znth code base_length_tab) (Znth code extra_lbits) else o1) /\
                 bitpos (if negb (Znth code extra_lbits =? 0)
                         then send_bits o1 (lc - Znth code base_length_tab) (Znth code extra_lbits) else o1) =
                 bitpos o1 + Znth code extra_lbits /\
                 1 <= o_bi_valid (if negb (Znth code extra_lbits =? 0)
                         then send_bits o1 (lc - Znth code base_length_tab) (Znth code extra_lbits) else o1)).
    { destruct (Z.eqb_spec (Znth code extra_lbits) 0) as [E|E]; simpl.
      - split; [split; [apply writes_refl|split; auto]|]. split; [lia|lia].
      - apply send_bits_step; auto; lia. }
    destruct X1 as [S2 [B2 V2]].
    set (o2 := if negb (Znth code extra_lbits =? 0)
               then send_bits o1 (lc - Znth code base_length_tab) (Znth code extra_lbits) else o1) in *.
    assert (Ho2 : bits_ok o2) by (destruct S2 as [_ [H _]]; exact H).
    destruct (send_bits_step o2 (Znth dcode dcodes) (Znth dcode dlens)) as [S3 [B3 V3]]; auto; try lia.
    set (o3 := send_bits o2 (Znth dcode dcodes) (Znth dcode dlens)) in *.
    assert (Ho3 : bits_ok o3) by (destruct S3 as [_ [H _]]; exact H).
    destruct (Z.eqb_spec (Znth dcode extra_dbits) 0) as [E|E]; simpl.
    + split; [eapply step_ok_trans; [exact S1|eapply step_ok_trans; [exact S2|exact S3]]|].
      split; [lia|lia].
    + destruct (send_bits_step o3 (dist - 1 - Znth dcode base_dist_tab) (Znth dcode extra_dbits))
        as [S4 [B4 V4]]; auto; try lia.
      split; [eapply step_ok_trans; [exact S1|eapply step_ok_trans; [exact S2|
              eapply step_ok_trans; [exact S3|exact S4]]]|].
      split; [lia|lia].
Qed.

(** ** Writes happen only at [pending, pending') (no hypothesis needed) *)

Lemma send_bits_writes : forall o value length, writes o (send_bits o value length).
Proof.
  intros. unfold send_bits.
  destruct (_ >? _).
  - eapply writes_trans; [apply set_bits_writes|].
    match goal with |- writes _ (set_bits (put_short ?o1 ?w) _ _) =>
      eapply writes_trans; [apply (proj2 (proj2 (proj2 (put_short_spec o1 w))))|] end.
    apply set_bits_writes.
  - apply set_bits_writes.
Qed.

Lemma send_code_writes : forall o c codes lens, writes o (send_code o c codes lens).
Proof. intros; apply send_bits_writes. Qed.

Lemma send_symbol_writes : forall o lcodes llens dcodes dlens dist lc,
  writes o (send_symbol o lcodes llens dcodes dlens dist lc).
Proof.
  intros. unfold send_symbol.
  destruct (dist =? 0); [apply send_code_writes|].
  eapply writes_trans; [|destruct (negb _); [apply send_bits_writes|apply writes_refl]].
  eapply writes_trans; [|apply send_code_writes].
  eapply writes_trans; [apply send_code_writes|].
  destruct (negb _); [apply send_bits_writes|apply writes_refl].
Qed.

(** ** The separated block loop *)

Fixpoint compress_sep (o : outbuf) (lcodes llens dcodes dlens : list Z) (syms : list (Z * Z)) : outbuf :=
  match syms with
  | [] => o
  | (d, l) :: r => compress_sep (send_symbol o lcodes llens dcodes dlens d l) lcodes llens dcodes dlens r
  end.

(** The bytes _tr_tally stores for the symbols (for valid symbols: [u8 dist], [u8 (dist >> 8)], [lc]). *)
Definition sym_bytes (syms : list (Z * Z)) : list Z :=
  concat (map (fun s => [fst s mod 256; fst s / 256; snd s]) syms).

Lemma sym_bytes_cons : forall s r, sym_bytes (s :: r) = fst s mod 256 :: fst s / 256 :: snd s :: sym_bytes r.
Proof. reflexivity. Qed.

Lemma Zlength_sym_bytes : forall syms, Zlength (sym_bytes syms) = 3 * Zlength syms.
Proof.
  induction syms as [|s r IH]; [reflexivity|].
  rewrite sym_bytes_cons, !Zlength_cons, IH. lia.
Qed.

Lemma compress_sep_writes : forall syms o lcodes llens dcodes dlens,
  writes o (compress_sep o lcodes llens dcodes dlens syms).
Proof.
  induction syms as [|[d l] r IH]; intros; simpl; [apply writes_refl|].
  eapply writes_trans; [apply send_symbol_writes|]. apply IH.
Qed.

Lemma compress_sep_app : forall a b o lcodes llens dcodes dlens,
  compress_sep o lcodes llens dcodes dlens (a ++ b) =
  compress_sep (compress_sep o lcodes llens dcodes dlens a) lcodes llens dcodes dlens b.
Proof. induction a as [|[d l] r IH]; intros; simpl; auto. Qed.

Lemma read_dist : forall d, 0 <= d <= 65535 ->
  Z.land (d mod 256) 255 + Z.shiftl (Z.land (d / 256) 255) 8 = d.
Proof.
  intros d Hd. change 255 with (Z.ones 8). rewrite !Z.land_ones by lia.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
  rewrite Z.mod_mod by lia. rewrite (Z.mod_small (d / 256)) by (split; [apply Z.div_pos|apply Z.div_lt_upper_bound]; lia).
  assert (H := Z.div_mod d 256 ltac:(lia)). lia.
Qed.

(** The loop of compress_block over the overlaid buffer computes the separated loop, as long as each symbol's
    bytes are still in place when it is read: the bytes at [L + sx ..] hold the remaining symbols and, after the
    first [m] of them, the output position is at most [L + sx + 3m]. *)
Lemma compress_loop_sep : forall rest fuel o sx L sym_next lcodes llens dcodes dlens,
  rest <> [] -> (length rest <= fuel)%nat -> sym_next = sx + 3 * Zlength rest ->
  (forall s, In s rest -> 0 <= fst s <= 65535) ->
  (forall i, 0 <= i < 3 * Zlength rest -> Znth (L + sx + i) (o_buf o) = Znth i (sym_bytes rest)) ->
  (forall m, (1 <= m < length rest)%nat ->
     o_pending (compress_sep o lcodes llens dcodes dlens (firstn m rest)) <= L + sx + 3 * Z.of_nat m) ->
  compress_loop fuel L sym_next lcodes llens dcodes dlens o sx = compress_sep o lcodes llens dcodes dlens rest.
Proof.
  induction rest as [|[d l] r IH]; intros fuel o sx L sym_next lcodes llens dcodes dlens Hne Hf Hsn Hd Hb Hp;
    [congruence|].
  destruct fuel as [|fuel]; [simpl in Hf; lia|].
  assert (Hlen : Zlength ((d, l) :: r) = 1 + Zlength r) by (rewrite Zlength_cons; lia).
  assert (Hr0 := Zlength_nonneg r).
  assert (B0 := Hb 0 ltac:(lia)). assert (B1 := Hb 1 ltac:(lia)). assert (B2 := Hb 2 ltac:(lia)).
  rewrite sym_bytes_cons in B0, B1, B2. rewrite Z.add_0_r in B0.
  rewrite Znth_0_cons in B0. rewrite Znth_pos_cons, Znth_0_cons in B1 by lia.
  rewrite !Znth_pos_cons, Znth_0_cons in B2 by lia. simpl fst in B0, B1. simpl snd in B2.
  cbn [compress_loop compress_sep].
  replace (L + sx + 1) with (L + sx + 1) by lia.
  rewrite B0, B1, B2, read_dist by (apply (Hd (d, l)); left; auto).
  set (o1 := send_symbol o lcodes llens dcodes dlens d l).
  destruct (Z.ltb_spec (sx + 3) sym_next) as [Hlt|Hge].
  - destruct r as [|s r']; [rewrite Hsn in Hlt; simpl in Hlt; lia|].
    assert (Hp1 := Hp 1%nat ltac:(simpl; lia)). simpl firstn in Hp1. cbn [compress_sep] in Hp1. fold o1 in Hp1.
    apply IH; auto.
    + congruence.
    + simpl in Hf |- *; lia.
    + rewrite Hsn, Hlen; lia.
    + intros s0 Hs0; apply Hd; right; auto.
    + intros i Hi.
      destruct (send_symbol_writes o lcodes llens dcodes dlens d l) as [_ [_ [_ W]]]. fold o1 in W.
      rewrite W by (right; simpl in Hp1; lia).
      replace (L + (sx + 3) + i) with (L + sx + (i + 3)) by lia.
      rewrite Hb by lia. rewrite sym_bytes_cons, !Znth_pos_cons by lia.
      replace (i + 3 - 1 - 1 - 1) with i by lia; reflexivity.
    + intros m Hm.
      assert (Hm' := Hp (S m) ltac:(simpl in Hm |- *; lia)). simpl firstn in Hm'. cbn [compress_sep] in Hm'. fold o1 in Hm'.
      rewrite Nat2Z.inj_succ in Hm'. lia.
  - destruct r as [|s r']; [reflexivity|].
    rewrite Hsn in Hge. rewrite !Zlength_cons in Hge. assert (Hz := Zlength_nonneg r'). lia.
Qed.

(** compress_block over the overlaid buffer, for a block of [n >= 1] symbols stored at [L], with sym_next = 3n. *)
Theorem compress_block_sep : forall o L syms lcodes llens dcodes dlens,
  syms <> [] ->
  (forall s, In s syms -> 0 <= fst s <= 65535) ->
  (forall i, 0 <= i < 3 * Zlength syms -> Znth (L + i) (o_buf o) = Znth i (sym_bytes syms)) ->
  (forall m, (1 <= m < length syms)%nat ->
     o_pending (compress_sep o lcodes llens dcodes dlens (firstn m syms)) <= L + 3 * Z.of_nat m) ->
  compress_block o L (3 * Zlength syms) lcodes llens dcodes dlens =
  send_code (compress_sep o lcodes llens dcodes dlens syms) END_BLOCK lcodes llens.
Proof.
  intros o L syms lcodes llens dcodes dlens Hne Hd Hb Hp.
  assert (Hpos : 0 < Zlength syms) by (destruct syms; [congruence|rewrite Zlength_cons; pose proof (Zlength_nonneg syms); lia]).
  unfold compress_block. destruct (Z.eqb_spec (3 * Zlength syms) 0) as [E|E]; [lia|]. simpl negb. cbv iota.
  f_equal. apply compress_loop_sep; auto.
  - rewrite Zlength_correct in *. lia.
  - intros i Hi. rewrite Z.add_0_r. apply Hb; auto.
  - intros m Hm. rewrite Z.add_0_r. apply Hp; auto.
Qed.

Theorem compress_block_empty : forall o L lcodes llens dcodes dlens,
  compress_block o L 0 lcodes llens dcodes dlens = send_code o END_BLOCK lcodes llens.
Proof. reflexivity. Qed.

(** The symbol region as a sublist of the buffer. *)
Lemma sym_region_Znth : forall buf L syms,
  0 <= L -> L + 3 * Zlength syms <= Zlength buf ->
  sublist L (L + 3 * Zlength syms) buf = sym_bytes syms ->
  forall i, 0 <= i < 3 * Zlength syms -> Znth (L + i) buf = Znth i (sym_bytes syms).
Proof.
  intros buf L syms HL HLen E i Hi. rewrite <- E. rewrite Znth_sublist by lia. f_equal; lia.
Qed.

(** Untouched bytes: when symbol [k] is read, the bytes at [L + 3k] and above are the original ones. *)
Lemma compress_sep_untouched : forall o lcodes llens dcodes dlens syms k L,
  o_pending (compress_sep o lcodes llens dcodes dlens (firstn k syms)) <= L + 3 * Z.of_nat k ->
  forall i, L + 3 * Z.of_nat k <= i ->
  Znth i (o_buf (compress_sep o lcodes llens dcodes dlens (firstn k syms))) = Znth i (o_buf o).
Proof.
  intros. destruct (compress_sep_writes (firstn k syms) o lcodes llens dcodes dlens) as [_ [_ [_ W]]].
  apply W. right. lia.
Qed.

(** ** Bit accounting of the separated loop *)

Fixpoint cost_sum (llens dlens : list Z) (syms : list (Z * Z)) : Z :=
  match syms with [] => 0 | (d, l) :: r => sym_cost llens dlens d l + cost_sum llens dlens r end.

Theorem compress_sep_spec : forall syms o lcodes llens dcodes dlens,
  bits_ok o ->
  (forall s, In s syms -> valid_sym (fst s) (snd s) /\ sym_codes_ok lcodes llens dcodes dlens (fst s) (snd s)) ->
  let o' := compress_sep o lcodes llens dcodes dlens syms in
  step_ok o o' /\ bitpos o' = bitpos o + cost_sum llens dlens syms /\
  (syms <> [] -> 1 <= o_bi_valid o').
Proof.
  induction syms as [|[d l] r IH]; intros o lcodes llens dcodes dlens Ho Hs o'.
  - unfold o'; simpl. split; [split; [apply writes_refl|split; auto]|]. split; [lia|]. congruence.
  - unfold o'; cbn [compress_sep cost_sum].
    destruct (Hs (d, l) (or_introl eq_refl)) as [Hv Hc]. simpl in Hv, Hc.
    destruct (send_symbol_spec o lcodes llens dcodes dlens d l Ho Hv Hc) as [S1 [B1 V1]].
    assert (Ho1 : bits_ok (send_symbol o lcodes llens dcodes dlens d l)) by (destruct S1 as [_ [H _]]; exact H).
    destruct (IH (send_symbol o lcodes llens dcodes dlens d l) lcodes llens dcodes dlens Ho1
                (fun s Hs' => Hs s (or_intror Hs'))) as [S2 [B2 V2]].
    split; [eapply step_ok_trans; eauto|]. split; [lia|].
    intros _. destruct r as [|s r']; [simpl; exact V1|]. apply V2. congruence.
Qed.

(** With the hypothesis in bit form (as Overlay.overlay_compress uses it): the strict assertion of zlib
    ([pending < lit_bufsize + sx] after each symbol) and the hypothesis of [compress_block_sep]. *)
Corollary pending_from_bits : forall o lcodes llens dcodes dlens syms L m,
  bits_ok o ->
  (forall s, In s syms -> valid_sym (fst s) (snd s) /\ sym_codes_ok lcodes llens dcodes dlens (fst s) (snd s)) ->
  (1 <= m)%nat ->
  bitpos (compress_sep o lcodes llens dcodes dlens (firstn m syms)) <= 8 * (L + 3 * Z.of_nat m) ->
  (m <= length syms)%nat ->
  o_pending (compress_sep o lcodes llens dcodes dlens (firstn m syms)) < L + 3 * Z.of_nat m.
Proof.
  intros o lcodes llens dcodes dlens syms L m Ho Hs Hm Hb Hle.
  assert (Hs' : forall s, In s (firstn m syms) ->
            valid_sym (fst s) (snd s) /\ sym_codes_ok lcodes llens dcodes dlens (fst s) (snd s))
    by (intros s Hin; apply Hs; eapply firstn_In; eauto).
  destruct (compress_sep_spec (firstn m syms) o lcodes llens dcodes dlens Ho Hs') as [_ [_ V]].
  assert (Hne : firstn m syms <> []).
  { destruct syms; [simpl in Hle; lia|]. destruct m; [lia|]. simpl; congruence. }
  specialize (V Hne). unfold bitpos in Hb. lia.
Qed.
