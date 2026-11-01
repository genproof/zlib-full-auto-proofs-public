(* The bits that the mains of rj_bad_block and rj_far_back write (BBFacts.bb_bits_stmt, FBFacts.fb_bits_stmt), from
   the model of the bit writer (BWModel.v). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.rfc1951.DecKit.
Require Import Zlib.proof.harness.bit_writer.BWModel.
Require Import Zlib.proof.harness.bit_writer.BBFacts.
Require Import Zlib.proof.harness.bit_writer.FBFacts.
Import ListNotations.
Local Open Scope Z_scope.

(* a Huffman code of n bits has n bits *)
Lemma bw_bits_msb_len : forall v n, 0 <= n -> Zlength (bits_msb v n) = n.
Proof. intros. unfold bits_msb. rewrite Zlength_rev. apply dkit_bits_le_len. auto. Qed.

(* two writes one after the other are one write of the concatenated bits *)
Lemma bw_write_bits_join : forall S q a q' b, q' = q + Zlength a ->
  write_bits (write_bits S q a) q' b = write_bits S q (a ++ b).
Proof. intros. subst q'. symmetry. apply write_bits_app. Qed.

(* the literals are bytes, i.e. literal symbols *)
Lemma bw_lits_range : forall lits, is_bytes lits -> Forall (fun l => 0 <= l < 256) lits.
Proof.
  intros lits H. eapply Forall_impl; [|exact H]. intros l Hl. simpl in Hl.
  change Integers.Byte.max_unsigned with 255 in Hl. lia.
Qed.

(* the bits of the written stream when the writes are one write of B from bit q *)
Lemma bw_window : forall S0 q B, is_bytes S0 -> 0 <= q -> q + Zlength B <= 8 * Zlength S0 ->
  Zlength (write_bits S0 q B) = Zlength S0 /\ is_bytes (write_bits S0 q B) /\
  sublist q (q + Zlength B) (bytes_bits (write_bits S0 q B)) = B.
Proof.
  intros S0 q B HS Hq HB. destruct (write_bits_ok B S0 q HS Hq HB) as (H1 & H2 & H3).
  split; [exact H1|]. split; [exact H2|]. rewrite H3.
  pose proof (dkit_bytes_bits_len S0). pose proof (Zlength_nonneg B).
  assert (HX: Zlength (sublist 0 q (bytes_bits S0)) = q) by (rewrite Zlength_sublist; lia).
  rewrite <- HX at 1 2. apply dkit_sublist_mid.
Qed.

(* the length of a concatenation of written elements; LL: lits_len lits = |the literals' codes| *)
Ltac bw_len LL :=
  repeat first [ rewrite Zlength_app | rewrite bw_bits_msb_len by lia | rewrite dkit_bits_le_len by lia
               | rewrite <- LL ]; lia.

Lemma bw_bb_bits : bb_bits_stmt.
Proof.
  intros S0 kind which lits Hok. destruct Hok as (Hk & Hw & _ & Hlb & _ & HS0 & HS0n & _).
  destruct (put_lits_send lits (put_bits_m S0 1 (bb_btype kind) 2 0) 3 (bw_lits_range lits Hlb)) as [PL LL].
  pose proof (lits_len_bounds lits) as LB. pose proof (Zlength_nonneg lits).
  set (L := concat (map (send_sym fixed_ll) lits)) in *.
  assert (HT: Zlength (bb_tail_bits kind which) <= 12).
  { unfold bb_tail_bits. destruct (kind =? 2); [bw_len LL|]. destruct (kind =? 3); [bw_len LL|].
    destruct (kind =? 4); [bw_len LL|]. rewrite Zlength_nil. lia. }
  assert (E: bb_bytes S0 kind which lits = write_bits S0 1 (bits_le (bb_btype kind) 2 ++ L ++ bb_tail_bits kind which)).
  { unfold bb_bytes, bb_tail_bits. cbv zeta. rewrite PL. unfold put_bits_m, pb_bits. cbn [Z.eqb].
    rewrite bw_write_bits_join by bw_len LL.
    destruct (kind =? 2); [rewrite bw_write_bits_join by bw_len LL; reflexivity|].
    destruct (kind =? 3); [rewrite !bw_write_bits_join by bw_len LL; reflexivity|].
    destruct (kind =? 4); [rewrite bw_write_bits_join by bw_len LL; reflexivity|].
    rewrite !app_nil_r. reflexivity. }
  cbv zeta. rewrite E.
  assert (HB: Zlength (bits_le (bb_btype kind) 2 ++ L ++ bb_tail_bits kind which) = 2 + lits_len lits + Zlength (bb_tail_bits kind which))
    by (rewrite !Zlength_app, dkit_bits_le_len, <- LL by lia; lia).
  rewrite HB. destruct (bw_window S0 1 (bits_le (bb_btype kind) 2 ++ L ++ bb_tail_bits kind which) HS0 ltac:(lia)
    ltac:(rewrite HB; pose proof (Zlength_nonneg (bb_tail_bits kind which)); lia)) as (H1 & H2 & H3).
  rewrite HB in H3. split; [exact H1|]. split; [exact H2|]. split; [pose proof (Zlength_nonneg (bb_tail_bits kind which)); lia|].
  exact H3.
Qed.

Lemma bw_fb_bits : fb_bits_stmt.
Proof.
  intros S0 fin lits lc lx dc extra Hok.
  destruct Hok as (Hf & Hlb & Hln & Hlc & Hlx & Hdc & Hex & _ & HS0 & HS0n).
  destruct (put_lits_send lits (put_bits_m (put_bits_m S0 0 fin 1 0) 1 1 2 0) 3 (bw_lits_range lits Hlb)) as [PL LL].
  pose proof (lits_len_bounds lits) as LB. pose proof (Zlength_nonneg lits).
  set (L := concat (map (send_sym fixed_ll) lits)) in *.
  assert (HLB: 0 <= fb_lbits lc <= 5).
  { unfold fb_lbits. destruct (andb (265 <=? lc) (lc <=? 284)) eqn:E; [|lia].
    rewrite andb_true_iff, !Z.leb_le in E.
    assert ((lc - 261) / 4 < 6) by (apply Z.div_lt_upper_bound; lia).
    assert (0 <= (lc - 261) / 4) by (apply Z.div_pos; lia). lia. }
  assert (HDB: 0 <= fb_dbits dc <= 13).
  { unfold fb_dbits. destruct (4 <=? dc) eqn:E; [|lia]. rewrite Z.leb_le in E.
    assert (2 <= dc / 2) by (apply Z.div_le_lower_bound; lia).
    assert (dc / 2 < 15) by (apply Z.div_lt_upper_bound; lia). lia. }
  assert (E: fb_bytes S0 fin lits lc lx dc extra = write_bits S0 0 (fb_bits fin lits lc lx dc extra)).
  { unfold fb_bytes, fb_bits. cbv zeta. rewrite PL. unfold put_bits_m, pb_bits. cbn [Z.eqb].
    destruct (lc <? 280); rewrite !bw_write_bits_join by bw_len LL; reflexivity. }
  cbv zeta. rewrite E.
  assert (HB: Zlength (fb_bits fin lits lc lx dc extra) <= 34 + lits_len lits).
  { unfold fb_bits. fold L. destruct (lc <? 280); bw_len LL. }
  pose proof (Zlength_nonneg (fb_bits fin lits lc lx dc extra)).
  destruct (bw_window S0 0 (fb_bits fin lits lc lx dc extra) HS0 ltac:(lia) ltac:(lia)) as (H1 & H2 & H3).
  split; [exact H1|]. split; [exact H2|]. split; [lia|]. exact H3.
Qed.

Lemma bw_bits : bb_bits_stmt /\ fb_bits_stmt.
Proof. exact (conj bw_bb_bits bw_fb_bits). Qed.
