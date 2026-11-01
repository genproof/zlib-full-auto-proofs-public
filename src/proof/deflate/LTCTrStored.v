(** * TREES part, sub-part STORED: see LTCTrKit.v for the statement and its purpose. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTCTrKit.
Require Import Zlib.proof.huffman.Bits.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** The checked bit-output steps succeed when their bytes fit *)

Lemma st_put_byte_some o m c :
  0 <= o_pending o < Zlength (o_buf o) -> exists m', c_put_byte (o, m) c = Some (put_byte o c, m').
Proof.
  intros H. rewrite c_put_byte_spec.
  replace (in_range (o_pending o) (Zlength (o_buf o))) with true; [eauto|].
  symmetry. unfold in_range. apply andb_true_iff. rewrite Z.leb_le, Z.ltb_lt. lia.
Qed.

Lemma st_put_byte_len o c : Zlength (o_buf (put_byte o c)) = Zlength (o_buf o).
Proof. unfold put_byte. cbn [o_buf]. apply Zlength_upd_Znth_any. Qed.

Lemma st_put_short_some o m w :
  0 <= o_pending o -> o_pending o + 2 <= Zlength (o_buf o) ->
  exists m', c_put_short (o, m) w = Some (put_short o w, m').
Proof.
  intros H1 H2. unfold c_put_short, put_short.
  destruct (st_put_byte_some o m (Z.land w 255)) as [m1 E1]; [lia|]. rewrite E1. cbn [bind].
  apply st_put_byte_some. rewrite st_put_byte_len. unfold put_byte. cbn [o_pending]. lia.
Qed.

Lemma st_send_bits_some o m v l :
  0 <= o_bi_valid o <= 16 -> 0 <= o_pending o ->
  (16 - l < o_bi_valid o -> o_pending o + 2 <= Zlength (o_buf o)) ->
  exists m', c_send_bits (o, m) v l = Some (send_bits o v l, m').
Proof.
  intros Hv Hp Hf. unfold c_send_bits, send_bits.
  replace ((0 <=? o_bi_valid o) && (o_bi_valid o <=? Buf_size)) with true.
  2: { symmetry. apply andb_true_iff. unfold Buf_size. rewrite !Z.leb_le. lia. }
  cbn [guard bind].
  destruct (Z.gtb_spec (o_bi_valid o) (Buf_size - l)) as [G|G]; [|eauto].
  unfold Buf_size in G.
  destruct (st_put_short_some (set_bits o (u16 (Z.lor (o_bi_buf o) (Z.shiftl (u16 v) (o_bi_valid o))))
                                 (o_bi_valid o)) m
              (u16 (Z.lor (o_bi_buf o) (Z.shiftl (u16 v) (o_bi_valid o))))) as [m1 E1].
  { unfold set_bits. cbn [o_pending]. lia. }
  { unfold set_bits. cbn [o_pending o_buf]. lia. }
  rewrite E1. cbn [bind]. eauto.
Qed.

Lemma st_bi_windup_some o m :
  bits_ok o -> o_pending o + (o_bi_valid o + 7) / 8 <= Zlength (o_buf o) ->
  exists m', c_bi_windup (o, m) = Some (bi_windup o, m').
Proof.
  intros [Hv [Hb Hp]] Hf. unfold c_bi_windup, bi_windup.
  replace ((0 <=? o_bi_valid o) && (o_bi_valid o <=? 16)) with true.
  2: { symmetry. apply andb_true_iff. rewrite !Z.leb_le. lia. }
  cbn [guard bind].
  destruct (Z.gtb_spec (o_bi_valid o) 8) as [G|G].
  - assert (2 <= (o_bi_valid o + 7) / 8) by (apply Z.div_le_lower_bound; lia).
    destruct (st_put_short_some o m (o_bi_buf o)) as [m1 E1]; [lia|lia|].
    rewrite E1. cbn [bind]. eauto.
  - destruct (Z.gtb_spec (o_bi_valid o) 0) as [G'|G'].
    + assert (1 <= (o_bi_valid o + 7) / 8) by (apply Z.div_le_lower_bound; lia).
      destruct (st_put_byte_some o m (o_bi_buf o)) as [m1 E1]; [lia|].
      rewrite E1. cbn [bind]. eauto.
    + cbn [bind]. eauto.
Qed.

Lemma st_div8 p v : (8 * p + v + 7) / 8 = p + (v + 7) / 8.
Proof.
  replace (8 * p + v + 7) with (v + 7 + p * 8) by lia. rewrite Z.div_add by lia. lia.
Qed.

Theorem stored_some : stored_statement.
Proof.
  intros o m b sl last Hok Hm Hl Hsl Hfit.
  assert (Hval : 0 <= Z.shiftl STORED_BLOCK 1 + last < 2 ^ 3) by (unfold STORED_BLOCK; simpl; lia).
  pose proof Hok as [Hv [Hbb Hp]].
  (* send_bits *)
  destruct (st_send_bits_some o m (Z.shiftl STORED_BLOCK 1 + last) 3) as [m1 E1]; [lia|lia| |].
  { intros G. assert (2 <= (o_bi_valid o + 3 + 7) / 8) by (apply Z.div_le_lower_bound; lia). lia. }
  destruct (send_bits_spec o (Z.shiftl STORED_BLOCK 1 + last) 3 Hok ltac:(lia) Hval)
    as [S1 [_ [S3 [_ [S5 [S6 _]]]]]].
  set (o1 := send_bits o (Z.shiftl STORED_BLOCK 1 + last) 3) in *.
  (* bi_windup *)
  assert (P1 : o_pending o1 + (o_bi_valid o1 + 7) / 8 = o_pending o + (o_bi_valid o + 3 + 7) / 8).
  { rewrite <- !st_div8. unfold bitpos in S1. f_equal. lia. }
  destruct (st_bi_windup_some o1 m1) as [m2 E2]; [exact S3|lia|].
  destruct (bi_windup_spec o1 S3) as [W1 [W2 [_ [_ [_ [W6 _]]]]]].
  set (o2 := bi_windup o1) in *.
  assert (0 <= (o_bi_valid o1 + 7) / 8) by (destruct S3 as [? _]; apply Z.div_pos; lia).
  (* LEN, NLEN *)
  destruct (st_put_short_some o2 m2 (u16 sl)) as [m3 E3]; [lia|lia|].
  destruct (put_short_spec o2 (u16 sl)) as [Q1 [_ [_ [_ [Q5 _]]]]].
  set (o3 := put_short o2 (u16 sl)) in *.
  destruct (st_put_short_some o3 m3 (u16 (Z.lnot sl))) as [m4 E4]; [lia|lia|].
  destruct (put_short_spec o3 (u16 (Z.lnot sl))) as [R1 [_ [_ [_ [R5 _]]]]].
  set (o4 := put_short o3 (u16 (Z.lnot sl))) in *.
  assert (Ex : exists r, c_tr_stored_block (o, m) b sl last = Some r).
  { unfold c_tr_stored_block.
    rewrite E1. cbn [bind]. rewrite E2. cbn [bind]. rewrite E3. cbn [bind]. rewrite E4. cbn [bind].
    destruct (Z.eqb_spec sl 0) as [Z0|Z0]; cbn [negb].
    - cbn [bind]. eauto.
    - replace ((0 <? sl) && (sl <=? Zlength b)) with true.
      2: { symmetry. apply andb_true_iff. rewrite Z.ltb_lt, Z.leb_le. lia. }
      replace (o_pending o4 + sl <=? Zlength (o_buf o4)) with true.
      2: { symmetry. rewrite Z.leb_le. lia. }
      cbn [guard bind]. eauto. }
  destruct Ex as [[o' m'] E]. exists m'. rewrite E.
  pose proof (crel_tr_stored_block o m b sl last _ E) as Q. cbn [fst] in Q. subst o'. reflexivity.
Qed.
