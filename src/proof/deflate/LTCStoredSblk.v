(** * deflate_stored at level 0: _tr_stored_block
    Statement and design: LTCStoredKit.v and its header. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTCStoredKit.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.
Require Import Zlib.proof.trees.CEquiv Zlib.proof.huffman.BlockStored.

(** ** Helpers: the checked output primitives step like the pure ones, and pending_buf only grows *)

Lemma pb_grow_refl o m : pb_grow o m o m.
Proof. unfold pb_grow. split; [reflexivity|]. split; [reflexivity|]. split; auto. Qed.

Lemma pb_grow_trans o1 m1 o2 m2 o3 m3 :
  pb_grow o1 m1 o2 m2 -> pb_grow o2 m2 o3 m3 -> pb_grow o1 m1 o3 m3.
Proof.
  unfold pb_grow. intros (A & B & C & D) (E & F & G & H).
  split; [congruence|]. split; [congruence|]. split; auto.
Qed.

Lemma mask_after_mono m m' lo hi i : mask_after m m' lo hi -> Znth i m = true -> Znth i m' = true.
Proof.
  intros (Hlh & HL & HP) Hi.
  destruct (Z_le_gt_dec 0 i); [destruct (Z_lt_ge_dec i (Zlength m))|].
  - rewrite HP by lia. destruct ((lo <=? i) && (i <? hi)); auto.
  - rewrite Znth_outofbounds in Hi |- * by lia. exact Hi.
  - rewrite Znth_outofbounds in Hi |- * by lia. exact Hi.
Qed.

Lemma put_byte_step o m c :
  0 <= o_pending o < Zlength (o_buf o) ->
  c_put_byte (o, m) c = Some (put_byte o c, upd_Znth (o_pending o) m true) /\
  pb_grow o m (put_byte o c) (upd_Znth (o_pending o) m true).
Proof.
  intros H. split.
  - unfold c_put_byte, wr, in_range, bind.
    rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
  - unfold pb_grow, put_byte; cbn [o_buf mb_val mb_def].
    split; [apply Zlength_upd_Znth_any|]. split; [apply Zlength_upd_Znth_any|].
    split; [intros i; apply mask_after_mono with (lo := o_pending o) (hi := o_pending o + 1);
            apply mask_after_upd|].
    intros [HL HB]. cbn [mb_val mb_def] in *. unfold mb_ok; cbn [mb_val mb_def].
    split; [rewrite !Zlength_upd_Znth_any; exact HL|].
    rewrite Zlength_upd_Znth_any. intros i Hi Hd.
    destruct (Z.eq_dec i (o_pending o)) as [->|Hne].
    + rewrite upd_Znth_same by lia. apply Z.mod_pos_bound. lia.
    + rewrite upd_Znth_diff in Hd by lia. rewrite upd_Znth_diff by lia. apply HB; auto.
Qed.

Lemma put_short_step o m w :
  0 <= o_pending o -> o_pending o + 2 <= Zlength (o_buf o) ->
  exists m', c_put_short (o, m) w = Some (put_short o w, m') /\ pb_grow o m (put_short o w) m'.
Proof.
  intros H1 H2. unfold c_put_short, put_short.
  destruct (put_byte_step o m (Z.land w 255)) as [E1 G1]; [lia|]. rewrite E1. cbn [bind].
  destruct (put_byte_step (put_byte o (Z.land w 255)) (upd_Znth (o_pending o) m true) (Z.shiftr (u16 w) 8))
    as [E2 G2].
  { unfold put_byte; cbn [o_pending o_buf]. rewrite Zlength_upd_Znth_any. lia. }
  eexists. split; [exact E2|]. eapply pb_grow_trans; eassumption.
Qed.

Lemma send_bits_step o m v l :
  bits_ok o -> 1 <= l <= 16 -> o_pending o + 2 <= Zlength (o_buf o) ->
  exists m', c_send_bits (o, m) v l = Some (send_bits o v l, m') /\ pb_grow o m (send_bits o v l) m'.
Proof.
  intros (Hv & Hb & Hp) Hl Hr. unfold c_send_bits, send_bits.
  replace ((0 <=? o_bi_valid o) && (o_bi_valid o <=? Buf_size)) with true
    by (symmetry; rewrite andb_true_iff, !Z.leb_le; unfold Buf_size; lia).
  cbn [guard bind].
  destruct (o_bi_valid o >? Buf_size - l).
  - set (bb := u16 (Z.lor (o_bi_buf o) (Z.shiftl (u16 v) (o_bi_valid o)))).
    destruct (put_short_step (set_bits o bb (o_bi_valid o)) m bb) as [m1 [E1 G1]];
      [unfold set_bits; cbn [o_pending o_buf]; lia..|].
    rewrite E1. cbn [bind]. eexists. split; [reflexivity|]. exact G1.
  - eexists. split; [reflexivity|]. exact (pb_grow_refl o m).
Qed.

Lemma bi_windup_step o m :
  bits_ok o -> o_pending o + 2 <= Zlength (o_buf o) ->
  exists m', c_bi_windup (o, m) = Some (bi_windup o, m') /\ pb_grow o m (bi_windup o) m'.
Proof.
  intros (Hv & Hb & Hp) Hr. unfold c_bi_windup, bi_windup.
  replace ((0 <=? o_bi_valid o) && (o_bi_valid o <=? 16)) with true
    by (symmetry; rewrite andb_true_iff, !Z.leb_le; lia).
  cbn [guard bind].
  destruct (o_bi_valid o >? 8); [|destruct (o_bi_valid o >? 0)].
  - destruct (put_short_step o m (o_bi_buf o)) as [m1 [E1 G1]]; [lia|lia|].
    rewrite E1. cbn [bind]. eexists. split; [reflexivity|]. exact G1.
  - destruct (put_byte_step o m (o_bi_buf o)) as [E1 G1]; [lia|].
    rewrite E1. cbn [bind]. eexists. split; [reflexivity|]. exact G1.
  - cbn [bind]. eexists. split; [reflexivity|]. exact (pb_grow_refl o m).
Qed.

Lemma copy_step b p src m :
  0 <= p -> p + Zlength src <= Zlength b -> bytes src ->
  pb_grow (mkOut b 0 0 0 0) m (mkOut (copy_bytes b p src) 0 0 0 0) (mask_set_n (Z.to_nat (Zlength src)) m p).
Proof.
  intros H1 H2 Hs. pose proof (Zlength_nonneg src) as H0.
  assert (LC : Zlength (copy_bytes b p src) = Zlength b).
  { unfold copy_bytes. rewrite !Zlength_app, !Zlength_sublist by lia. lia. }
  pose proof (mask_set_n_after (Z.to_nat (Zlength src)) m p) as MA.
  pose proof MA as (_ & ML & MP).
  unfold pb_grow; cbn [o_buf]. split; [exact LC|]. split; [exact ML|].
  split; [intros i; apply mask_after_mono with (1 := MA)|].
  intros [HL HB]. cbn [mb_val mb_def] in *. unfold mb_ok; cbn [mb_val mb_def]. split; [congruence|].
  rewrite LC. intros i Hi Hd. rewrite MP in Hd by lia.
  rewrite Z2Nat.id in Hd by (apply Zlength_nonneg).
  unfold copy_bytes.
  destruct (Z_lt_ge_dec i p).
  - rewrite app_Znth1 by (rewrite Zlength_sublist by lia; lia).
    rewrite Znth_sublist by lia. rewrite Z.add_0_r.
    replace ((p <=? i) && (i <? p + Zlength src)) with false in Hd
      by (destruct (Z.leb_spec p i); simpl; auto; lia).
    apply HB; auto.
  - rewrite app_Znth2 by (rewrite Zlength_sublist by lia; lia).
    rewrite Zlength_sublist by lia.
    destruct (Z_lt_ge_dec (i - (p - 0)) (Zlength src)).
    + rewrite app_Znth1 by lia. unfold bytes in Hs. rewrite Forall_forall in Hs.
      apply Hs. apply Znth_In. lia.
    + rewrite app_Znth2 by lia. rewrite Znth_sublist by lia.
      replace ((p <=? i) && (i <? p + Zlength src)) with false in Hd
        by (destruct (Z.ltb_spec i (p + Zlength src)); rewrite ?andb_false_r; auto; lia).
      replace (i - (p - 0) - Zlength src + (p + Zlength src)) with i by lia.
      apply HB; auto.
Qed.


Theorem sblk_ok : sblk_stmt.
Proof.
  intros o m buf len last Hok Hlast Hlen Hmax Hbytes Hm Hroom.
  pose proof Hok as (Hv & Hb & Hp).
  assert (D4 : (o_bi_valid o + 42) / 8 = (o_bi_valid o + 10) / 8 + 4).
  { replace (o_bi_valid o + 42) with (o_bi_valid o + 10 + 4 * 8) by lia. apply Z.div_add; lia. }
  assert (D0 : 1 <= (o_bi_valid o + 10) / 8) by (apply Z.div_le_lower_bound; lia).
  assert (Dp : (8 * o_pending o + o_bi_valid o + 10) / 8 = o_pending o + (o_bi_valid o + 10) / 8).
  { replace (8 * o_pending o + o_bi_valid o + 10) with (o_bi_valid o + 10 + o_pending o * 8) by lia.
    rewrite Z.div_add by lia. lia. }
  (* send_bits *)
  set (v := Z.shiftl STORED_BLOCK 1 + last).
  assert (Hvv : 0 <= v < 2 ^ 3) by (unfold v, STORED_BLOCK; simpl; lia).
  destruct (send_bits_spec o v 3 Hok ltac:(lia) Hvv) as (S1 & _ & S3 & S4 & S5).
  destruct S5 as (_ & L1 & _ & _).
  destruct (send_bits_step o m v 3 Hok ltac:(lia) ltac:(lia)) as (m1 & E1 & G1).
  set (o1 := send_bits o v 3) in *.
  (* bi_windup *)
  destruct (windup_bitpos o1 S3) as (W1 & W2).
  destruct (bi_windup_spec o1 S3) as (_ & V2 & B2 & _ & _ & L2 & _).
  destruct (bi_windup_step o1 m1 S3 ltac:(lia)) as (m2 & E2 & G2).
  set (o2 := bi_windup o1) in *.
  assert (P2 : o_pending o2 = o_pending o + (o_bi_valid o + 10) / 8).
  { unfold bitpos in *. rewrite V2 in W1.
    replace (8 * o_pending o1 + o_bi_valid o1 + 7) with (8 * o_pending o + o_bi_valid o + 10) in W1 by lia.
    rewrite Dp in W1. lia. }
  (* the two put_shorts *)
  destruct (put_short_spec o2 (u16 len)) as (Q1 & Q2 & Q3 & (_ & L3 & _ & _)).
  destruct (put_short_step o2 m2 (u16 len) ltac:(lia) ltac:(lia)) as (m3 & E3 & G3).
  set (o3 := put_short o2 (u16 len)) in *.
  destruct (put_short_spec o3 (u16 (Z.lnot len))) as (R1 & R2 & R3 & (_ & L4 & _ & _)).
  destruct (put_short_step o3 m3 (u16 (Z.lnot len)) ltac:(lia) ltac:(lia)) as (m4 & E4 & G4).
  set (o4 := put_short o3 (u16 (Z.lnot len))) in *.
  assert (G14 : pb_grow o m o4 m4).
  { eapply pb_grow_trans; [exact G1|]. eapply pb_grow_trans; [exact G2|].
    eapply pb_grow_trans; [exact G3|]. exact G4. }
  (* the copy *)
  assert (Ex : exists o' m', c_tr_stored_block (o, m) buf len last = Some (o', m') /\
                 o_pending o' = o_pending o4 + len /\ o_bi_valid o' = o_bi_valid o4 /\
                 o_bi_buf o' = o_bi_buf o4 /\ pb_grow o m o' m').
  { unfold c_tr_stored_block. fold v. rewrite E1. cbn [bind]. rewrite E2. cbn [bind].
    rewrite E3. cbn [bind]. rewrite E4. cbn [bind].
    destruct (Z.eqb_spec len 0) as [->|Hn].
    - cbn [negb Z.eqb bind]. eexists _, _. split; [reflexivity|].
      cbn [o_pending o_bi_valid o_bi_buf]. split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
      exact G14.
    - replace (negb (len =? 0)) with true by (rewrite (proj2 (Z.eqb_neq _ _) Hn); reflexivity).
      replace ((0 <? len) && (len <=? Zlength buf)) with true
        by (symmetry; rewrite andb_true_iff, Z.ltb_lt, Z.leb_le; lia).
      replace (o_pending o4 + len <=? Zlength (o_buf o4)) with true by (symmetry; rewrite Z.leb_le; lia).
      cbn [guard bind]. eexists _, _. split; [reflexivity|].
      cbn [o_pending o_bi_valid o_bi_buf]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|].
      eapply pb_grow_trans; [exact G14|].
      pose proof (copy_step (o_buf o4) (o_pending o4) (sublist 0 len buf) m4) as C.
      rewrite Zlength_sublist in C by lia. replace (len - 0) with len in C by lia.
      apply C; [lia|lia|]. apply Forall_sublist. exact Hbytes. }
  destruct Ex as (o' & m' & E & P' & V' & B' & G').
  assert (Po : o_pending o' = o_pending o + (o_bi_valid o + 42) / 8 + len) by lia.
  exists o', m'. split; [exact E|]. split; [exact Po|].
  split; [lia|].
  split; [unfold bits_ok; rewrite V', B', R3, Q3, V2, R2, Q2, B2; split; [lia|]; split; [cbn; lia|]; lia|].
  split; [unfold bitpos; rewrite V', R3, Q3, V2, P'; rewrite R1, Q1, P2;
          rewrite Dp; lia|].
  split; [exact G'|].
  intros i Hi.
  destruct (@capp _ _ _ (capp_tr_stored_block o m buf len last) o' m' E) as (_ & _ & MP).
  rewrite MP by lia.
  replace ((o_pending o <=? i) && (i <? o_pending o')) with true
    by (symmetry; rewrite andb_true_iff, Z.leb_le, Z.ltb_lt; lia).
  reflexivity.
Qed.
