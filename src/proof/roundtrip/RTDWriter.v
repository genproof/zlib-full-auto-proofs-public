(* RT-D: the bit writer, _tr_stored_block and _tr_align append Format's bits (specs: RTDBits.v). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDBits.
Require Import Zlib.proof.trees.CEquiv.
Import ListNotations.
Local Open Scope Z_scope.

(** ** bits_le *)

Lemma rtdw_bits_le_ext x y n : 0 <= n ->
  (forall i, 0 <= i < n -> Z.testbit x i = Z.testbit y i) -> F.bits_le x n = F.bits_le y n.
Proof.
  intros Hn H. unfold F.bits_le. apply map_ext_in. intros i Hi. apply in_seq in Hi.
  apply H. destruct Hi as [_ Hi]. simpl in Hi. apply Nat2Z.inj_lt in Hi. rewrite Z2Nat.id in Hi by lia. lia.
Qed.

Lemma rtdw_map_testbit_seq x a : 0 <= a -> forall b s,
  map (fun i => Z.testbit x (Z.of_nat i)) (seq (s + Z.to_nat a) b) =
  map (fun i => Z.testbit (Z.shiftr x a) (Z.of_nat i)) (seq s b).
Proof.
  intros Ha b. induction b; intros s; simpl; [reflexivity|].
  rewrite Z.shiftr_spec by lia. f_equal.
  - f_equal. rewrite Nat2Z.inj_add, Z2Nat.id by lia. lia.
  - specialize (IHb (S s)). simpl in IHb. exact IHb.
Qed.

Lemma rtdw_bits_le_split x a b : 0 <= a -> 0 <= b ->
  F.bits_le x (a + b) = F.bits_le x a ++ F.bits_le (Z.shiftr x a) b.
Proof.
  intros Ha Hb. unfold F.bits_le. rewrite Z2Nat.inj_add by lia. rewrite seq_app, map_app. f_equal.
  apply (rtdw_map_testbit_seq x a Ha _ 0).
Qed.

Lemma rtdw_bits_le_mod x n m : 0 <= n <= m -> F.bits_le (x mod 2 ^ m) n = F.bits_le x n.
Proof. intros. apply rtdw_bits_le_ext; [lia|]. intros i Hi. apply Z.mod_pow2_bits_low. lia. Qed.

Lemma rtdw_bits_le_lor a b k n : 0 <= k -> 0 <= n -> 0 <= a < 2 ^ k ->
  F.bits_le (Z.lor a (Z.shiftl b k)) (k + n) = F.bits_le a k ++ F.bits_le b n.
Proof.
  intros Hk Hn Ha. rewrite rtdw_bits_le_split by lia. f_equal.
  - apply rtdw_bits_le_ext; [lia|]. intros i Hi. rewrite Z.lor_spec, Z.shiftl_spec by lia.
    rewrite (Z.testbit_neg_r b (i - k)) by lia. apply orb_false_r.
  - apply rtdw_bits_le_ext; [lia|]. intros i Hi. rewrite Z.shiftr_spec, Z.lor_spec, Z.shiftl_spec by lia.
    rewrite <- (Z.mod_small a (2 ^ k)) by lia. rewrite Z.mod_pow2_bits_high by lia. simpl. f_equal; lia.
Qed.

Lemma rtdw_bits_le_zero k : F.bits_le 0 k = F.zeros k.
Proof.
  unfold F.bits_le, F.zeros. rewrite <- (seq_length (Z.to_nat k) 0) at 2.
  generalize (seq 0 (Z.to_nat k)). induction l; simpl; [reflexivity|]. rewrite Z.testbit_0_l. f_equal; auto.
Qed.

(* the bits above the bit count of a bounded value are zeros *)
Lemma rtdw_bits_le_high x a b : 0 <= a -> 0 <= b -> 0 <= x < 2 ^ a ->
  F.bits_le x (a + b) = F.bits_le x a ++ F.zeros b.
Proof.
  intros Ha Hb Hx. rewrite rtdw_bits_le_split by lia. f_equal.
  rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. apply rtdw_bits_le_zero.
Qed.

Lemma rtdw_bits_le_u8 c : F.bits_le (u8 c) 8 = F.bits_le c 8.
Proof. unfold u8. change 256 with (2 ^ 8). apply rtdw_bits_le_mod. lia. Qed.

Lemma rtdw_bits_le_u16 c n : 0 <= n <= 16 -> F.bits_le (u16 c) n = F.bits_le c n.
Proof. intros. unfold u16. change 65536 with (2 ^ 16). apply rtdw_bits_le_mod. lia. Qed.

Lemma rtdw_bits_le_short w :
  F.bits_le (u8 (Z.land w 255)) 8 ++ F.bits_le (u8 (Z.shiftr (u16 w) 8)) 8 = F.bits_le w 16.
Proof.
  rewrite !rtdw_bits_le_u8. replace 16 with (8 + 8) by reflexivity. rewrite rtdw_bits_le_split by lia. f_equal.
  - change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply rtdw_bits_le_mod; lia.
  - apply rtdw_bits_le_ext; [lia|]. intros i Hi. unfold u16. change 65536 with (2 ^ 16).
    rewrite !Z.shiftr_spec by lia. apply Z.mod_pow2_bits_low. lia.
Qed.

(** ** The pending bytes *)

Definition rtdw_pb (o : outbuf) : list bool := F.bytes_bits (sublist 0 (o_pending o) (o_buf o)).

Lemma rtdw_obits o : obits o = rtdw_pb o ++ F.bits_le (o_bi_buf o) (o_bi_valid o).
Proof. reflexivity. Qed.

Lemma rtdw_bytes_bits_app l l' : F.bytes_bits (l ++ l') = F.bytes_bits l ++ F.bytes_bits l'.
Proof. unfold F.bytes_bits. apply flat_map_app. Qed.

Lemma rtdw_put_byte o m c o' m' : 0 <= o_pending o -> c_put_byte (o, m) c = Some (o', m') ->
  rtdw_pb o' = rtdw_pb o ++ F.bits_le c 8 /\ o_pending o' = o_pending o + 1 /\ o_bi_buf o' = o_bi_buf o /\
  o_bi_valid o' = o_bi_valid o /\ Zlength (o_buf o') = Zlength (o_buf o).
Proof.
  intros Hp H. rewrite c_put_byte_spec in H.
  destruct (in_range (o_pending o) (Zlength (o_buf o))) eqn:E; [|discriminate].
  inversion H; subst; clear H. unfold in_range in E. apply andb_true_iff in E. destruct E as [_ E].
  apply Z.ltb_lt in E. unfold rtdw_pb, put_byte; simpl.
  split; [|split; [reflexivity|split; [reflexivity|split; [reflexivity|apply Zlength_upd_Znth_any]]]].
  rewrite (sublist_split 0 (o_pending o) (o_pending o + 1)) by (rewrite ?Zlength_upd_Znth_any; lia).
  rewrite sublist_upd_Znth_l by lia. rewrite sublist_len_1 by (rewrite Zlength_upd_Znth_any; lia).
  rewrite upd_Znth_same by lia. rewrite rtdw_bytes_bits_app. f_equal. change (F.bytes_bits [u8 c]) with (F.bits_le (u8 c) 8 ++ []). rewrite app_nil_r.
  apply rtdw_bits_le_u8.
Qed.

Lemma rtdw_put_short o m w o' m' : 0 <= o_pending o -> c_put_short (o, m) w = Some (o', m') ->
  rtdw_pb o' = rtdw_pb o ++ F.bits_le w 16 /\ o_pending o' = o_pending o + 2 /\ o_bi_buf o' = o_bi_buf o /\
  o_bi_valid o' = o_bi_valid o /\ Zlength (o_buf o') = Zlength (o_buf o).
Proof.
  intros Hp H. unfold c_put_short in H.
  destruct (c_put_byte (o, m) (Z.land w 255)) as [[o1 m1]|] eqn:E1; [|discriminate]. cbn [bind] in H.
  apply rtdw_put_byte in E1; [|lia]. destruct E1 as [A1 [B1 [C1 [D1 F1]]]].
  apply rtdw_put_byte in H; [|lia]. destruct H as [A2 [B2 [C2 [D2 F2]]]].
  rewrite A2, A1, <- app_assoc, <- rtdw_bits_le_short, !rtdw_bits_le_u8.
  repeat split; congruence || lia.
Qed.

(** ** The writer *)

Lemma rtdw_send_bits o m v n o' m' :
  bits_ok o -> 1 <= n <= 16 -> 0 <= v < 2 ^ n -> c_send_bits (o, m) v n = Some (o', m') ->
  bits_ok o' /\ obits o' = obits o ++ F.bits_le v n /\ bitpos o' = bitpos o + n.
Proof.
  intros Ho Hn Hval H.
  pose proof (crel_send_bits o m v n _ H) as Em. simpl in Em.
  destruct (send_bits_spec o v n Ho Hn Hval) as [Hbp [_ [Hok _]]]. rewrite <- Em in Hbp, Hok.
  split; [exact Hok|]. split; [|exact Hbp]. clear Em Hbp Hok.
  destruct Ho as [Hv [Hb Hp]].
  assert (H16 : 2 ^ n <= 2 ^ 16) by (apply Z.pow_le_mono_r; lia).
  assert (Hu : u16 v = v) by (apply u16_id; change (2 ^ 16) with 65536 in H16; lia).
  unfold c_send_bits, Buf_size in H. rewrite Hu in H.
  destruct ((0 <=? o_bi_valid o) && (o_bi_valid o <=? 16)); [|discriminate]. cbn [guard bind] in H.
  set (bv := o_bi_valid o) in *. set (X := Z.lor (o_bi_buf o) (Z.shiftl v bv)) in H.
  destruct (Z.gtb_spec bv (16 - n)) as [Hc|Hc].
  - destruct (c_put_short (set_bits o (u16 X) bv, m) (u16 X)) as [[o1 m1]|] eqn:E; [|discriminate].
    cbn [bind] in H. inversion H; subst; clear H.
    apply rtdw_put_short in E; [|simpl; lia]. destruct E as [P1 _].
    rewrite !rtdw_obits. unfold set_bits; simpl. unfold rtdw_pb at 1. simpl. fold (rtdw_pb o1). rewrite P1.
    change (rtdw_pb (set_bits o (u16 X) bv)) with (rtdw_pb o). rewrite <- !app_assoc. f_equal.
    rewrite rtdw_bits_le_u16 by lia.
    assert (SX : F.bits_le X 16 = F.bits_le (o_bi_buf o) bv ++ F.bits_le v (16 - bv))
      by (rewrite <- rtdw_bits_le_lor by lia; f_equal; lia).
    assert (Sv : F.bits_le v n = F.bits_le v (16 - bv) ++ F.bits_le (Z.shiftr v (16 - bv)) (bv + n - 16))
      by (rewrite <- rtdw_bits_le_split by lia; f_equal; lia).
    rewrite SX, Sv, app_assoc. reflexivity.
  - inversion H; subst; clear H. rewrite !rtdw_obits. unfold set_bits; simpl.
    change (rtdw_pb {| o_buf := o_buf o; o_pending := o_pending o; o_bi_buf := u16 X; o_bi_valid := bv + n;
                       o_bi_used := o_bi_used o |}) with (rtdw_pb o). rewrite <- app_assoc. f_equal.
    rewrite rtdw_bits_le_u16 by lia. subst X bv. apply rtdw_bits_le_lor; lia.
Qed.

Lemma rtdw_put_byte_w o m c o' m' :
  bits_ok o -> o_bi_valid o = 0 -> 0 <= c < 256 -> c_put_byte (o, m) c = Some (o', m') ->
  bits_ok o' /\ o_bi_valid o' = 0 /\ obits o' = obits o ++ F.bits_le c 8.
Proof.
  intros [Hv [Hb Hp]] H0 Hc H. apply rtdw_put_byte in H; [|lia]. destruct H as [A [B [C [D _]]]].
  split; [unfold bits_ok; rewrite B, C, D; lia|]. split; [congruence|].
  rewrite !rtdw_obits, A, C, D, H0. simpl. rewrite !app_nil_r. reflexivity.
Qed.

Lemma rtdw_flush o m o' m' :
  bits_ok o -> c_tr_flush_bits (o, m) = Some (o', m') ->
  bits_ok o' /\ o_bi_valid o' <= 7 /\ obits o' = obits o.
Proof.
  intros Ho H. unfold c_tr_flush_bits in H.
  pose proof (crel_bi_flush o m _ H) as Em. simpl in Em.
  destruct (bi_flush_spec o Ho) as [_ [Hok [H7 _]]]. rewrite <- Em in Hok, H7.
  split; [exact Hok|]. split; [exact H7|]. clear Em Hok H7.
  destruct Ho as [Hv [Hb Hp]]. unfold c_bi_flush in H.
  destruct (Z.eqb_spec (o_bi_valid o) 16) as [E16|E16].
  - destruct (c_put_short (o, m) (o_bi_buf o)) as [[o1 m1]|] eqn:E; [|discriminate].
    cbn [bind] in H. inversion H; subst; clear H.
    apply rtdw_put_short in E; [|lia]. destruct E as [P1 _].
    rewrite !rtdw_obits. unfold set_bits; simpl. unfold rtdw_pb at 1; simpl. fold (rtdw_pb o1).
    rewrite P1, E16. simpl. rewrite app_nil_r. reflexivity.
  - destruct (Z.geb_spec (o_bi_valid o) 8) as [E8|E8].
    + destruct (c_put_byte (o, m) (o_bi_buf o)) as [[o1 m1]|] eqn:E; [|discriminate].
      cbn [bind] in H. inversion H; subst; clear H.
      apply rtdw_put_byte in E; [|lia]. destruct E as [P1 [_ [P3 P4]]].
      rewrite !rtdw_obits. unfold set_bits; simpl. unfold rtdw_pb at 1; simpl. fold (rtdw_pb o1).
      rewrite P1, P3, <- app_assoc. f_equal.
      rewrite <- rtdw_bits_le_split by lia. f_equal. lia.
    + inversion H; subst. reflexivity.
Qed.

Lemma rtdw_pad8_small b : 0 <= b <= 8 -> F.pad8 b = 8 - b \/ (b = 0 /\ F.pad8 b = 0).
Proof. intros. assert (b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8) by lia.
  intuition subst; (left; reflexivity) || (right; split; reflexivity). Qed.

Lemma rtdw_windup o m o' m' :
  bits_ok o -> c_bi_windup (o, m) = Some (o', m') ->
  bits_ok o' /\ o_bi_valid o' = 0 /\ obits o' = obits o ++ F.zeros (F.pad8 (o_bi_valid o)).
Proof.
  intros Ho H. destruct Ho as [Hv [Hb Hp]]. unfold c_bi_windup in H.
  destruct ((0 <=? o_bi_valid o) && (o_bi_valid o <=? 16)); [|discriminate]. cbn [guard bind] in H.
  destruct (Z.gtb_spec (o_bi_valid o) 8) as [E8|E8].
  - destruct (c_put_short (o, m) (o_bi_buf o)) as [[o1 m1]|] eqn:E; [|discriminate].
    cbn [bind] in H. inversion H; subst; clear H.
    apply rtdw_put_short in E; [|lia]. destruct E as [P1 [P2 _]].
    split; [unfold bits_ok; simpl; lia|]. split; [reflexivity|].
    rewrite !rtdw_obits. unfold rtdw_pb at 1; simpl. fold (rtdw_pb o1). rewrite P1, app_nil_r, <- app_assoc.
    f_equal. assert (Pd : F.pad8 (o_bi_valid o) = 16 - o_bi_valid o).
    { assert (Hm : o_bi_valid o mod 8 = o_bi_valid o - 8 \/ o_bi_valid o = 16).
      { destruct (Z.eq_dec (o_bi_valid o) 16); [right; auto|left].
        rewrite (Z.mod_unique (o_bi_valid o) 8 1 (o_bi_valid o - 8)); lia. }
      unfold F.pad8. destruct Hm as [Hm| ->]; [|reflexivity]. rewrite Hm. rewrite Z.mod_small by lia. lia. }
    rewrite Pd. replace 16 with (o_bi_valid o + (16 - o_bi_valid o)) at 1 by lia.
    apply rtdw_bits_le_high; lia.
  - destruct (Z.gtb_spec (o_bi_valid o) 0) as [E0|E0].
    + destruct (c_put_byte (o, m) (o_bi_buf o)) as [[o1 m1]|] eqn:E; [|discriminate].
      cbn [bind] in H. inversion H; subst; clear H.
      apply rtdw_put_byte in E; [|lia]. destruct E as [P1 [P2 _]].
      split; [unfold bits_ok; simpl; lia|]. split; [reflexivity|].
      rewrite !rtdw_obits. unfold rtdw_pb at 1; simpl. fold (rtdw_pb o1). rewrite P1, app_nil_r, <- app_assoc.
      f_equal. destruct (rtdw_pad8_small (o_bi_valid o) ltac:(lia)) as [Pd|[Pd _]]; [|lia].
      rewrite Pd. replace 8 with (o_bi_valid o + (8 - o_bi_valid o)) at 1 by lia.
      apply rtdw_bits_le_high; lia.
    + inversion H; subst; clear H.
      split; [unfold bits_ok; simpl; lia|]. split; [reflexivity|].
      assert (V0 : o_bi_valid o = 0) by lia.
      rewrite !rtdw_obits. simpl. rewrite V0. unfold rtdw_pb, F.bits_le, F.zeros; simpl. rewrite !app_nil_r. reflexivity.
Qed.

Lemma rtdw_writer : writer_fspec.
Proof.
  split; [|split; [|split]].
  - intros o m v n o' m' Ho Hn Hv H. destruct (rtdw_send_bits o m v n o' m' Ho Hn Hv H) as [A [B _]]. auto.
  - intros. eapply rtdw_put_byte_w; eauto.
  - intros. eapply rtdw_flush; eauto.
  - intros. eapply rtdw_windup; eauto.
Qed.

(** ** _tr_stored_block *)

Lemma rtdw_u16_lnot len : 0 <= len <= 65535 -> u16 (Z.lnot len) = 65535 - len.
Proof.
  intros. unfold u16. replace (Z.lnot len) with ((65535 - len) + (-1) * 65536) by (unfold Z.lnot; lia).
  rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

Lemma rtdw_copy dst pos src : 0 <= pos -> pos + Zlength src <= Zlength dst ->
  sublist 0 (pos + Zlength src) (copy_bytes dst pos src) = sublist 0 pos dst ++ src.
Proof.
  intros H0 H1. pose proof (Zlength_nonneg src). unfold copy_bytes.
  rewrite sublist0_app2 by (rewrite Zlength_app, !Zlength_sublist by lia; lia).
  rewrite Zlength_sublist by lia. f_equal. replace (pos + Zlength src - (pos - 0)) with (Zlength src) by lia.
  rewrite sublist0_app1 by lia. apply sublist_same; lia.
Qed.

Lemma rtdw_stored : stored_block_fspec.
Proof.
  intros o m buf len last o' m' p Ho Hl Hlen Hbuf Hbytes Hp Hmod H.
  unfold c_tr_stored_block in H.
  destruct (c_send_bits (o, m) (Z.shiftl STORED_BLOCK 1 + last) 3) as [[o1 m1]|] eqn:E1; [|discriminate].
  cbn [bind] in H.
  destruct (c_bi_windup (o1, m1)) as [[o2 m2]|] eqn:E2; [|discriminate]. cbn [bind] in H.
  destruct (c_put_short (o2, m2) (u16 len)) as [[o3 m3]|] eqn:E3; [|discriminate]. cbn [bind] in H.
  destruct (c_put_short (o3, m3) (u16 (Z.lnot len))) as [[o4 m4]|] eqn:E4; [|discriminate]. cbn [bind] in H.
  change (Z.shiftl STORED_BLOCK 1 + last) with (0 + last) in E1.
  apply rtdw_send_bits in E1; [|exact Ho|lia|simpl; lia]. destruct E1 as [Ok1 [Ob1 Bp1]].
  apply rtdw_windup in E2; [|exact Ok1]. destruct E2 as [Ok2 [V2 Ob2]].
  assert (Hb2 : o_bi_buf o2 = 0) by (destruct Ok2 as [_ [Hb _]]; rewrite V2 in Hb; simpl in Hb; lia).
  assert (Pp2 : 0 <= o_pending o2) by (destruct Ok2 as [_ [_ X]]; exact X).
  apply rtdw_put_short in E3; [|lia]. destruct E3 as [A3 [P3 [B3 [V3 L3]]]].
  apply rtdw_put_short in E4; [|lia]. destruct E4 as [A4 [P4 [B4 [V4 L4]]]].
  assert (Hlb : len <= Zlength buf) by (destruct Hbuf; [subst; pose proof (Zlength_nonneg buf); lia | lia]).
  assert (Hlen' : Zlength (sublist 0 len buf) = len) by (rewrite Zlength_sublist by lia; lia).
  assert (Ob' : obits o' = rtdw_pb o4 ++ F.bytes_bits (sublist 0 len buf) /\ bits_ok o' /\ o_bi_valid o' = 0).
  { destruct (negb (len =? 0)) eqn:Ez; cbn [bind] in H.
    - destruct ((0 <? len) && (len <=? Zlength buf)); [|discriminate]. cbn [guard bind] in H.
      destruct (o_pending o4 + len <=? Zlength (o_buf o4)) eqn:G2; [|discriminate]. cbn [guard bind] in H.
      apply Z.leb_le in G2.
      inversion H; subst; clear H.
      rewrite rtdw_obits; unfold rtdw_pb at 1; simpl.
      replace (o_pending o4 + len) with (o_pending o4 + Zlength (sublist 0 len buf)) by lia.
      rewrite rtdw_copy by lia. rewrite rtdw_bytes_bits_app.
      rewrite V4, V3, V2. change (F.bits_le (o_bi_buf o4) 0) with (@nil bool). rewrite app_nil_r.
      split; [reflexivity|]. split; [|reflexivity].
      unfold bits_ok; simpl; rewrite B4, B3, Hb2, Hlen'; simpl; lia.
    - apply negb_false_iff, Z.eqb_eq in Ez. subst len. inversion H; subst; clear H.
      rewrite rtdw_obits; unfold rtdw_pb at 1; simpl. rewrite Z.add_0_r.
      rewrite V4, V3, V2. change (F.bits_le (o_bi_buf o4) 0) with (@nil bool).
      rewrite !app_nil_r.
      split; [reflexivity|]. split; [|reflexivity].
      unfold bits_ok; simpl; rewrite B4, B3, Hb2; simpl; lia. }
  destruct Ob' as [Ob' [Ok' V']]. split; [exact Ok'|]. split; [exact V'|].
  rewrite Ob', A4, A3. rewrite rtdw_u16_lnot by lia. rewrite rtdw_bits_le_u16 by lia.
  rewrite rtdw_obits, V2 in Ob2. change (F.bits_le (o_bi_buf o2) 0) with (@nil bool) in Ob2.
  rewrite app_nil_r in Ob2. rewrite Ob2, Ob1, <- !app_assoc. f_equal.
  assert (Hpad : F.pad8 (o_bi_valid o1) = F.pad8 (p + 3)).
  { unfold F.pad8. f_equal. f_equal. apply Z.mod_divide in Hmod; [|lia]. destruct Hmod as [k Hk].
    unfold bitpos in Bp1. replace (o_bi_valid o1) with ((p + 3) + (o_pending o - o_pending o1 - k) * 8) by lia.
    apply Z_mod_plus_full. }
  assert (Hl3 : F.bits_le (0 + last) 3 = [last =? 1; false; false])
    by (assert (last = 0 \/ last = 1) as [-> | ->] by lia; reflexivity).
  unfold F.enc_block. rewrite Hlen', Hpad, Hl3. reflexivity.
Qed.

(** ** _tr_align *)

Lemma rtdw_align : align_fspec.
Proof.
  intros o m o' m' p Ho H. unfold c_tr_align in H.
  destruct (c_send_bits (o, m) (Z.shiftl STATIC_TREES 1) 3) as [[o1 m1]|] eqn:E1; [|discriminate].
  cbn [bind] in H.
  destruct (c_send_code (o1, m1) END_BLOCK static_ltree_code static_ltree_len) as [[o2 m2]|] eqn:E2;
    [|discriminate].
  cbn [bind] in H.
  change (Z.shiftl STATIC_TREES 1) with 2 in E1.
  apply rtdw_send_bits in E1; [|exact Ho|lia|simpl; lia]. destruct E1 as [Ok1 [Ob1 _]].
  unfold c_send_code in E2.
  assert (R1 : rd static_ltree_len END_BLOCK = Some 7) by (vm_compute; reflexivity).
  assert (R2 : rd static_ltree_code END_BLOCK = Some 0) by (vm_compute; reflexivity).
  rewrite R1, R2 in E2. cbn [bind] in E2.
  apply rtdw_send_bits in E2; [|exact Ok1|lia|simpl; lia]. destruct E2 as [Ok2 [Ob2 _]].
  assert (H' : c_tr_flush_bits (o2, m2) = Some (o', m')) by exact H.
  apply rtdw_flush in H'; [|exact Ok2]. destruct H' as [Ok3 [V3 Ob3]].
  split; [exact Ok3|]. split; [exact V3|].
  rewrite Ob3, Ob2, Ob1, <- app_assoc. f_equal.
Qed.

Theorem rtd_writer_ok : writer_fspec /\ stored_block_fspec /\ align_fspec.
Proof. exact (conj rtdw_writer (conj rtdw_stored rtdw_align)). Qed.
