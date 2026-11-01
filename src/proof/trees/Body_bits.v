(** * The bodies of trees.c's bit writer against TSpec.v: bi_flush, bi_windup, _tr_flush_bits, bi_reverse *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Import Zlib.proof.trees.TSpec.
Require Import Zlib.proof.trees.TLemmas.
Require Import Zlib.trees.code.

#[export] Existing Instance DCS.CS.

Open Scope cmodel_scope.

Lemma body_bi_flush : semax_body Vprog Gprog_bi_flush f_bi_flush bi_flush_spec.
Proof.
  start_function.
  destruct o as [buf p bb bv bu]. unfold out_at. Intros.
  pose proof H0 as Hok. destruct H0 as [[Hm Hd] [Hb [Hp [Hbb [Hbv Hbu]]]]].
  cbn [o_buf o_pending o_bi_buf o_bi_valid o_bi_used mb_val mb_def] in *.
  assert (Hbb' : 0 <= bb <= 65535) by lia.
  unfold vi, vl.
  forward.
  forward_if.
  - (* bi_valid == 16: put_short(s, s->bi_buf); bi_buf = 0; bi_valid = 0 *)
    subst bv.
    unfold c_bi_flush in H. cbn [o_bi_valid Z.eqb Pos.eqb] in H.
    inv_bind H. unfold c_put_short in Ha. inv_bind Ha.
    apply c_put_byte_inv' in Ha0. cbn [fst snd o_buf o_pending o_bi_buf] in Ha0. destruct Ha0 as [Hi1 ->].
    apply c_put_byte_inv' in Ha. cbn [fst snd put_byte_c o_buf o_pending o_bi_buf] in Ha. destruct Ha as [Hi2 ->].
    cbn [fst snd put_byte_c o_buf o_pending o_bi_buf o_bi_valid o_bi_used set_bits] in H.
    inversion H; subst r; clear H.
    fwd. fwd. fwd. fwd. fwd.
    fold_put_byte. open_out_at.
    fwd. fwd. fwd. fwd. fwd.
    fold_put_byte. open_out_at.
    forward. forward.
    rewrite zext16_repr. change (0 mod 65536) with 0.
    sep_apply (out_at_fields _ _ 0 0 bu _ sp pbp
                 (out_ok_set_bits _ _ _ _ _ _ 0 0 bu H0 ltac:(lia) ltac:(rep_lia) ltac:(rep_lia))).
    go_lower. cancel; apply derives_refl.
  - (* bi_valid >= 8: put_byte(s, (Byte)s->bi_buf); bi_buf >>= 8; bi_valid -= 8 *)
    unfold c_bi_flush in H. cbn [o_bi_valid o_bi_buf] in H.
    rewrite (proj2 (Z.eqb_neq bv 16) H0) in H.
    forward.
    forward_if.
    + rewrite (proj2 (Z.geb_le bv 8) ltac:(lia)) in H.
      inv_bind H.
      apply c_put_byte_inv' in Ha. cbn [fst snd o_buf o_pending o_bi_buf] in Ha. destruct Ha as [Hi1 ->].
      cbn [fst snd put_byte_c o_buf o_pending o_bi_buf o_bi_valid o_bi_used set_bits] in H.
      inversion H; subst r; clear H.
      fwd. fwd. fwd. fwd. fwd.
      fold_put_byte. open_out_at.
      fwd. fwd. fwd. fwd.
      assert (Hsh : Z.shiftr bb 8 = bb / 256) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
      assert (Hsh' : 0 <= bb / 256 < 65536) by (apply div256_ush; lia).
      rewrite shr_repr by (cbn; rep_lia). change (two_p 8) with 256.
      rewrite zext16_repr, Z.mod_small by lia. rewrite sub_repr32. rewrite <- Hsh.
      sep_apply (out_at_fields _ _ (Z.shiftr bb 8) (bv - 8) bu _ sp pbp
                   (out_ok_set_bits _ _ _ _ _ _ (Z.shiftr bb 8) (bv - 8) bu H ltac:(rewrite Hsh; lia) ltac:(rep_lia) ltac:(rep_lia))).
      go_lower. cancel; apply derives_refl.
    + rewrite Z.geb_leb, (proj2 (Z.leb_gt 8 bv) ltac:(lia)) in H.
      inversion H; subst r; clear H.
      forward.
      sep_apply (out_at_fields buf p bb bv bu m sp pbp Hok).
      entailer!.
Qed.

Lemma body_tr_flush_bits : semax_body Vprog Gprog_tr_flush_bits f__tr_flush_bits tr_flush_bits_spec.
Proof.
  start_function.
  forward_call (sp, pbp, o, m, r).
  entailer!.
Qed.

(** ** bi_windup *)
Lemma body_bi_windup : semax_body Vprog Gprog_bi_windup f_bi_windup bi_windup_spec.
Proof.
  start_function.
  destruct o as [buf p bb bv bu].
  unfold c_bi_windup in H. inv_bind H. destruct x.
  apply guard_inv in Ha. cbn [o_bi_valid] in Ha. apply andb_prop in Ha. destruct Ha as [Hg1 Hg2].
  apply Z.leb_le in Hg1. apply Z.leb_le in Hg2.
  cbv beta in H. rename H into H0. assert (H : Int.min_signed < bv) by rep_lia.
  unfold out_at. Intros.
  pose proof H1 as Hok. destruct H1 as [[Hm Hd] [Hb [Hp [Hbb [Hbv Hbu]]]]].
  cbn [o_buf o_pending o_bi_buf o_bi_valid o_bi_used mb_val mb_def] in *.
  assert (Hbb' : 0 <= bb <= 65535) by lia.
  inv_bind H0. destruct x as [o1 m1].
  assert (Hbits : o_bi_buf o1 = bb /\ o_bi_valid o1 = bv /\ o_bi_used o1 = bu).
  { cbn [o_bi_valid o_bi_buf] in Ha.
    destruct (bv >? 8); [apply c_put_short_bits in Ha; exact Ha|].
    destruct (bv >? 0); [apply c_put_byte_bits in Ha; exact Ha|]. inversion Ha; auto. }
  cbn beta iota in H0. inversion H0; subst r; clear H0.
  unfold vi, vl.
  forward.
  forward_if (PROP () LOCAL (temp _s sp) SEP (out_at o1 m1 sp pbp)).
  - (* bi_valid > 8: put_short *)
    cbn [o_bi_valid o_bi_buf] in Ha. rewrite Z.gtb_ltb, (proj2 (Z.ltb_lt 8 bv) ltac:(lia)) in Ha.
    unfold c_put_short in Ha. inv_bind Ha.
    apply c_put_byte_inv' in Ha0. cbn [fst snd o_buf o_pending o_bi_buf] in Ha0. destruct Ha0 as [Hi1 ->].
    apply c_put_byte_inv' in Ha. cbn [fst snd put_byte_c o_buf o_pending o_bi_buf] in Ha.
    destruct Ha as [Hi2 Ha]. inversion Ha; subst o1 m1; clear Ha.
    fwd. fwd. fwd. fwd. fwd.
    fold_put_byte. open_out_at.
    fwd. fwd. fwd. fwd. fwd.
    fold_put_byte.
    entailer!.
  - fwd.
    forward_if.
    + (* 0 < bi_valid <= 8: put_byte *)
      cbn [o_bi_valid o_bi_buf] in Ha. rewrite Z.gtb_ltb, (proj2 (Z.ltb_ge 8 bv) ltac:(lia)) in Ha.
      rewrite Z.gtb_ltb, (proj2 (Z.ltb_lt 0 bv) ltac:(lia)) in Ha.
      apply c_put_byte_inv' in Ha. cbn [fst snd o_buf o_pending o_bi_buf] in Ha.
      destruct Ha as [Hi1 Ha]. inversion Ha; subst o1 m1; clear Ha.
      fwd. fwd. fwd. fwd. fwd.
      fold_put_byte.
      entailer!.
    + cbn [o_bi_valid o_bi_buf] in Ha. rewrite Z.gtb_ltb, (proj2 (Z.ltb_ge 8 bv) ltac:(lia)) in Ha.
      rewrite Z.gtb_ltb, (proj2 (Z.ltb_ge 0 bv) ltac:(lia)) in Ha.
      inversion Ha; subst o1 m1; clear Ha.
      forward.
      sep_apply (out_at_fields buf p bb bv bu m sp pbp Hok).
      entailer!.
  - destruct o1 as [buf1 p1 bb1 bv1 bu1]. cbn [o_bi_buf o_bi_valid o_bi_used] in Hbits.
    destruct Hbits as [-> [-> ->]].
    open_out_at.
    forward.
    forward.
    { entailer!. rewrite land7_mod. pose proof (Z.mod_pos_bound (bv - 1) 8).
      rewrite Int.signed_repr by rep_lia. rep_lia. }
    forward. forward.
    rewrite sub_repr32, and_repr32, add_repr32, zext16_repr. change (0 mod 65536) with 0.
    assert (Hu : 0 <= Z.land (bv - 1) 7 < 8) by (rewrite land7_mod; apply Z.mod_pos_bound; lia).
    sep_apply (out_at_fields _ _ 0 0 (Z.land (bv - 1) 7 + 1) _ sp pbp
                 (out_ok_set_bits _ _ _ _ _ _ 0 0 (Z.land (bv - 1) 7 + 1) H0 ltac:(lia) ltac:(rep_lia)
                    ltac:(rep_lia))).
    go_lower. cancel; apply derives_refl.
Qed.

(** ** bi_reverse *)
Lemma body_bi_reverse : semax_body Vprog Gprog_bi_reverse f_bi_reverse bi_reverse_spec.
Proof.
  start_function.
  unfold c_bi_reverse in H1. inv_bind H1. destruct x.
  apply guard_inv, Z.leb_le in Ha. rename Ha into Hlen. cbv beta in H1.
  inv_bind H1. rename x into rr. injection H1 as <-.
  unfold vi.
  forward.
  forward_loop
    (EX f : nat, EX c : Z, EX rs : Z, EX l : Z,
      PROP ((f <= 16)%nat; c_bi_reverse_loop f c rs l = Some rr; 0 <= c <= Int.max_unsigned;
            0 <= rs < 2 ^ (17 - Z.of_nat f); Int.min_signed < l <= Int.max_signed)
      LOCAL (temp _res (Vint (Int.repr rs)); temp _code (Vint (Int.repr c)); temp _len (Vint (Int.repr l)))
      SEP ())
    continue:
    (EX f : nat, EX c : Z, EX rs : Z, EX l : Z,
      PROP ((f < 16)%nat;
            (if l - 1 >? 0 then c_bi_reverse_loop f c rs (l - 1) else Some rs) = Some rr;
            0 <= c <= Int.max_unsigned; 0 <= rs < 2 ^ (17 - Z.of_nat f); Int.min_signed < l <= Int.max_signed)
      LOCAL (temp _res (Vint (Int.repr rs)); temp _code (Vint (Int.repr c)); temp _len (Vint (Int.repr l)))
      SEP ())
    break:
    (PROP (0 <= rr < 2 ^ 17) LOCAL (temp _res (Vint (Int.repr rr))) SEP ()).
  - Exists 16%nat code 0 len. entailer!.
  - Intros f c rs l.
    destruct f as [|f]; [discriminate|].
    rewrite c_bi_reverse_loop_S in H2.
    forward. forward. forward.
    Exists f (Z.shiftr c 1) (Z.shiftl (Z.lor rs (Z.land c 1)) 1) l.
    entailer!.
    rewrite shl1_repr, shru1_repr by auto.
    split; [apply shiftr1_range; auto|]. split; [|auto].
    pose proof (bi_reverse_res_step rs c (17 - Z.of_nat (S f)) ltac:(lia) H4).
    replace (17 - Z.of_nat f) with (17 - Z.of_nat (S f) + 1) by lia. auto.
  - Intros f c rs l.
    forward. forward.
    forward_if.
    + forward.
      rewrite Z.gtb_ltb, (proj2 (Z.ltb_lt 0 (l - 1)) ltac:(lia)) in H2.
      Exists f c rs (l - 1).
      entailer!.
    + forward.
      rewrite Z.gtb_ltb, (proj2 (Z.ltb_ge 0 (l - 1)) ltac:(lia)) in H2. injection H2 as ->.
      assert (2 ^ (17 - Z.of_nat f) <= 2 ^ 17) by (apply Z.pow_le_mono_r; lia).
      entailer!.
  - forward.
    entailer!. rewrite shru1_repr by rep_lia. auto.
Qed.

(** ** The obligations of these four functions (Obligations.v) *)
Require Import Zlib.proof.deflate.Obligations.

Theorem trees_bits : ob_bi_reverse /\ ob_bi_flush /\ ob_bi_windup /\ ob_tr_flush_bits.
Proof.
  unfold ob_bi_reverse, ob_bi_flush, ob_bi_windup, ob_tr_flush_bits.
  split; [exact body_bi_reverse|]. split; [exact body_bi_flush|]. split; [exact body_bi_windup|].
  exact body_tr_flush_bits.
Qed.
