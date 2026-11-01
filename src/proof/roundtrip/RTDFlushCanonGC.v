(* RT-D FLUSH part CANON, sub-part GC: gen_codes assigns the canonical codes of RFC 1951 3.2.2
   (bit-reversed, as send_bits sends them least significant bit first) when bl_count holds the exact counts of
   the lengths of the symbols 0..max_code. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.huffman.Model.
Require Zlib.proof.rfc1951.Format.
Module F := Zlib.proof.rfc1951.Format.
Import ListNotations.
Local Open Scope Z_scope.

(* gen_codes(t, mc, blc): blc[l] (0 <= l <= 15) is the number of symbols x <= mc of length l (none of length 0);
   then the Code field of every symbol x <= mc with a nonzero length, sent least significant bit first, is the
   canonical code of the lengths 0..mc sent most significant bit first.  (No Kraft hypothesis: all the
   arithmetic of gen_next_code / gen_codes_loop / bi_reverse agrees modulo 2^16 with Format's, and only the
   low len bits matter.) *)
Definition gc_canon_stmt : Prop :=
  forall t mc blc,
    0 <= mc < HEAP_SIZE -> mc < Zlength (fc t) -> mc < Zlength (dl t) ->
    (forall i, 0 <= i <= mc -> 0 <= Znth i (dl t) <= 15) ->
    (forall l, 0 <= l <= 15 -> Znth l blc = F.count_of (sublist 0 (mc + 1) (dl t)) l) ->
    forall x, 0 <= x <= mc -> Znth x (dl t) <> 0 ->
      F.bits_le (Znth x (fc (gen_codes t mc blc))) (Znth x (dl t)) = F.send_sym (sublist 0 (mc + 1) (dl t)) x.

(** ** Helpers *)

Lemma gc_bit0 : forall r (b : bool), Z.testbit (2 * r + Z.b2z b) 0 = b.
Proof.
  intros r b. destruct b; simpl.
  - apply Z.testbit_odd_0.
  - rewrite Z.add_0_r. apply Z.testbit_even_0.
Qed.

Lemma gc_brl_bits : forall fuel code r len, (Z.to_nat len <= fuel)%nat -> 1 <= len -> 0 <= r ->
  forall k, 0 <= k ->
  Z.testbit (bi_reverse_loop fuel code (2 * r) len) k =
    if k =? 0 then false else if k <=? len then Z.testbit code (len - k) else Z.testbit r (k - 1 - len).
Proof.
  induction fuel as [|fuel IH]; intros code r len Hf Hl Hr k Hk; [lia|].
  cbn [bi_reverse_loop].
  assert (Eb : Z.land code 1 = Z.b2z (Z.testbit code 0)).
  { change 1 with (Z.ones 1). rewrite Z.land_ones by lia. rewrite Zmod_odd, Z.bit0_odd.
    destruct (Z.odd code); reflexivity. }
  rewrite Eb.
  assert (Hor : Z.lor (2 * r) (Z.b2z (Z.testbit code 0)) = 2 * r + Z.b2z (Z.testbit code 0)).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.lor_spec.
    destruct (Z.eq_dec n 0) as [->|Hn0].
    - rewrite Z.testbit_even_0, gc_bit0. destruct (Z.testbit code 0); reflexivity.
    - replace n with (Z.succ (Z.pred n)) by lia.
      rewrite Z.testbit_even_succ by lia. rewrite Z.testbit_succ_r by lia.
      replace (Z.b2z (Z.testbit code 0)) with (2 * 0 + Z.b2z (Z.testbit code 0)) by lia.
      rewrite Z.testbit_succ_r by lia. rewrite Z.bits_0. apply orb_false_r. }
  rewrite Hor. rewrite Z.shiftl_mul_pow2 by lia. replace (2 ^ 1) with 2 by reflexivity.
  replace ((2 * r + Z.b2z (Z.testbit code 0)) * 2) with (2 * (2 * r + Z.b2z (Z.testbit code 0))) by lia.
  assert (Hq : 0 <= 2 * r + Z.b2z (Z.testbit code 0)) by (destruct (Z.testbit code 0); simpl; lia).
  assert (Hb : forall j, 0 <= j -> Z.testbit (2 * r + Z.b2z (Z.testbit code 0)) j =
                               if j =? 0 then Z.testbit code 0 else Z.testbit r (j - 1)).
  { intros j Hj. destruct (Z.eqb_spec j 0) as [->|Hj0].
    - apply gc_bit0.
    - replace j with (Z.succ (j - 1)) at 1 by lia. rewrite Z.testbit_succ_r by lia. reflexivity. }
  destruct (Z.gtb_spec (len - 1) 0) as [Hgt|Hle].
  - rewrite IH by lia.
    destruct (Z.eqb_spec k 0); [reflexivity|].
    destruct (Z.leb_spec k (len - 1)).
    + rewrite (proj2 (Z.leb_le k len)) by lia. rewrite Z.shiftr_spec by lia. f_equal; lia.
    + rewrite Hb by lia. destruct (Z.eqb_spec (k - 1 - (len - 1)) 0).
      * rewrite (proj2 (Z.leb_le k len)) by lia. f_equal; lia.
      * rewrite (proj2 (Z.leb_gt k len)) by lia. f_equal; lia.
  - assert (len = 1) by lia. subst len.
    destruct (Z.eqb_spec k 0) as [->|Hk0].
    + rewrite Z.testbit_even_0. reflexivity.
    + replace k with (Z.succ (k - 1)) at 1 by lia. rewrite Z.testbit_even_succ by lia.
      rewrite Hb by lia. destruct (Z.eqb_spec (k - 1) 0).
      * rewrite (proj2 (Z.leb_le k 1)) by lia. f_equal; lia.
      * rewrite (proj2 (Z.leb_gt k 1)) by lia. f_equal; lia.
Qed.

Lemma gc_bi_reverse_bits : forall c len, 1 <= len <= 15 -> forall j, 0 <= j < len ->
  Z.testbit (bi_reverse c len) j = Z.testbit c (len - 1 - j).
Proof.
  intros c len Hl j Hj. unfold bi_reverse. rewrite Z.shiftr_spec by lia.
  replace 0 with (2 * 0) by lia. rewrite gc_brl_bits by lia.
  rewrite (proj2 (Z.eqb_neq (j + 1) 0)) by lia. rewrite (proj2 (Z.leb_le (j + 1) len)) by lia.
  f_equal; lia.
Qed.

Lemma gc_rev_map_seq : forall (g : nat -> bool) n,
  rev (map g (seq 0 n)) = map (fun i => g (n - 1 - i)%nat) (seq 0 n).
Proof.
  intros g n. induction n as [|n IH]; [reflexivity|].
  rewrite (seq_S n 0) at 1. rewrite map_app, rev_app_distr. cbn [map rev app seq]. rewrite IH.
  f_equal; [f_equal; lia|].
  rewrite <- seq_shift, map_map. apply map_ext_in. intros i Hi. apply in_seq in Hi. f_equal. lia.
Qed.

Lemma gc_bits_le_rev : forall c len, 1 <= len <= 15 ->
  F.bits_le (bi_reverse c len) len = rev (F.bits_le c len).
Proof.
  intros c len Hl. unfold F.bits_le. rewrite gc_rev_map_seq.
  apply map_ext_in. intros i Hi. apply in_seq in Hi.
  rewrite gc_bi_reverse_bits by lia. f_equal. lia.
Qed.

Lemma gc_bits_le_mod : forall v n m, 0 <= n <= m -> F.bits_le (v mod 2 ^ m) n = F.bits_le v n.
Proof.
  intros v n m Hn. unfold F.bits_le. apply map_ext_in. intros i Hi. apply in_seq in Hi.
  apply Z.mod_pow2_bits_low. lia.
Qed.

Lemma gc_bits_le_eqm : forall a b n, 0 <= n <= 16 -> a mod 65536 = b mod 65536 ->
  F.bits_le a n = F.bits_le b n.
Proof.
  intros a b n Hn E. rewrite <- (gc_bits_le_mod a n 16), <- (gc_bits_le_mod b n 16) by lia.
  change (2 ^ 16) with 65536. rewrite E. reflexivity.
Qed.

Lemma gc_mod32_16 : forall a, (a mod 4294967296) mod 65536 = a mod 65536.
Proof.
  intros a. change 4294967296 with (65536 * 65536). rewrite Z.rem_mul_r by lia.
  rewrite (Z.mul_comm 65536 ((a / 65536) mod 65536)), Z.mod_add by lia. apply Z.mod_mod; lia.
Qed.

(** gen_next_code computes next_code_n modulo 2^16. *)
Lemma gc_next_code_inv : forall lens blc fuel nc code bits,
  (forall l, 0 <= l <= 15 -> Znth l blc = F.count_of lens l) ->
  1 <= bits <= 16 -> (Z.to_nat (16 - bits) <= fuel)%nat -> Zlength nc = 16 ->
  code mod 65536 = F.next_code_n lens (Z.to_nat (bits - 1)) mod 65536 ->
  (forall l, 1 <= l < bits -> Znth l nc mod 65536 = F.next_code_n lens (Z.to_nat l) mod 65536) ->
  let r := gen_next_code fuel blc nc code bits in
  Zlength r = 16 /\ forall l, 1 <= l <= 15 -> Znth l r mod 65536 = F.next_code_n lens (Z.to_nat l) mod 65536.
Proof.
  intros lens blc. induction fuel as [|fuel IH]; intros nc code bits Hblc Hb Hf Hnc Hc Hl.
  - cbn [gen_next_code]. split; [exact Hnc|]. intros l Hl'. apply Hl. lia.
  - cbn [gen_next_code]. destruct (Z.leb_spec bits MAX_BITS) as [Hle|Hgt]; unfold MAX_BITS in *.
    + set (code' := u32 (Z.shiftl (code + Znth (bits - 1) blc) 1)).
      assert (Hc' : code' mod 65536 = F.next_code_n lens (Z.to_nat bits) mod 65536).
      { unfold code', u32. rewrite gc_mod32_16.
        rewrite Z.shiftl_mul_pow2 by lia. replace (2 ^ 1) with 2 by reflexivity.
        replace (Z.to_nat bits) with (S (Z.to_nat (bits - 1))) by lia. cbn [F.next_code_n].
        rewrite Hblc by lia. rewrite Z.mul_mod, Z.add_mod, Hc by lia.
        rewrite <- Z.add_mod, <- Z.mul_mod by lia. f_equal. f_equal. f_equal. f_equal. lia. }
      apply IH; auto; try lia.
      * rewrite upd_Znth_Zlength; lia.
      * replace (bits + 1 - 1) with bits by lia. exact Hc'.
      * intros l Hl'. destruct (Z.eq_dec l bits) as [->|Hne].
        -- rewrite upd_Znth_same by lia. unfold u16. rewrite Z.mod_mod by lia. exact Hc'.
        -- rewrite upd_Znth_diff' by lia. apply Hl. lia.
    + split; [exact Hnc|]. intros l Hl'. apply Hl. lia.
Qed.

Lemma gc_next_code_ok : forall lens blc,
  (forall l, 0 <= l <= 15 -> Znth l blc = F.count_of lens l) ->
  let r := gen_next_code 16 blc (repeat 0 (Z.to_nat (MAX_BITS + 1))) 0 1 in
  Zlength r = 16 /\ forall l, 1 <= l <= 15 -> Znth l r mod 65536 = F.next_code_n lens (Z.to_nat l) mod 65536.
Proof.
  intros lens blc Hblc. apply gc_next_code_inv; auto; try lia; try reflexivity.
Qed.

(** gen_codes_loop leaves the codes before n alone. *)
Lemma gc_loop_keep : forall fuel mc t nc n,
  dl (gen_codes_loop fuel mc t nc n) = dl t /\
  forall x, x < n -> Znth x (fc (gen_codes_loop fuel mc t nc n)) = Znth x (fc t).
Proof.
  induction fuel as [|fuel IH]; intros mc t nc n; cbn [gen_codes_loop]; [split; auto|].
  destruct (n <=? mc); [|split; auto].
  destruct (Znth n (dl t) =? 0).
  - destruct (IH mc t nc (n + 1)) as [A B]. split; [exact A|]. intros x Hx. apply B. lia.
  - match goal with |- context [gen_codes_loop fuel mc ?t1 ?nc1 (n + 1)] =>
      destruct (IH mc t1 nc1 (n + 1)) as [A B] end.
    split; [rewrite A; reflexivity|]. intros x Hx. rewrite B by lia. unfold set_fc; simpl.
    destruct (Z_lt_dec x 0).
    + rewrite !Znth_underflow by lia. reflexivity.
    + destruct (Z_lt_dec n (Zlength (fc t))).
      * apply upd_Znth_diff'; lia.
      * rewrite upd_Znth_out_of_range by lia. reflexivity.
Qed.

Lemma gc_loop_main : forall lens fuel mc t nc n,
  lens = sublist 0 (mc + 1) (dl t) -> mc < Zlength (dl t) -> mc < Zlength (fc t) ->
  (forall i, 0 <= i <= mc -> 0 <= Znth i (dl t) <= 15) ->
  0 <= n -> (Z.to_nat (mc + 1 - n) <= fuel)%nat -> Zlength nc = 16 ->
  (forall l, 1 <= l <= 15 -> Znth l nc mod 65536 =
     (F.next_code_n lens (Z.to_nat l) + Zlength (filter (fun y => y =? l) (sublist 0 n lens))) mod 65536) ->
  forall x, n <= x <= mc -> Znth x (dl t) <> 0 ->
    F.bits_le (Znth x (fc (gen_codes_loop fuel mc t nc n))) (Znth x (dl t)) = F.send_sym lens x.
Proof.
  intros lens. induction fuel as [|fuel IH]; intros mc t nc n Hlens Hdl Hfc Hr Hn Hf Hnc Hinv x Hx Hxz; [lia|].
  assert (HZl : Zlength lens = mc + 1) by (subst lens; rewrite Zlength_sublist; lia).
  assert (Hnm : n <= mc) by lia.
  assert (Hsub : sublist 0 (n + 1) lens = sublist 0 n lens ++ [Znth n (dl t)]).
  { rewrite sublist_last_1 by lia. f_equal. rewrite Hlens, Znth_sublist by lia. rewrite Z.add_0_r. reflexivity. }
  cbn [gen_codes_loop]. rewrite (proj2 (Z.leb_le n mc)) by lia.
  destruct (Z.eqb_spec (Znth n (dl t)) 0) as [Hz|Hnz].
  - assert (x <> n) by (intro; subst; contradiction).
    apply IH; auto; try lia.
    intros l Hl. rewrite Hinv by lia. rewrite Hsub, filter_app, Zlength_app. simpl.
    rewrite Hz. destruct (Z.eqb_spec 0 l); [lia|]. rewrite Zlength_nil. f_equal; lia.
  - set (len := Znth n (dl t)) in *.
    assert (Hlen : 1 <= len <= 15) by (pose proof (Hr n ltac:(lia)); lia).
    set (c := Znth len nc).
    set (t1 := set_fc t n (u16 (bi_reverse c len))).
    assert (Hdl1 : dl t1 = dl t) by reflexivity.
    assert (Hfc1 : Zlength (fc t1) = Zlength (fc t)) by (unfold t1, set_fc; simpl; apply upd_Znth_Zlength; lia).
    destruct (Z.eq_dec x n) as [->|Hxn].
    + destruct (gc_loop_keep fuel mc t1 (upd_Znth len nc (u16 (c + 1))) (n + 1)) as [_ B].
      rewrite B by lia. unfold t1, set_fc; simpl. rewrite upd_Znth_same by lia. fold len.
      unfold u16. change 65536 with (2 ^ 16). rewrite gc_bits_le_mod by lia.
      rewrite gc_bits_le_rev by lia. assert (Hn' : Znth n lens = len).
      { rewrite Hlens, Znth_sublist by lia. rewrite Z.add_0_r. reflexivity. }
      unfold F.send_sym, F.bits_msb. rewrite Hn'. f_equal.
      apply gc_bits_le_eqm; [lia|].
      unfold F.code. rewrite Hn'. unfold c. apply Hinv. lia.
    + rewrite <- Hdl1. apply IH; rewrite ?Hdl1, ?Hfc1; auto; try lia.
      * rewrite upd_Znth_Zlength; lia.
      * intros l Hl. rewrite Hsub, filter_app, Zlength_app. simpl.
        destruct (Z.eq_dec l len) as [->|Hne].
        -- rewrite upd_Znth_same by lia. rewrite Z.eqb_refl. unfold u16. rewrite Z.mod_mod by lia.
           unfold c. rewrite Z.add_mod, Hinv, <- Z.add_mod by lia. f_equal.
           rewrite Zlength_cons, Zlength_nil. lia.
        -- rewrite upd_Znth_diff' by lia. rewrite Hinv by lia.
           destruct (Z.eqb_spec len l); [lia|]. rewrite Zlength_nil. f_equal; lia.
Qed.

Theorem gc_canon_ok : gc_canon_stmt.
Proof.
  intros t mc blc Hmc Hfc Hdl Hr Hblc x Hx Hxz.
  set (lens := sublist 0 (mc + 1) (dl t)).
  destruct (gc_next_code_ok lens blc Hblc) as [Hnl Hnc].
  unfold gen_codes. apply (gc_loop_main lens); auto; try lia.
  intros l Hl. rewrite Hnc by lia. rewrite sublist_nil, Zlength_nil, Z.add_0_r. reflexivity.
Qed.
