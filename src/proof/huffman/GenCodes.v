(** * gen_codes: every code of a nonzero length is a proper code (below 2^len); the lengths are kept *)

From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.huffman.Model Zlib.proof.huffman.Bits.
Import ListNotations.
Local Open Scope Z_scope.

Lemma lor_even_bit : forall r (bb : bool), 0 <= r -> Z.lor (2 * r) (Z.b2z bb) = 2 * r + Z.b2z bb.
Proof.
  intros r bb Hr. apply Z.bits_inj'. intros n Hn. rewrite Z.lor_spec.
  destruct (Z.eq_dec n 0) as [->|Hn0].
  - rewrite Z.testbit_even_0. replace (Z.b2z bb) with (2 * 0 + Z.b2z bb) at 1 by lia.
    rewrite !Z.testbit_0_r. reflexivity.
  - replace n with (Z.succ (Z.pred n)) by lia.
    rewrite Z.testbit_even_succ by lia. rewrite Z.testbit_succ_r by lia.
    replace (Z.b2z bb) with (2 * 0 + Z.b2z bb) by lia. rewrite Z.testbit_succ_r by lia.
    rewrite Z.bits_0. apply orb_false_r.
Qed.

Lemma bi_reverse_loop_bound : forall fuel code r j len,
  (Z.to_nat len <= fuel)%nat -> 1 <= len -> 0 <= r < 2 ^ j -> 0 <= j ->
  let res := bi_reverse_loop fuel code (2 * r) len in
  exists r', res = 2 * r' /\ 0 <= r' < 2 ^ (j + len).
Proof.
  induction fuel as [|fuel IH]; intros code r j len Hf Hl Hr Hj; [lia|].
  cbn [bi_reverse_loop].
  assert (Eb : Z.land code 1 = Z.b2z (Z.odd code)).
  { change 1 with (Z.ones 1). rewrite Z.land_ones by lia. rewrite Zmod_odd. destruct (Z.odd code); reflexivity. }
  set (b := Z.land code 1).
  assert (Hb : 0 <= b <= 1) by (unfold b; rewrite Eb; destruct (Z.odd code); simpl; lia).
  assert (Hor : Z.lor (2 * r) b = 2 * r + b) by (unfold b; rewrite Eb; apply lor_even_bit; lia).
  rewrite Hor. rewrite Z.shiftl_mul_pow2 by lia. replace (2 ^ 1) with 2 by reflexivity.
  replace ((2 * r + b) * 2) with (2 * (2 * r + b)) by lia.
  assert (Hr' : 0 <= 2 * r + b < 2 ^ (j + 1)) by (rewrite Z.pow_add_r by lia; lia).
  destruct (Z.gtb_spec (len - 1) 0) as [Hgt|Hle].
  - destruct (IH (Z.shiftr code 1) (2 * r + b) (j + 1) (len - 1)) as [r' [E1 E2]]; try lia.
    exists r'. split; [exact E1|]. replace (j + len) with (j + 1 + (len - 1)) by lia. exact E2.
  - exists (2 * r + b). split; [reflexivity|]. replace (j + len) with (j + 1) by lia. exact Hr'.
Qed.

Lemma bi_reverse_bound : forall code len, 1 <= len <= 15 -> 0 <= bi_reverse code len < 2 ^ len.
Proof.
  intros code len Hl. unfold bi_reverse.
  destruct (bi_reverse_loop_bound 16 code 0 0 len ltac:(lia) ltac:(lia) ltac:(simpl; lia) ltac:(lia)) as [r' [E1 E2]].
  replace (2 * 0) with 0 in E1 by lia. rewrite E1.
  rewrite Z.shiftr_div_pow2 by lia. replace (2 ^ 1) with 2 by reflexivity.
  rewrite Z.mul_comm, Z.div_mul by lia. simpl in E2. exact E2.
Qed.

Lemma gen_codes_loop_spec : forall fuel mc t nc n,
  (forall i, 0 <= i <= mc -> Znth i (dl t) <> 0 -> 1 <= Znth i (dl t) <= 15) ->
  0 <= n -> (Z.to_nat (mc + 1 - n) <= fuel)%nat ->
  let t' := gen_codes_loop fuel mc t nc n in
  dl t' = dl t /\ Zlength (fc t') = Zlength (fc t) /\
  (forall i, (i < n \/ mc < i) -> Znth i (fc t') = Znth i (fc t)) /\
  (forall i, n <= i <= mc -> Znth i (dl t) <> 0 -> 0 <= i < Zlength (fc t) -> code_ok (fc t') (dl t') i).
Proof.
  induction fuel as [|fuel IH]; intros mc t nc n Hlen Hn Hf.
  - cbn [gen_codes_loop]. split; [reflexivity|]. split; [reflexivity|]. split; [auto|].
    intros i Hi. lia.
  - cbn [gen_codes_loop]. destruct (Z.leb_spec n mc) as [Hle|Hgt].
    + destruct (Z.eqb_spec (Znth n (dl t)) 0) as [Hz|Hnz].
      * destruct (IH mc t nc (n + 1) Hlen ltac:(lia) ltac:(lia)) as [A [B [C D]]].
        split; [exact A|]. split; [exact B|]. split; [intros i Hi; apply C; lia|].
        intros i Hi Hdi Hr. destruct (Z.eq_dec i n) as [->|Hin]; [contradiction|]. apply D; auto; lia.
      * set (len := Znth n (dl t)) in *.
        set (t1 := set_fc t n (u16 (bi_reverse (Znth len nc) len))).
        assert (Hlen1 : forall i, 0 <= i <= mc -> Znth i (dl t1) <> 0 -> 1 <= Znth i (dl t1) <= 15) by exact Hlen.
        destruct (IH mc t1 (upd_Znth len nc (u16 (Znth len nc + 1))) (n + 1) Hlen1 ltac:(lia) ltac:(lia))
          as [A [B [C D]]].
        assert (Hdl1 : dl t1 = dl t) by reflexivity.
        assert (HL1 : Zlength (fc t1) = Zlength (fc t)) by (unfold t1, set_fc; simpl; apply Zlength_upd_Znth_any).
        split; [rewrite A; exact Hdl1|]. split; [rewrite B; exact HL1|].
        split.
        { intros i Hi. rewrite C by lia. unfold t1, set_fc; simpl. apply Znth_upd_Znth_other. lia. }
        intros i Hi Hdi Hr. destruct (Z.eq_dec i n) as [->|Hin].
        -- assert (Hl := Hlen n ltac:(lia) Hnz). fold len in Hl.
           split; [rewrite A, Hdl1; exact Hl|].
           rewrite C by lia. rewrite A, Hdl1. fold len. unfold t1, set_fc; simpl.
           rewrite upd_Znth_same by lia. unfold u16.
           assert (Hb := bi_reverse_bound (Znth len nc) len Hl).
           assert (2 ^ len <= 2 ^ 15) by (apply Z.pow_le_mono_r; lia).
           rewrite Z.mod_small by (change (2 ^ 15) with 32768 in *; lia). exact Hb.
        -- apply D; auto; [lia|]. rewrite HL1. exact Hr.
    + split; [reflexivity|]. split; [reflexivity|]. split; [auto|]. intros i Hi. lia.
Qed.

Theorem gen_codes_spec : forall t mc bl_count,
  0 <= mc < HEAP_SIZE ->
  (forall i, 0 <= i <= mc -> Znth i (dl t) <> 0 -> 1 <= Znth i (dl t) <= 15) ->
  let t' := gen_codes t mc bl_count in
  dl t' = dl t /\ Zlength (fc t') = Zlength (fc t) /\
  (forall i, mc < i -> Znth i (fc t') = Znth i (fc t)) /\
  (forall i, 0 <= i <= mc -> Znth i (dl t) <> 0 -> i < Zlength (fc t) -> code_ok (fc t') (dl t') i).
Proof.
  intros t mc bl_count Hmc Hlen. unfold gen_codes.
  destruct (gen_codes_loop_spec (Z.to_nat HEAP_SIZE) mc t
              (gen_next_code 16 bl_count (repeat 0 (Z.to_nat (MAX_BITS + 1))) 0 1) 0 Hlen ltac:(lia)
              ltac:(unfold HEAP_SIZE in *; lia)) as [A [B [C D]]].
  split; [exact A|]. split; [exact B|]. split; [intros i Hi; apply C; lia|].
  intros i Hi Hdi Hr. apply D; auto; lia.
Qed.
