(* Part of DecDec.group_dec: NEEDBITS(n) reading n extra bits.  Statement: DecDecDefs.v. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.rfc1951.DecDecDefs.
Import ListNotations.
Local Open Scope Z_scope.

Lemma need_bval_seq v s k : 0 <= v ->
  bval (map (fun i => Z.testbit v (Z.of_nat i)) (seq s k)) = Z.shiftr v (Z.of_nat s) mod 2 ^ Z.of_nat k.
Proof.
  intros Hv. revert s. induction k as [|k IH]; intros s.
  - cbn. symmetry. apply Z.mod_1_r.
  - cbn [seq map bval]. rewrite IH.
    set (w := Z.shiftr v (Z.of_nat s)).
    assert (Hw : 0 <= w) by (apply Z.shiftr_nonneg; lia).
    replace (Z.shiftr v (Z.of_nat (S s))) with (w / 2).
    2:{ unfold w. rewrite Nat2Z.inj_succ, <- Z.add_1_r, <- Z.shiftr_shiftr by lia.
        rewrite (Z.shiftr_div_pow2 _ 1) by lia. reflexivity. }
    replace (Z.testbit v (Z.of_nat s)) with (Z.testbit w 0).
    2:{ unfold w. rewrite Z.shiftr_spec by lia. f_equal. }
    rewrite Z.bit0_mod.
    replace (2 ^ Z.of_nat (S k)) with (2 * 2 ^ Z.of_nat k) by (rewrite Nat2Z.inj_succ, Z.pow_succ_r; lia).
    rewrite Z.rem_mul_r by lia. reflexivity.
Qed.

Lemma need_bval_bits_le v n : 0 <= v -> 0 <= n -> bval (bits_le v n) = v mod 2 ^ n.
Proof.
  intros Hv Hn. unfold bits_le. rewrite need_bval_seq by lia.
  rewrite Z.shiftr_0_r, Z2Nat.id by lia. reflexivity.
Qed.

Lemma need_gen (K: dkit_stmt) G pos inp n v q k m :
  in_ctx G pos inp -> m_buf G pos inp m -> q = 8 * (pos + m_nx m) - m_bits m -> m_leave m = 0 ->
  1 <= n <= 15 -> 0 <= v < 2 ^ n ->
  sublist q (q + n) (sbits G) = bits_le v n -> q + n <= 8 * slen G ->
  m_bits m < n + 8 -> n <= m_bits m + 8 * Z.of_nat k ->
  exists nx h b lv,
    needbits_f k n m = set_m_leave (set_m_bits (set_m_hold (set_m_nx m nx) h) b) lv /\
    m_nx m <= nx <= Zlength inp /\ hold_ok G (pos + nx) h b /\ 8 * (pos + nx) - b = q /\
    ((lv = 1 /\ nx = Zlength inp /\ b < n /\ pos + Zlength inp < slen G) \/
     (lv = 0 /\ n <= b < n + 8 /\ h mod 2 ^ n = v)).
Proof.
  intros HC. revert m. induction k as [|k IH]; intros m HB Hq HL Hn Hv HS Hsl Hb Hk.
  - destruct HB as (Hi & Hnx & HO).
    exists (m_nx m), (m_hold m), (m_bits m), (m_leave m). split; [destruct m; reflexivity|].
    split; [lia|]. split; [exact HO|]. split; [lia|]. right. split; [lia|]. split; [lia|].
    rewrite (dk_bitsn K _ _ _ _ n HO) by lia. rewrite <- Hq, HS.
    rewrite need_bval_bits_le by lia. apply Z.mod_small. lia.
  - cbn [needbits_f]. destruct HB as (Hi & Hnx & HO).
    pose proof HO as (HO1 & HO2 & HO3).
    destruct (Z.ltb_spec (m_bits m) n) as [L|L].
    + destruct (Z.eqb_spec (m_have m) 0) as [H0|H0].
      * unfold m_have in H0. rewrite Hi in H0.
        exists (m_nx m), (m_hold m), (m_bits m), 1. split; [destruct m; reflexivity|].
        split; [lia|]. split; [exact HO|]. split; [lia|]. left. split; [lia|]. split; [lia|].
        split; lia.
      * unfold m_have in H0. rewrite Hi in H0. destruct HC as (HD & Hpos & Hlen & Hinp).
        assert (Hsrc : bytes_ok (dc_src G)) by (destruct HD as (_ & _ & _ & _ & _ & _ & X & _); exact X).
        assert (Hz : Znth (m_nx m) (m_inp m) = Znth (pos + m_nx m) (dc_src G)).
        { rewrite Hi. rewrite Hinp at 1. rewrite Znth_sublist by lia. f_equal; lia. }
        assert (HP : m_buf G pos inp (pull m)).
        { unfold m_buf. cbn [pull m_inp m_nx m_hold m_bits set_m_bits set_m_hold set_m_nx].
          split; [exact Hi|]. split; [lia|].
          unfold u32, u64. rewrite (Z.mod_small (m_bits m + 8)) by lia. rewrite Hz.
          replace (pos + (m_nx m + 1)) with (pos + m_nx m + 1) by lia.
          apply (dk_pull K); auto; lia. }
        assert (Hb' : m_bits (pull m) = m_bits m + 8).
        { cbn [pull m_bits set_m_bits]. unfold u32. apply Z.mod_small. lia. }
        assert (Hnx' : m_nx (pull m) = m_nx m + 1) by reflexivity.
        assert (Hl' : m_leave (pull m) = 0) by (cbn [pull m_leave set_m_bits set_m_hold set_m_nx]; exact HL).
        destruct (IH (pull m) HP ltac:(lia) Hl' Hn Hv HS Hsl
                   ltac:(lia) ltac:(lia)) as (nx & h & b & lv & E & R1 & R2 & R3 & R4).
        rewrite E. exists nx, h, b, lv. split; [destruct m; reflexivity|].
        split; [lia|]. split; [exact R2|]. split; [exact R3|]. exact R4.
    + exists (m_nx m), (m_hold m), (m_bits m), (m_leave m). split; [destruct m; reflexivity|].
      split; [lia|]. split; [exact HO|]. split; [lia|]. right. split; [lia|]. split; [lia|].
      rewrite (dk_bitsn K _ _ _ _ n HO) by lia. rewrite <- Hq, HS.
      rewrite need_bval_bits_le by lia. apply Z.mod_small. lia.
Qed.

Lemma need_ok : dkit_stmt -> need_stmt.
Proof.
  intros K G pos inp m n v q HC HB Hq HL Hn Hv HS Hsl Hb.
  pose proof HB as (_ & _ & HO1 & _).
  destruct (need_gen K G pos inp n v q 4 m HC HB Hq HL Hn Hv HS Hsl ltac:(lia) ltac:(cbn; lia))
    as (nx & h & b & lv & E & R).
  unfold needbits. rewrite E. exists nx, h, b.
  replace (m_leave (set_m_leave (set_m_bits (set_m_hold (set_m_nx m nx) h) b) lv)) with lv
    by (destruct m; reflexivity).
  split; [reflexivity|]. exact R.
Qed.
