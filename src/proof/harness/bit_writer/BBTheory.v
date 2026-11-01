(* Law rj_bad_block: the theory (BBFacts.v).  Kinds 2 and 3 (fixed-Huffman literals then the code 286/287, or the
   length code 257 then the distance code 30/31) from the fixed-block run theory (FRFacts.v); kinds 0 (stored,
   NLEN not the complement of LEN), 1 (BTYPE 11) and 4 (HLIT 30/31) from the block header alone. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.bit_writer.FRFacts.
Require Import Zlib.proof.harness.bit_writer.BBFacts.
Require Import Zlib.proof.harness.bit_writer.BBRun.
Require Import Zlib.proof.rfc1951.DecKit.
Import ListNotations.
Local Open Scope Z_scope.

(* the reasons fr_stop gives for a call to return early do not apply when everything up to fr_end is offered, the
   output space holds all the literals, the tail is not a far distance and (for Z_TREES) the call does not start
   at the block header *)
Lemma bbt_nostop C pos used ninp nob now aout flush :
  (flush = Z_TREES -> pos <> 0) -> 0 <= nob -> Zlength (fr_lits C) <= aout -> ~ is_far (fr_tail C) ->
  fr_end C <= 8 * (pos + ninp) -> ~ fr_stop C pos used ninp nob now aout flush.
Proof.
  intros Ht Hn Ha Hf He. unfold fr_stop.
  intros [(F & P & _) | [(N & [Lt | (Fa & _)]) | X]]; [apply Ht in F; contradiction | lia | contradiction | lia].
Qed.

(* kinds 2 and 3: the first call is offered the whole stream with room for every literal; it reaches the error, or
   (flush = Z_TREES) stops at the end of the block header after one byte, and then the second call reaches it *)
Lemma bbt_fr I (FI: fr_facts I) C S sp w L z flush res :
  fr_ok C -> fr_src C = S -> ~ is_far (fr_tail C) -> -15 <= w <= -8 -> l_s L = l_s (init_live sp w) ->
  live_ok L -> zf_ok z -> Zlength (fr_lits C) <= zf_ao z -> Int.min_signed <= flush <= Int.max_signed ->
  Zlength S <= Int.max_unsigned ->
  run2 flush lenfix_list distfix_list (m_init z L S) res ->
  (flush = Z_TREES -> r_ret res = Z_OK /\ m_ow (r_m res) = [] /\ m_snx (r_m res) = 1) ->
  r_ret res = Z_DATA_ERROR \/
  (r_ret res = Z_OK /\ flush = Z_TREES /\ m_ow (r_m res) = [] /\
   forall L' z' res',
     l_s L' = m_s (r_m res) -> live_ok L' -> zf_ok z' -> Zlength (fr_lits C) <= zf_ao z' ->
     run2 flush lenfix_list distfix_list (m_init z' L' (sublist (m_snx (r_m res)) (Zlength S) S)) res' ->
     r_ret res' = Z_DATA_ERROR).
Proof.
  intros Hok HS Hnf Hw HL Hlive Hz Hao Hfl HSl Hrun Htr.
  pose proof Hok as (_ & _ & _ & _ & Hend & _).
  rewrite HS in Hend.
  assert (W0 : i_wsize (l_s L) = 0) by (rewrite HL; apply (bbt_init sp w Hw)).
  assert (I0 : I C 0 [] (l_s L)) by (rewrite HL; apply (fr_init I FI); auto).
  assert (Hcall := fr_call I FI C 0 [] L z S flush res Hok I0 Hlive Hz ltac:(lia)
                     ltac:(rewrite HS; lia) ltac:(rewrite HS, Z.add_0_l, sublist_same; reflexivity || lia)
                     HSl Hfl Hrun).
  destruct Hcall as (Hsnx & Hsow & Hlow & Hws & Hcase).
  rewrite Zlength_nil in Hcase.
  destruct (Z.eq_dec flush Z_TREES) as [Ft|Ft].
  - destruct (Htr Ft) as (R1 & O1 & N1).
    rewrite O1, N1 in *.
    destruct Hcase as [(R & _) | [(R & _) | (_ & _ & I1)]]; [rewrite R1 in R; discriminate R | rewrite R1 in R; discriminate R |].
    right. split; [exact R1|]. split; [exact Ft|]. split; [reflexivity|].
    intros L' z' res' HL' Hlive' Hz' Hao' Hrun'.
    assert (W1 : i_wsize (l_s L') = 0) by (rewrite HL'; apply Hws; auto).
    set (inp := sublist 1 (Zlength S) S) in *.
    assert (Li : Zlength inp = Zlength S - 1) by (unfold inp; rewrite Zlength_sublist; lia).
    assert (I1' : I C 1 [] (l_s L')) by (rewrite HL'; exact I1).
    assert (Hcall := fr_call I FI C 1 [] L' z' inp flush res' Hok I1' Hlive' Hz' ltac:(lia)
                       ltac:(rewrite HS; lia)
                       ltac:(rewrite HS, Li; replace (1 + (Zlength S - 1)) with (Zlength S) by lia; reflexivity)
                       ltac:(lia) Hfl Hrun').
    destruct Hcall as (_ & _ & _ & _ & Hcase').
    rewrite Zlength_nil in Hcase'.
    destruct Hcase' as [(R & _) | [(R & [St | Wn]) | (_ & St & _)]]; [exact R | | contradiction |];
      exfalso; revert St; apply bbt_nostop; auto; try lia.
  - destruct Hcase as [(R & _) | [(R & [St | Wn]) | (_ & St & _)]]; [left; exact R | | contradiction |];
      exfalso; revert St; apply bbt_nostop; auto; try lia.
Qed.


(* the Z_TREES stop of kinds 2 and 3: after the fixed block header (one byte) the call returns Z_OK, nothing
   written, one byte consumed *)
Lemma bbt_trees z L S sp w res x c :
  -15 <= w <= -8 -> l_s L = l_s (init_live sp w) -> 0 < Zlength S ->
  Znth 0 S = x + 2 * 1 + 8 * c -> 0 <= x <= 1 -> 0 <= c < 32 ->
  run2 Z_TREES lenfix_list distfix_list (m_init z L S) res ->
  r_ret res = Z_OK /\ m_ow (r_m res) = [] /\ m_snx (r_m res) = 1.
Proof.
  intros Hw HL Hl E Hx Hc (o & Lp & Ro).
  destruct (bbt_hdr Z_TREES lenfix_list distfix_list z L S sp w o x 1 c Hw HL Hl E Hx ltac:(lia) Hc Lp)
    as (m2 & M2 & L2).
  change (andb (1 =? 1) (Z_TREES =? Z_TREES)) with true in M2, L2. cbv iota in L2. subst o.
  assert (Ok : leave_ok Z_TREES m2 = false).
  { unfold leave_ok, m_left. rewrite (mv_wsize _ _ _ _ _ _ _ M2), (mv_out _ _ _ _ _ _ _ M2), (mv_ow _ _ _ _ _ _ _ M2).
    rewrite Zlength_nil, Z.sub_0_r, !Z.eqb_refl. reflexivity. }
  inversion Ro as [Ok' _|]; [congruence|].
  destruct (bbt_lf _ _ Ok) as (-> & -> & ->).
  rewrite (mv_ow _ _ _ _ _ _ _ M2), (mv_nx _ _ _ _ _ _ _ M2), (mv_ret _ _ _ _ _ _ _ M2).
  replace (m_in m2 - m_have m2) with 1
    by (unfold m_have; rewrite (mv_in _ _ _ _ _ _ _ M2), (mv_inp _ _ _ _ _ _ _ M2), (mv_nx _ _ _ _ _ _ _ M2); lia).
  auto.
Qed.

Lemma bb_theory : fr_theory_stmt -> bb_bits_stmt -> bb_theory_stmt.
Proof.
  intros [I FI] BB S0 kind which lits w sp L z flush res Hok Hw HL Hlive Hz Hao Hfl.
  cbv zeta. intros Hrun.
  pose proof (BB S0 kind which lits Hok) as HB. cbv zeta in HB.
  set (S := bb_bytes S0 kind which lits) in *.
  set (Rest := concat (map (send_sym fixed_ll) lits) ++ bb_tail_bits kind which) in HB.
  set (B := bits_le (bb_btype kind) 2 ++ Rest) in HB.
  destruct HB as (HlS & HbS & Hfit & Hbits).
  pose proof Hok as (Hk & Hwh & Hlits & Hbl & Hll & HbS0 & HS0 & Hk0).
  assert (LB : Zlength B = 2 + Zlength Rest) by (unfold B; rewrite Zlength_app, dkit_bits_le_len; lia).
  assert (Hfit' : 1 + Zlength B <= 8 * Zlength S) by lia.
  pose proof (Zlength_nonneg Rest) as LR. pose proof (Zlength_nonneg lits) as LL.
  assert (Hhd : sublist 1 3 (bytes_bits S) = bits_le (bb_btype kind) 2).
  { pose proof (bbt_sub S B 0 2 Hbits Hfit' ltac:(lia) ltac:(lia)) as X.
    change (1 + 0) with 1 in X. change (1 + 2) with 3 in X. rewrite X. unfold B.
    rewrite sublist_app1 by (rewrite ?dkit_bits_le_len; lia).
    apply sublist_same; [lia | rewrite dkit_bits_le_len; lia]. }
  assert (Hrest : sublist 3 (1 + Zlength B) (bytes_bits S) = Rest).
  { pose proof (bbt_sub S B 2 (Zlength B) Hbits Hfit' ltac:(lia) ltac:(lia)) as X.
    change (1 + 2) with 3 in X. rewrite X, LB. unfold B.
    rewrite sublist_app2 by (rewrite ?dkit_bits_le_len; lia). rewrite dkit_bits_le_len by lia.
    apply sublist_same; lia. }
  destruct (bbt_byte0 S HbS ltac:(lia)) as (E0 & Rx & Rc). rewrite Hhd in E0.
  set (x := bval (sublist 0 1 (bytes_bits S))) in *.
  set (c := bval (sublist 3 8 (bytes_bits S))) in *.
  pose proof Hrun as (o & Lp & Ro).
  assert (kind = 0 \/ kind = 1 \/ kind = 2 \/ kind = 3 \/ kind = 4) as [K|[K|[K|[K|K]]]] by lia; subst kind.
  - (* stored, NLEN not ~LEN *)
    change (bval (bits_le (bb_btype 0) 2)) with 0 in E0.
    destruct (bbt_hdr flush lenfix_list distfix_list z L S sp w o x 0 c Hw HL ltac:(lia) E0 Rx ltac:(lia) Rc Lp)
      as (m2 & M2 & L2).
    assert (M2' : mv m2 S STORED 1 c 5 0) by exact M2.
    assert (L2' : loop2 flush lenfix_list distfix_list m2 o) by exact L2.
    destruct (bbt_stored flush lenfix_list distfix_list m2 S c M2' Rc ltac:(lia) HbS (Hk0 eq_refl))
      as (m3 & H3 & Bm & Lv3 & Ws3).
    pose proof (bbt_next _ _ _ _ _ _ H3 ltac:(rewrite Lv3; discriminate) L2') as L3.
    left. exact (bbt_bad _ _ _ _ _ res Bm Ws3 L3 Ro).
  - (* BTYPE 11 *)
    change (bval (bits_le (bb_btype 1) 2)) with 3 in E0.
    destruct (bbt_hdr flush lenfix_list distfix_list z L S sp w o x 3 c Hw HL ltac:(lia) E0 Rx ltac:(lia) Rc Lp)
      as (m2 & M2 & L2).
    assert (M2' : mv m2 S BAD 1 c 5 0) by exact M2.
    assert (L2' : loop2 flush lenfix_list distfix_list m2 o) by exact L2.
    left. exact (bbt_bad _ _ _ _ _ res (mv_mode _ _ _ _ _ _ _ M2') (mv_wsize _ _ _ _ _ _ _ M2') L2' Ro).
  - (* literals, then the literal/length code 286 + which *)
    change (bval (bits_le (bb_btype 2) 2)) with 1 in E0.
    set (C := FRC S lits (TLL which)).
    assert (Hfr : fr_ok C).
    { unfold fr_ok, fr_end, fr_body, C. cbn [fr_src fr_lits fr_tail].
      rewrite (proj1 (bbt_tail which Hwh)). fold Rest.
      replace (3 + Zlength Rest) with (1 + Zlength B) by lia.
      split; [exact HbS|]. split.
      { eapply Forall_impl; [|exact Hbl]. intros l Hl'. cbv beta in Hl' |- *. change Byte.max_unsigned with 255 in Hl'. lia. }
      split; [rep_lia|]. split; [cbn; lia|]. split; [lia|]. split; [rewrite Hhd; reflexivity|]. exact Hrest. }
    apply (bbt_fr I FI C S sp w L z flush res Hfr eq_refl (fun f => f) Hw HL Hlive Hz Hao Hfl ltac:(lia) Hrun).
    intros Ft. rewrite Ft in Hrun. exact (bbt_trees z L S sp w res x c Hw HL ltac:(lia) E0 Rx Rc Hrun).
  - (* literals, then the length code 257 and the distance code 30 + which *)
    change (bval (bits_le (bb_btype 3) 2)) with 1 in E0.
    set (C := FRC S lits (TDCode which)).
    assert (Hfr : fr_ok C).
    { unfold fr_ok, fr_end, fr_body, C. cbn [fr_src fr_lits fr_tail].
      rewrite (proj2 (bbt_tail which Hwh)). fold Rest.
      replace (3 + Zlength Rest) with (1 + Zlength B) by lia.
      split; [exact HbS|]. split.
      { eapply Forall_impl; [|exact Hbl]. intros l Hl'. cbv beta in Hl' |- *. change Byte.max_unsigned with 255 in Hl'. lia. }
      split; [rep_lia|]. split; [cbn; lia|]. split; [lia|]. split; [rewrite Hhd; reflexivity|]. exact Hrest. }
    apply (bbt_fr I FI C S sp w L z flush res Hfr eq_refl (fun f => f) Hw HL Hlive Hz Hao Hfl ltac:(lia) Hrun).
    intros Ft. rewrite Ft in Hrun. exact (bbt_trees z L S sp w res x c Hw HL ltac:(lia) E0 Rx Rc Hrun).
  - (* dynamic block, HLIT 30 + which *)
    change (bval (bits_le (bb_btype 4) 2)) with 2 in E0.
    assert (Hl0 : lits = []) by (apply Hlits; discriminate).
    assert (ER : Rest = bits_le (30 + which) 5) by (unfold Rest; rewrite Hl0; reflexivity).
    assert (Hc4 : c = 30 + which).
    { assert (L8 : 1 + Zlength B = 8) by (rewrite LB, ER, dkit_bits_le_len; lia).
      assert (Lb : Zlength (bytes_bits S) = 8 * Zlength S) by apply dkit_bytes_bits_len.
      assert (X : sublist 3 8 (bytes_bits S) = sublist 0 5 (sublist 3 (1 + Zlength B) (bytes_bits S)))
        by (rewrite L8, sublist_sublist by lia; reflexivity).
      unfold c. rewrite X, Hrest, ER. assert (which = 0 \/ which = 1) as [W|W] by lia; subst which; reflexivity. }
    destruct (bbt_hdr flush lenfix_list distfix_list z L S sp w o x 2 c Hw HL ltac:(lia) E0 Rx ltac:(lia) Rc Lp)
      as (m2 & M2 & L2).
    assert (M2' : mv m2 S TABLE 1 c 5 0) by exact M2.
    assert (L2' : loop2 flush lenfix_list distfix_list m2 o) by exact L2.
    destruct (bbt_table flush lenfix_list distfix_list m2 S c M2' ltac:(lia) ltac:(lia) HbS)
      as (m3 & H3 & Bm & Lv3 & Ws3).
    pose proof (bbt_next _ _ _ _ _ _ H3 ltac:(rewrite Lv3; discriminate) L2') as L3.
    left. exact (bbt_bad _ _ _ _ _ res Bm Ws3 L3 Ro).
Qed.
