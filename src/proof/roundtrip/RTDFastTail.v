(** * RT-D part FAST, piece: ftail_stmt (statement and definitions: RTDFastKit.v). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDFastKit.
Require Zlib.proof.huffman.Lemmas.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** set_insert_end only changes insert, which kcore reads only at lookahead >= MIN_MATCH *)
Lemma ftail_kcore_ins dict D BS syms s :
  d_lookahead s = 0 -> kcore dict D BS syms s -> kcore dict D BS syms (set_insert_end s).
Proof.
  intros H0 ((K1 & K2 & K3 & K4 & K5 & K6 & K7) & Kh1 & Kh2).
  split; [split; [exact K1|split; [exact K2|split; [exact K3|split; [exact K4|split; [exact K5|split; [exact K6|exact K7]]]]]]|].
  split; [exact Kh1|]. intros _ L. cbn [set_insert_end set_d_insert d_lookahead] in L. unfold MIN_MATCH in L. lia.
Qed.

(** FLUSH_BLOCK_ONLY at the tail: one block, the symbols cleared *)
Lemma ftail_block s z flush dict D BS syms p last s'' z'' :
  fbo_fspec ->
  W s -> outok s -> quiet s -> zall z -> adler_ok (d_wrap s) (z_adler z) -> fn_of s = 1 ->
  0 <= flush <= 5 -> d_lookahead s = 0 -> d_strstart s < d_w_size s + MAX_DIST s ->
  kcore dict D BS syms s -> 0 <= p -> (p - d_bi_valid s) mod 8 = 0 ->
  0 <= last <= 1 -> (last = 1 -> flush = Z_FINISH) ->
  (last = 0 -> Zlength syms = d_L s - 1 \/ (flush <> Z_NO_FLUSH /\ flush <> Z_FINISH)) ->
  c_flush_block_only (set_insert_end s) z last = Some (s'', z'') ->
  exists x blk,
    zstep (d_wrap s) z z'' 0 x /\
    kcore dict D (BS ++ [blk]) [] s'' /\
    F.bytes_bits (x ++ pend s'') ++ bibits s'' = bibits s ++ enc_out p [blk] (last =? 1).
Proof.
  intros Hfbo2 HW Ho Hq Hz Ha Hfn Hfl Hla Hss Hk Hpp Hp0 Hl Hl1 Hl0 E.
  destruct Zlib.proof.huffman.Lemmas.huffman_lemmas as [Hov _].
  destruct (trees_ok2 Hov) as (_ & Htf & Hroom).
  pose proof (fbo_ok Htf Hroom) as Hfb.
  set (s1 := set_insert_end s) in *.
  assert (HW1 := tail_W_ins s HW).
  assert (Hss1 : d_strstart s1 < d_window_size s1).
  { destruct HW as (_ & Hs & _). destruct Hs as (_ & _ & Hwsz & _).
    cbn [s1 set_insert_end set_d_insert d_strstart d_window_size].
    unfold MAX_DIST, MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in Hss. lia. }
  destruct (W_TS0 s1 HW1 Ho Hq Hfn Hss1) as (syms0 & HT0 & HL2).
  assert (Hk1 : kcore dict D BS syms s1) by (apply ftail_kcore_ins; assumption).
  pose proof HT0 as (Hp & Hs & Hpos & Hw & Hh & Hm & Ht & HL & Hf & Hb & Ho1 & Hq1 & Hfn1 & Hss2).
  assert (Hlev := fn_of_fast s1 Hp Hfn1).
  assert (Hma : d_match_available s1 = 0).
  { destruct Hm as (_ & _ & [A|A] & _ & B); [exact A|]. destruct (B A) as (C & _). lia. }
  destruct (kcore_kt _ _ _ _ _ Hma Hk1) as (Hkt & Hwt).
  assert (syms0 = syms) by (destruct Hwt as (Hwt & _); exact (tree_ok_uniq _ _ _ _ Ht Hwt)). subst syms0.
  destruct (fbw_ok Hfb s1 z flush syms last HT0 Hz Ha Hfl Hl Hl1 Hl0)
    as (s3 & z3 & e & Hc3 & Hcr & _ & _ & _ & _ & Hla3 & Hss3 & Hbs3 & _).
  rewrite Hc3 in E. injection E as <- <-.
  pose proof Hp as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15).
  pose proof Hs as (S1 & S2 & S3 & S4 & S5).
  pose proof Hpos as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
  assert (Hws : d_w_size s1 <= 32768).
  { rewrite P2. assert (2 ^ d_w_bits s1 <= 2 ^ 15) by (apply Z.pow_le_mono_r; lia).
    change (2 ^ 15) with 32768 in H. lia. }
  pose proof Hz as [Hzi Hzo0]. pose proof Hzo0 as (Z1 & Z2 & Z3).
  assert (Hpre : fbo_pre s1 z syms last).
  { unfold fbo_pre. split; [exact Hp|]. split; [exact Hs|]. split; [lia|]. split; [exact Ht|].
    split; [exact HL|]. split; [exact Hb|]. split; [lia|]. split; [lia|].
    split; [intros Hbs; split; [lia|split; [lia|]]; intros i Hi; apply Hw; lia|].
    split; [exact Ho1|]. split; [exact Hq1|]. split; [exact Hl|]. exact Hzo0. }
  destruct (Hfb s1 z syms last Hpre) as (s2 & z2 & x0 & buf & Hc & _ & _ & _ & _ & _ & Hkeep & Hbs'
    & Ht' & Hcfg & _).
  rewrite Hc3 in Hc. injection Hc as <- <-.
  destruct Hkt as (K1 & K4 & K5 & K6 & K7 & Kh).
  destruct (Hfbo2 s1 z s3 z3 syms last dict D BS p Hpre K1 K4 K5 K6 K7 Hpp Hp0 Hc3)
    as (x & blk & Zo & Bok & Bex & Bits).
  assert (Hav : 0 <= z_avail_out z3) by (eapply fbw_fbo_avail; [exact Hc3|exact Z1]).
  exists x, blk. split; [exact (zout_only_zstep _ _ _ _ Hz Ha Zo Hav)|].
  split; [|exact Bits].
  assert (E_wb : d_w_bits s3 = d_w_bits s1) by exact (f_equal d_w_bits Hkeep).
  assert (E_ma : d_match_available s3 = d_match_available s1) by exact (f_equal d_match_available Hkeep).
  assert (E_lev : d_level s3 = d_level s1) by exact (f_equal (fun c => snd (fst c)) Hcfg).
  destruct Hcr as (HW3 & _).
  destruct HW3 as (_ & _ & _ & _ & _ & _ & _ & sy & Hwt3).
  assert (sy = []) by (destruct Hwt3 as (Hwt3 & _); exact (tree_ok_uniq _ _ _ _ Hwt3 Ht')). subst sy.
  split.
  - split.
    { assert (Kw : kwin (dict ++ D) (fbo_keep s1)) by exact K1. rewrite <- Hkeep in Kw. exact Kw. }
    split; [unfold kmatch; intros A; lia|].
    split; [exact Hwt3|].
    rewrite E_wb, Hla3, Hss3, Hbs3. split; [exact Bok|]. split; [exact Bex|].
    split; [exact I|]. rewrite E_ma, Hma, Z.sub_0_r. exact Bex.
  - destruct Kh as (Kh1 & _). split.
    + rewrite E_lev. assert (E0 : (d_level s1 =? 0) = false) by (apply Z.eqb_neq; lia).
      rewrite E0. rewrite E0 in Kh1.
      assert (Kc : chain_hok (fbo_keep s1)) by exact Kh1. rewrite <- Hkeep in Kc. exact Kc.
    + intros _ L. rewrite Hla3 in L. cbn [s1 set_insert_end set_d_insert d_lookahead] in L. unfold MIN_MATCH in L. lia.
Qed.

Theorem ftail_ok : ftail_stmt.
Proof.
  intros s z flush s' z' bs dict D BS syms p Hfbo2 HW Ho Hq Hz Ha Hfn Hfl Hnf Hla Hai Hss Hdict HD Hk Hpp Hp0 Ec.
  unfold c_deflate_tail in Ec.
  destruct (Z.eqb_spec flush Z_FINISH) as [EF|EF].
  - unfold c_flush_block in Ec.
    destruct (c_flush_block_only (set_insert_end s) z 1) as [[s2 z2]|] eqn:E; [|discriminate]. cbn [bind] in Ec.
    destruct (ftail_block s z flush dict D BS syms p 1 s2 z2 Hfbo2 HW Ho Hq Hz Ha Hfn Hfl Hla Hss Hk Hpp Hp0
                ltac:(lia) ltac:(intros; exact EF) ltac:(intros; lia) E) as (x & blk & Zs & K & B).
    assert (Hb : s' = s2 /\ z' = z2 /\ fin_bs bs = true).
    { destruct (_ && _); cbn in Ec; injection Ec as <- <- <-; auto. }
    destruct Hb as (-> & -> & Hfin).
    exists x, [blk], []. rewrite Hfin. split; [exact Zs|]. split; [exact K|]. split; [exact B|].
    intros _; discriminate.
  - destruct (Z.eqb_spec (d_sym_next (set_insert_end s)) 0) as [S0|S0]; cbn [negb] in Ec.
    + injection Ec as <- <- <-.
      assert (Hsy : syms = []).
      { destruct Hk as ((_ & _ & (Ht & _) & _) & _). exact (tail_syms_nil _ _ Ht S0). }
      subst syms.
      exists [], [], []. rewrite app_nil_r. split; [apply zstep_refl; auto|].
      split; [apply ftail_kcore_ins; auto|].
      split; [|cbn; discriminate].
      rewrite (quiet_pend (set_insert_end s) Hq). cbn. rewrite app_nil_r. reflexivity.
    + unfold c_flush_block in Ec.
      destruct (c_flush_block_only (set_insert_end s) z 0) as [[s2 z2]|] eqn:E; [|discriminate]. cbn [bind] in Ec.
      destruct (ftail_block s z flush dict D BS syms p 0 s2 z2 Hfbo2 HW Ho Hq Hz Ha Hfn Hfl Hla Hss Hk Hpp Hp0
                  ltac:(lia) ltac:(intros; lia) ltac:(intros; right; split; assumption) E) as (x & blk & Zs & K & B).
      assert (Hb : s' = s2 /\ z' = z2 /\ fin_bs bs = false).
      { destruct (_ && _); cbn in Ec; injection Ec as <- <- <-; auto. }
      destruct Hb as (-> & -> & Hfin).
      exists x, [blk], []. rewrite Hfin. split; [exact Zs|]. split; [exact K|]. split; [exact B|].
      intros; discriminate.
Qed.
