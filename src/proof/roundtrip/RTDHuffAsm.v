(* RT-D part HUFF: the assembly of comp_fspec 3 c_deflate_huff from the part statements of
   RTDHuffKit.v and the safety parts of the deflate laws (RTDLTCHuffKit.v statements, proved in RTDLTCHuff*.v).
   The loop invariant is the safety one ([HFI]) with the functional facts [FK]: the bytes consumed so far
   extend the history, the blocks emitted so far are [BS'], the bits added are their encoding. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDHuffKit.
Require Import Zlib.proof.roundtrip.RTDLTCHuffLoop Zlib.proof.roundtrip.RTDLTCHuffTail.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** Bits and blocks *)

Lemma ha_bits_le_len v n : 0 <= n -> Zlength (F.bits_le v n) = n.
Proof.
  intros H. unfold F.bits_le. rewrite Zlength_map, Zlength_correct, seq_length. lia.
Qed.

Lemma ha_bytes_bits_app a b : F.bytes_bits (a ++ b) = F.bytes_bits a ++ F.bytes_bits b.
Proof. unfold F.bytes_bits. apply flat_map_app. Qed.

Lemma ha_bytes_bits_len l : Zlength (F.bytes_bits l) = 8 * Zlength l.
Proof.
  induction l as [|b l IH]; [reflexivity|].
  change (F.bytes_bits (b :: l)) with (F.bits_le b 8 ++ F.bytes_bits l).
  rewrite Zlength_app, IH, ha_bits_le_len, Zlength_cons by lia. lia.
Qed.

Lemma ha_bibits_len s : 0 <= d_bi_valid s -> Zlength (bibits s) = d_bi_valid s.
Proof. intros H. unfold bibits. apply ha_bits_le_len. exact H. Qed.

Lemma ha_enc_from_app p bs b fin :
  enc_from p (bs ++ [b]) fin = enc_from p bs false ++ enc_from (p + Zlength (enc_from p bs false)) [b] fin.
Proof.
  revert p. induction bs as [|b0 bs IH]; intros p.
  - cbn [app enc_from]. rewrite Zlength_nil, Z.add_0_r. reflexivity.
  - cbn [app enc_from]. rewrite IH.
    assert (E : (fin && match bs ++ [b] with [] => true | _ :: _ => false end) = false)
      by (destruct bs; cbn; apply andb_false_r).
    rewrite E. cbn [andb]. rewrite <- app_assoc. f_equal. f_equal.
    rewrite Zlength_app, Z.add_assoc. reflexivity.
Qed.

Lemma ha_enc_out_app p bs b fin :
  enc_out p (bs ++ [b]) fin = enc_from p bs false ++ enc_out (p + Zlength (enc_from p bs false)) [b] fin.
Proof.
  unfold enc_out. rewrite ha_enc_from_app. destruct fin; [|reflexivity].
  rewrite <- app_assoc. f_equal. f_equal. f_equal. f_equal. rewrite Zlength_app, Z.add_assoc. reflexivity.
Qed.

Lemma ha_enc_out_false p bs : enc_out p bs false = enc_from p bs false.
Proof. reflexivity. Qed.

(** the bit position of the next block is on the same byte phase as the bit buffer *)
Lemma ha_phase s0 s p x E :
  0 <= d_bi_valid s -> 0 <= d_bi_valid s0 -> (p - d_bi_valid s0) mod 8 = 0 ->
  F.bytes_bits x ++ bibits s = bibits s0 ++ E -> (p + Zlength E - d_bi_valid s) mod 8 = 0.
Proof.
  intros H1 H2 Hp Hb. apply (f_equal (@Zlength bool)) in Hb.
  rewrite !Zlength_app, ha_bytes_bits_len, !ha_bibits_len in Hb by assumption.
  replace (p + Zlength E - d_bi_valid s) with ((p - d_bi_valid s0) + 8 * Zlength x) by lia.
  rewrite Z.add_mod, Hp by lia. rewrite Z.mul_comm, Z.mod_mul by lia. reflexivity.
Qed.

(** ** Small state facts *)

Lemma HS0_wtrees s syms : HS0 s syms -> Zlength syms <= d_L s - 2 -> wtrees s syms.
Proof.
  intros (Hp & Hs & Hpos & Hw & Hh & Hm & Ht & HL & Hf & Hb & Hlit & Ho & Hq & Hfn) HL2.
  assert (Hlev := fn_of_huff s Hp Hfn).
  assert (Ha : d_match_available s = 0).
  { destruct Hm as (_ & _ & [A|A] & _ & B); [exact A|]. destruct (B A) as (C & _). lia. }
  unfold wtrees. split; [exact Ht|]. split; [exact HL2|]. split; [exact Hf|].
  split; [intros; lia|]. intros _. rewrite Ha. lia.
Qed.

Lemma quiet_pend s : quiet s -> pend s = [].
Proof. intros (Q1 & _ & _). unfold pend. rewrite Q1, Z.add_0_r. apply sublist_nil. Qed.

Lemma HFI_bv s0 z0 flush s z evs : HFI s0 z0 flush s z evs -> 0 <= d_bi_valid s.
Proof.
  intros (_ & _ & (_ & _ & (_ & Hb & _) & _) & _). destruct Hb as (B & _). unfold d_bi_valid. lia.
Qed.

(** ** The loop *)

Section HuffF.
Hypothesis Href : hrefill_stmt.
Hypothesis Hbfl : hbflush_stmt.
Hypothesis Htail : htail_stmt.
Hypothesis Hflit : hflit_stmt.
Hypothesis Hfflush : hfflush_stmt.
Hypothesis Hfrefill : hfrefill_stmt.

Variables (s0 : dstate) (z0 : strm) (flush : Z) (dict D : list Z) (BS : list F.block) (p : Z).
Hypothesis Hfl : 0 <= flush <= 5.
Hypothesis Hfn0 : fn_of s0 = 3.
Hypothesis Hp0 : 0 <= p.
Hypothesis Hp8 : (p - d_bi_valid s0) mod 8 = 0.
Hypothesis Hbv0 : 0 <= d_bi_valid s0.

Definition Dk (k : Z) : list Z := D ++ sublist (z_next_in z0) (z_next_in z0 + k) (z_in z0).

(* the functional facts at a loop state *)
Definition FK (s : dstate) (z : strm) : Prop :=
  exists k x BS' syms,
    zstep (d_wrap s0) z0 z k x /\ wtrees s syms /\ hk3 dict (Dk k) (BS ++ BS') syms s /\
    F.bytes_bits x ++ bibits s = bibits s0 ++ enc_from p BS' false.

(* the facts of the result of the call *)
Definition FR (s : dstate) (z : strm) (bs : bstate) : Prop :=
  exists k x BS' syms,
    zstep (d_wrap s0) z0 z k x /\ kcore dict (Dk k) (BS ++ BS') syms s /\
    F.bytes_bits (x ++ pend s) ++ bibits s = bibits s0 ++ enc_out p BS' (fin_bs bs) /\
    (fin_bs bs = true -> BS' <> []).

Definition FP (a : dstate * strm) : Prop := (exists evs, HFI s0 z0 flush (fst a) (snd a) evs) /\ FK (fst a) (snd a).
Definition FQ (r : dexit) : Prop :=
  let '(s', z', o) := r in
  match o with
  | Some bs => FR s' z' bs
  | None => (exists evs, HFI s0 z0 flush s' z' evs) /\ FK s' z' /\
            d_lookahead s' = 0 /\ z_avail_in z' = 0 /\ flush <> Z_NO_FLUSH
  end.

Lemma HFI_W s z evs : HFI s0 z0 flush s z evs -> W s /\ fn_of s = 3.
Proof.
  intros (_ & _ & Hc & _). split; [exact (proj1 Hc)|]. rewrite (fn_of_hcrel _ _ _ _ _ _ Hc). exact Hfn0.
Qed.

(* a loop state that exits: the result facts *)
Lemma FK_FR s z evs bs : HFI s0 z0 flush s z evs -> FK s z -> fin_bs bs = false -> FR s z bs.
Proof.
  intros HI (k & x & BS' & syms & Hz & Ht & Hk & Hb) Hf.
  destruct (HFI_W s z evs HI) as [HW Hfn].
  assert (Hq : quiet s) by (destruct HI as (_ & _ & _ & Q & _); exact Q).
  exists k, x, BS', syms. split; [exact Hz|].
  split; [apply (proj2 (kcore_hk3 _ _ _ _ _ HW Hfn)); exact (conj Ht Hk)|].
  rewrite Hf, quiet_pend, app_nil_r by exact Hq. split; [exact Hb|]. intros E; discriminate E.
Qed.

(* FLUSH_BLOCK_ONLY at an [HS0] state reached from a loop state [s] (same stream z) *)
Lemma flush_FK s z evs k x BS' s3 syms3 last sa za :
  HFI s0 z0 flush s z evs -> zstep (d_wrap s0) z0 z k x ->
  F.bytes_bits x ++ bibits s = bibits s0 ++ enc_from p BS' false ->
  HS0 s3 syms3 -> hk3 dict (Dk k) (BS ++ BS') syms3 s3 -> bibits s3 = bibits s -> d_bi_valid s3 = d_bi_valid s ->
  0 <= last <= 1 ->
  c_flush_block_only s3 z last = Some (sa, za) ->
  exists x' blk,
    zstep (d_wrap s0) z0 za k (x ++ x') /\ wtrees sa [] /\ hk3 dict (Dk k) (BS ++ BS' ++ [blk]) [] sa /\
    F.bytes_bits ((x ++ x') ++ pend sa) ++ bibits sa = bibits s0 ++ enc_out p (BS' ++ [blk]) (last =? 1).
Proof.
  intros HI Hz Hb HS Hk Eb Ev Hl Ef.
  pose proof HI as (Hz0 & Ha0 & Hc & Hq & Hzz & Ha & _).
  assert (Hbv := HFI_bv _ _ _ _ _ _ HI).
  assert (Hph := ha_phase s0 s p x _ Hbv Hbv0 Hp8 Hb).
  destruct (Hfflush s3 z syms3 last sa za dict (Dk k) (BS ++ BS') (p + Zlength (enc_from p BS' false)) HS Hzz Hl Hk
              ltac:(pose proof (Zlength_nonneg (enc_from p BS' false)); lia) ltac:(rewrite Ev; exact Hph) Ef)
    as (x' & blk & Hzo & Ht' & Hk' & Hb').
  exists x', blk.
  assert (Hw : d_wrap s = d_wrap s0) by exact (wrap_hcrel _ _ _ _ _ _ Hc).
  assert (Hav : 0 <= z_avail_out za).
  { apply (flush_block_only_avail s3 z last sa za Ef). destruct Hzz as (_ & Z1 & _). exact Z1. }
  assert (Hz' : zstep (d_wrap s0) z za 0 x') by (rewrite <- Hw; exact (zout_only_zstep _ _ _ _ Hzz Ha Hzo Hav)).
  split.
  { pose proof (zstep_trans _ _ _ _ _ _ _ _ (proj1 Hz0) Ha0 Hz Hz') as T. rewrite Z.add_0_r in T. exact T. }
  split; [exact Ht'|]. split; [rewrite app_assoc; exact Hk'|].
  rewrite <- app_assoc, ha_bytes_bits_app, <- app_assoc, Hb', Eb, app_assoc.
  rewrite Hb, <- app_assoc, ha_enc_out_app. reflexivity.
Qed.

Lemma HFI_facts s z evs : HFI s0 z0 flush s z evs ->
  W s /\ huff_extra s /\ outok s /\ quiet s /\ fn_of s = 3 /\ zall z /\ adler_ok (d_wrap s) (z_adler z) /\
  d_wrap s = d_wrap s0.
Proof.
  intros (_ & _ & Hc & Hq & Hz & Ha & _).
  assert (Hfn := fn_of_hcrel _ _ _ _ _ _ Hc). rewrite Hfn0 in Hfn.
  assert (Hw := wrap_hcrel _ _ _ _ _ _ Hc).
  destruct Hc as (HW & He & Ho & _). auto 10.
Qed.

Lemma quiet_bv s s3 : quiet s -> quiet s3 -> hfr s s3 -> d_bi_valid s3 = d_bi_valid s.
Proof.
  intros (Q1 & _) (R1 & _) (_ & _ & _ & G). specialize (G 0). unfold Gb in G. lia.
Qed.

(* the literal step and [if (bflush) FLUSH_BLOCK(s, 0)] *)
Lemma lit_FP s z evs : HFI s0 z0 flush s z evs -> FK s z -> 1 <= d_lookahead s ->
  exists r, (let* (s, bf) := hlit s in c_bflush s z bf) = Some r /\
  match r with inl a' => FP a' | inr e => FQ e end.
Proof.
  intros HI HK Hla.
  destruct (HFI_facts s z evs HI) as (HW & He & Ho & Hq & Hfn & Hzz & Ha & Hw).
  destruct HK as (k & x & BS' & syms & Hz & Ht & Hk & Hb).
  destruct (Hflit s syms dict (Dk k) (BS ++ BS') HW He Ho Hq Hfn Hla Ht Hk)
    as (s3 & bf & c & E & HS & Hbf & Hfr & Hla3 & Hk3 & Eb3).
  assert (Hq3 : quiet s3) by (destruct HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Q & _); exact Q).
  assert (Ev3 := quiet_bv s s3 Hq Hq3 Hfr).
  rewrite E. cbn [bind].
  destruct (Hbfl s0 z0 flush s z evs s3 _ bf HI Hfl Hfn0 HS Hbf Hfr) as (r & Er & Hr).
  exists r. split; [exact Er|].
  destruct bf.
  - unfold c_bflush, c_flush_block in Er.
    destruct (c_flush_block_only s3 z 0) as [[sa za]|] eqn:Ef; [|discriminate Er]. cbn [bind] in Er.
    destruct (flush_FK s z evs k x BS' s3 _ 0 sa za HI Hz Hb HS Hk3 Eb3 Ev3 ltac:(lia) Ef)
      as (x' & blk & Hz' & Ht' & Hk' & Hb').
    change (0 =? 1) with false in Hb'.
    destruct ((z_avail_out za =? 0) && _); cbn [bind Z.eqb] in Er; injection Er as <-.
    + destruct Hr as (_ & evs' & Hc & _). cbn [FQ].
      assert (HW' := proj1 Hc). assert (Hfn' : fn_of sa = 3) by (rewrite (fn_of_hcrel _ _ _ _ _ _ Hc); exact Hfn0).
      exists k, (x ++ x'), (BS' ++ [blk]), []. split; [exact Hz'|].
      split; [apply (proj2 (kcore_hk3 _ _ _ _ _ HW' Hfn')); exact (conj Ht' Hk')|].
      split; [exact Hb'|]. intros D0; discriminate D0.
    + destruct Hr as ((evs' & HI') & _ & _). split; [exists evs'; exact HI'|].
      assert (Hqa : quiet sa) by (destruct HI' as (_ & _ & _ & Q & _); exact Q).
      exists k, (x ++ x'), (BS' ++ [blk]), []. split; [exact Hz'|]. split; [exact Ht'|]. split; [exact Hk'|].
      rewrite (quiet_pend sa Hqa), app_nil_r in Hb'. exact Hb'.
  - cbn [c_bflush] in Er. injection Er as <-.
    destruct Hr as ((evs' & HI') & _ & _). split; [exists evs'; exact HI'|].
    assert (HL : Zlength (syms ++ [(0, c)]) <= d_L s3 - 2).
    { destruct HS as (_ & _ & _ & _ & _ & _ & _ & L & _). symmetry in Hbf. apply Z.eqb_neq in Hbf. lia. }
    exists k, x, BS', (syms ++ [(0, c)]). split; [exact Hz|]. split; [exact (HS0_wtrees _ _ HS HL)|].
    split; [exact Hk3|]. cbn [fst snd]. rewrite Eb3. exact Hb.
Qed.

Lemma Dk_ext k x z k' z2 :
  zin_in z0 -> zstep (d_wrap s0) z0 z k x -> zstep (d_wrap s0) z z2 k' [] -> 0 <= k + k' <= z_avail_in z0 ->
  Dk k ++ sublist (z_next_in z) (z_next_in z + k') (z_in z) = Dk (k + k').
Proof.
  intros (_ & Hn & _ & Hl & _) (A1 & A2 & A3 & _) (B1 & B2 & _) Hkk.
  unfold Dk. rewrite <- app_assoc. f_equal. rewrite A1, A3.
  rewrite <- (sublist_split (z_next_in z0) (z_next_in z0 + k) (z_next_in z0 + k + k')) by lia.
  f_equal. lia.
Qed.

Lemma step_FP a : FP a ->
  (exists r, huff_body flush a = Some (inr r) /\ FQ r) \/
  (exists a', huff_body flush a = Some (inl a') /\ FP a').
Proof.
  destruct a as [s z]. intros [[evs HI] HK]. cbn [fst snd] in HI, HK.
  rewrite huff_body_eq. unfold hrefill.
  destruct (Z.eqb_spec (d_lookahead s) 0) as [Hl0|Hl0].
  - destruct (Href s0 z0 flush s z evs HI Hfn0 Hl0) as (s2 & z2 & E & HI2 & Hsum & Hz2).
    rewrite E. cbn [bind].
    destruct (HFI_facts s z evs HI) as (HW & He & Ho & Hq & Hfn & Hzz & Ha & Hw).
    destruct HK as (k & x & BS' & syms & Hz & Ht & Hk & Hb).
    destruct (Hfrefill s z s2 z2 syms dict (Dk k) (BS ++ BS') HW Hfn Hzz Ha Ht Hk E)
      as (k' & Hzs & Ht2 & Hk2 & Eb2 & Ep2).
    rewrite Hw in Hzs.
    assert (Hz0 : zall z0) by (destruct HI as (Z & _); exact Z).
    assert (Ha0 : adler_ok (d_wrap s0) (z_adler z0)) by (destruct HI as (_ & A & _); exact A).
    assert (Hzt := zstep_trans _ _ _ _ _ _ _ _ (proj1 Hz0) Ha0 Hz Hzs). rewrite app_nil_r in Hzt.
    assert (Hkk : 0 <= k + k' <= z_avail_in z0) by (destruct Hzt as (_ & B & _); exact B).
    rewrite (Dk_ext k x z k' z2 (proj1 Hz0) Hz Hzs Hkk) in Hk2.
    assert (HK2 : FK s2 z2).
    { exists (k + k'), x, BS', syms. split; [exact Hzt|]. split; [exact Ht2|]. split; [exact Hk2|].
      rewrite Eb2. exact Hb. }
    destruct (Z.eqb_spec (d_lookahead s2) 0) as [Hl2|Hl2].
    + left. destruct (Z.eqb_spec flush Z_NO_FLUSH) as [Hnf|Hnf].
      * eexists. split; [reflexivity|]. cbn [FQ]. exact (FK_FR s2 z2 evs need_more HI2 HK2 eq_refl).
      * eexists. split; [reflexivity|]. cbn [FQ]. split; [exists evs; exact HI2|].
        split; [exact HK2|]. split; [exact Hl2|]. split; [exact (Hz2 Hl2)|exact Hnf].
    + cbn [bind].
      destruct (lit_FP s2 z2 evs HI2 HK2 ltac:(destruct (HFI_facts s2 z2 evs HI2) as (HW2 & _);
                                               pose proof (W_la_bound s2 HW2); lia)) as (r & Er & Hr).
      rewrite Er. destruct r as [a'|e].
      * right. exists a'. split; [reflexivity|exact Hr].
      * left. exists e. split; [reflexivity|exact Hr].
  - cbn [bind].
    destruct (lit_FP s z evs HI HK ltac:(destruct (HFI_facts s z evs HI) as (HW & _);
                                         pose proof (W_la_bound s HW); lia)) as (r & Er & Hr).
    rewrite Er. destruct r as [a'|e].
    + right. exists a'. split; [reflexivity|exact Hr].
    + left. exists e. split; [reflexivity|exact Hr].
Qed.

Lemma loop2_FP : forall d a x, FP a -> loop2 d (huff_body flush) a = Some x ->
  match x with inl a' => FP a' | inr r => FQ r end.
Proof.
  induction d as [|d IH]; intros a x Ha E; cbn [loop2] in E.
  - destruct (step_FP a Ha) as [(r & Er & Hr)|(a' & Er & Ha')]; rewrite Er in E; injection E as <-; assumption.
  - destruct (loop2 d (huff_body flush) a) as [[a1|r1]|] eqn:E1.
    + exact (IH a1 x (IH a (inl a1) Ha E1) E).
    + injection E as <-. exact (IH a _ Ha E1).
    + discriminate E.
Qed.

Lemma loop_FQ d a r : FP a -> loop d (huff_body flush) a = Some r -> FQ r.
Proof.
  intros Ha E. unfold loop in E.
  destruct (loop2 d (huff_body flush) a) as [[a'|r']|] eqn:E2; try discriminate E.
  injection E as <-. exact (loop2_FP d a (inr r') Ha E2).
Qed.

(* after the loop: deflate_tail *)
Lemma tail_FR s z evs s' z' bs :
  HFI s0 z0 flush s z evs -> FK s z -> d_lookahead s = 0 -> z_avail_in z = 0 -> flush <> Z_NO_FLUSH ->
  c_deflate_tail (set_d_insert s 0) z flush = Some (s', z', bs) -> FR s' z' bs.
Proof.
  intros HI HK Hla Hai Hnf E.
  destruct (Htail s0 z0 flush s z evs HI Hfl Hfn0 Hnf Hla Hai) as (s2 & z2 & bs2 & evs' & E2 & Hc2 & _).
  rewrite E in E2. injection E2 as <- <- <-.
  assert (HW' := proj1 Hc2). assert (Hfn' : fn_of s' = 3) by (rewrite (fn_of_hcrel _ _ _ _ _ _ Hc2); exact Hfn0).
  destruct (HFI_facts s z evs HI) as (HW & He & Ho & Hq & Hfn & Hzz & Ha & Hw).
  destruct HK as (k & x & BS' & syms & Hz & Ht & Hk & Hb).
  set (s1 := set_d_insert s 0) in *.
  assert (HW1 : W s1) by exact (W_insert0 s HW).
  assert (Ht1 : wtrees s1 syms) by exact Ht.
  assert (Hk1 : hk3 dict (Dk k) (BS ++ BS') syms s1) by exact Hk.
  destruct (W_HS0_syms s1 syms HW1 Ht1 He Ho Hq Hfn) as [HS _].
  assert (Hlast : forall last sa za, 0 <= last <= 1 -> c_flush_block_only s1 z last = Some (sa, za) ->
    exists x' blk,
      zstep (d_wrap s0) z0 za k (x ++ x') /\ wtrees sa [] /\ hk3 dict (Dk k) (BS ++ BS' ++ [blk]) [] sa /\
      F.bytes_bits ((x ++ x') ++ pend sa) ++ bibits sa = bibits s0 ++ enc_out p (BS' ++ [blk]) (last =? 1))
    by (intros last sa za Hl Ef; exact (flush_FK s z evs k x BS' s1 syms last sa za HI Hz Hb HS Hk1
                                          eq_refl eq_refl Hl Ef)).
  unfold c_deflate_tail in E.
  destruct (flush =? Z_FINISH).
  - unfold c_flush_block in E.
    destruct (c_flush_block_only s1 z 1) as [[sa za]|] eqn:Ef; [|discriminate E]. cbn [bind] in E.
    destruct (Hlast 1 sa za ltac:(lia) Ef) as (x' & blk & Hz' & Ht' & Hk' & Hb').
    change (1 =? 1) with true in Hb'.
    destruct ((z_avail_out za =? 0) && _); cbn [bind Z.eqb Pos.eqb] in E; injection E as <- <- <-;
      (exists k, (x ++ x'), (BS' ++ [blk]), []; split; [exact Hz'|];
       split; [apply (proj2 (kcore_hk3 _ _ _ _ _ HW' Hfn')); exact (conj Ht' Hk')|];
       split; [exact Hb'|]; intros _; destruct BS'; discriminate).
  - destruct (negb (d_sym_next s1 =? 0)).
    + unfold c_flush_block in E.
      destruct (c_flush_block_only s1 z 0) as [[sa za]|] eqn:Ef; [|discriminate E]. cbn [bind] in E.
      destruct (Hlast 0 sa za ltac:(lia) Ef) as (x' & blk & Hz' & Ht' & Hk' & Hb').
      change (0 =? 1) with false in Hb'.
      destruct ((z_avail_out za =? 0) && _); cbn [bind Z.eqb Pos.eqb] in E; injection E as <- <- <-;
        (exists k, (x ++ x'), (BS' ++ [blk]), []; split; [exact Hz'|];
         split; [apply (proj2 (kcore_hk3 _ _ _ _ _ HW' Hfn')); exact (conj Ht' Hk')|];
         split; [exact Hb'|]; intros D0; discriminate D0).
    + injection E as <- <- <-.
      exists k, x, BS', syms. split; [exact Hz|].
      split; [apply (proj2 (kcore_hk3 _ _ _ _ _ HW' Hfn')); exact (conj Ht1 Hk1)|].
      rewrite (quiet_pend s1 Hq), app_nil_r. split; [exact Hb|]. intros D0; discriminate D0.
Qed.

End HuffF.

Lemma ha_bind_some {A B} (o : option A) (f : A -> option B) r :
  bind o f = Some r -> exists a, o = Some a /\ f a = Some r.
Proof. destruct o as [a|]; cbn; [eauto|discriminate]. Qed.


(* the kernel must never compute [loop FUEL] (2^40 iterations) while checking a conversion *)
Local Strategy opaque [loop loop2].

Theorem huff_fasm : hrefill_stmt -> hbflush_stmt -> htail_stmt ->
  hflit_stmt -> hfflush_stmt -> hfrefill_stmt -> comp_fspec 3 c_deflate_huff.
Proof.
  intros Href Hbfl Htail Hflit Hfflush Hfrefill
    s z flush s' z' bs dict D BS syms p HW3 Ho Hq Hfl Hzi Hwr Had Hfn Hdi HD HK Hp Hp8 R.
  destruct HW3 as [[HW _] He].
  assert (Hz := zin_ok_zall z Hzi). assert (Ha := adler_pre_ok _ _ Had).
  assert (Hbv0 : 0 <= d_bi_valid s) by (destruct Ho as (_ & (B & _) & _); unfold d_bi_valid; lia).
  assert (HI : HFI s z flush s z []).
  { unfold HFI. split; [exact Hz|]. split; [exact Ha|]. split; [exact (hcrel_refl s z flush HW He Ho Hz Ha)|].
    split; [exact Hq|]. split; [exact Hz|]. split; [exact Ha|constructor]. }
  assert (HP0 : FP s z flush dict D BS p (s, z)).
  { split; [exists []; exact HI|]. cbn [fst snd].
    destruct (proj1 (kcore_hk3 _ _ _ _ _ HW Hfn) HK) as [Ht Hk].
    exists 0, [], [], syms. split; [exact (zstep_refl _ _ Hz Ha)|]. split; [exact Ht|].
    split; [unfold Dk; rewrite Z.add_0_r, sublist_nil, !app_nil_r; exact Hk|].
    rewrite app_nil_r. reflexivity. }
  unfold c_deflate_huff in R. revert R. generalize FUEL. intros fuel R.
  destruct (ha_bind_some _ _ _ R) as ([[s1 z1] o] & EL & R2).
  pose proof (loop_FQ Href Hbfl Hflit Hfflush Hfrefill s z flush dict D BS p Hfl Hfn Hp Hp8 Hbv0
                fuel (s, z) (s1, z1, o) HP0 EL) as HQ.
  cbn [FQ] in HQ. cbv beta iota in R2.
  destruct o as [b1|].
  - injection R2 as <- <- <-. exact HQ.
  - destruct HQ as ((evs & HI') & HK' & Hla & Hai & Hnf).
    exact (tail_FR Htail Hfflush s z flush dict D BS p Hfl Hfn Hp Hp8 Hbv0 s1 z1 evs s' z' bs
             HI' HK' Hla Hai Hnf R2).
Qed.
