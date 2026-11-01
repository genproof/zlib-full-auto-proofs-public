(* Part of fact_decode: the model's main loop run from init_state ends with the final table dfinal (decode_defs.v). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.inftrees.facts.
Require Import Zlib.proof.inftrees.fact_result.
Require Import Zlib.proof.inftrees.model_inv.
Require Import Zlib.proof.inftrees.decode_defs.
Import ListNotations.
Local Open Scope Z_scope.

Lemma drun_rep_fill_len : forall n t base incr e,
  Zlength (rep_fill t base incr n e) = Zlength t.
Proof.
  induction n; intros; cbn [rep_fill]; auto. rewrite IHn. apply (upd_len 0).
Qed.

Lemma drun_step_break_len : forall type lens W root mx s s',
  step type lens W root mx s = Break s' -> Zlength (s_tab s') = Zlength (s_tab s).
Proof.
  intros. unfold step in H.
  destruct (_ && _); [inversion H; subst; cbn [s_tab]; apply drun_rep_fill_len|].
  destruct (_ && _); [destruct (over _ _)|]; discriminate.
Qed.

Section Run.
Variables (type: Z) (lens W ls: list Z) (root: Z) (old: list entry).
Context (HD : dhyps type lens W ls root old).
Context (Hbits : bits_stmt).
Context (Hsub : subbits_stmt).
Context (Hdstep : dstep_stmt).
Context (Hdlast : dlast_stmt).

Definition drun_last (sl s': state) : Prop :=
  inv ls root old (Zlength ls - 1) sl /\
  step type lens W root (Znth (Zlength ls - 1) ls) sl = Break s' /\
  s_used s' = s_used sl /\ s_next s' = s_next sl /\ s_len s' = s_len sl /\ s_drop s' = s_drop sl /\
  s_huff s' = next_huff (s_huff sl) (s_len sl) /\
  (forall j, 0 <= j < Zlength ls -> fills_done type W ls root j (s_tab s') /\ link_done ls root j (s_tab s')).

Lemma drun_from : forall n i s,
  inv ls root old i s -> dcontent type W ls root i (s_tab s) -> Zlength ls <= i + Z.of_nat n ->
  (exists sl s', drun_last sl s' /\ run type lens W root (Znth (Zlength ls - 1) ls) n s = Break s') \/
  (exists s', run type lens W root (Znth (Zlength ls - 1) ls) n s = Full s').
Proof.
  pose proof HD as HD'.
  destruct HD' as (Hrange & Hsorted & HN & HWls & HWr & Hroot & Hk & Hinc & Htype & Hcodes & Hcap & Hcap0 & Hold & Hl1).
  induction n as [|n IH]; intros i s Hinv Hc Hn.
  - exfalso. destruct Hinv as (Hi & _). simpl in Hn. lia.
  - cbn [run].
    assert (Hi: 0 <= i < Zlength ls) by (destruct Hinv; lia).
    destruct (Z_lt_dec (i + 1) (Zlength ls)) as [Hlt|Hge].
    + destruct (step_inv type lens W ls root old Hrange Hsorted HN HWls HWr Hroot Hk Hinc Htype Hcodes Hcap
                  Hbits Hsub i s Hinv Hlt) as [[s' [Hs Hinv']]|[s' [Hs _]]].
      * rewrite Hs. apply (IH (i + 1) s' Hinv').
        -- eapply Hdstep; eauto.
        -- lia.
      * rewrite Hs. right. eauto.
    + assert (i = Zlength ls - 1) by lia. subst i.
      destruct (Hdlast type lens W ls root old s HD Hbits Hsub Hinv Hc) as [s' [Hs Hr]].
      rewrite Hs. left. exists s, s'. split; auto. split; auto.
Qed.

Lemma drun_final : forall sl s', drun_last sl s' -> dfinal type W ls root (s_used s') (finish s').
Proof.
  pose proof HD as HD'.
  destruct HD' as (Hrange & Hsorted & HN & HWls & HWr & Hroot & Hk & Hinc & Htype & Hcodes & Hcap & Hcap0 & Hold & Hl1).
  intros sl s' (Hinv & Hstep & Hu & Hnx & Hln & Hdr & Hhf & Hfl).
  pose proof (root_range ls root Hrange HN Hroot) as Hr.
  set (N := Zlength ls) in *.
  assert (HlN := l_range ls Hrange (N - 1) ltac:(lia)).
  destruct Hinv as (_ & _ & Hlen & Hhuff & _ & _ & Hshort & Hlong & Htl & _ & _ & Hucap).
  assert (HM: MAXBITS = 15) by reflexivity.
  assert (Hused: 2 ^ root <= s_used s' /\
    (forall j, 0 <= j < N -> root < Znth j ls ->
       dnxt ls root (pfx ls root j) + 2 ^ (gmax ls root (pfx ls root j) - root) <= s_used s')).
  { rewrite Hu. destruct (Z_le_gt_dec (Znth (N - 1) ls) root) as [Hs|Hs]; [|apply Z.gt_lt in Hs].
    - destruct (Hshort Hs) as (_ & _ & _ & -> & _). split; [lia|].
      intros. assert (Znth j ls <= Znth (N - 1) ls) by (apply Hsorted; lia). lia.
    - destruct (Hlong Hs) as (_ & _ & Hcu & Hne & Hus).
      assert (Hp := pfx_range ls root Hrange HN Hroot Hk (N - 1) ltac:(lia)).
      assert (HfqN := fq_long ls root Hrange HN Hroot (N - 1) ltac:(lia) Hs).
      rewrite <- Hcu in HfqN.
      assert (Hsq := sumq_succ ls root (pfx ls root (N - 1)) ltac:(lia)).
      split.
      + pose proof (sumq_nonneg ls root (pfx ls root (N - 1)) ltac:(lia)).
        pose proof (gmax_long ls root Hrange (N - 1) ltac:(lia) Hs).
        pose proof (Z.pow_pos_nonneg 2 (s_curr sl) ltac:(lia) ltac:(lia)). lia.
      + intros j Hj Hjl. unfold dnxt.
        assert (Hpj := pfx_range ls root Hrange HN Hroot Hk j Hj).
        rewrite <- (fq_long ls root Hrange HN Hroot j Hj Hjl).
        pose proof (sumq_succ ls root (pfx ls root j) ltac:(lia)).
        assert (pfx ls root j <= pfx ls root (N - 1)) by (apply (pfx_mono ls root Hrange HN Hroot); lia).
        pose proof (sumq_mono ls root (pfx ls root j + 1) (pfx ls root (N - 1) + 1) ltac:(lia)).
        lia. }
  destruct Hused as [Hu1 Hu2].
  destruct (Z_lt_ge_dec (ksum ls) (2 ^ MAXBITS)) as [Hinc'|Hcomp].
  - (* incomplete: one code of length 1 *)
    specialize (Hl1 Hinc'). unfold N in *.
    assert (H0: Znth 0 ls = 1) by (pose proof (l_range ls Hrange 0 ltac:(lia)); pose proof (Hsorted 0 (Zlength ls - 1)); lia).
    assert (HN1: Zlength ls = 1).
    { destruct (Z_lt_ge_dec 1 (Zlength ls)); [|lia]. exfalso.
      assert (Znth 1 ls = 1) by (pose proof (l_range ls Hrange 1 ltac:(lia)); pose proof (Hsorted 1 (Zlength ls - 1)); lia).
      pose proof (kpre_S ls 0 ltac:(lia)). pose proof (kpre_S ls 1 ltac:(lia)).
      rewrite kpre_0 in *. simpl in *.
      pose proof (kpre_mono ls 2 (Zlength ls) ltac:(lia) ltac:(lia)). rewrite kpre_full in *.
      rewrite H0 in *. replace (1 + 1) with 2 in * by lia. rewrite H in *. rewrite HM in *. simpl in *. lia. }
    assert (Hr1: root = 1) by (rewrite HN1 in Hroot; simpl in Hroot; lia).
    rewrite HN1 in *. replace (1 - 1) with 0 in * by lia. rewrite H0 in *. subst root.
    destruct (Hshort ltac:(lia)) as (Hd & _ & Hnx0 & Hus & _).
    assert (Hh0: s_huff sl = 0) by (rewrite Hhuff, kpre_0, Zdiv_0_l; apply reverse_bits_0).
    assert (Hh1: s_huff s' = 1) by (rewrite Hhf, Hh0, Hlen; reflexivity).
    assert (Hfin: finish s' = upd_Znth 1 (s_tab s') (invalid_entry 1)).
    { unfold finish. rewrite Hh1. cbn. rewrite Hnx, Hnx0, Hln, Hdr, Hd, Hlen. reflexivity. }
    assert (Htl': Zlength (s_tab s') = Zlength old).
    { rewrite (drun_step_break_len _ _ _ _ _ _ _ Hstep). auto. }
    rewrite Hfin. split; [|split; [lia|split; [intros j Hj Hjl; apply Hu2; auto; lia|]]].
    + intros j Hj. assert (j = 0) by lia. subst j. destruct (Hfl 0 ltac:(lia)) as [F L].
      split; [split|].
      * intros _ k Hk'. rewrite H0 in Hk'. simpl in Hk'. assert (k = 0) by lia. subst k.
        destruct F as [F _]. specialize (F ltac:(lia) 0 ltac:(rewrite H0; simpl; lia)).
        assert (Hdh: dhuff ls 0 = 0).
        { unfold dhuff, dcode. rewrite kpre_0, Zdiv_0_l. apply reverse_bits_0. }
        rewrite Hdh in *. simpl Z.add in *. rewrite upd_Znth_diff' by (simpl in Hcap0; lia). auto.
      * intros; lia.
      * intros Hlt; lia.
    + intros _. repeat split; auto. lia.
      rewrite upd_Znth_same by (simpl in Hcap0; lia). reflexivity.
  - (* complete code: the final huff is 0 *)
    assert (Hcomp': ksum ls = 2 ^ MAXBITS) by lia.
    destruct (C_facts type ls root Hrange Hsorted HN Hk Htype (N - 1) ltac:(lia)) as (HC0 & _ & HS & HC1 & _).
    replace (N - 1 + 1) with N in HS by lia. unfold N in HS. rewrite kpre_full, Hcomp' in HS. fold N in HS.
    set (l := Znth (N - 1) ls) in *.
    set (C := kpre ls (N - 1) / 2 ^ (MAXBITS - l)) in *.
    assert (HC: C + 1 = 2 ^ l).
    { assert (Hpw: 2 ^ MAXBITS = 2 ^ l * 2 ^ (MAXBITS - l)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
      rewrite Hpw in HS. apply Z.mul_reg_r in HS; auto. apply Z.pow_nonzero; lia. }
    destruct Hbits as (B1 & B2 & B3 & B4 & B5).
    assert (Hh: s_huff s' = 0).
    { rewrite Hhf, Hhuff, Hlen. fold l C. rewrite B5 by lia. rewrite HC, Z.mod_same by (apply Z.pow_nonzero; lia).
      apply reverse_bits_0. }
    assert (Hfin: finish s' = s_tab s') by (unfold finish; rewrite Hh; reflexivity).
    rewrite Hfin. split; [auto|split; [auto|split; [auto|]]]. intros; lia.
Qed.

End Run.

Lemma drun_ok : drun_stmt.
Proof.
  intros type lens req old s Hss Hb Hsb Hds Hdl Hlens Hmax HD Hrun.
  destruct (Hss lens Hlens) as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9).
  assert (Hne: sl lens <> []) by (intro E; apply S8 in E; contradiction).
  destruct (S9 Hne) as [Hmin Hmaxl].
  rewrite <- Hmaxl in Hrun.
  set (W := sorted_syms lens) in *. set (ls := sl lens) in *. set (root := root_of req lens) in *.
  pose proof HD as HD'.
  destruct HD' as (Hrange & Hsorted & HN & HWls & HWr & Hroot & Hk & Hinc & Htype & Hcodes & Hcap & Hcap0 & Hold & Hl1).
  assert (HlW: Zlength ls = Zlength W) by (unfold ls, sl; apply Zlength_map).
  assert (Hinv: inv ls root old 0 (init_state lens root old)).
  { unfold inv, init_state. cbn [s_huff s_sym s_len s_curr s_drop s_low s_used s_next s_cnt s_tab].
    rewrite pow2_shiftl by (pose proof (root_range ls root Hrange HN Hroot); lia).
    split; [lia|]. split; [auto|]. split; [auto|].
    split; [rewrite kpre_0, Zdiv_0_l; symmetry; apply reverse_bits_0|].
    split; [auto|].
    split; [intros; rewrite S5 by auto; rewrite sublist_same by lia; reflexivity|].
    split; [intros; repeat split; auto|].
    split; [intros; lia|].
    repeat split; auto. }
  assert (Hc: dcontent type W ls root 0 (s_tab (init_state lens root old))).
  { split; [intros; lia|]. intros j Hj Hj'. assert (j = 0) by lia. subst j. intros Hlt. lia. }
  assert (Hn: Zlength ls <= 0 + Z.of_nat (length W)) by (rewrite <- Zlength_correct; lia).
  destruct (drun_from type lens W ls root old HD Hb Hsb Hds Hdl (length W) 0 _ Hinv Hc Hn)
    as [[sl' [s' [Hl Hr]]]|[s' Hr]]; rewrite Hr in Hrun; destruct Hrun as [E|E]; inversion E; subst.
  eapply drun_final; eauto.
Qed.
