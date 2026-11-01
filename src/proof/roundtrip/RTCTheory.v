(* Round-trip laws, part RT-C: compress2 over the model (RTC2.c2_ok), from the round-trip
   invariant (kfacts) and the deflate laws' theory (rt_init_facts, rt_bound_once). *)
Require Import Zlib.proof.roundtrip.RTC2.
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Import ListNotations.
Local Open Scope Z_scope.

Lemma rtc_cb_range : forall n, 0 <= n <= 1048576 -> n <= c_compressBound n <= 2097152.
Proof.
  intros n Hn. unfold c_compressBound, compressBound_z.
  rewrite !Z.shiftr_div_pow2 by lia.
  assert (H1 : 0 <= n / 2 ^ 12 <= n) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  assert (H2 : 0 <= n / 2 ^ 14 <= n / 2 ^ 12).
  { split; [apply Z.div_pos; lia|]. apply Z.div_le_compat_l; [lia | split; [lia|]].
    apply Z.pow_le_mono_r; lia. }
  assert (H3 : 0 <= n / 2 ^ 25 <= n / 2 ^ 12).
  { split; [apply Z.div_pos; lia|]. apply Z.div_le_compat_l; [lia | split; [lia|]].
    apply Z.pow_le_mono_r; lia. }
  assert (H4 : n / 2 ^ 12 <= 256).
  { apply Z.div_le_upper_bound; [lia|]. change (2 ^ 12 * 256) with 1048576. lia. }
  unfold u64. rewrite Z.mod_small by lia.
  destruct (_ <? n) eqn:E; [apply Z.ltb_lt in E; lia | lia].
Qed.

Lemma rtc_params : forall level, rparams_ok level 8 15 8 0 = true <-> -1 <= level <= 9.
Proof.
  intros level. unfold rparams_ok. cbn [rwb_of rwrap_of].
  destruct (level =? -1) eqn:E.
  - apply Z.eqb_eq in E; subst. cbn. lia.
  - apply Z.eqb_neq in E. cbn.
    rewrite !andb_true_r, andb_true_iff, !Z.leb_le. lia.
Qed.

Lemma rtc_rs32 : forall x, -1 <= x <= 15 -> rs32 x.
Proof. unfold rs32; lia. Qed.

(* the first iteration of the loop from the setup stream *)
Lemma rtc_give : forall src tin tout adler msg,
  0 <= Zlength src <= 1048576 ->
  c2_give src (mkST src 0 0 tin [] 0 tout adler msg) (c_compressBound (Zlength src)) (Zlength src) =
  (rzcall src 0 (Zlength src) tin (c_compressBound (Zlength src)) tout adler msg,
   0, 0, Z_FINISH).
Proof.
  intros src tin tout adler msg Hn. pose proof (rtc_cb_range _ Hn) as Hc.
  unfold c2_give, rzcall; cbn [z_avail_out z_avail_in z_next_in z_total_in z_total_out z_adler z_msg].
  rewrite !Z.eqb_refl. rewrite !Z.min_l by (unfold umax; lia). rewrite !Z.sub_diag. reflexivity.
Qed.

Theorem rt_c2_fact : forall K, kfacts K -> rt_init_facts -> rt_bound_once -> c2_ok.
Proof.
  intros K HK Hinit Hbound src level a1 a2 a3 a4 a5 z0 Hsrc Hn Hlv.
  pose proof (Zlength_nonneg src) as Hn0.
  assert (Hn' : 0 <= Zlength src <= 1048576) by lia.
  pose proof (rtc_cb_range _ Hn') as Hcb.
  destruct (Hinit level 8 15 8 0 a1 a2 a3 a4 a5 z0 Hlv) as [[[[os z1] code] Hr] Hcodes];
    try (apply rtc_rs32; lia).
  destruct (Hcodes _ _ _ Hr) as (Hc & Hse & Hok).
  (* the case of a successful init *)
  assert (Hrun : code = Z_OK -> exists s s' z',
    os = Some s /\ d_gzhead s = None /\ -1 <= level <= 9 /\
    c_deflate s (rzcall src 0 (Zlength src) (z_total_in z1) (c_compressBound (Zlength src)) (z_total_out z1)
                   (z_adler z1) (z_msg z1)) Z_FINISH = Some (s', z', Z_STREAM_END) /\
    d_gzhead s' = d_gzhead s /\ z_avail_in z' = 0 /\
    rcall_ok src (c_compressBound (Zlength src)) (z_total_in z1) (z_total_out z1) z' /\
    dfinal [] 1 15 None src (z_out z')).
  { intros ->. destruct (Hok eq_refl) as (s & -> & Hgz).
    assert (Hl : -1 <= level <= 9).
    { apply rtc_params. destruct (rparams_ok level 8 15 8 0) eqn:E; [reflexivity|].
      discriminate (proj2 Hse eq_refl). }
    destruct (Hbound level a1 a2 a3 a4 a5 z0 s z1 src (z_msg z1) Hl Hsrc Hn Hr)
      as (s' & z' & Hd & Hgz' & Hai & Hco).
    exists s, s', z'. do 7 (split; [auto|]).
    destruct (kf_init K HK level 8 15 8 0 a1 a2 a3 a4 a5 z0 s z1) as (Hw & Hg & HK0);
      try (apply rtc_rs32; lia); [exact Hr|].
    edestruct (kf_deflate K HK [] 1 [] [] None s _ _ _ src (c_compressBound (Zlength src)) Z_FINISH
                 (z_msg z1) s' z' Z_STREAM_END HK0) as [_ Hf];
      try (unfold Z_FINISH; lia); try lia; try eassumption.
    all: try (rewrite ?Zlength_nil; unfold Z_FINISH; lia).
    all: try (intros R HR; discriminate).
    all: try (intro H; discriminate).
    all: try (split; [reflexivity | assumption]).
    all: try (right; left; reflexivity).
    cbv zeta in Hf. rewrite Z.eqb_refl in Hf. rewrite Hai, Z.sub_0_r, sublist_same in Hf by reflexivity.
      rewrite Hw, Hg in Hf. exact Hf. }
  split.
  - destruct (Z.eq_dec code Z_OK) as [E|E].
    + destruct (Hrun E) as (s & s' & z' & -> & Hgz & _ & Hd & Hgz' & _ & Hco & _).
      exists Z_OK, ([] ++ z_out z'). exists (Some s), z1, code. split; [exact Hr|]. right. split; [exact E|].
      exists s, Z_STREAM_END, s', z'. split; [reflexivity|]. split; [exact Hgz|]. split; [|reflexivity].
      eapply c2r_last; [apply rtc_give; exact Hn' | exact Hd | exact Hgz' | | discriminate].
      destruct Hco as (_ & Hai & Hni & _ & Hao & Hlo & _). unfold c2_step, rzcall; cbn. lia.
    + exists code, []. exists os, z1, code. split; [exact Hr|]. left. auto.
  - intros r out (os2 & z2 & code2 & Hr2 & Hcase). rewrite Hr in Hr2. inversion Hr2; subst os2 z2 code2.
    destruct Hcase as [(Hne & -> & ->) | (E & s & err & sf & zf & Hs & _ & Hloop & ->)].
    + split; [destruct Hc as [|[|]]; auto; contradiction|].
      split; [|split; [rewrite Zlength_nil; lia | intro; contradiction]].
      rewrite Hse. rewrite <- rtc_params. destruct (rparams_ok level 8 15 8 0); intuition discriminate.
    + destruct (Hrun E) as (s0 & s' & z' & Hs0 & _ & Hl & Hd & _ & _ & Hco & Hf).
      rewrite Hs in Hs0. inversion Hs0; subst s0.
      inversion Hloop; subst.
      * match goal with H : c2_give _ _ _ _ = _ |- _ => rewrite rtc_give in H by exact Hn'; inversion H; subst end.
        match goal with H : c_deflate _ _ _ = Some _ |- _ => rewrite Hd in H; injection H as _ _ E' end.
        unfold Z_STREAM_END, Z_OK in E'; lia.
      * match goal with H : c2_give _ _ _ _ = _ |- _ => rewrite rtc_give in H by exact Hn'; inversion H; subst end.
        match goal with H : c_deflate _ _ _ = Some _ |- _ => rewrite Hd in H; inversion H; subst end.
        cbn. split; [auto|]. split; [split; [discriminate | lia]|].
        destruct Hco as (_ & _ & _ & _ & Hao & Hlo & _). split; [lia|]. intros _; exact Hf.
Qed.
