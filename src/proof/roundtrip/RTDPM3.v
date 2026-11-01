(* RT-D: deflateParams, deflateInit2_, deflateTune, deflateSetHeader over interface v3 (Krt3, RTDV3.v).
   Ports of the v2 proofs (RTDParams2.v). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDV3.
Require Import Zlib.proof.roundtrip.RTDLTCMisc Zlib.proof.roundtrip.RTDLTCore Zlib.proof.roundtrip.RTDParamsFrame Zlib.proof.roundtrip.RTDParams2 Zlib.proof.roundtrip.RTDMiscKit.
Import ListNotations.
Local Open Scope Z_scope.

(** ** params_tail keeps KF3 *)
Lemma kmatch3_frame : forall H s s', pframe s s' -> kmatch3 H s -> kmatch3 H s'.
Proof. intros H s s' P K. pf_destruct P. unfold kmatch3 in *. pf_rw. exact K. Qed.

Lemma kdata3_params : forall dict D BS syms s lv st s2,
  W s -> kdata3 dict D BS syms s -> 0 <= lv <= 9 -> pcase s lv st ->
  params_tail s lv st = Some s2 -> kdata3 dict D BS syms s2.
Proof.
  intros dict D BS syms s lv st s2 HW Kd Hlv Hc E.
  destruct (params_tail_shape s lv st s2 E) as (P & Hl2 & Hs2 & _).
  pose proof (prm_level s HW) as Hls.
  unfold kdata3 in *. destruct Kd as (K1 & K2 & K3 & K4 & K5 & K6 & K7).
  pose proof (kwin_frame _ _ _ P K1) as K1'. pose proof (kmatch3_frame _ _ _ P K2) as K2'.
  destruct Hc as [(Hf & Hst) | (Hla & Hss)].
  - destruct (cfg_f_class lv Hlv) as (A1 & A2 & _). destruct (cfg_f_class (d_level s) Hls) as (B1 & B2 & _).
    assert (C0 : d_level s2 = 0 <-> d_level s = 0) by (rewrite Hl2, <- A1, Hf, B1; tauto).
    assert (C4 : 4 <= d_level s2 <-> 4 <= d_level s) by (rewrite Hl2, <- A2, Hf, B2; tauto).
    assert (K3' : wtrees s2 syms).
    { apply (wtrees_frame s s2 syms P K3).
      - destruct K3 as (_ & _ & F & _). eapply Forall_impl; [|exact F].
        intros x (V1 & V2 & V3). pose proof P as P'. pf_destruct P'. unfold sym_ok, MAX_DIST in *.
        rewrite Pws, Hs2, Hst. split; [exact V1|]. split; [exact V2|].
        intros H4. apply V3. apply C4. exact H4.
      - intros L0. apply K3. apply C0. exact L0.
      - intros L0. apply K3. intros L1. apply L0. apply C0. exact L1. }
    pf_destruct P. pf_rw. cbv zeta in *.
    split; [exact K1'|]. split; [exact K2'|]. split; [exact K3'|].
    split; [exact K4|]. split; [exact K5|]. split; [exact K6|].
    replace (d_level s2 =? 0) with (d_level s =? 0); [exact K7|].
    destruct (Z.eqb_spec (d_level s) 0), (Z.eqb_spec (d_level s2) 0); tauto.
  - destruct (W_empty s syms HW K3 Hla Hss) as [Hma ->].
    assert (K3' : wtrees s2 []).
    { apply (wtrees_frame s s2 [] P K3); [constructor|reflexivity|]. intros _. rewrite Hma, Hss. unfold blk_len. cbn. lia. }
    pf_destruct P. pf_rw. cbv zeta in *.
    split; [exact K1'|]. split; [exact K2'|]. split; [exact K3'|].
    split; [exact K4|]. split; [exact K5|]. split; [exact K6|].
    rewrite K7. f_equal. rewrite Hma, Hss. destruct (d_level s =? 0), (d_level s2 =? 0); lia.
Qed.

Lemma kf3_params : forall dict wrap D O fin s tin tout adler lv st s2,
  W s -> KF3 dict wrap D O fin s tin tout adler -> 0 <= lv <= 9 -> pcase s lv st ->
  params_tail s lv st = Some s2 -> KF3 dict wrap D O fin s2 tin tout adler.
Proof.
  intros dict wrap D O fin s tin tout adler lv st s2 HW (Hgz & BS & syms & (Kd & Kh) & Hst) Hlv Hc E.
  destruct (params_tail_shape s lv st s2 E) as (P & _).
  pose proof (kdata3_params dict D BS syms s lv st s2 HW Kd Hlv Hc E) as Kd'.
  pose proof (khash_params s lv st s2 HW Kh Hlv Hc E) as Kh'.
  pose proof (allbits_frame O s s2 P) as Eab. pose proof (bi_valid_frame s s2 P) as Ebv.
  pose proof (fun HDR => khdr_frame dict wrap s s2 HDR P) as Hkh.
  pose proof P as P'. pf_destruct P'.
  split; [rewrite Pgz; exact Hgz|]. exists BS, syms. split; [split; assumption|].
  rewrite Pst, Eab, Ebv, Pwr. unfold pend, d_pending. rewrite Ppo, Pout. fold (pend s).
  destruct Hst as [(H1 & H2 & H3 & H4 & HDR & K1 & K2) | [(H1 & HDR & K1 & K2) | (H1 & H2 & H3 & HDR & K1 & K2)]].
  - left. do 4 (split; [assumption|]). exists HDR. split; [apply Hkh; exact K1|exact K2].
  - right; left. split; [exact H1|]. exists HDR. split; [apply Hkh; exact K1|exact K2].
  - right; right. split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
    exists HDR. split; [apply Hkh; exact K1|exact K2].
Qed.

(** ** Header witnesses *)
Lemma pm3_pend0 : forall W HI dict wrap D fin s tin tout adler,
  Iapi W HI dict wrap D [] fin s tin tout adler -> d_status s <> BUSY_STATE -> d_status s <> FINISH_STATE ->
  pend s = [].
Proof.
  intros W HI dict wrap D fin s tin tout adler HI' N1 N2.
  destruct HI' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hph).
  destruct Hph as [P0 | (_ & [P1 | [P2 | P3]])].
  - destruct P0 as (_ & _ & _ & _ & Hp & _). unfold pend. rewrite Hp, Z.add_0_r.
    apply sublist_nil.
  - destruct P1 as (_ & _ & Hne & _). congruence.
  - destruct P2 as (Hs & _). contradiction.
  - destruct P3 as (Hs & _). contradiction.
Qed.

Lemma pm3_flg0 : forall wb, exists flg, zflg_ok wb false flg.
Proof.
  intros wb. exists ((31 - (zcmf wb * 256) mod 31) mod 31).
  set (x := zcmf wb * 256).
  pose proof (Z.mod_pos_bound x 31 ltac:(lia)) as Hx.
  pose proof (Z.mod_pos_bound (31 - x mod 31) 31 ltac:(lia)) as Hy.
  unfold zflg_ok. fold x. split; [lia|]. split.
  - rewrite Z.add_mod_idemp_r by lia. pose proof (Z.div_mod x 31 ltac:(lia)) as Hd.
    replace (x + (31 - x mod 31)) with ((x / 31 + 1) * 31) by lia.
    apply Z.mod_mul. lia.
  - apply Z.bits_above_log2; [lia|].
    assert (Hl : Z.log2 ((31 - x mod 31) mod 31) <= Z.log2 31) by (apply Z.log2_le_mono; lia).
    change (Z.log2 31) with 4 in Hl. lia.
Qed.

Lemma pm3_khdr0 : forall wrap s, exists HDR, khdr [] wrap s HDR.
Proof.
  intros wrap s. unfold khdr.
  destruct (wrap =? 0); [exists []; reflexivity|].
  destruct (wrap =? 1).
  - destruct (pm3_flg0 (d_w_bits s)) as (flg & Hf). eexists. exists flg. split; [exact Hf|reflexivity].
  - eexists. exists 0. split; [left; reflexivity|reflexivity].
Qed.

Lemma pm3_khdr2 : forall dict s, exists HDR, khdr dict 2 s HDR.
Proof. intros dict s. unfold khdr. cbn. eexists. exists 0. split; [left; reflexivity|reflexivity]. Qed.

Lemma pm3_kcore3_gzhead : forall dict D BS syms s g,
  kcore3 dict D BS syms s -> kcore3 dict D BS syms (set_d_gzhead s g).
Proof. intros dict D BS syms s g H. destruct s. exact H. Qed.

Lemma pm3_KF3_tune : forall dict wrap D O fin s tin tout adler g l n c,
  KF3 dict wrap D O fin s tin tout adler -> KF3 dict wrap D O fin (tune_set s g l n c) tin tout adler.
Proof. intros dict wrap D O fin s tin tout adler g l n c H. destruct s. exact H. Qed.

Theorem rtd_pm3_ok : Zlib.proof.huffman.Overlay.overlay_statement ->
  (kf_deflate_stmt Krt3 -> kf_params_stmt Krt3) /\ kf_init_stmt Krt3 /\ kf_tune_stmt Krt3 /\ kf_head_stmt Krt3.
Proof.
  intros Hov. split; [|split; [|split]].
  - exact (params_gen KF3 (fun dict wrap D O fin s tin tout adler lv st s2 =>
             kf3_params dict wrap D O fin s tin tout adler lv st s2)).
  - intros level method wbits mem strategy a1 a2 a3 a4 a5 z s z' H1 H2 H3 H4 H5 E.
    destruct (misc_init Hov level method wbits mem strategy a1 a2 a3 a4 a5 z s z' H1 H2 H3 H4 H5 E)
      as (Hwb & Hgz & HI & HW & Hss & Hla & Hbs & Hsn & Hbv & Hn1 & Hn2).
    split; [exact Hwb|]. split; [exact Hgz|]. split; [exact HI|].
    split; [intros _; exact Hgz|]. exists [], [].
    assert (Hma : d_match_available s = 0) by exact (W_ma0 s (proj1 (proj1 HW)) Hss).
    split; [apply (kcore3_iff _ _ _ _ _ Hma); exact (proj2 (misc_kcore0 s (proj1 (proj1 HW)) Hss Hla Hbs Hsn))|].
    left. do 4 (split; [auto|]).
    destruct (pm3_khdr0 (rwrap_of wbits) s) as (HDR & Hk). exists HDR. split; [exact Hk|].
    rewrite (pm3_pend0 _ _ _ _ _ _ _ _ _ _ HI Hn1 Hn2). reflexivity.
  - intros wrap s tin tout adler good lazy nice chain z s' z' code [HI HK] H1 H2 H3 H4 E.
    destruct (misc_tune Hov wrap s tin tout adler good lazy nice chain z s' z' code HI H1 H2 H3 H4 E)
      as (-> & Hwb & Hg & HI1).
    split; [exact Hwb|]. split; [exact Hg|]. split; [exact HI1|]. apply pm3_KF3_tune; exact HK.
  - intros dict s tin tout adler h [HI HK] Hh.
    pose proof (misc_head_iapi Hov dict s tin tout adler h HI Hh) as HI1.
    split; [exact HI1|].
    destruct (misc_status_O0 _ _ _ _ _ _ _ _ _ HI1) as [N1 N2].
    destruct HK as (_ & BS & syms & Hk & Hph).
    split; [intros C; exfalso; apply C; reflexivity|].
    exists BS, syms. split; [apply pm3_kcore3_gzhead; exact Hk|].
    destruct Hph as [(P1 & P2 & P3 & P4 & _) | [(P & _) | (P & _)]]; [|contradiction|contradiction].
    left. split; [exact N1|]. split; [exact N2|]. split; [exact P3|]. split.
    { destruct s. exact P4. }
    destruct (pm3_khdr2 dict (set_d_gzhead s (Some h))) as (HDR & Hk2). exists HDR. split; [exact Hk2|].
    rewrite (pm3_pend0 _ _ _ _ _ _ _ _ _ _ HI1 N1 N2). reflexivity.
Qed.
