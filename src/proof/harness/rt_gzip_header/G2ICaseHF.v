(* Law rt_gzip_header on the round-2 harness, inflate side: the header cases HEAD (c_HEAD2) and FLAGS (c_FLAGS2),
   adapted from law inflate_header's IHTCaseHF.v *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.rt_gzip_header.G2ICaseKit.
Import ListNotations.
Local Open Scope Z_scope.

Lemma g2c_flags : g2c_flags_stmt.
Proof.
  intros KIT CT g src h0 wb pos inp aout tin m G HW LY X K L0 MD.
  pose proof K as [Ki Kn Kw Ko Kt Kr Kl Kc Kj Ks Kf].
  unfold m_mode in MD.
  destruct Kj as [E|E Pr B Ck Dn Hx Hn Hc La|E|E|E|E|E|E|E|E]; try solve [ihk_nomode].
  pose proof (g2k_flg g G) as FR.
  destruct (proj1 (k2_bits KIT) (g_flg g) FR) as (S32 & F255 & F57 & _ & _ & _ & _ & F8 & _).
  pose proof X as (X0 & X1 & X2). destruct B as [Bb Bh].
  destruct (g2k_lay_src g src LY) as (XS & NH & NH10).
  unfold c_FLAGS2. cbv zeta.
  destruct (k2_nb KIT src inp pos 2 16 m (l2_bytes _ _ LY) X0 X1 X2 Ki Kn ltac:(lia) ltac:(lia)
              ltac:(change ((16 + 7) / 8) with 2; lia) Bb Bh)
    as (nx' & lv' & EN & R & C).
  rewrite EN. ihk_red.
  change ((16 + 7) / 8) with 2 in C.
  destruct C as [(-> & -> & C) | (-> & C)].
  - rewrite Z.eqb_refl. cbn [ok_out2].
    g2k_km K.
    + right. split; [reflexivity|]. split; [lia|]. split; [lia|].
      rewrite E. unfold FLAGS, Zlib.proof.inflate.Model.TYPE. lia.
    + g2k_jc.
    + apply J2_FLAGS; [exact E | lia | split; [lia | reflexivity] | exact Ck | exact Dn | exact Hx | exact Hn
                      | exact Hc | exact La].
    + exact Ks.
  - rewrite L0. cbn [Z.eqb].
    assert (P4: pos + nx' = 4) by lia. rewrite P4 in *. rewrite (proj1 (l2_fl _ _ LY)).
    rewrite S32, F255, Z.eqb_refl. cbn [negb]. rewrite F57.
    assert (NR: ih_reserved g = false) by apply G.
    assert (RS: (Z.land (g_flg g) 224 =? 0) = true)
      by (unfold ih_reserved in NR; destruct (Z.land (g_flg g) 224 =? 0); [reflexivity | discriminate]).
    rewrite RS. cbn [negb].
    rewrite (jc2_head _ _ _ _ Kc). ihk_red.
    rewrite (g2k_crc_if KIT g); ihk_red; [| exact FR | reflexivity | apply (jc2_wrap _ _ _ _ Kc)].
    unfold hT in *.
    destruct (fl g 2) eqn:F2; ihk_red;
      (apply CT; [exact G | exact HW | exact LY | exact X | | reflexivity | reflexivity]);
      (g2k_km K; [left; reflexivity | g2k_jc | | g2k_swf]);
      (apply J2_TIME; [reflexivity | lia | rewrite P4; apply g2k_bb0 | unfold fg; reflexivity | exact NR
                      | | exact Dn | exact F8 | exact Hx | exact Hn | exact Hc | exact La ]);
      unfold ck2; intros F2'.
    + cbn [i_check set_i_mode set_i_check set_i_flags]. rewrite Ck, (proj2 (l2_fl _ _ LY)).
      apply (k2_crc KIT); [apply (l2_bytes _ _ LY) | lia | lia].
    + congruence.
Qed.

(* HEAD, for a nonzero window size wb (Jc2: inflateInit2(16 + wb) with 9 <= wb <= 15): the gzip branch keeps
   wbits *)
Lemma g2c_head_nz : forall (KIT: g2_kit) g src h0 wb pos inp aout tin m,
    wb <> 0 -> g2h_ok g -> hwf8 h0 -> lay2 g src -> ctx2 src pos inp ->
    Km2 g src h0 wb pos inp aout tin m -> m_leave m = 0 -> m_mode m = HEAD ->
    ok_out2 g src h0 wb pos inp aout tin (c_HEAD2 m).
Proof.
  intros KIT g src h0 wb pos inp aout tin m WB G HW LY X K L0 MD.
  pose proof K as [Ki Kn Kw Ko Kt Kr Kl Kc Kj Ks Kf].
  unfold m_mode in MD.
  destruct Kj as [E Pr B Dn Hx Hn Hc La|E|E|E|E|E|E|E|E|E]; try solve [ihk_nomode].
  pose proof (jc2_wrap _ _ _ _ Kc) as W6.
  assert (WB0: (i_wbits (m_s m) =? 0) = false) by (rewrite (jc2_wbits _ _ _ _ Kc); apply Z.eqb_neq; exact WB).
  destruct (g2k_lay_src g src LY) as (XS & NH & NH10).
  destruct X as (X0 & X1 & X2). destruct B as [Bb Bh].
  unfold c_HEAD2. rewrite W6. cbn [Z.eqb]. cbv zeta.
  destruct (k2_nb KIT src inp pos 0 16 m (l2_bytes _ _ LY) X0 X1 X2 Ki Kn ltac:(lia) ltac:(lia)
              ltac:(change ((16 + 7) / 8) with 2; lia) Bb Bh)
    as (nx' & lv' & EN & R & C).
  rewrite EN. ihk_red.
  change ((16 + 7) / 8) with 2 in C.
  destruct C as [(-> & -> & C) | (-> & C)].
  - rewrite Z.eqb_refl. cbn [ok_out2].
    g2k_km K.
    + right. split; [reflexivity|]. split; [lia|]. split; [lia|].
      rewrite E. unfold HEAD, Zlib.proof.inflate.Model.TYPE. lia.
    + g2k_jc.
    + apply J2_HEAD; auto; try lia. split; [lia | reflexivity].
    + exact Ks.
  - rewrite L0. cbn [Z.eqb]. rewrite W6.
    assert (P2: pos + nx' = 2) by lia. rewrite P2 in *. rewrite (proj1 (l2_id _ _ LY)).
    change (negb (Z.land 6 2 =? 0) && (35615 =? 35615))%bool with true. cbv iota.
    cbn [ok_out2]. unfold set_mode, initbits, upd_s. ihk_red. rewrite WB0.
    g2k_km K.
    + left; first [exact L0 | reflexivity].
    + g2k_jc.
    + apply J2_FLAGS; ihk_red; auto; try lia; try (rewrite P2; apply g2k_bb0).
      rewrite (proj2 (l2_id _ _ LY)); reflexivity.
    + apply g2k_swf_mode; [| unfold HEAD, FLAGS, SYNC; lia].
      apply g2k_swf_check; [| apply g2k_crc_lrange, g2k_hb2].
      apply g2k_swf_wbits; [exact Ks | apply (sw_wbits _ Ks) | right; reflexivity].
Qed.
