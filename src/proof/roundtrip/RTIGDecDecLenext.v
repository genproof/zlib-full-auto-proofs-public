(* RT-I: copy of rfc1951/DecDecLenext.v over the generalized definitions RTIGDefs.v. *)
(* Part of DecDec.group_dec: the pass from LENEXT (falls through to DIST).  Statements: DecDecDefs.v; helpers: DecDecKd.v; template:
   DecDecLit.v (pass_lit). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.roundtrip.RTIGDecDecKd.
Import ListNotations.
Local Open Scope Z_scope.

Lemma lx_bits_le_len v n : 0 <= n -> Zlength (bits_le v n) = n.
Proof.
  intros Hn. unfold bits_le. rewrite Zlength_map, Zlength_correct, seq_length. apply Z2Nat.id; exact Hn.
Qed.

Lemma lx_sub_mid (S A B C: list bool) p :
  0 <= p -> sublist p (p + Zlength (A ++ B ++ C)) S = A ++ B ++ C ->
  sublist (p + Zlength A) (p + Zlength A + Zlength B) S = B.
Proof.
  intros Hp E.
  assert (EB : sublist (Zlength A) (Zlength A + Zlength B) (A ++ B ++ C) = B).
  { rewrite sublist_app2 by (pose proof (Zlength_nonneg A); lia).
    replace (Zlength A - Zlength A) with 0 by lia. replace (Zlength A + Zlength B - Zlength A) with (Zlength B) by lia.
    rewrite sublist_app1 by (pose proof (Zlength_nonneg B); lia). apply sublist_same; reflexivity. }
  rewrite <- E in EB. rewrite sublist_sublist in EB.
  - replace (p + Zlength A + Zlength B) with (Zlength A + Zlength B + p) by lia.
    replace (p + Zlength A) with (Zlength A + p) by lia. exact EB.
  - exact Hp.
  - pose proof (Zlength_nonneg A); pose proof (Zlength_nonneg B); lia.
  - rewrite !Zlength_app. pose proof (Zlength_nonneg A); pose proof (Zlength_nonneg B); pose proof (Zlength_nonneg C); lia.
Qed.

Lemma lx_dsp G pos inp ob flush m m0 o :
  m_ow m = m_ow m0 -> dstep_post G pos inp ob flush m o -> dstep_post G pos inp ob flush m0 o.
Proof.
  intros E. destruct o; cbn; auto. intros (A & (d & B) & C). split; [exact A|]. split; [|exact C].
  exists d. rewrite B, E. reflexivity.
Qed.

Lemma lx_u32 x : 0 <= x < 2 ^ 32 -> u32 x = x.
Proof. intros H. unfold u32. apply Z.mod_small; exact H. Qed.

Lemma lx_epos k : forall bs p, p <= epos p bs k.
Proof.
  induction k as [|k IHk]; intros bs p.
  - destruct bs; apply Z.le_refl.
  - destruct bs as [|b r]; [apply Z.le_refl|].
    change (epos p (b :: r) (S k)) with (epos (p + Zlength (enc_block p false b)) r k).
    specialize (IHk r (p + Zlength (enc_block p false b))).
    pose proof (Zlength_nonneg (enc_block p false b)). lia.
Qed.

Lemma lx_p0 G s k j ll dl syms p0 : in_huff G s k j ll dl syms p0 -> 0 <= p0.
Proof.
  intros (_ & _ & _ & _ & _ & ->). unfold bpos, D0, sym_off.
  pose proof (lx_epos (Z.to_nat k) (dc_bs G) 0).
  pose proof (Zlength_nonneg (hdr_bytes (dc_w G))).
  pose proof (Zlength_nonneg (flat_map (send_one ll dl) (firstn (Z.to_nat j) syms))).
  assert (0 <= hb_hdr (blk G k)).
  { destruct (blk G k) as [s0|bt|nl nd cl tk sy]; unfold hb_hdr; try lia.
    pose proof (Zlength_nonneg cl). pose proof (Zlength_nonneg (flat_map (send_tok (cl_lens cl)) tk)). lia. }
  lia.
Qed.

Ltac lx_simp := cbn [set_mode upd_s dropbits bitsn m_s m_nx m_hold m_bits m_ow m_inp m_out m_aout m_tout m_ret
  m_leave set_m_s set_m_leave set_m_bits set_m_hold set_m_nx i_length i_mode set_i_mode set_i_was set_i_length
  set_i_back].

Lemma pass_lenext : dkit_stmt -> lay_stmt -> tabs_stmt -> need_stmt -> pass_ok DIST (c_DIST lenfix_list distfix_list) -> pass_ok LENEXT (c_LENEXT lenfix_list distfix_list).
Proof.
  intros DK LAY TABS NEED PD G pos inp ob flush m Ctx K D Hl Hmd.
  pose proof Ctx as (Gok & Hpos & _).
  pose proof (kd_at _ _ _ _ _ K) as At.
  pose proof (kd_inp _ _ _ _ _ K) as Hinp.
  destruct (at_mode_lenext_e _ _ _ _ _ _ At Hmd)
    as (Hh & k & j & ll & dl & syms & p0 & len & dist & IH & Hj & Hs & Ho & Hlen & Hex & Hq & Hb).
  destruct (LAY G (m_s m) k j ll dl syms p0 Gok IH) as (_ & _ & _ & _ & _ & _ & L1 & _).
  destruct (L1 Hj) as (SO & Sb & Sle & _ & _). clear L1. rewrite Hs in SO, Sb, Sle.
  destruct SO as (Hln & _).
  destruct TABS as (T1 & _).
  destruct (T1 len Hln) as (Ti & Tx & Tb). clear T1.
  pose proof (lx_p0 _ _ _ _ _ _ _ _ IH) as Hp0.
  cbn [send_one] in Sb, Sle.
  pose proof (lx_sub_mid _ _ _ _ _ Hp0 Sb) as Sx.
  rewrite lx_bits_le_len in Sx by lia.
  rewrite !Zlength_app in Sle. rewrite lx_bits_le_len in Sle by lia.
  pose proof (Zlength_nonneg (send_sym dl (dist_code dist))).
  pose proof (Zlength_nonneg (bits_le (dist - Znth (dist_code dist) dist_base) (Znth (dist_code dist) dist_extra))).
  assert (Hmd' : md_dec (m_mode m)) by (unfold md_dec; tauto).
  pose proof D as (_ & _ & Dnx & Dow & Dwn).
  pose proof (proj1 Hh) as Hb0.
  unfold c_LENEXT. cbv beta zeta.
  destruct (i_extra (m_s m) =? 0) eqn:EX.
  - (* no extra bits *)
    apply Z.eqb_eq in EX. rewrite EX in Hex.
    cbv beta iota delta [negb].
    eapply lx_dsp; [|apply PD; auto].
    + reflexivity.
    + apply kd_tr with m; auto; try reflexivity.
      * unfold set_mode, upd_s. sf_auto.
      * right. cbn. unfold md_dec; tauto.
      * lx_simp. apply at_mode_dist_i; [exact Hh|reflexivity|].
        exists k, j, ll, dl, syms, p0, len, dist.
        split; [apply in_huff_tr with (m_s m); [sf_auto|exact IH]|].
        split; [exact Hj|]. split; [exact Hs|]. split; [exact Ho|]. cbv zeta. lx_simp.
        rewrite <- Hex in Tb. rewrite Z.pow_0_r in Tb.
        split; [lia|]. split; [rewrite <- Hex; lia|]. left. destruct Hb; lia.
  - (* extra bits *)
    apply Z.eqb_neq in EX.
    cbv beta iota delta [negb].
    remember (i_extra (m_s m)) as n eqn:En.
    assert (Hn : 1 <= n <= 5) by lia.
    destruct (NEED G pos inp m n (len - Znth (len_code len) len_base) (8 * (pos + m_nx m) - m_bits m))
      as (nx & h & b & E & Hnx & Hhb & Hqb & C).
    + exact Ctx.
    + split; [exact Hinp|]. split; [rewrite <- Hinp; exact Dnx|exact Hh].
    + reflexivity.
    + exact Hl.
    + lia.
    + rewrite <- Hex in Tb. lia.
    + rewrite Hq, Hex. exact Sx.
    + rewrite Hq, Hex. lia.
    + rewrite Hex. exact Hb.
    + rewrite E. destruct C as [(Lv & Hnxe & Hbn & Hslen)|(Lv & Hbn & Hmod)]; rewrite Lv.
      * cbn [m_leave set_m_leave]. rewrite Z.eqb_refl. cbn [dstep_post]. split; [|split].
        -- apply kd_tr with m; auto; try reflexivity.
           ++ sf_auto.
           ++ right; exact Hmd'.
           ++ lx_simp. apply at_mode_lenext_i; [exact Hhb|exact Hmd|].
              exists k, j, ll, dl, syms, p0, len, dist.
              split; [exact IH|]. split; [exact Hj|]. split; [exact Hs|]. split; [exact Ho|]. cbv zeta.
              split; [exact Hlen|]. split; [rewrite <- En; exact Hex|]. split; [lia|]. right. lia.
        -- exists []. rewrite app_nil_r. reflexivity.
        -- intros _. right; left. lx_simp. split; [exact Hnxe|exact Hslen].
      * cbn [m_leave set_m_leave Z.eqb].
        assert (Hu : u32 (b - n) = b - n) by (apply lx_u32; lia).
        assert (Hv : u32 (i_length (m_s m) + h mod 2 ^ n) = len).
        { rewrite Hmod, Hlen. replace (Znth (len_code len) len_base + (len - Znth (len_code len) len_base)) with len by lia.
          apply lx_u32. lia. }
        pose proof (dk_drop DK G (pos + nx) h b n Hhb ltac:(lia)) as Hd.
        eapply lx_dsp; [|apply PD].
        -- reflexivity.
        -- exact Ctx.
        -- apply kd_tr with m; auto; try reflexivity.
           ++ unfold set_mode, upd_s. sf_auto.
           ++ right. cbn. unfold md_dec; tauto.
           ++ unfold bitsn; lx_simp. rewrite Hu, Hv. apply at_mode_dist_i; [exact Hd|reflexivity|].
              exists k, j, ll, dl, syms, p0, len, dist.
              split; [apply in_huff_tr with (m_s m); [sf_auto|exact IH]|].
              split; [exact Hj|]. split; [exact Hs|]. split; [exact Ho|]. cbv zeta. lx_simp.
              split; [reflexivity|]. split; [rewrite <- Hex; lia|]. left. lia.
        -- apply dw_tr with m; auto; try reflexivity.
           ++ unfold set_mode, upd_s. sf_auto.
           ++ lx_simp. rewrite Hinp. rewrite Hinp in Dnx. lia.
           ++ lx_simp. lia.
        -- reflexivity.
        -- reflexivity.
Qed.
