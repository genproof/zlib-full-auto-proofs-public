(* RT-I: copy of rfc1951/DecDecDist.v over the generalized definitions RTIGDefs.v. *)
(* Part of DecDec.group_dec: the pass from DIST (falls through to DISTEXT).  Statements: DecDecDefs.v; helpers: DecDecKd.v; template:
   DecDecLit.v (pass_lit). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.roundtrip.RTIGDecDecKd.
Import ListNotations.
Local Open Scope Z_scope.

(* c_DIST through dcode *)
Lemma c_DIST_dcode m :
  c_DIST lenfix_list distfix_list m =
  let '(here, m', ok) := dcode (islink DISTS) (i_distcode (m_s m)) (i_distbits (m_s m)) m in
  if negb ok then IBrk m' else
  if negb (Z.land (e_op here) 64 =? 0) then IBrk (set_bad m' M_d_code) else
  c_DISTEXT (set_mode (upd_s m' (fun s => set_i_extra (set_i_offset s (e_val here)) (Z.land (e_op here) 15))) DISTEXT).
Proof.
  unfold c_DIST, dcode. destruct (lookup1 _ _ _ _ m) as [[h1 m1] ok1].
  destruct ok1; [|reflexivity]. cbv beta iota zeta.
  replace (islink DISTS (e_op h1)) with (Z.land (e_op h1) 240 =? 0) by reflexivity.
  destruct (Z.land (e_op h1) 240 =? 0).
  - destruct (lookup2 _ _ _ _ _) as [[h2 m2] ok2]. destruct ok2; reflexivity.
  - reflexivity.
Qed.

Lemma dext_facts d : 0 <= d <= 29 ->
  Z.land (16 + Znth d dist_extra) 64 = 0 /\ Z.land (16 + Znth d dist_extra) 15 = Znth d dist_extra.
Proof.
  intros H.
  assert (d = 0 \/ d = 1 \/ d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6 \/ d = 7 \/ d = 8 \/ d = 9 \/
          d = 10 \/ d = 11 \/ d = 12 \/ d = 13 \/ d = 14 \/ d = 15 \/ d = 16 \/ d = 17 \/ d = 18 \/ d = 19 \/
          d = 20 \/ d = 21 \/ d = 22 \/ d = 23 \/ d = 24 \/ d = 25 \/ d = 26 \/ d = 27 \/ d = 28 \/ d = 29) by lia.
  repeat (destruct H0 as [H0|H0]; [subst; split; reflexivity|]). subst; split; reflexivity.
Qed.

Lemma dist_code_range dist : 0 <= dist_code dist <= 29.
Proof.
  unfold dist_code. pose proof (Zlength_nonneg (filter (fun b => b <=? dist) (sublist 1 30 dist_base))).
  split; [lia|].
  rewrite !Zlength_correct in *. pose proof (filter_length_le (fun b => b <=? dist) (sublist 1 30 dist_base)).
  assert (length (sublist 1 30 dist_base) = 29%nat) by reflexivity. lia.
Qed.

Lemma Zlength_bits_le v n : 0 <= n -> Zlength (bits_le v n) = n.
Proof.
  intros H. unfold bits_le. rewrite Zlength_map, Zlength_correct, length_seq. lia.
Qed.

Lemma Zlength_send_sym lens s : 0 <= Znth s lens -> Zlength (send_sym lens s) = Znth s lens.
Proof.
  intros H. unfold send_sym, bits_msb. rewrite Zlength_rev. apply Zlength_bits_le; exact H.
Qed.

Lemma empty_used lens s : empty_code lens -> used lens s -> False.
Proof.
  unfold empty_code, nused, used. intros E (Hs & Hn).
  rewrite Zlength_correct in E. destruct (filter _ lens) eqn:F; [|cbn in E; lia].
  assert (I : In (Znth s lens) lens) by (apply Znth_In; exact Hs).
  assert (I' : In (Znth s lens) (filter (fun l => negb (l =? 0)) lens)).
  { apply filter_In. split; [exact I|]. apply Z.eqb_neq in Hn. rewrite Hn. reflexivity. }
  rewrite F in I'. inversion I'.
Qed.

Lemma dstep_post_ow G pos inp ob flush m m1 o :
  m_ow m1 = m_ow m -> dstep_post G pos inp ob flush m1 o -> dstep_post G pos inp ob flush m o.
Proof.
  intros E. destruct o as [m'|r m']; cbn [dstep_post]; [|tauto].
  intros (K & (d & Hd) & L). split; [exact K|]. split; [exists d; rewrite Hd, E; reflexivity|exact L].
Qed.

Lemma sub_mid (L X1 X2 Y W: list bool) p : 0 <= p ->
  sublist p (p + Zlength (X1 ++ X2 ++ Y ++ W)) L = X1 ++ X2 ++ Y ++ W ->
  sublist (p + Zlength X1 + Zlength X2) (p + Zlength X1 + Zlength X2 + Zlength Y) L = Y.
Proof.
  intros Hp E. rewrite app_assoc in E.
  pose proof (Zlength_nonneg X1). pose proof (Zlength_nonneg X2). pose proof (Zlength_nonneg Y).
  pose proof (Zlength_nonneg W).
  assert (Z1 : Zlength ((X1 ++ X2) ++ Y ++ W) = Zlength X1 + Zlength X2 + Zlength Y + Zlength W)
    by (rewrite !Zlength_app; lia).
  replace (sublist (p + Zlength X1 + Zlength X2) (p + Zlength X1 + Zlength X2 + Zlength Y) L)
    with (sublist (Zlength (X1 ++ X2)) (Zlength (X1 ++ X2) + Zlength Y)
            (sublist p (p + Zlength ((X1 ++ X2) ++ Y ++ W)) L)).
  - rewrite E, sublist_app2 by (rewrite Zlength_app; lia). rewrite Z.sub_diag, Z.add_simpl_l.
    rewrite sublist_app1 by lia. apply sublist_same; lia.
  - rewrite sublist_sublist by (rewrite ?Zlength_app; lia). rewrite ?Zlength_app. f_equal; lia.
Qed.

Lemma epos_ge p bs k : p <= epos p bs k.
Proof.
  revert p bs. induction k as [|k IHk]; intros p bs; destruct bs as [|b r]; cbn [epos]; try lia.
  specialize (IHk (p + Zlength (enc_block p false b)) r). pose proof (Zlength_nonneg (enc_block p false b)). lia.
Qed.

Lemma p0_nonneg G s k j ll dl syms p0 : in_huff G s k j ll dl syms p0 -> 0 <= p0.
Proof.
  intros (_ & _ & _ & _ & _ & ->). unfold bpos, D0, sym_off.
  pose proof (epos_ge 0 (dc_bs G) (Z.to_nat k)).
  assert (0 <= hb_hdr (blk G k)).
  { destruct (blk G k) as [?|?|nl nd cs tk sy]; cbn [hb_hdr]; try lia.
    pose proof (Zlength_nonneg cs). pose proof (Zlength_nonneg (flat_map (send_tok (cl_lens cs)) tk)). lia. }
  pose proof (Zlength_nonneg (hdr_bytes (dc_w G))).
  pose proof (Zlength_nonneg (flat_map (send_one ll dl) (firstn (Z.to_nat j) syms))). lia.
Qed.

Ltac msimp := cbn [set_mode upd_s m_s m_ow m_inp m_nx m_hold m_bits m_leave m_aout m_out m_tout m_ret
  set_m_s set_m_leave set_m_bits set_m_hold set_m_nx i_mode i_length i_offset i_extra
  set_i_mode set_i_back set_i_offset set_i_extra m_mode].

Lemma pass_dist : lay_stmt -> tabs_stmt -> dcode_stmt -> pass_ok DISTEXT c_DISTEXT -> pass_ok DIST (c_DIST lenfix_list distfix_list).
Proof.
  intros LAY TABS DC PX G pos inp ob flush m Ctx K D Hl Hmd.
  pose proof Ctx as (Gok & Hpos & _).
  pose proof (kd_at _ _ _ _ _ K) as At.
  destruct (at_mode_dist_e _ _ _ _ _ _ At Hmd) as (Hh & k & j & ll & dl & syms & p0 & len & dist & IH & Hj & Hs & Ho & Hlen & Hq & Hb).
  destruct (LAY G (m_s m) k j ll dl syms p0 Gok IH) as (_ & _ & _ & Ldl & Cdl & _ & L1 & _).
  destruct (L1 Hj) as (SO & Sb & Sle & _ & _). clear L1. rewrite Hs in SO, Sb, Sle.
  destruct SO as (Hlr & Hd1 & Hdw & _ & _ & Hdl & Hdn).
  pose proof (dist_code_range dist) as Hdr.
  set (d := dist_code dist) in *.
  assert (Ud : used dl d) by (split; [lia|exact Hdn]).
  assert (Cdl' : complete dl \/ single dl).
  { destruct Cdl as [C|[C|C]]; auto. exfalso. exact (empty_used _ _ C Ud). }
  assert (Dnn : 0 <= Znth d dl).
  { unfold lens_ok in Ldl. rewrite Forall_forall in Ldl.
    assert (I : In (Znth d dl) dl) by (apply Znth_In; lia). specialize (Ldl _ I). lia. }
  pose proof (p0_nonneg _ _ _ _ _ _ _ _ IH) as P0.
  destruct TABS as (T1 & _ & _ & _ & _ & T6).
  destruct (T1 len Hlr) as (_ & Hie & _).
  unfold send_one in Sb, Sle. cbv zeta in Sb, Sle. fold d in Sb, Sle.
  pose proof (sub_mid (sbits G) _ _ _ _ p0 P0 Sb) as Sub.
  rewrite Zlength_bits_le, (Zlength_send_sym dl d) in Sub by lia. rewrite <- Hq in Sub.
  assert (Qle : 8 * (pos + m_nx m) - m_bits m + Znth d dl <= 8 * slen G).
  { rewrite !Zlength_app, Zlength_bits_le, (Zlength_send_sym dl d) in Sle by lia.
    pose proof (Zlength_nonneg (bits_le (dist - Znth d dist_base) (Znth d dist_extra))). lia. }
  pose proof D as (Tl & Tv & Hnx & Haout & Hwn).
  pose proof IH as (_ & _ & _ & _ & Td & _).
  assert (MB : m_buf G pos inp m) by (split; [exact (kd_inp _ _ _ _ _ K)|split; [rewrite <- (kd_inp _ _ _ _ _ K); exact Hnx|exact Hh]]).
  pose proof (DC G pos inp m DISTS (i_distcode (m_s m)) (i_distbits (m_s m)) dl d _ Ctx MB eq_refl
                (or_intror eq_refl) Tv Td Ldl Cdl' Ud Sub Qle Hb) as R.
  rewrite c_DIST_dcode. revert R. destruct (dcode _ _ _ m) as [[here m'] ok].
  intros (nx & h & b & bk & lv & Em & Hnx' & Hh' & OK & NOK).
  assert (Hmd0 : md_dec (m_mode m)) by (unfold md_dec; tauto).
  assert (SF : same_fix (m_s m) (m_s m')) by (subst m'; unfold upd_s; sf_auto).
  destruct ok.
  - destruct (OK eq_refl) as (Elv & Ms & Qb & Hb8). clear OK NOK.
    destruct (T6 d (e_op here) (e_val here) Hdr Ms) as (Eop & Eval).
    destruct (dext_facts d Hdr) as (F64 & F15). rewrite Eop, F64. cbn [Z.eqb negb].
    set (m2 := set_mode (upd_s m' (fun s => set_i_extra (set_i_offset s (e_val here)) (Z.land (16 + Znth d dist_extra) 15))) DISTEXT).
    assert (SF2 : same_fix (m_s m) (m_s m2)) by (subst m2 m'; unfold set_mode, upd_s; sf_auto).
    apply dstep_post_ow with m2; [subst m2 m'; reflexivity|].
    apply (PX G pos inp ob flush m2); [exact Ctx|..].
    + apply kd_tr with m; auto; try (subst m2 m'; reflexivity).
      * right. subst m2. msimp. unfold md_dec; tauto.
      * apply at_mode_distext_i.
        -- subst m2 m'. msimp. exact Hh'.
        -- subst m2. msimp. reflexivity.
        -- exists k, j, ll, dl, syms, p0, len, dist.
           split; [apply in_huff_tr with (m_s m); auto|]. split; [exact Hj|]. split; [exact Hs|].
           split; [subst m2 m'; msimp; exact Ho|].
           subst m2 m'. msimp. fold d. split; [exact Hlen|]. split; [exact Eval|]. split; [exact F15|].
           split; [lia|]. left; lia.
    + apply dw_tr with m; auto; subst m2 m'; msimp; try reflexivity. rewrite (kd_inp _ _ _ _ _ K). lia. lia.
    + subst m2 m'. msimp. rewrite Elv; exact Hl.
    + subst m2. msimp. reflexivity.
  - destruct (NOK eq_refl) as (Elv & Enx & Qb & Hbl & Hsl). clear OK NOK. cbn [negb].
    cbn [dstep_post]. split; [|split].
    + apply kd_tr with m; auto; try (subst m'; reflexivity).
      * right. subst m'. msimp. unfold m_mode in Hmd. rewrite Hmd. unfold md_dec; tauto.
      * apply at_mode_dist_i.
        -- subst m'. msimp. exact Hh'.
        -- subst m'. msimp. exact Hmd.
        -- exists k, j, ll, dl, syms, p0, len, dist.
           split; [apply in_huff_tr with (m_s m); auto|]. split; [exact Hj|]. split; [exact Hs|].
           split; [subst m'; msimp; exact Ho|].
           subst m'. msimp. fold d. split; [exact Hlen|]. split; [lia|]. right; exact Hbl.
    + exists []. rewrite app_nil_r. subst m'. reflexivity.
    + intros _. right; left. subst m'. msimp. split; [exact Enx|exact Hsl].
Qed.
