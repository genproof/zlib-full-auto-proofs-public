(* RT-I: copy of rfc1951/DecDecDistext.v over the generalized definitions RTIGDefs.v. *)
(* Part of DecDec.group_dec: the pass from DISTEXT (falls through to MATCH).  Statements: DecDecDefs.v; helpers: DecDecKd.v; template:
   DecDecLit.v (pass_lit). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.roundtrip.RTIGDecDecKd.
Import ListNotations.
Local Open Scope Z_scope.

Lemma de_bits_le_len v n : 0 <= n -> Zlength (bits_le v n) = n.
Proof.
  intros H. unfold bits_le. rewrite Zlength_map, Zlength_correct, seq_length. apply Z2Nat.id; exact H.
Qed.

Lemma de_send_sym_len lens s : 0 <= Znth s lens -> Zlength (send_sym lens s) = Znth s lens.
Proof. intros H. unfold send_sym, bits_msb. rewrite Zlength_rev. apply de_bits_le_len; exact H. Qed.

Lemma de_epos_ge p bs k : p <= epos p bs k.
Proof.
  revert p bs. induction k as [|k IH]; intros p bs; [destruct bs; cbn; lia|]. destruct bs as [|b r]; [cbn; lia|].
  cbn [epos]. specialize (IH (p + Zlength (enc_block p false b)) r). pose proof (Zlength_nonneg (enc_block p false b)). lia.
Qed.

Lemma de_p0_nonneg G s k j ll dl syms p0 : in_huff G s k j ll dl syms p0 -> 0 <= p0.
Proof.
  intros (_ & _ & _ & _ & _ & E). rewrite E. unfold bpos, D0, sym_off.
  pose proof (de_epos_ge 0 (dc_bs G) (Z.to_nat k)).
  pose proof (Zlength_nonneg (hdr_bytes (dc_w G))).
  pose proof (Zlength_nonneg (flat_map (send_one ll dl) (firstn (Z.to_nat j) syms))).
  assert (0 <= hb_hdr (blk G k)).
  { unfold hb_hdr. destruct (blk G k); try lia.
    match goal with |- context [17 + 3 * Zlength ?a + Zlength ?b] =>
      pose proof (Zlength_nonneg a); pose proof (Zlength_nonneg b) end. lia. }
  lia.
Qed.

(* the tail D of a part A ++ D of the bits *)
Lemma de_sub_tail (S A D: list bool) p0 :
  0 <= p0 -> sublist p0 (p0 + Zlength (A ++ D)) S = A ++ D ->
  sublist (p0 + Zlength A) (p0 + Zlength A + Zlength D) S = D.
Proof.
  intros H0 E. rewrite Zlength_app in E.
  pose proof (Zlength_nonneg A). pose proof (Zlength_nonneg D).
  assert (X : sublist (Zlength A) (Zlength A + Zlength D) (sublist p0 (p0 + (Zlength A + Zlength D)) S) = D).
  { rewrite E. rewrite sublist_app2 by lia. replace (Zlength A - Zlength A) with 0 by lia.
    replace (Zlength A + Zlength D - Zlength A) with (Zlength D) by lia. apply sublist_same; lia. }
  rewrite sublist_sublist in X by lia.
  transitivity (sublist (Zlength A + p0) (Zlength A + Zlength D + p0) S); [f_equal; lia|exact X].
Qed.

(* the result of a pass from a state with the same output *)
Lemma de_post_ow G pos inp ob flush m m1 o :
  m_ow m1 = m_ow m -> dstep_post G pos inp ob flush m1 o -> dstep_post G pos inp ob flush m o.
Proof. intros E. destruct o; cbn [dstep_post]; [|tauto]. rewrite E. tauto. Qed.

(* falling through to MATCH with the reference read *)
Lemma de_to_match G pos inp ob flush m m2 k j ll dl syms p0 len dist :
  pass_ok MATCH c_MATCH -> in_ctx G pos inp -> Kd G pos inp ob m -> m_mode m = DISTEXT -> dw m ->
  m_inp m2 = m_inp m -> m_out m2 = m_out m -> m_aout m2 = m_aout m -> m_tout m2 = m_tout m ->
  m_ret m2 = m_ret m -> m_ow m2 = m_ow m -> same_fix (m_s m) (m_s m2) ->
  m_mode m2 = MATCH -> m_leave m2 = 0 -> 0 <= m_nx m2 <= Zlength (m_inp m2) ->
  hold_ok G (pos + m_nx m2) (m_hold m2) (m_bits m2) ->
  in_huff G (m_s m) k j ll dl syms p0 -> j < Zlength syms -> sym_at syms j = Ref len dist ->
  i_offset (m_s m2) = dist -> i_length (m_s m2) = len -> 3 <= len ->
  ob ++ m_ow m = outj G k syms j ->
  8 * (pos + m_nx m2) - m_bits m2 = p0 + Zlength (send_one ll dl (Ref len dist)) -> m_bits m2 < 8 ->
  dstep_post G pos inp ob flush m (c_MATCH m2).
Proof.
  intros MP Ctx K Hmd D Ei Eo Ea Et Er Ew F Hmd2 Hl2 Hn Hh IH Hj Hs Hoff Hlen Hl3 Ho Hq Hb.
  apply de_post_ow with m2; [exact Ew|]. apply MP; auto.
  - apply kd_tr with m; auto.
    + rewrite Hmd. unfold md_dec; tauto.
    + right. unfold m_mode in Hmd2. rewrite Hmd2. unfold md_dec; tauto.
    + apply at_mode_match_i; [exact Hh|exact Hmd2|].
      exists k, j, ll, dl, syms, p0, len, dist. split; [apply in_huff_tr with (m_s m); auto|].
      split; [exact Hj|]. split; [exact Hs|]. split; [exact Hoff|]. split; [lia|].
      split; [|split; [exact Hq|exact Hb]].
      rewrite Ew, Ho, Hlen, Z.sub_diag. reflexivity.
  - apply dw_tr with m; auto. destruct D as (_ & _ & _ & A). rewrite Ew, Ea. lia.
Qed.

Lemma pass_distext : dkit_stmt -> lay_stmt -> tabs_stmt -> need_stmt -> pass_ok MATCH c_MATCH -> pass_ok DISTEXT c_DISTEXT.
Proof.
  intros DK LAY TABS NEED MP G pos inp ob flush m Ctx K D Hl Hmd.
  pose proof Ctx as (Gok & _).
  pose proof (kd_at _ _ _ _ _ K) as At.
  destruct (at_mode_distext_e _ _ _ _ _ _ At Hmd)
    as (Hh & k & j & ll & dl & syms & p0 & len & dist & IH & Hj & Hs & Ho & Hlen & Hoff & Hex & Hq & Hb).
  destruct (LAY G (m_s m) k j ll dl syms p0 Gok IH) as (_ & _ & _ & LO & _ & _ & L1 & _).
  destruct (L1 Hj) as (SO & Sub & Slen & Oj & IH1). clear L1. rewrite Hs in SO, Sub, Slen, Oj, IH1.
  cbn [sym_ok] in SO. destruct SO as (Hl3 & Hd1 & Hdw & _ & _ & Hdc & Hdn).
  pose proof (p0_nonneg := de_p0_nonneg _ _ _ _ _ _ _ _ IH).
  assert (Hwb : dc_wb G <= 15).
  { destruct (kd_glob _ _ _ _ _ K) as (_ & _ & G4 & _).
    assert (N : m_mode m <> HEAD) by (rewrite Hmd; unfold DISTEXT, HEAD; lia). specialize (G4 N). lia. }
  assert (Hd32 : dist <= 32768).
  { assert (2 ^ dc_wb G <= 2 ^ 15).
    { destruct (Z.ltb_spec (dc_wb G) 0); [rewrite Z.pow_neg_r by lia; lia|apply Z.pow_le_mono_r; lia]. }
    change (2 ^ 15) with 32768 in *. lia. }
  destruct TABS as (T1 & T2 & _).
  destruct (T1 len ltac:(lia)) as (Ti & Tie & _).
  destruct (T2 dist ltac:(lia)) as (Td & Tde & Tdb).
  set (i := len_code len) in *. set (d := dist_code dist) in *.
  assert (Hdl : 0 <= Znth d dl) by (assert (Rd : 0 <= d < Zlength dl) by lia; pose proof (Forall_Znth _ _ d Rd LO) as X; cbv beta in X; lia).
  cbn [send_one] in Sub, Slen. fold i d in Sub, Slen.
  rewrite !Zlength_app, de_bits_le_len, de_bits_le_len, (de_send_sym_len dl d) in Slen by lia.
  rewrite !app_assoc in Sub.
  apply de_sub_tail in Sub; [|exact p0_nonneg].
  rewrite !Zlength_app, de_bits_le_len, (de_send_sym_len dl d), de_bits_le_len in Sub by lia.
  assert (EL : p0 + Zlength (send_one ll dl (Ref len dist)) =
               8 * (pos + m_nx m) - m_bits m + Znth d dist_extra).
  { cbn [send_one]. fold i d. rewrite !Zlength_app, de_bits_le_len, de_bits_le_len, (de_send_sym_len dl d) by lia.
    lia. }
  pose proof Hh as (Hb0 & _ & _).
  replace (p0 + (Zlength (send_sym ll (257 + i)) + Znth i len_extra + Znth d dl)) with
    (8 * (pos + m_nx m) - m_bits m) in Sub by lia.
  unfold c_DISTEXT. rewrite Hex.
  destruct (Znth d dist_extra =? 0) eqn:EX; cbn [negb].
  - apply Z.eqb_eq in EX.
    apply de_to_match with k j ll dl syms p0 len dist; auto; try reflexivity.
    + unfold set_mode, upd_s. sf_auto.
    + destruct D as (_ & _ & Dn & _). exact Dn.
    + cbn [set_mode upd_s m_s set_m_s set_i_mode i_offset]. rewrite Hoff.
      rewrite EX, Z.pow_0_r in Tdb. lia.
    + lia.
    + cbn [set_mode upd_s m_s set_m_s m_nx m_bits]. rewrite EL, EX. lia.
    + cbn [set_mode upd_s m_s set_m_s m_bits]. rewrite EX in Hb. lia.
  - apply Z.eqb_neq in EX.
    set (n := Znth d dist_extra) in *.
    destruct (NEED G pos inp m n (dist - Znth d dist_base) (8 * (pos + m_nx m) - m_bits m))
      as (nx & h & b & En & Hnx & Hhb & Hqb & C).
    { exact Ctx. }
    { destruct D as (_ & _ & Dn & _). split; [exact (kd_inp _ _ _ _ _ K)|]. split; [|exact Hh].
      rewrite <- (kd_inp _ _ _ _ _ K). exact Dn. }
    { reflexivity. }
    { exact Hl. }
    { lia. }
    { lia. }
    { exact Sub. }
    { lia. }
    { exact Hb. }
    remember (m_leave (needbits n m)) as lv eqn:Elv. clear Elv.
    cbv zeta. rewrite En.
    destruct C as [(Hlv & Hnxe & Hbn & Hpos) | (Hlv & Hbn & Hhv)]; subst lv.
    + rewrite Z.eqb_refl. cbn [dstep_post]. split; [|split].
      * apply kd_tr with m; auto; try reflexivity.
        -- rewrite Hmd. unfold md_dec; tauto.
        -- apply same_fix_refl.
        -- right. change (md_dec (m_mode m)). rewrite Hmd. unfold md_dec; tauto.
        -- cbn [m_s m_nx m_hold m_bits m_ow set_m_leave set_m_bits set_m_hold set_m_nx].
           apply at_mode_distext_i; [exact Hhb|exact Hmd|].
           exists k, j, ll, dl, syms, p0, len, dist. split; [exact IH|]. split; [exact Hj|]. split; [exact Hs|].
           split; [exact Ho|]. cbv zeta. fold i d. split; [exact Hlen|]. split; [exact Hoff|]. split; [exact Hex|].
           split; [rewrite Hqb; exact Hq|]. right. exact Hbn.
      * exists []. rewrite app_nil_r. reflexivity.
      * intros _. right; left. cbn [m_nx set_m_leave set_m_bits set_m_hold set_m_nx]. split; [exact Hnxe|exact Hpos].
    + change (0 =? 1) with false. cbv iota.
      assert (U : u32 (b - n) = b - n) by (unfold u32; apply Z.mod_small; change (2 ^ 32) with 4294967296; lia).
      apply de_to_match with k j ll dl syms p0 len dist; auto; try reflexivity.
      all: cbn [set_mode upd_s dropbits m_s m_nx m_hold m_bits m_leave m_inp set_m_s set_m_leave set_m_bits set_m_hold set_m_nx
                set_i_mode set_i_offset set_i_back i_offset i_length bitsn].
      * sf_auto.
      * destruct D as (_ & _ & Dn & _). rewrite (kd_inp _ _ _ _ _ K). lia.
      * rewrite U. apply (dk_drop DK); [exact Hhb|lia].
      * unfold bitsn. cbn [m_hold set_m_leave set_m_bits set_m_hold set_m_nx]. rewrite Hoff, Hhv.
        replace (Znth d dist_base + (dist - Znth d dist_base)) with dist by lia.
        unfold u32; apply Z.mod_small; change (2 ^ 32) with 4294967296; lia.
      * lia.
      * rewrite U, EL. lia.
      * rewrite U. lia.
Qed.
