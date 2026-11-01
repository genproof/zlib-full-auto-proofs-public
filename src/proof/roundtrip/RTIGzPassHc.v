(* RT-I part rti_gz_pass: the case HCRC of the gzip header pass (stage 7 -> TYPE) *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.roundtrip.RTIKit.
Require Import Zlib.proof.roundtrip.RTIGDefs.
Require Import Zlib.proof.roundtrip.RTIGzPassDefs.
Import ListNotations.
Local Open Scope Z_scope.

(* NEEDBITS(16) on an empty bit buffer with two bytes there *)
Lemma gphc_nb16 m b0 b1 :
  m_bits m = 0 -> m_hold m = 0 -> 0 <= m_nx m -> m_nx m + 2 <= Zlength (m_inp m) ->
  Znth (m_nx m) (m_inp m) = b0 -> Znth (m_nx m + 1) (m_inp m) = b1 -> 0 <= b0 < 256 -> 0 <= b1 < 256 ->
  needbits 16 m = set_m_bits (set_m_hold (set_m_nx m (m_nx m + 2)) (b0 + 256 * b1)) 16.
Proof.
  intros Hb Hh N0 N2 E0 E1 B0 B1.
  unfold needbits. cbn [needbits_f]. rewrite Hb. change (0 <? 16) with true. cbv iota.
  unfold m_have. replace (Zlength (m_inp m) - m_nx m =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  cbv iota.
  assert (P1: m_bits (pull m) = 8 /\ m_nx (pull m) = m_nx m + 1 /\ m_inp (pull m) = m_inp m /\
              m_hold (pull m) = b0).
  { unfold pull. cbn [m_bits m_nx m_inp m_hold set_m_bits set_m_hold set_m_nx].
    rewrite Hb, Hh, E0. unfold u32, u64. rewrite Z.mod_small by lia.
    rewrite Z.mod_small by (rewrite Z.mul_1_r; lia). repeat split; lia. }
  destruct P1 as (P1b & P1n & P1i & P1h).
  rewrite P1b. change (8 <? 16) with true. cbv iota.
  rewrite P1n, P1i. replace (Zlength (m_inp m) - (m_nx m + 1) =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  cbv iota.
  assert (P2: m_bits (pull (pull m)) = 16).
  { unfold pull at 1. cbn [m_bits set_m_bits set_m_hold set_m_nx]. rewrite P1b. reflexivity. }
  rewrite P2. change (16 <? 16) with false. cbv iota.
  unfold pull at 1. rewrite P1b, P1n, P1i, P1h.
  replace (Znth (m_nx m + 1) (m_inp m)) with b1 by auto.
  unfold pull. cbn [m_nx set_m_bits set_m_hold set_m_nx m_bits].
  rewrite Hb. change (u32 (0 + 8)) with 8. change (u32 (8 + 8)) with 16.
  replace (m_nx m + 1 + 1) with (m_nx m + 2) by lia.
  replace (u64 (b0 + b1 * 2 ^ 8)) with (b0 + 256 * b1)
    by (unfold u64; rewrite Z.mod_small; change (2 ^ 8) with 256; lia).
  destruct m; reflexivity.
Qed.

Lemma gphc_fl h : Z.land (8 + 256 * gz_flg h) 512 = (if gz_hcrc h then 512 else 0) /\
  Z.land (Z.shiftr (8 + 256 * gz_flg h) 9) 1 = (if gz_hcrc h then 1 else 0).
Proof.
  unfold gz_flg. destruct (gz_text h), (gz_hcrc h), (gz_extra h), (gz_name h), (gz_comment h); split; reflexivity.
Qed.

Lemma gphc_le2 c : le_bytes c 2 = [c mod 256; Z.shiftr c 8 mod 256].
Proof. unfold le_bytes. reflexivity. Qed.

Lemma gphc_land c : c mod 256 + 256 * (Z.shiftr c 8 mod 256) = Z.land c 65535.
Proof.
  change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. rewrite Z.shiftr_div_pow2 by lia.
  change (2 ^ 8) with 256. change (2 ^ 16) with 65536.
  pose proof (Z.div_mod c 256 ltac:(lia)). pose proof (Z.div_mod (c / 256) 256 ltac:(lia)).
  pose proof (Z.mod_pos_bound c 256 ltac:(lia)). pose proof (Z.mod_pos_bound (c / 256) 256 ltac:(lia)).
  apply Z.mod_unique with (q := c / 256 / 256); lia.
Qed.

Lemma gphc_gb h : gz_hcrc h = true ->
  gz_bytes h = gz_bytes0 h ++ le_bytes (Zlib.proof.crc32.Model.ref_crc32 0 (gz_bytes0 h)) 2.
Proof. intros E. unfold gz_bytes. cbv zeta. rewrite E. reflexivity. Qed.

Lemma gphc_gb0 h : gz_hcrc h = false -> gz_bytes h = gz_bytes0 h.
Proof. intros E. unfold gz_bytes. cbv zeta. rewrite E. reflexivity. Qed.

Lemma gphc_hv g xfl b : RF.rhdr_ok g -> gz_hcrc (RF.fhdr_of (Some g) xfl) = b -> (if b then 1 else 0) = DS.gz_hcrc g.
Proof.
  intros R <-. cbn [RF.fhdr_of gz_hcrc]. destruct R as (_ & [E|E] & _); rewrite E; reflexivity.
Qed.

Lemma gphc_at8 xfl h0 g x nm cm :
  gh_at xfl h0 8 g x nm cm = set_h_done (set_h_hcrc (gh_at xfl h0 7 g x nm cm) (DS.gz_hcrc g)) 1.
Proof. unfold gh_at. cbn [Nat.leb]. reflexivity. Qed.

Lemma gp_hc_ok : gp_hcrc_stmt.
Proof.
  intros gh xfl O z hd h0 m OK [M [FL [CK HH]]].
  destruct OK as ([rest EO] & BO & RH & XF & LO).
  change (RF.fhdr_of gh xfl) with (gp_H gh xfl) in EO.
  unfold gp_fl, gp_F in FL. unfold gp_ck in CK.
  destruct (gphc_fl (gp_H gh xfl)) as [F512 F9].
  destruct M as [Mi Mn Mh Mb Ml Mo Mout Ma Mr Mt Mmd Mla Mtot Mw Mws Mwb Mhd].
  cbn [gp_p] in Mn.
  (* the gz_header's done/hcrc value *)
  assert (HV: forall b, gz_hcrc (gp_H gh xfl) = b -> hd = true ->
            exists g x nm cm, gh = Some g /\ head_bufs g x nm cm h0 /\ h_done h0 = 0 /\
              m_h m = gh_at xfl h0 7 g x nm cm /\ (if b then 1 else 0) = DS.gz_hcrc g).
  { intros b Eb Hd. destruct (HH Hd) as (g & x & nm & cm & Eg & Hb & Hdn & Hm).
    exists g, x, nm, cm. subst gh. refine (conj eq_refl (conj Hb (conj Hdn (conj Hm _)))). apply (gphc_hv g xfl b (RH g eq_refl) Eb). }
  clear HH.
  unfold c_HCRC. cbv beta zeta. rewrite FL, F512.
  destruct (gz_hcrc (gp_H gh xfl)) eqn:HC.
  - change (negb (512 =? 0)) with true. cbv iota.
    rewrite (gphc_gb _ HC), gphc_le2 in EO.
    specialize (CK eq_refl).
    set (A := gz_bytes0 (gp_H gh xfl)) in *.
    remember (Zlib.proof.crc32.Model.ref_crc32 0 A) as c eqn:Ec.
    assert (EI: m_inp m = A ++ [c mod 256; Z.shiftr c 8 mod 256] ++ rest)
      by (rewrite Mi, EO, app_assoc; reflexivity).
    assert (LA: 0 <= Zlength A) by apply Zlength_nonneg.
    assert (Lr: 0 <= Zlength rest) by apply Zlength_nonneg.
    assert (C0: 0 <= c mod 256 < 256) by (apply Z.mod_pos_bound; lia).
    assert (C1: 0 <= Z.shiftr c 8 mod 256 < 256) by (apply Z.mod_pos_bound; lia).
    rewrite (gphc_nb16 m (c mod 256) (Z.shiftr c 8 mod 256)); auto; try lia.
    2: { rewrite EI, !Zlength_app, !Zlength_cons, Zlength_nil. lia. }
    2: { rewrite EI, Mn, app_Znth2 by lia. rewrite Z.sub_diag. reflexivity. }
    2: { rewrite EI, Mn, app_Znth2 by lia. replace (Zlength A + 1 - Zlength A) with 1 by lia. reflexivity. }
    cbn [m_leave m_s m_h m_hold set_m_bits set_m_hold set_m_nx]. rewrite Ml. change (0 =? 1) with false. cbv iota.
    rewrite Mw. change (negb (Z.land 15 4 =? 0)) with true.
    assert (CKA: i_check (m_s m) = c).
    { rewrite CK. change (gp_p gh xfl 7) with (Zlength A). rewrite EO, <- app_assoc, sublist_app1 by lia. rewrite sublist_same by lia. exact (eq_sym Ec). }
    rewrite CKA, gphc_land, Z.eqb_refl. cbv [negb andb]. cbv iota.
    unfold initbits. cbn [m_s set_m_bits set_m_hold set_m_nx]. rewrite Mhd.
    destruct hd.
    + destruct (HV true eq_refl eq_refl) as (g & x & nm & cm & Eg & Hb & Hdn & Hm & Hv).
      eexists; split; [reflexivity|].
      unfold upd_h, set_mode, set_m_adler, upd_s, gp_fl, gp_hh, gp_F.
      cbn [m_s m_h m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave m_adler m_tin m_tout
           set_m_s set_m_h set_m_bits set_m_hold set_m_nx set_m_adler i_mode i_last i_total i_wrap i_wsize
           i_wbits i_head i_flags i_check set_i_mode set_i_check].
      rewrite FL, F9.
      split; [|split; [reflexivity|split]].
      * constructor; cbn [m_s m_h m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave m_adler m_tin m_tout
           set_m_s set_m_h set_m_bits set_m_hold set_m_nx set_m_adler i_mode i_last i_total i_wrap i_wsize
           i_wbits i_head i_flags i_check set_i_mode set_i_check]; auto.
        cbn [gp_p]. rewrite (gphc_gb _ HC), gphc_le2. fold A. rewrite Zlength_app, Mn. reflexivity.
      * intros _. exists g, x, nm, cm. refine (conj Eg (conj Hb (conj Hdn _))). rewrite Hm, gphc_at8, <- Hv. reflexivity.
      * reflexivity.
    + eexists; split; [reflexivity|].
      unfold set_mode, set_m_adler, upd_s, gp_fl, gp_hh, gp_F.
      cbn [m_s m_h m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave m_adler m_tin m_tout
           set_m_s set_m_h set_m_bits set_m_hold set_m_nx set_m_adler i_mode i_last i_total i_wrap i_wsize
           i_wbits i_head i_flags i_check set_i_mode set_i_check].
      split; [|split; [exact FL|split]].
      * constructor; cbn [m_s m_h m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave m_adler m_tin m_tout
           set_m_s set_m_h set_m_bits set_m_hold set_m_nx set_m_adler i_mode i_last i_total i_wrap i_wsize
           i_wbits i_head i_flags i_check set_i_mode set_i_check]; auto.
        cbn [gp_p]. rewrite (gphc_gb _ HC), gphc_le2. fold A. rewrite Zlength_app, Mn. reflexivity.
      * discriminate.
      * reflexivity.
  - change (negb (0 =? 0)) with false. cbv iota.
    rewrite Mhd. destruct hd.
    + destruct (HV false eq_refl eq_refl) as (g & x & nm & cm & Eg & Hb & Hdn & Hm & Hv).
      eexists; split; [reflexivity|].
      unfold upd_h, set_mode, set_m_adler, upd_s, gp_fl, gp_hh, gp_F.
      cbn [m_s m_h m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave m_adler m_tin m_tout
           set_m_s set_m_h set_m_bits set_m_hold set_m_nx set_m_adler i_mode i_last i_total i_wrap i_wsize
           i_wbits i_head i_flags i_check set_i_mode set_i_check].
      rewrite FL, F9.
      split; [|split; [reflexivity|split]].
      * constructor; cbn [m_s m_h m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave m_adler m_tin m_tout
           set_m_s set_m_h set_m_bits set_m_hold set_m_nx set_m_adler i_mode i_last i_total i_wrap i_wsize
           i_wbits i_head i_flags i_check set_i_mode set_i_check]; auto.
        cbn [gp_p]. rewrite (gphc_gb0 _ HC). exact Mn.
      * intros _. exists g, x, nm, cm. refine (conj Eg (conj Hb (conj Hdn _))). rewrite Hm, gphc_at8, <- Hv. reflexivity.
      * reflexivity.
    + eexists; split; [reflexivity|].
      unfold set_mode, set_m_adler, upd_s, gp_fl, gp_hh, gp_F.
      cbn [m_s m_h m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave m_adler m_tin m_tout
           set_m_s set_m_h set_m_bits set_m_hold set_m_nx set_m_adler i_mode i_last i_total i_wrap i_wsize
           i_wbits i_head i_flags i_check set_i_mode set_i_check].
      split; [|split; [exact FL|split]].
      * constructor; cbn [m_s m_h m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave m_adler m_tin m_tout
           set_m_s set_m_h set_m_bits set_m_hold set_m_nx set_m_adler i_mode i_last i_total i_wrap i_wsize
           i_wbits i_head i_flags i_check set_i_mode set_i_check]; auto.
        cbn [gp_p]. rewrite (gphc_gb0 _ HC). exact Mn.
      * discriminate.
      * reflexivity.
Qed.
