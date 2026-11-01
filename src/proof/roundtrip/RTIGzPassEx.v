(* RT-I part rti_gz_pass: the cases EXLEN and EXTRA of the gzip header pass (stages 3 -> 4 -> 5) *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.roundtrip.RTIKit.
Require Import Zlib.proof.roundtrip.RTIGDefs.
Require Import Zlib.proof.roundtrip.RTIGzPassDefs.
Require Zlib.proof.crc32.Combine Zlib.proof.adler32.Bytes.
Import ListNotations.
Local Open Scope Z_scope.

(* the flag bits of state->flags = 8 + 256 * FLG that EXLEN/EXTRA test *)
Lemma gpx_bits (H: gzhdr) :
  (Z.land (8 + 256 * gz_flg H) 1024 =? 0) = match gz_extra H with Some _ => false | None => true end /\
  (Z.land (8 + 256 * gz_flg H) 512 =? 0) = negb (gz_hcrc H).
Proof.
  unfold gz_flg. destruct (gz_text H), (gz_hcrc H), (gz_extra H), (gz_name H), (gz_comment H); split; reflexivity.
Qed.

Lemma gpx_le2 v : le_bytes v 2 = [v mod 256; Z.shiftr v 8 mod 256].
Proof. reflexivity. Qed.

Lemma gpx_zlen_le v n : 0 <= n -> Zlength (le_bytes v n) = n.
Proof. intros N. unfold le_bytes. rewrite Zlength_map, Zlength_correct, seq_length. lia. Qed.

Lemma gpx_gA H : Zlength (gA H) = 10.
Proof. unfold gA. rewrite !Zlength_app, gpx_zlen_le by lia. reflexivity. Qed.

(* the layout of O around the extra field *)
Lemma gpx_lay gh xfl O :
  gp_ok gh xfl O ->
  exists R, O = gA (gp_H gh xfl) ++ gX (gp_H gh xfl) ++ R.
Proof.
  intros ((rest & E) & _).
  exists (gN (gp_H gh xfl) ++ gC (gp_H gh xfl) ++
          (if gz_hcrc (gp_H gh xfl) then le_bytes (ref_crc32 0 (gz_bytes0 (gp_H gh xfl))) 2 else []) ++ rest).
  rewrite E. unfold gz_bytes. fold (gp_H gh xfl). rewrite gz_bytes0_split.
  destruct (gz_hcrc (gp_H gh xfl)); rewrite <- !app_assoc; reflexivity.
Qed.

(* the extra field of the header: the user's, of length extra_len <= 4096 *)
Lemma gpx_xlen gh xfl O x :
  gp_ok gh xfl O -> gz_extra (gp_H gh xfl) = Some x -> Zlength x <= 4096.
Proof.
  intros (_ & _ & RH & _) EX. unfold gp_H, RF.fhdr_of in EX. destruct gh as [g|]; [|discriminate].
  cbn [gz_extra] in EX. destruct (DS.gz_extra g) as [x0|] eqn:E0; [|discriminate]. cbn [option_map] in EX. injection EX as <-.
  destruct (RH g eq_refl) as (_ & _ & _ & _ & L & X & _). destruct (X x0 E0) as [Lx _].
  rewrite Zlength_sublist by lia. lia.
Qed.

Lemma gpx_hb gh xfl O g x nm cm h :
  gp_ok gh xfl O -> gh = Some g -> head_bufs g x nm cm h ->
  gz_extra (gp_H gh xfl) = Some x /\ Zlength x = DS.gz_extra_len g.
Proof.
  intros (_ & _ & RH & _) -> HB. destruct HB as (X & _).
  destruct (RH g eq_refl) as (_ & _ & _ & _ & L & XX & _). destruct (XX x X) as [Lx _].
  unfold gp_H, RF.fhdr_of. cbn [gz_extra]. rewrite X. cbn [option_map]. rewrite <- Lx, sublist_same by lia. auto.
Qed.

Lemma gpx_nbS k n m : m_bits m < n -> m_have m <> 0 -> needbits_f (S k) n m = needbits_f k n (pull m).
Proof.
  intros B Hv. cbn [needbits_f]. destruct (Z.ltb_spec (m_bits m) n); [|lia].
  destruct (Z.eqb_spec (m_have m) 0); [lia|]. reflexivity.
Qed.

Lemma gpx_nbE k n m : n <= m_bits m -> needbits_f (S k) n m = m.
Proof. intros B. cbn [needbits_f]. destruct (Z.ltb_spec (m_bits m) n); [lia|]. reflexivity. Qed.

(* NEEDBITS(16) from an empty bit buffer, two bytes available *)
Lemma gpx_nb16 m :
  m_bits m = 0 -> m_hold m = 0 -> 0 <= m_nx m -> m_nx m + 2 <= Zlength (m_inp m) ->
  0 <= Znth (m_nx m) (m_inp m) < 256 -> 0 <= Znth (m_nx m + 1) (m_inp m) < 256 ->
  needbits 16 m = set_m_bits (set_m_hold (set_m_nx m (m_nx m + 2))
                    (Znth (m_nx m) (m_inp m) + 256 * Znth (m_nx m + 1) (m_inp m))) 16.
Proof.
  intros B H N L B0 B1. unfold needbits.
  rewrite gpx_nbS by (unfold m_have; lia).
  rewrite gpx_nbS by (unfold pull, m_have, u32; cbn [m_bits m_nx m_inp set_m_bits set_m_hold set_m_nx];
                      try rewrite B; try (rewrite Z.mod_small by lia); lia).
  rewrite gpx_nbE by (unfold pull, u32; cbn [m_bits set_m_bits]; rewrite B, (Z.mod_small (0 + 8)), Z.mod_small; lia).
  destruct m as [s h inp ao nx ow hold bits i o r lv ad msg ti tou snx sow]; cbn [m_bits m_hold m_nx m_inp] in *; subst.
  unfold pull, u32, u64. cbn [m_bits m_hold m_nx m_inp set_m_bits set_m_hold set_m_nx].
  rewrite (Z.mod_small (0 + 8)) by lia. rewrite (Z.mod_small (8 + 8)) by lia.
  change (2 ^ 0) with 1. change (2 ^ 8) with 256.
  rewrite (Z.mod_small (0 + _ * 1)) by lia. rewrite Z.mod_small by lia.
  replace (nx + 1 + 1) with (nx + 2) by lia.
  replace (0 + Znth nx inp * 1 + Znth (nx + 1) inp * 256)
    with (Znth nx inp + 256 * Znth (nx + 1) inp) by ring.
  reflexivity.
Qed.

(* crc_if under the stage invariant: the CRC is updated exactly with FHCRC *)
Lemma gpx_crc_if (H: gzhdr) m d :
  i_flags (m_s m) = 8 + 256 * gz_flg H -> i_wrap (m_s m) = 15 ->
  crc_if m d = if gz_hcrc H then upd_s m (fun s => set_i_check s (ref_crc32 (i_check s) d)) else m.
Proof.
  intros F W. unfold crc_if. rewrite F, W, (proj2 (gpx_bits H)). destruct (gz_hcrc H); reflexivity.
Qed.

Ltac gpx_red :=
  cbn [m_s m_h m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave m_adler m_msg m_tin m_tout m_snx m_sow
       set_m_s set_m_h set_m_nx set_m_hold set_m_bits upd_s upd_h set_mode initbits
       i_mode i_last i_wrap i_flags i_check i_total i_head i_wbits i_wsize i_length
       set_i_mode set_i_length set_i_check
       h_extra_len h_xbuf h_xp h_extra_max set_h_extra_len set_h_xbuf].

Lemma gp_exlen_ok : gp_exlen_stmt.
Proof.
  intros gh xfl O z hd h0 m OK (M & FL & CK & HH).
  unfold gp_fl, gp_ck, gp_hh, gp_F in *. unfold gp_st, gp_fl, gp_ck, gp_hh, gp_F.
  set (H := gp_H gh xfl) in *.
  destruct M as [Mi Mn Mh Mb Ml Mow Mo Ma Mr Mt Mm Mla Mtot Mw Mws Mwb Mhd].
  cbn [gp_p] in Mn.
  pose proof (gpx_bits H) as [B1024 B512].
  unfold c_EXLEN2. rewrite FL, B1024.
  destruct (gz_extra H) as [x|] eqn:EX.
  - (* FEXTRA: XLEN *)
    cbn [negb].
    destruct (gpx_lay _ _ _ OK) as [R EO]. fold H in EO. unfold gX in EO. rewrite EX in EO.
    pose proof (gpx_xlen _ _ _ x OK EX) as XL.
    pose proof OK as (_ & BO & _).
    set (v := Zlength x) in *.
    assert (V0: 0 <= v) by apply Zlength_nonneg.
    assert (LO: Zlength O = 12 + v + Zlength R) by (rewrite EO, !Zlength_app, gpx_gA, gpx_zlen_le; lia).
    assert (S12: sublist 10 12 O = le_bytes v 2).
    { rewrite EO. pose proof (gpx_gA H). pose proof (gpx_zlen_le v 2 ltac:(lia)). pose proof (Zlength_nonneg x).
      rewrite sublist_app2 by lia. rewrite H0. change (10 - 10) with 0. change (12 - 10) with 2.
      rewrite sublist_app1 by (rewrite ?Zlength_app; lia).
      rewrite sublist_app1 by lia. apply sublist_same; lia. }
    assert (Z10: Znth 10 O = v mod 256 /\ Znth 11 O = Z.shiftr v 8 mod 256).
    { rewrite gpx_le2 in S12. split.
      - replace (Znth 10 O) with (Znth 0 (sublist 10 12 O)) by (rewrite Znth_sublist; [f_equal|..]; lia).
        rewrite S12. reflexivity.
      - replace (Znth 11 O) with (Znth 1 (sublist 10 12 O)) by (rewrite Znth_sublist; [f_equal|..]; lia).
        rewrite S12. reflexivity. }
    destruct Z10 as [Z10 Z11].
    assert (HV: v mod 256 + 256 * (Z.shiftr v 8 mod 256) = v /\ u32 v = v).
    { pose proof (Zlength_nonneg x). rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
      unfold u32. rewrite (Z.mod_small (v / 256)) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
      rewrite (Z.mod_small v (2 ^ 32)) by lia. pose proof (Z.div_mod v 256 ltac:(lia)). lia. }
    destruct HV as [HV UV].
    pose proof (Zlength_nonneg R) as R0.
    rewrite (gpx_nb16 m) by (rewrite ?Mb, ?Mh, ?Mn, ?Mi; try change (10 + 1) with 11; rewrite ?Z10, ?Z11;
       first [lia | pose proof (Z.mod_pos_bound v 256); pose proof (Z.mod_pos_bound (Z.shiftr v 8) 256); lia]).
    rewrite Mi, Mn. change (10 + 1) with 11. change (10 + 2) with 12. rewrite Z10, Z11, HV.
    cbn [m_s m_h m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave m_adler m_msg m_tin m_tout m_snx m_sow
         set_m_s set_m_h set_m_nx set_m_hold set_m_bits upd_s upd_h i_head i_flags i_wrap set_i_length].
    rewrite Ml, UV, Mhd. change (0 =? 1) with false. cbv iota.
    eexists; split; [reflexivity|].
    pose proof (gpx_crc_if H) as CI.
    assert (HB: hbytes2 v = sublist 10 12 O) by (rewrite S12, gpx_le2; reflexivity).
    assert (CK12: ref_crc32 (ref_crc32 0 (sublist 0 10 O)) (sublist 10 12 O) = ref_crc32 0 (sublist 0 12 O)).
    { rewrite Combine.ref_crc32_app by (apply Bytes.is_bytes_sublist; exact BO).
      rewrite <- sublist_split by lia. reflexivity. }
    cbn [gp_p] in CK |- *. fold H. rewrite EX. change (10 + 2) with 12.
    destruct hd; rewrite CI by (gpx_red; assumption); destruct (gz_hcrc H) eqn:HC; gpx_red.
    all: split; [split; [constructor; gpx_red; first [assumption | reflexivity] |] |
                 intros x0 E0; injection E0 as <-; reflexivity].
    all: split; [assumption|].
    all: split; [intros T; try congruence; rewrite HB, (CK eq_refl), CK12; reflexivity|].
    all: intros T; try discriminate.
    all: destruct (HH eq_refl) as (g & x0 & nm & cm & G & HB0 & D0 & HM).
    all: exists g, x0, nm, cm; split; [exact G|]; split; [exact HB0|]; split; [exact D0|].
    all: destruct (gpx_hb _ _ _ _ _ _ _ _ OK G HB0) as [EX0 LX0]; fold H in EX0;
         rewrite EX in EX0; injection EX0 as <-.
    all: rewrite HM; unfold gh_at; cbn [Nat.leb]; rewrite <- LX0; reflexivity.
  - (* no FEXTRA: nothing read *)
    cbn [negb]. cbv iota.
    eexists; split; [reflexivity|].
    assert (HD: hd = false).
    { destruct hd; [|reflexivity]. destruct (HH eq_refl) as (g & x0 & nm & cm & G & HB0 & _).
      destruct (gpx_hb _ _ _ _ _ _ _ _ OK G HB0) as [EX0 _]. fold H in EX0. congruence. }
    rewrite HD in Mhd, HH |- *. rewrite Mhd. cbn [gp_p] in CK |- *. fold H. rewrite EX. change (10 + 0) with 10.
    split; [|intros x0 E0; discriminate].
    split; [constructor; unfold set_mode; gpx_red; first [assumption | reflexivity | congruence]|].
    unfold set_mode; gpx_red. split; [assumption|]. split; [exact CK|]. intros T; discriminate.
Qed.

Lemma gpx_xbuf_eta h : set_h_xbuf h (h_xbuf h) = h.
Proof. destruct h; reflexivity. Qed.

Lemma gp_extra_ok : gp_extra_stmt.
Proof.
  intros gh xfl O z hd h0 m OK (M & FL & CK & HH) LEN.
  unfold gp_fl, gp_ck, gp_hh, gp_F in *. unfold gp_st, gp_fl, gp_ck, gp_hh, gp_F.
  set (H := gp_H gh xfl) in *.
  destruct M as [Mi Mn Mh Mb Ml Mow Mo Ma Mr Mt Mm Mla Mtot Mw Mws Mwb Mhd].
  cbn [gp_p] in Mn, CK |- *. fold H in Mn, CK |- *.
  pose proof (gpx_bits H) as [B1024 B512].
  pose proof (gpx_crc_if H) as CI.
  unfold c_EXTRA2. cbv zeta. rewrite FL, B1024.
  destruct (gz_extra H) as [x|] eqn:EX.
  - (* FEXTRA: the field *)
    cbn [negb]. specialize (LEN x eq_refl).
    destruct (gpx_lay _ _ _ OK) as [R EO]. fold H in EO. unfold gX in EO |- *. rewrite EX in EO |- *.
    pose proof (gpx_xlen _ _ _ x OK EX) as XL.
    pose proof OK as (_ & BO & _).
    set (v := Zlength x) in *.
    assert (V0: 0 <= v) by apply Zlength_nonneg.
    pose proof (Zlength_nonneg R) as R0.
    assert (LO: Zlength O = 12 + v + Zlength R) by (rewrite EO, !Zlength_app, gpx_gA, gpx_zlen_le; lia).
    assert (SX: sublist 12 (12 + v) O = x).
    { rewrite EO. pose proof (gpx_gA H). pose proof (gpx_zlen_le v 2 ltac:(lia)).
      rewrite sublist_app2 by lia. rewrite H0. change (12 - 10) with 2. replace (12 + v - 10) with (2 + v) by lia.
      rewrite sublist_app1 by (rewrite ?Zlength_app; lia).
      rewrite sublist_app2 by lia. rewrite H1, Z.sub_diag. replace (2 + v - 2) with v by lia.
      apply sublist_same; lia. }
    assert (P5: Zlength (gA H ++ le_bytes v 2 ++ x) = 12 + v)
      by (rewrite !Zlength_app, gpx_gA, gpx_zlen_le; lia).
    rewrite P5.
    assert (CP: Z.min (i_length (m_s m)) (m_have m) = v) by (unfold m_have; rewrite LEN, Mi, Mn; lia).
    rewrite CP. change (10 + 2) with 12 in CK, Mn.
    destruct (Z.eqb_spec v 0) as [V|V].
    + (* an empty field: nothing copied *)
      rewrite V. cbn [negb Z.eqb]. cbv iota. rewrite LEN, V. cbn [negb Z.eqb]. cbv iota.
      eexists; split; [reflexivity|].
      unfold set_mode; gpx_red. rewrite Z.add_0_r.
      split; [|reflexivity].
      split; [constructor; gpx_red; first [assumption | reflexivity | congruence]|].
      split; [assumption|]. split; [exact CK|].
      intros T. destruct (HH T) as (g & x0 & nm & cm & G & HB0 & D0 & HM).
      exists g, x0, nm, cm; split; [exact G|]; split; [exact HB0|]; split; [exact D0|].
      destruct (gpx_hb _ _ _ _ _ _ _ _ OK G HB0) as [EX0 _]; fold H in EX0.
      rewrite EX in EX0; injection EX0 as <-.
      assert (X0: x = []) by (apply Zlength_nil_inv; exact V). rewrite X0 in HB0 |- *.
      pose proof HB0 as (_ & _ & _ & _ & _ & XB & _).
      apply Zlength_nil_inv in XB.
      rewrite HM. unfold gh_at; cbn [Nat.leb]. cbv iota.
      rewrite <- XB. symmetry.
      change (h_xbuf h0) with (h_xbuf (set_h_extra_len (set_h_os (set_h_xflags (set_h_time (set_h_text h0
        (DS.gz_text g)) (DS.gz_time g)) xfl) (DS.gz_os g)) (DS.gz_extra_len g))).
      apply gpx_xbuf_eta.
    + (* the whole field copied in one go *)
      assert (IB: forall m1, m_inp m1 = O -> m_nx m1 = 12 -> inbytes m1 v = x)
        by (intros m1 I1 N1; unfold inbytes; rewrite I1, N1; exact SX).
      set (h1 := if hd then set_h_xbuf (m_h m) x else m_h m).
      match goal with |- context [if ?c then upd_h m ?f else m] =>
        assert (E1: (if c then upd_h m f else m) = set_m_h m h1); [|rewrite E1; clear E1] end.
      { unfold h1. rewrite Mhd. destruct hd; cbn [andb].
        - destruct (HH eq_refl) as (g & x0 & nm & cm & G & HB0 & D0 & HM).
          destruct (gpx_hb _ _ _ _ _ _ _ _ OK G HB0) as [EX0 LX0]; fold H in EX0.
          rewrite EX in EX0; injection EX0 as <-.
          pose proof HB0 as (_ & _ & _ & XP & XM & XB & _).
          rewrite HM. unfold gh_at; cbn [Nat.leb]. cbv iota.
          cbn [h_xp h_extra_len h_extra_max h_xbuf set_h_extra_len set_h_os set_h_xflags set_h_time set_h_text].
          rewrite XP, XM, LEN, <- LX0. fold v. rewrite Z.sub_diag.
          change (u32 0) with 0. rewrite (proj2 (Z.ltb_lt 0 v)) by lia. cbn [andb].
          rewrite Z.add_0_l. unfold u32. rewrite (Z.mod_small v) by lia. rewrite Z.ltb_irrefl.
          rewrite IB by assumption. unfold upd_h. f_equal.
          rewrite HM. unfold gh_at; cbn [Nat.leb]. cbv iota. rewrite <- LX0. fold v.
          cbn [h_xbuf set_h_extra_len set_h_os set_h_xflags set_h_time set_h_text].
          unfold put_bytes. rewrite sublist_nil, Z.add_0_l. fold v. rewrite XB. fold v.
          rewrite sublist_nil, app_nil_r. reflexivity.
        - destruct m; reflexivity. }
      replace (negb (v =? 0)) with true by (symmetry; apply negb_true_iff, Z.eqb_neq; exact V). cbv iota.
      rewrite CI by (gpx_red; assumption).
      rewrite IB by (gpx_red; assumption).
      cbn [negb]. cbv iota.
      destruct (gz_hcrc H) eqn:HC; gpx_red; rewrite LEN, Z.sub_diag; cbn [negb Z.eqb]; cbv iota.
      all: eexists; split; [reflexivity|].
      all: unfold set_mode; gpx_red.
      all: split; [|reflexivity].
      all: split; [constructor; gpx_red; first [assumption | reflexivity | congruence | lia]|].
      all: split; [assumption|].
      all: split; [intros T; try congruence|].
      1: { rewrite (CK eq_refl), Combine.ref_crc32_app by (apply Bytes.is_bytes_sublist; exact BO).
           rewrite <- SX, <- sublist_split by lia. reflexivity. }
      all: intros T; destruct (HH T) as (g & x0 & nm & cm & G & HB0 & D0 & HM).
      all: exists g, x0, nm, cm; split; [exact G|]; split; [exact HB0|]; split; [exact D0|].
      all: destruct (gpx_hb _ _ _ _ _ _ _ _ OK G HB0) as [EX0 _]; fold H in EX0;
           rewrite EX in EX0; injection EX0 as <-.
      all: unfold h1; rewrite T, HM; unfold gh_at; cbn [Nat.leb]; reflexivity.
  - (* no FEXTRA *)
    cbn [negb]. cbv iota.
    eexists; split; [reflexivity|].
    assert (HD: hd = false).
    { destruct hd; [|reflexivity]. destruct (HH eq_refl) as (g & x0 & nm & cm & G & HB0 & _).
      destruct (gpx_hb _ _ _ _ _ _ _ _ OK G HB0) as [EX0 _]. fold H in EX0. congruence. }
    rewrite HD in Mhd, HH |- *.
    unfold gX. rewrite EX, app_nil_r, gpx_gA. rewrite Z.add_0_r in Mn, CK.
    unfold set_mode; gpx_red.
    split; [|reflexivity].
    split; [constructor; gpx_red; first [assumption | reflexivity | congruence]|].
    split; [assumption|]. split; [exact CK|]. intros T; discriminate.
Qed.

Lemma gp_ex_ok : gp_exlen_stmt /\ gp_extra_stmt.
Proof. exact (conj gp_exlen_ok gp_extra_ok). Qed.
