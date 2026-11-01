(* RT-H: case EXTRA's zmemcpy into head->extra on the partial header head_rep6 (the copied bytes
   extend the defined prefix of the extra buffer). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.roundtrip.RTHSpec.
Require Import Zlib.proof.roundtrip.RTHEx6Kit.
Require Import Zlib.proof.inflate.ExtraKit5.
Require Import Zlib.proof.inflate.MwfLemmas.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Module IM := Zlib.proof.inflate.Model.

(* the extra buffer after the copy of data at len *)
Lemma bufok6_put: forall lx max len xbuf data,
  bufok6 lx max len xbuf -> Zlength xbuf = max -> len + Zlength data <= max ->
  bufok6 (sublist 0 len lx ++ byte_vals data ++ sublist (len + Zlength data) max lx) max (len + Zlength data)
    (put_bytes xbuf len data).
Proof.
  intros lx max len xbuf data (L & C & S) LX D.
  pose proof (Zlength_nonneg data). pose proof (Zlength_byte_vals data).
  unfold put_bytes. split; [ | split].
  - list_solve.
  - lia.
  - rewrite !app_assoc. rewrite !sublist_app1 by list_solve. rewrite !sublist_same by list_solve. rewrite S.
    assert (Z1: Zlength (sublist 0 len xbuf ++ data) = len + Zlength data).
    { rewrite Zlength_app, Zlength_sublist by lia. lia. }
    rewrite sublist_app1 by lia.
    rewrite (sublist_same 0 (len + Zlength data) (sublist 0 len xbuf ++ data)) by lia.
    rewrite byte_vals_app. reflexivity.
Qed.

Lemma hbuf6_pos: forall b max l, b <> nullval -> hbuf6 b max l = data_at Ews (tarray tuchar max) l b.
Proof. intros b max l H. unfold hbuf6. rewrite if_false by exact H. reflexivity. Qed.

Lemma hph_extra: forall s, i_mode s = IM.EXTRA -> hph s = 4.
Proof. intros s H. unfold hph. rewrite H. reflexivity. Qed.

Lemma cx6_extra: forall s h, i_mode s = IM.EXTRA ->
  cx6 s h = if h_xp h then Z.min (h_extra_len h - i_length s) (h_extra_max h) else 0.
Proof. intros s h H. unfold cx6. rewrite H. reflexivity. Qed.

Lemma cn6_extra: forall s h, i_mode s = IM.EXTRA -> cn6 s h = 0.
Proof. intros s h H. unfold cn6. rewrite H. reflexivity. Qed.

Lemma cc6_extra: forall s h, i_mode s = IM.EXTRA -> cc6 s h = 0.
Proof. intros s h H. unfold cc6. rewrite H. reflexivity. Qed.

Lemma hinv6_extra_step: forall s h L' h',
  hinv6 s h -> i_mode s = IM.EXTRA -> (h_xp h' = true -> 0 <= L' <= h_extra_len h') ->
  h_done h' = h_done h -> h_xp h' = h_xp h -> hinv6 (set_i_length s L') h'.
Proof.
  intros s h L' h' (I1 & I2 & I3 & I4 & I5) HM HL HD HX.
  unfold hinv6, fextra in *. cbn [i_mode i_length i_flags set_i_length] in *. rewrite HM in *.
  split; [congruence | ]. split; [rewrite HX; auto | ]. split; [auto | ].
  unfold IM.EXTRA, IM.NAME, IM.COMMENT, RTHSpec.IM.NAME, RTHSpec.IM.COMMENT. split; intros E; discriminate E.
Qed.

Lemma semax_extra_mb6 {Espec: OracleKind} sp headp hsh xb nb cb s h L c ish ip ilo inn icont inp nx:
  writable_share hsh -> hwf h -> (h_xp h = true -> xb <> nullval) -> i_mode s = IM.EXTRA -> i_length s = L ->
  in_ok (InBuf ish ip ilo inn icont) inp -> 0 <= nx -> nx + c <= Zlength inp -> 0 < c <= Int.max_signed ->
  c <= L -> urange L ->
  semax Delta_cases5
   (PROP () LOCAL (temp _state sp; temp _copy (zv c); temp _next (offset_val (ilo + nx) ip))
    SEP (field_at Ews t_state (DOT _head) headp sp;
         field_at Ews t_state (DOT _length) (zv L) sp;
         head_rep6 hsh headp xb nb cb s h;
         data_at ish (tarray tuchar inn) icont ip;
         hd_tok true xb nb cb h))
   ex_mb
   (normal_ret_assert
    (PROP () LOCAL (temp _state sp; temp _copy (zv c); temp _next (offset_val (ilo + nx) ip))
     SEP (field_at Ews t_state (DOT _head) headp sp;
          field_at Ews t_state (DOT _length) (zv L) sp;
          head_rep6 hsh headp xb nb cb (set_i_length s (L - c)) (xb_upd true h L c inp nx);
          data_at ish (tarray tuchar inn) icont ip;
          hd_tok true xb nb cb h))).
Proof.
  intros HS HW HX HM HL HIN HNX HNC HC HCL HUL.
  unfold ex_mb.
  assert (HM': i_mode (set_i_length s (L - c)) = IM.EXTRA) by exact HM.
  unfold head_rep6, head_rep6p.
  rewrite (hph_extra s HM), (hph_extra _ HM'), (cx6_extra s h HM), (cn6_extra s h HM), (cc6_extra s h HM).
  rewrite (cx6_extra _ _ HM'), (cn6_extra _ _ HM'), (cc6_extra _ _ HM').
  Intros vt vtm vxf vos vxl vhc lx ln lc.
  rename H into HI. rename H0 into P1, H1 into P2, H2 into P3, H3 into P4, H4 into P5, H5 into P6, H6 into P7,
    H7 into P8.
  destruct (h_xp h) eqn:Hxp.
  2:{ unfold xb_upd. rewrite Hxp. cbn [andb]. unfold hd_tok.
      abbreviate_semax. Intros. forward.
      match goal with |- semax _ (PROPx ?A (LOCALx (_ :: ?Q) (SEPx ?R))) _ _ =>
        forward_if (PROPx A (LOCALx (temp _t'26 (Vint Int.zero) :: Q) (SEPx R))) end.
      { forward. forward. forward. entailer!. }
      { assert_PROP (isptr headp) by entailer!. subst. contradiction. }
      match goal with |- semax _ (PROPx ?A (LOCALx (_ :: ?Q) (SEPx ?R))) _ _ =>
        forward_if (PROPx A (LOCALx (temp _t'27 (Vint Int.zero) :: Q) (SEPx R))) end.
      { exfalso. auto. }
      { forward. entailer!. }
      forward_if.
      { exfalso. auto. }
      forward. Exists vt vtm vxf vos vxl vhc lx ln lc. rewrite Hxp.
      entailer!.
      apply (hinv6_extra_step s h); auto. rewrite Hxp. discriminate. }
  pose proof HI as HI'. unfold hinv6 in HI'. destruct HI' as (I1 & I2 & I3 & I4 & I5).
  assert (FX: fextra s = true) by (apply I2; [rewrite HM; reflexivity | exact Hxp]).
  assert (LL: 0 <= L <= h_extra_len h) by (subst L; apply I3; auto).
  assert (VXL: vxl = zv (h_extra_len h)) by (apply P4; [lia | exact FX]).
  subst vxl.
  assert (XB: xb <> nullval) by auto.
  rewrite !(hbuf6_pos xb) by exact XB.
  assert (XBT: btok xb (h_extra_max h) = if zeq (h_extra_max h) 0 then malloc_token Ews (tarray tuchar 0) xb else emp).
  { unfold btok. rewrite if_false by exact XB. reflexivity. }
  unfold hd_tok. rewrite !XBT. clear XBT.
  pose proof (hw_extra_len _ HW) as UXL. pose proof (hw_extra_max _ HW) as XM.
  pose proof (hw_xbuf _ HW) as [XL XOK].
  set (lv0 := h_extra_len h - L) in *.
  assert (U0: u32 lv0 = lv0) by (unfold u32; apply Z.mod_small; unfold urange in UXL; rep_lia).
  assert (XU: xb_upd true h L c inp nx =
              if lv0 <? h_extra_max h then
                set_h_xbuf h (put_bytes (h_xbuf h) lv0
                  (sublist nx (nx + extra_n lv0 c (h_extra_max h)) inp))
              else h) by (unfold xb_upd; rewrite Hxp; fold lv0; rewrite U0; reflexivity).
  rewrite XU. clear XU.
  abbreviate_semax. Intros. forward.
  match goal with |- semax _ (PROPx ?A (LOCALx (_ :: ?Q) (SEPx ?R))) _ _ =>
        forward_if (PROPx A (LOCALx (temp _t'26 (Vint Int.one) :: Q) (SEPx R))) end.
  { forward. forward. forward.
    { entailer!. eapply derives_trans; [ | apply (xb_weak_valid xb (h_extra_max h) lx TT)];
        [cancel | auto | lia]. }
    entailer!. apply xb_cmp_one. auto. }
  { assert_PROP (isptr headp) by entailer!. subst. contradiction. }
  match goal with |- semax _ (PROPx ?A (LOCALx (_ :: ?Q) (SEPx ?R))) _ _ =>
        forward_if (PROPx A (LOCALx (temp _t'27 (Vint (Int.repr (if lv0 <? h_extra_max h then 1 else 0))) ::
                                     temp _len (Vint (Int.repr lv0)) :: Q) (SEPx R))) end.
  { forward. forward. forward. forward. forward. forward. forward. forward.
    entailer!. symmetry. rewrite ex_ltu_u32 by rep_lia. rewrite U0. reflexivity. }
  { exfalso. apply Int.one_not_zero. assumption. }
  unfold abbreviate in POSTCONDITION. subst POSTCONDITION.
  destruct (lv0 <? h_extra_max h) eqn:Hlt.
  - apply Z.ltb_lt in Hlt.
    pose proof (extra_n_range lv0 c (h_extra_max h) ltac:(lia) ltac:(lia) ltac:(rep_lia)) as [N1 N2].
    assert (Ulc: u32 (lv0 + c) = lv0 + c) by (unfold u32; apply Z.mod_small; unfold urange in UXL; rep_lia).
    assert (NE1: h_extra_max h < lv0 + c -> extra_n lv0 c (h_extra_max h) = h_extra_max h - lv0).
    { intros E. unfold extra_n. rewrite Ulc, (proj2 (Z.ltb_lt _ _) E). reflexivity. }
    assert (NE2: lv0 + c <= h_extra_max h -> extra_n lv0 c (h_extra_max h) = c).
    { intros E. unfold extra_n. rewrite Ulc, (proj2 (Z.ltb_ge _ _) E). reflexivity. }
    set (n := extra_n lv0 c (h_extra_max h)) in *.
    abbreviate_semax.
    forward_if.
    2:{ exfalso. apply Int.one_not_zero. assumption. }
    forward. forward.
    destruct (zeq (h_extra_max h) 0); [lia | ].
    match goal with |- semax _ (PROPx ?A (LOCALx (_ :: _ :: ?Q) (SEPx ?R))) _ _ =>
        forward_if (PROPx A (LOCALx (temp _t'25 (Vint (Int.repr n)) :: Q) (SEPx R))) end.
    { forward. forward. forward. rewrite (NE1 H0). entailer!. }
    { forward. rewrite (NE2 ltac:(lia)). entailer!. }
    forward. forward.
    pose proof HIN as HIN'.
    destruct HIN' as (HIS & HIP & HILO & HINN & HIC & HIMAX & HISUB & HIB).
    assert_PROP (field_compatible (tarray tuchar inn) [] ip) as FCI by entailer!.
    assert_PROP (field_compatible (tarray tuchar (h_extra_max h)) [] xb) as FCX by entailer!.
    assert (MN: Z.min (h_extra_len h - (L - c)) (h_extra_max h) = lv0 + n).
    { destruct (Z_lt_le_dec (h_extra_max h) (lv0 + c)) as [E | E];
        [rewrite (NE1 E) | rewrite (NE2 E)]; unfold lv0 in *; lia. }
    assert (M0: Z.min (h_extra_len h - L) (h_extra_max h) = lv0) by (unfold lv0 in *; lia).
    remember (sublist nx (nx + n) inp) as data eqn:Hd.
    assert (HZ: Zlength data = n) by (subst data; rewrite Zlength_sublist by lia; lia).
    rewrite (ex_in_slice ish ip ilo inn icont inp nx n) by (auto; lia).
    assert (LXL: Zlength lx = h_extra_max h) by apply P6.
    rewrite (ex_arr_slice Ews xb (h_extra_max h) lx lv0 n) by (auto; lia).
    rewrite <- Hd. clearbody n. rewrite <- HZ in *.
    sep_apply (data_at_data_at_ Ews (tarray tuchar (Zlength data)) (sublist lv0 (lv0 + Zlength data) lx) (offset_val lv0 xb)).
    forward_call (Ews, offset_val lv0 xb, ish, offset_val (ilo + nx) ip, data).
    { rewrite Hd. unfold bytes_ok in *. apply Forall_sublist. exact HIB. }
    rewrite (ex_in_slice ish ip ilo inn icont inp nx (Zlength data)) by (auto; lia).
    rewrite <- Hd.
    cbn [set_h_xbuf h_text h_time h_xflags h_os h_xp h_extra_len h_extra_max h_np h_name_max h_cp h_comm_max
         h_hcrc h_done h_xbuf h_nbuf h_cbuf].
    change (i_length (set_i_length s (L - c))) with (L - c).
    rewrite Hxp, MN.
    Exists vt vtm vxf vos (zv (h_extra_len h)) vhc
      (sublist 0 lv0 lx ++ byte_vals data ++ sublist (lv0 + Zlength data) (h_extra_max h) lx) ln lc.
    rewrite (hbuf6_pos xb) by exact XB.
    rewrite (ex_arr_slice Ews xb (h_extra_max h) (sublist 0 lv0 lx ++ byte_vals data ++ sublist (lv0 + Zlength data) (h_extra_max h) lx) lv0 (Zlength data))
      by (auto; try lia; pose proof (Zlength_byte_vals data); list_solve).
    pose proof (Zlength_byte_vals data) as ZB.
    assert (LA: Zlength (sublist 0 lv0 lx) = lv0) by (rewrite Zlength_sublist by lia; lia).
    assert (SA: sublist 0 lv0 (sublist 0 lv0 lx ++ byte_vals data ++ sublist (lv0 + Zlength data) (h_extra_max h) lx)
                = sublist 0 lv0 lx) by list_solve.
    assert (SB: sublist lv0 (lv0 + Zlength data)
                  (sublist 0 lv0 lx ++ byte_vals data ++ sublist (lv0 + Zlength data) (h_extra_max h) lx)
                = byte_vals data) by list_solve.
    assert (SC: sublist (lv0 + Zlength data) (h_extra_max h)
                  (sublist 0 lv0 lx ++ byte_vals data ++ sublist (lv0 + Zlength data) (h_extra_max h) lx)
                = sublist (lv0 + Zlength data) (h_extra_max h) lx) by list_solve.
    rewrite SA, SB, SC.
    assert (HI': hinv6 (set_i_length s (L - c)) (set_h_xbuf h (put_bytes (h_xbuf h) lv0 data))).
    { apply (hinv6_extra_step s h); auto. intros _. cbn. lia. }
    rewrite HL, M0 in P6.
    pose proof (bufok6_put lx (h_extra_max h) lv0 (h_xbuf h) data P6 XL N2) as BP.
    entailer!.
  - apply Z.ltb_ge in Hlt.
    abbreviate_semax. forward_if.
    { exfalso. auto. }
    forward.
    assert (MX: Z.min (h_extra_len h - (L - c)) (h_extra_max h) = Z.min (h_extra_len h - i_length s) (h_extra_max h))
      by (unfold lv0 in *; lia).
    assert (HI': hinv6 (set_i_length s (L - c)) h).
    { apply (hinv6_extra_step s h); auto. intros _. lia. }
    Exists vt vtm vxf vos (zv (h_extra_len h)) vhc lx ln lc.
    change (i_length (set_i_length s (L - c))) with (L - c).
    rewrite Hxp, MX, (hbuf6_pos xb) by exact XB.
    entailer!.
Unshelve. all: exact 0.
Qed.
