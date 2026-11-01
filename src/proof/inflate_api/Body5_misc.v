(* Bodies of inflate.c's API functions, version 5: api_misc_stmt (Bodies5.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.Misc5Kit.
#[local] Existing Instance Zlib.units.Inflate.CS.

Local Open Scope logic.

Lemma body_inflateSyncPoint {E: OracleKind}:
  semax_body Vprog_inflate Gp_check f_inflateSyncPoint inflateSyncPoint_spec.
Proof.
  start_function.
  unfold istream_opt.
  destruct (eq_dec strmp nullval) as [Hn | Hn].
  - subst strmp.
    forward_call (nullval, shs, default_val t_strm, nullval, 0, false, gv).
    { simpl. cancel. }
    forward_if; [forward | discriminate].
  - destruct st as [L | ].
    2: { unfold istream, zstrm_at, strm_rep. Intros.
    remember (gv _zcalloc) as zca eqn:Hzca. remember (gv _zcfree) as zcf eqn:Hzcf.
    forward_call (strmp, shs, (zf_ni z, (Vint (Int.repr (zf_ai z)), (lv (zf_tin z), (zf_no z,
      (Vint (Int.repr (zf_ao z)), (lv (zf_tout z), (msg_val gv (zf_msg z), (nullval, (zca, (zcf,
      (nullval, (zv (zf_dt z), (lv (zf_adler z), zf_res z))))))))))))), nullval, 0, false, gv).
    { destruct (eq_dec strmp nullval); [contradiction | ]. cancel. }
    { right. split; [auto | ]. subst zca zcf. repeat split. }
    destruct (eq_dec strmp nullval); [contradiction | ].
    forward_if.
    { forward. unfold is_live, istream_opt. rewrite !if_false by auto. unfold istream, zstrm_at, strm_rep. entailer!. }
    { match goal with H: Int.repr 1 = Int.zero |- _ => inversion H end. } }
    destruct L as [sp winp s h headp hsh xb nb cb].
    unfold istream, state_mem, zstrm_at, strm_rep. cbn [l_sp l_winp l_s l_h l_headp]. rewrite state_rep_misc. Intros.
    match goal with H: live_ok _ |- _ => pose proof H as LOK; destruct H as (Hsp & SW & MW & HW & SW3 & HS & WW) end.
    cbn [l_sp l_s l_h] in Hsp, SW, MW, HW, SW3, HS, WW.
    remember (gv _zcalloc) as zca eqn:Hzca. remember (gv _zcfree) as zcf eqn:Hzcf.
    forward_call (strmp, shs, (zf_ni z, (Vint (Int.repr (zf_ai z)), (lv (zf_tin z), (zf_no z,
      (Vint (Int.repr (zf_ao z)), (lv (zf_tout z), (msg_val gv (zf_msg z), (sp, (zca, (zcf,
      (nullval, (zv (zf_dt z), (lv (zf_adler z), zf_res z))))))))))))), sp, i_mode s, true, gv).
    { destruct (eq_dec strmp nullval); [contradiction | ]. cancel. }
    { pose proof (sw_mode _ SW). split; [ | unfold HEAD, SYNC in *; rep_lia].
      right. split; [auto | ]. subst zca zcf. repeat split. }
    destruct (eq_dec strmp nullval) as [Hx | Hx]; [contradiction | ].
    pose proof (sw_mode _ SW) as HMD.
    rewrite (proj2 (Z.leb_le _ _) (proj1 HMD)), (proj2 (Z.leb_le _ _) (proj2 HMD)). simpl andb. cbv iota.
    forward_if; [contradiction | ]. Intros.
    forward. (* state *)
    forward. (* t'3 = mode *) forward.
    pose proof (sw_bits _ SW) as HB.
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp _t'2 (Vint (Int.repr (syncpoint_val s))) :: Q) (SEPx R))) end.
    { forward. forward. entailer!. unfold syncpoint_val.
      assert (EM: i_mode s = STORED).
      { match goal with H: Int.repr (i_mode s) = Int.repr _ |- _ =>
          apply (f_equal Int.unsigned) in H; rewrite !Int.unsigned_repr in H by (unfold HEAD, SYNC in *; rep_lia) end.
        unfold STORED; lia. }
      rewrite EM, Z.eqb_refl. simpl andb.
      destruct (zeq (i_bits s) 0) as [E0 | E0].
      - rewrite E0. reflexivity.
      - rewrite (proj2 (Z.eqb_neq _ _) E0). reflexivity. }
    { forward. entailer!. unfold syncpoint_val.
      destruct (Z.eqb_spec (i_mode s) STORED) as [E0 | E0]; [ | reflexivity].
      exfalso. match goal with H: Int.repr (i_mode s) <> _ |- _ => apply H end. rewrite E0. reflexivity. }
    forward.
    unfold istream_opt, is_live. rewrite !if_false by auto.
    unfold istream, state_mem, zstrm_at, strm_rep. cbn [l_sp l_winp l_s l_h l_headp]. rewrite state_rep_misc.
    entailer!.
Qed.

(* the new wrap keeps wrap & 3 *)
Lemma live_validate: forall check L, live_ok L -> live_ok (set_l_s L (validate_s check (l_s L))).
Proof.
  intros check L H. pose proof (sw_wrap _ (proj1 (proj2 H))) as HW.
  pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))) as H7.
  assert (A: forall w, (0 <= w <= 7 \/ 9 <= w <= 11 \/ 13 <= w <= 15) ->
    Z.land (Z.lor w 4) 3 = Z.land w 3 /\
    (Z.land w (Z.lnot 4) <> 0 -> w <> 0) /\ Z.land (Z.land w (Z.lnot 4)) 3 = Z.land w 3).
  { intros w Hw. wrap_cases Hw; cbn; lia. }
  destruct (A _ HW) as (A0 & A3 & A4).
  pose proof (wrap_clear4 _ HW) as A2.
  unfold validate_s. destruct (andb (negb (check =? 0)) (negb (i_wrap (l_s L) =? 0))) eqn:EB.
  - assert (NZ: i_wrap (l_s L) <> 0).
    { apply andb_prop in EB. destruct EB as [_ EB]. apply negb_true_iff in EB. apply Z.eqb_neq in EB. exact EB. }
    apply live_wrap; auto; first [exact (wrap_set4 _ HW NZ) | intro Z0; rewrite A0; apply (proj1 (H7 Z0))].
  - apply live_wrap; auto; first [exact A2 | intro Z0; rewrite A4; apply (proj1 (H7 Z0))].
Qed.

Lemma body_inflateValidate {E: OracleKind}:
  semax_body Vprog_inflate Gp_check f_inflateValidate inflateValidate_spec.
Proof.
  start_function.
  unfold istream_opt.
  destruct (eq_dec strmp nullval) as [Hn | Hn].
  - subst strmp.
    forward_call (nullval, shs, default_val t_strm, nullval, 0, false, gv).
    { simpl. cancel. }
    forward_if; [forward | discriminate].
  - destruct st as [L | ].
    2: { unfold istream, zstrm_at, strm_rep. Intros.
    remember (gv _zcalloc) as zca eqn:Hzca. remember (gv _zcfree) as zcf eqn:Hzcf.
    forward_call (strmp, shs, (zf_ni z, (Vint (Int.repr (zf_ai z)), (lv (zf_tin z), (zf_no z,
      (Vint (Int.repr (zf_ao z)), (lv (zf_tout z), (msg_val gv (zf_msg z), (nullval, (zca, (zcf,
      (nullval, (zv (zf_dt z), (lv (zf_adler z), zf_res z))))))))))))), nullval, 0, false, gv).
    { destruct (eq_dec strmp nullval); [contradiction | ]. cancel. }
    { right. split; [auto | ]. subst zca zcf. repeat split. }
    destruct (eq_dec strmp nullval); [contradiction | ].
    forward_if.
    { forward. unfold on_live, fst3, snd3, thd3, is_live, istream_opt. rewrite !if_false by auto. cbn [fst snd]. unfold istream, zstrm_at, strm_rep. entailer!. }
    { match goal with H: Int.repr 1 = Int.zero |- _ => inversion H end. } }
    destruct L as [sp winp s h headp hsh xb nb cb].
    unfold istream, state_mem, zstrm_at, strm_rep. cbn [l_sp l_winp l_s l_h l_headp]. rewrite state_rep_misc. Intros.
    match goal with H: live_ok _ |- _ => pose proof H as LOK; destruct H as (Hsp & SW & MW & HW & SW3 & HS & WW) end.
    cbn [l_sp l_s l_h] in Hsp, SW, MW, HW, SW3, HS, WW.
    remember (gv _zcalloc) as zca eqn:Hzca. remember (gv _zcfree) as zcf eqn:Hzcf.
    forward_call (strmp, shs, (zf_ni z, (Vint (Int.repr (zf_ai z)), (lv (zf_tin z), (zf_no z,
      (Vint (Int.repr (zf_ao z)), (lv (zf_tout z), (msg_val gv (zf_msg z), (sp, (zca, (zcf,
      (nullval, (zv (zf_dt z), (lv (zf_adler z), zf_res z))))))))))))), sp, i_mode s, true, gv).
    { destruct (eq_dec strmp nullval); [contradiction | ]. cancel. }
    { pose proof (sw_mode _ SW). split; [ | unfold HEAD, SYNC in *; rep_lia].
      right. split; [auto | ]. subst zca zcf. repeat split. }
    destruct (eq_dec strmp nullval) as [Hx | Hx]; [contradiction | ].
    pose proof (sw_mode _ SW) as HMD.
    rewrite (proj2 (Z.leb_le _ _) (proj1 HMD)), (proj2 (Z.leb_le _ _) (proj2 HMD)). simpl andb. cbv iota.
    forward_if; [contradiction | ]. Intros.
    forward. forward.
    pose proof (sw_wrap_range _ SW) as HWR.
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp _t'2 (Vint (Int.repr (if andb (negb (check =? 0)) (negb (i_wrap s =? 0)) then 1 else 0))) :: Q) (SEPx R))) end.
    { forward. forward. entailer!.
      rewrite (proj2 (Z.eqb_neq check 0) H3'). simpl negb.
      destruct (Z.eqb_spec (i_wrap s) 0) as [E0|E0]; [rewrite E0; reflexivity | rewrite Int.eq_false; [reflexivity | intro X; apply E0; apply (f_equal Int.unsigned) in X; rewrite Int.unsigned_repr in X by rep_lia; exact X]]. }
    { assert (check = 0) as C0 by (match goal with H: Int.repr check = Int.zero |- _ => apply (f_equal Int.signed) in H; rewrite Int.signed_repr in H by rep_lia; exact H end).
      subst check. forward. entailer!. }
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx Q (SEPx (replace_nth 5 R (field_at Ews t_state (DOT _wrap) (Vint (Int.repr (i_wrap (validate_s check s)))) sp))))) end.
    { forward. forward. cbn [replace_nth]. unfold validate_s.
      match goal with H: Int.repr (if ?b then 1 else 0) <> Int.zero |- _ =>
        destruct b; [ | exfalso; apply H; reflexivity] end.
      cbn [i_wrap set_i_wrap]. entailer!; apply derives_refl. }
    { forward. forward. cbn [replace_nth]. unfold validate_s.
      match goal with H: Int.repr (if ?b then 1 else 0) = Int.zero |- _ =>
        destruct b; [discriminate | ] end.
      cbn [i_wrap set_i_wrap].
      assert (EA: Int.and (Int.repr (i_wrap s)) (Int.not (Int.repr 4)) = Int.repr (Z.land (i_wrap s) (Z.lnot 4))).
      { destruct HWR as [Wl Wh]. remember (i_wrap s) as w. clear - Wl Wh.
        assert (w = 0 \/ w = 1 \/ w = 2 \/ w = 3 \/ w = 4 \/ w = 5 \/ w = 6 \/ w = 7 \/ w = 8 \/ w = 9 \/
                w = 10 \/ w = 11 \/ w = 12 \/ w = 13 \/ w = 14 \/ w = 15) as C by lia.
        destruct C as [C | [C | [C | [C | [C | [C | [C | [C | [C | [C | [C | [C | [C | [C | [C | C]]]]]]]]]]]]]]]; subst; reflexivity. }
      rewrite EA. entailer!; apply derives_refl. }
    forward.
    cbn [replace_nth].
    pose proof (live_validate check _ LOK) as LOK'.
    unfold on_live, fst3, snd3, thd3, is_live, istream_opt. rewrite !if_false by auto.
    unfold validate_f. cbn [fst snd].
    unfold istream, state_mem, zstrm_at, strm_rep. cbn [set_l_s l_sp l_winp l_s l_h l_headp] in LOK' |- *.
    rewrite state_rep_misc.
    unfold validate_s in LOK' |- *. destruct (andb (negb (check =? 0)) (negb (i_wrap s =? 0))) eqn:EB;
    match goal with |- context [U_misc ?g ?a ?b (set_i_wrap ?s0 ?w)] =>
      change (U_misc g a b (set_i_wrap s0 w)) with (U_misc g a b s0) end;
    match goal with |- context [win_rep ?a (set_i_wrap ?s0 ?w)] =>
      change (win_rep a (set_i_wrap s0 w)) with (win_rep a s0) end;
    cbn [i_mode i_wrap i_head i_hold i_bits i_length i_next i_codes i_back i_was set_i_wrap];
    entailer!.
    all: unfold fold_right_sepcon; cancel.
Qed.

Lemma wrap_and2: forall w, 0 <= w <= 15 ->
  Int.and (Int.repr w) (Int.repr 2) = Int.repr (Z.land w 2) /\ 0 <= Z.land w 2 <= 2.
Proof.
  intros w Hw. assert (C: w = 0 \/ w = 1 \/ w = 2 \/ w = 3 \/ w = 4 \/ w = 5 \/ w = 6 \/ w = 7 \/ w = 8 \/ w = 9 \/
            w = 10 \/ w = 11 \/ w = 12 \/ w = 13 \/ w = 14 \/ w = 15) by lia.
  destruct C as [C | [C | [C | [C | [C | [C | [C | [C | [C | [C | [C | [C | [C | [C | [C | C]]]]]]]]]]]]]]]; subst w; split; try reflexivity; cbn; lia.
Qed.

Lemma body_inflateGetHeader {E: OracleKind}:
  semax_body Vprog_inflate Gp_check f_inflateGetHeader inflateGetHeader_spec.
Proof.
  start_function.
  rename SH into HSH, H into HWF.
  unfold istream_opt.
  destruct (eq_dec strmp nullval) as [Hn | Hn].
  - subst strmp.
    forward_call (nullval, shs, default_val t_strm, nullval, 0, false, gv).
    { simpl. cancel. }
    forward_if; [forward; unfold is_live; rewrite if_true by auto; cancel | discriminate].
  - destruct st as [L | ].
    2: { unfold istream, zstrm_at, strm_rep. Intros.
    remember (gv _zcalloc) as zca eqn:Hzca. remember (gv _zcfree) as zcf eqn:Hzcf.
    forward_call (strmp, shs, (zf_ni z, (Vint (Int.repr (zf_ai z)), (lv (zf_tin z), (zf_no z,
      (Vint (Int.repr (zf_ao z)), (lv (zf_tout z), (msg_val gv (zf_msg z), (nullval, (zca, (zcf,
      (nullval, (zv (zf_dt z), (lv (zf_adler z), zf_res z))))))))))))), nullval, 0, false, gv).
    { destruct (eq_dec strmp nullval); [contradiction | ]. cancel. }
    { right. split; [auto | ]. subst zca zcf. repeat split. }
    destruct (eq_dec strmp nullval); [contradiction | ].
    forward_if.
    { forward. unfold is_live, istream_opt. rewrite !if_false by auto. unfold istream, zstrm_at, strm_rep. entailer!. }
    { match goal with H: Int.repr 1 = Int.zero |- _ => inversion H end. } }
    destruct L as [sp winp s h0 headp0 hsh0 xb0 nb0 cb0].
    unfold istream, state_mem, zstrm_at, strm_rep. cbn [l_sp l_winp l_s l_h l_headp]. rewrite state_rep_misc. Intros.
    match goal with H: live_ok _ |- _ => pose proof H as LOK; destruct H as (Hsp & SW & MW & HW & SW3 & HS & WW) end.
    cbn [l_sp l_s l_h] in Hsp, SW, MW, HW, SW3, HS, WW.
    remember (gv _zcalloc) as zca eqn:Hzca. remember (gv _zcfree) as zcf eqn:Hzcf.
    forward_call (strmp, shs, (zf_ni z, (Vint (Int.repr (zf_ai z)), (lv (zf_tin z), (zf_no z,
      (Vint (Int.repr (zf_ao z)), (lv (zf_tout z), (msg_val gv (zf_msg z), (sp, (zca, (zcf,
      (nullval, (zv (zf_dt z), (lv (zf_adler z), zf_res z))))))))))))), sp, i_mode s, true, gv).
    { destruct (eq_dec strmp nullval); [contradiction | ]. cancel. }
    { pose proof (sw_mode _ SW). split; [ | unfold HEAD, SYNC in *; rep_lia].
      right. split; [auto | ]. subst zca zcf. repeat split. }
    destruct (eq_dec strmp nullval) as [Hx | Hx]; [contradiction | ].
    pose proof (sw_mode _ SW) as HMD.
    rewrite (proj2 (Z.leb_le _ _) (proj1 HMD)), (proj2 (Z.leb_le _ _) (proj2 HMD)). simpl andb. cbv iota.
    forward_if; [contradiction | ]. Intros.
    forward. forward. forward. (* t'2 = wrap *)
    pose proof (sw_wrap_range _ SW) as HWR. destruct (wrap_and2 _ HWR) as [A2 R2].
    forward_if.
    { forward.
      assert (E2: Z.land (i_wrap s) 2 = 0).
      { match goal with H: Int.and _ _ = Int.repr 0 |- _ => rewrite A2 in H; apply repr_inj_unsigned in H; rep_lia end. }
      unfold is_live, istream_opt. rewrite !if_false by auto. cbn [l_s]. rewrite E2. cbn [Z.eqb].
      unfold istream, state_mem, zstrm_at, strm_rep. cbn [l_sp l_winp l_s l_h l_headp]. rewrite state_rep_misc.
      entailer!. }
    assert (E2: Z.land (i_wrap s) 2 <> 0).
    { intro X. match goal with H: Int.and _ _ <> Int.repr 0 |- _ => apply H; rewrite A2, X; reflexivity end. }
    unfold head_rep. Intros.
    forward. (* state->head = head *)
    forward. (* head->done = 0 *)
    forward.
    pose proof (live_head _ h headp hsh xb nb cb LOK HWF HSH ltac:(assumption) ltac:(assumption) ltac:(assumption)) as LOK'.
    unfold is_live, istream_opt. rewrite !if_false by auto. cbn [l_s]. rewrite (proj2 (Z.eqb_neq _ _) E2).
    unfold istream, state_mem, zstrm_at, strm_rep, head_mem.
    cbn [set_l_head set_l_s l_sp l_winp l_s l_h l_headp l_hsh l_xb l_nb l_cb] in LOK' |- *.
    rewrite state_rep_misc.
    match goal with |- context [U_misc ?g ?a ?b (set_i_head ?s0 ?w)] =>
      change (U_misc g a b (set_i_head s0 w)) with (U_misc g a b s0) end;
    match goal with |- context [win_rep ?a (set_i_head ?s0 ?w)] =>
      change (win_rep a (set_i_head s0 w)) with (win_rep a s0) end.
    unfold head_rep, hdr_btoks.
    cbn [i_mode i_wrap i_head i_hold i_bits i_length i_next i_codes i_back i_was set_i_head
         h_text h_time h_xflags h_os h_xp h_extra_len h_extra_max h_xbuf h_np h_name_max h_nbuf h_cp h_comm_max
         h_cbuf h_hcrc h_done set_h_done].
    entailer!.
Qed.

(* inflatePrime's arithmetic: 1L << bits, value & ((1L << bits) - 1) *)
Lemma shl1_64: forall b, 0 <= b <= 16 -> Int64.shl (Int64.repr 1) (Int64.repr b) = Int64.repr (2 ^ b).
Proof.
  intros b Hb. unfold Int64.shl. rewrite !Int64.unsigned_repr by rep_lia.
  rewrite Z.shiftl_1_l. reflexivity.
Qed.

Lemma pow_b16: forall b, 0 <= b <= 16 -> 0 < 2 ^ b <= 2 ^ 16.
Proof.
  intros b Hb. split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_le_mono_r; lia].
Qed.

Lemma prime_mask: forall value b, 0 < b <= 16 ->
  Int64.unsigned (Int64.and (Int64.repr value) (Int64.sub (Int64.repr (2 ^ b)) (Int64.repr 1))) =
  Z.land value (2 ^ b - 1) /\ 0 <= Z.land value (2 ^ b - 1) < 2 ^ b.
Proof.
  intros value b Hb. pose proof (pow_b16 b ltac:(lia)) as P.
  assert (P16: 2 ^ 16 = 65536) by reflexivity.
  unfold Int64.sub. rewrite (Int64.unsigned_repr (2 ^ b)) by rep_lia. rewrite (Int64.unsigned_repr 1) by rep_lia.
  unfold Int64.and. rewrite (Int64.unsigned_repr (2 ^ b - 1)) by rep_lia.
  replace (2 ^ b - 1) with (Z.ones b) by (rewrite Z.ones_equiv; lia).
  rewrite !Z.land_ones by lia.
  assert (D: (2 ^ b | Int64.modulus)).
  { exists (2 ^ (64 - b)). rewrite <- Z.pow_add_r by lia. replace (64 - b + b) with 64 by lia. reflexivity. }
  rewrite !Int64.unsigned_repr_eq.
  rewrite <- (Znumtheory.Zmod_div_mod (2 ^ b) Int64.modulus value) by (auto; try lia; reflexivity).
  pose proof (Z.mod_pos_bound value (2 ^ b) ltac:(lia)).
  rewrite (Z.mod_small _ Int64.modulus) by (change Int64.modulus with 18446744073709551616; lia). split; [reflexivity | lia].
Qed.

Lemma prime_hold: forall hold v ib, lrange hold -> 0 <= v < 2 ^ 16 -> 0 <= ib <= 31 ->
  Int64.add (Int64.repr hold) (Int64.shl (Int64.repr (Int.signed (Int.repr v))) (Int64.repr (Int.unsigned (Int.repr ib)))) =
  Int64.repr (u64 (hold + v * 2 ^ ib)).
Proof.
  intros hold v ib Hh Hv Hib. unfold lrange in Hh.
  assert (P: 0 < 2 ^ ib <= 2 ^ 31) by (split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_le_mono_r; lia]).
  assert (P16: 2 ^ 16 = 65536) by reflexivity. assert (P31: 2 ^ 31 = 2147483648) by reflexivity.
  rewrite Int.signed_repr, Int.unsigned_repr by rep_lia.
  unfold Int64.shl. rewrite !(Int64.unsigned_repr v), (Int64.unsigned_repr ib) by rep_lia.
  rewrite Z.shiftl_mul_pow2 by lia.
  unfold Int64.add. rewrite (Int64.unsigned_repr hold) by rep_lia.
  rewrite (Int64.unsigned_repr (v * 2 ^ ib)) by (split; [nia | ]; assert (v * 2 ^ ib <= 2 ^ 16 * 2 ^ 31) by nia; rep_lia).
  unfold u64. change (2 ^ 64) with Int64.modulus. rewrite <- Int64.unsigned_repr_eq, Int64.repr_unsigned. reflexivity.
Qed.

Lemma body_inflatePrime {E: OracleKind}:
  semax_body Vprog_inflate Gp_check f_inflatePrime inflatePrime_spec.
Proof.
  start_function.
  unfold istream_opt.
  destruct (eq_dec strmp nullval) as [Hn | Hn].
  - subst strmp.
    forward_call (nullval, shs, default_val t_strm, nullval, 0, false, gv).
    { simpl. cancel. }
    forward_if; [forward | discriminate].
  - destruct st as [L | ].
    2: { unfold istream, zstrm_at, strm_rep. Intros.
    remember (gv _zcalloc) as zca eqn:Hzca. remember (gv _zcfree) as zcf eqn:Hzcf.
    forward_call (strmp, shs, (zf_ni z, (Vint (Int.repr (zf_ai z)), (lv (zf_tin z), (zf_no z,
      (Vint (Int.repr (zf_ao z)), (lv (zf_tout z), (msg_val gv (zf_msg z), (nullval, (zca, (zcf,
      (nullval, (zv (zf_dt z), (lv (zf_adler z), zf_res z))))))))))))), nullval, 0, false, gv).
    { destruct (eq_dec strmp nullval); [contradiction | ]. cancel. }
    { right. split; [auto | ]. subst zca zcf. repeat split. }
    destruct (eq_dec strmp nullval); [contradiction | ].
    forward_if.
    { forward. unfold on_live, fst3, snd3, thd3, is_live, istream_opt. rewrite !if_false by auto. cbn [fst snd]. unfold istream, zstrm_at, strm_rep. entailer!. }
    { match goal with H: Int.repr 1 = Int.zero |- _ => inversion H end. } }
    destruct L as [sp winp s h headp hsh xb nb cb].
    unfold istream, state_mem, zstrm_at, strm_rep. cbn [l_sp l_winp l_s l_h l_headp]. rewrite state_rep_misc. Intros.
    match goal with H: live_ok _ |- _ => pose proof H as LOK; destruct H as (Hsp & SW & MW & HW & SW3 & HS & WW) end.
    cbn [l_sp l_s l_h] in Hsp, SW, MW, HW, SW3, HS, WW.
    remember (gv _zcalloc) as zca eqn:Hzca. remember (gv _zcfree) as zcf eqn:Hzcf.
    forward_call (strmp, shs, (zf_ni z, (Vint (Int.repr (zf_ai z)), (lv (zf_tin z), (zf_no z,
      (Vint (Int.repr (zf_ao z)), (lv (zf_tout z), (msg_val gv (zf_msg z), (sp, (zca, (zcf,
      (nullval, (zv (zf_dt z), (lv (zf_adler z), zf_res z))))))))))))), sp, i_mode s, true, gv).
    { destruct (eq_dec strmp nullval); [contradiction | ]. cancel. }
    { pose proof (sw_mode _ SW). split; [ | unfold HEAD, SYNC in *; rep_lia].
      right. split; [auto | ]. subst zca zcf. repeat split. }
    destruct (eq_dec strmp nullval) as [Hx | Hx]; [contradiction | ].
    pose proof (sw_mode _ SW) as HMD.
    rewrite (proj2 (Z.leb_le _ _) (proj1 HMD)), (proj2 (Z.leb_le _ _) (proj2 HMD)). simpl andb. cbv iota.
    forward_if; [contradiction | ]. Intros.
    pose proof (sw_bits _ SW) as HB. pose proof (sw_hold _ SW) as HH.
    forward_if.
    { forward.
      unfold on_live, is_live, prime_f, prime_s, istream_opt. rewrite !if_false by auto.
      cbn [Z.eqb fst3 snd3 thd3 fst snd l_s].
      unfold istream, state_mem, zstrm_at, strm_rep. cbn [set_l_s l_sp l_winp l_s l_h l_headp]. rewrite state_rep_misc.
      entailer!. }
    rename H4 into B0.
    forward. forward.
    forward_if.
    { forward. forward. forward.
      pose proof (live_hb _ 0 0 LOK ltac:(unfold lrange; rep_lia) ltac:(lia)) as LOK'.
      unfold on_live, is_live, prime_f, prime_s, istream_opt. rewrite !if_false by auto.
      rewrite (proj2 (Z.eqb_neq _ _) B0), (proj2 (Z.ltb_lt bits 0)) by lia.
      cbn [fst3 snd3 thd3 fst snd l_s].
      unfold istream, state_mem, zstrm_at, strm_rep. cbn [set_l_s l_sp l_winp l_s l_h l_headp] in LOK' |- *.
      rewrite state_rep_misc.
      change (U_misc gv sp winp (set_i_bits (set_i_hold s 0) 0)) with (U_misc gv sp winp s).
      change (win_rep winp (set_i_bits (set_i_hold s 0) 0)) with (win_rep winp s).
      cbn [i_mode i_wrap i_head i_hold i_bits i_length i_next i_codes i_back i_was set_i_hold set_i_bits].
      entailer!. }
    assert (BP: 0 < bits) by lia.
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp _t'2 (Vint (Int.repr (if orb (16 <? bits) (32 <? i_bits s + bits) then 1 else 0))) :: Q) (SEPx R))) end.
    { forward. entailer!. rewrite (proj2 (Z.ltb_lt 16 bits)) by lia. reflexivity. }
    { forward. forward. entailer!.
      rewrite (proj2 (Z.ltb_ge 16 bits)) by lia. cbn [orb].
      unfold bool2val. destruct (zlt 32 (i_bits s + bits)), (Z.ltb_spec 32 (i_bits s + bits)); try reflexivity; lia. }
    forward_if.
    { forward.
      unfold on_live, is_live, prime_f, prime_s, istream_opt. rewrite !if_false by auto.
      rewrite (proj2 (Z.eqb_neq _ _) B0), (proj2 (Z.ltb_ge bits 0)) by lia. cbn [l_s].
      destruct (orb (16 <? bits) (32 <? i_bits s + bits)) eqn:EO; [ | match goal with H: Int.repr 0 <> _ |- _ => contradiction H; reflexivity end].
      cbn [fst3 snd3 thd3 fst snd].
      unfold istream, state_mem, zstrm_at, strm_rep. cbn [set_l_s l_sp l_winp l_s l_h l_headp].
      rewrite state_rep_misc.
      entailer!. }
    match goal with H: Int.repr (if ?b then 1 else 0) = _ |- _ =>
      destruct b eqn:EO; [discriminate | ] end.
    apply orb_false_iff in EO. destruct EO as [E16 E32]. apply Z.ltb_ge in E16, E32.
    pose proof (pow_b16 bits ltac:(lia)) as PB.
    forward.
    { entailer!. rewrite shl1_64 by lia. rewrite Int64.signed_repr by rep_lia.
      change (Int.unsigned Int64.iwordsize') with 64. rep_lia. }
    rewrite (Int.signed_repr value), (Int.signed_repr 1), (Int.unsigned_repr bits) by rep_lia.
    rewrite shl1_64 by lia.
    destruct (prime_mask value bits ltac:(lia)) as [PM PR]. rewrite PM.
    set (v := Z.land value (2 ^ bits - 1)) in *.
    forward. forward. forward.
    { entailer!. change (Int.unsigned Int64.iwordsize') with 64. lia. }
    rewrite prime_hold by (auto; lia).
    forward. forward. forward.
    assert (LH: lrange (u64 (i_hold s + Z.land value (2 ^ bits - 1) * 2 ^ i_bits s))).
    { unfold lrange, u64. pose proof (Z.mod_pos_bound (i_hold s + Z.land value (2 ^ bits - 1) * 2 ^ i_bits s) (2 ^ 64) ltac:(lia)). rep_lia. }
    pose proof (live_hb _ _ (i_bits s + bits) LOK LH ltac:(lia)) as LOK'.
    unfold on_live, is_live, prime_f, prime_s, istream_opt. rewrite !if_false by auto.
    rewrite (proj2 (Z.eqb_neq _ _) B0), (proj2 (Z.ltb_ge bits 0)) by lia. cbn [l_s].
    rewrite (proj2 (Z.ltb_ge 16 bits)), (proj2 (Z.ltb_ge 32 _)) by lia. cbn [orb fst3 snd3 thd3 fst snd].
    unfold istream, state_mem, zstrm_at, strm_rep. cbn [set_l_s l_sp l_winp l_s l_h l_headp] in LOK' |- *.
    rewrite state_rep_misc.
    change (U_misc gv sp winp (set_i_bits (set_i_hold s (u64 (i_hold s + Z.land value (2 ^ bits - 1) * 2 ^ i_bits s))) (i_bits s + bits)))
      with (U_misc gv sp winp s).
    change (win_rep winp (set_i_bits (set_i_hold s (u64 (i_hold s + Z.land value (2 ^ bits - 1) * 2 ^ i_bits s))) (i_bits s + bits)))
      with (win_rep winp s).
    cbn [i_mode i_wrap i_head i_hold i_bits i_length i_next i_codes i_back i_was set_i_hold set_i_bits].
    entailer!.
Qed.

(* inflateMark's arithmetic: ((unsigned long)(long)back) << 16, as a long *)
Lemma mark_shl: forall b, -1 <= b <= 1000 -> Int64.shl (Int64.repr b) (Int64.repr 16) = Int64.repr (b * 65536).
Proof.
  intros b Hb. unfold Int64.shl. rewrite (Int64.unsigned_repr 16) by rep_lia.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 16) with 65536.
  apply Int64.eqm_samerepr. apply Int64.eqm_mult; [apply Int64.eqm_sym, Int64.eqm_unsigned_repr | apply Int64.eqm_refl].
Qed.

Lemma mark_val_eq: forall s, -1 <= i_back s <= 1000 ->
  mark_val s = i_back s * 65536 + (if i_mode s =? COPY then i_length s
                                   else if i_mode s =? MATCH then u32 (i_was s - i_length s) else 0).
Proof.
  intros s Hb. unfold mark_val. cbv zeta. f_equal.
  destruct (Z.eq_dec (i_back s) (-1)) as [E | E]; [rewrite E; reflexivity | ].
  assert (M64: 2 ^ 64 = 18446744073709551616) by reflexivity. assert (M63: 2 ^ 63 = 9223372036854775808) by reflexivity.
  rewrite M64, M63. rewrite (Z.mod_small (i_back s)) by lia.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 16) with 65536.
  rewrite Z.mod_small by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
Qed.

Lemma body_inflateMark {E: OracleKind}:
  semax_body Vprog_inflate Gp_check f_inflateMark inflateMark_spec.
Proof.
  start_function.
  unfold istream_opt.
  destruct (eq_dec strmp nullval) as [Hn | Hn].
  - subst strmp.
    forward_call (nullval, shs, default_val t_strm, nullval, 0, false, gv).
    { simpl. cancel. }
    forward_if; [forward | discriminate].
  - destruct st as [L | ].
    2: { unfold istream, zstrm_at, strm_rep. Intros.
    remember (gv _zcalloc) as zca eqn:Hzca. remember (gv _zcfree) as zcf eqn:Hzcf.
    forward_call (strmp, shs, (zf_ni z, (Vint (Int.repr (zf_ai z)), (lv (zf_tin z), (zf_no z,
      (Vint (Int.repr (zf_ao z)), (lv (zf_tout z), (msg_val gv (zf_msg z), (nullval, (zca, (zcf,
      (nullval, (zv (zf_dt z), (lv (zf_adler z), zf_res z))))))))))))), nullval, 0, false, gv).
    { destruct (eq_dec strmp nullval); [contradiction | ]. cancel. }
    { right. split; [auto | ]. subst zca zcf. repeat split. }
    destruct (eq_dec strmp nullval); [contradiction | ].
    forward_if.
    { forward. unfold is_live, istream_opt. rewrite !if_false by auto. unfold istream, zstrm_at, strm_rep. entailer!. }
    { match goal with H: Int.repr 1 = Int.zero |- _ => inversion H end. } }
    destruct L as [sp winp s h headp hsh xb nb cb].
    unfold istream, state_mem, zstrm_at, strm_rep. cbn [l_sp l_winp l_s l_h l_headp]. rewrite state_rep_misc. Intros.
    match goal with H: live_ok _ |- _ => pose proof H as LOK; destruct H as (Hsp & SW & MW & HW & SW3 & HS & WW) end.
    cbn [l_sp l_s l_h] in Hsp, SW, MW, HW, SW3, HS, WW.
    remember (gv _zcalloc) as zca eqn:Hzca. remember (gv _zcfree) as zcf eqn:Hzcf.
    forward_call (strmp, shs, (zf_ni z, (Vint (Int.repr (zf_ai z)), (lv (zf_tin z), (zf_no z,
      (Vint (Int.repr (zf_ao z)), (lv (zf_tout z), (msg_val gv (zf_msg z), (sp, (zca, (zcf,
      (nullval, (zv (zf_dt z), (lv (zf_adler z), zf_res z))))))))))))), sp, i_mode s, true, gv).
    { destruct (eq_dec strmp nullval); [contradiction | ]. cancel. }
    { pose proof (sw_mode _ SW). split; [ | unfold HEAD, SYNC in *; rep_lia].
      right. split; [auto | ]. subst zca zcf. repeat split. }
    destruct (eq_dec strmp nullval) as [Hx | Hx]; [contradiction | ].
    pose proof (sw_mode _ SW) as HMD.
    rewrite (proj2 (Z.leb_le _ _) (proj1 HMD)), (proj2 (Z.leb_le _ _) (proj2 HMD)). simpl andb. cbv iota.
    forward_if; [contradiction | ]. Intros.
    forward. forward. forward.
    pose proof (sw_length _ SW) as HL. pose proof (sw_was _ SW) as HWS. pose proof (sw_back _ SW) as HBK.
    unfold urange in HL, HWS.
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp _t'2 (Vint (Int.repr (if i_mode s =? COPY then i_length s
        else if i_mode s =? MATCH then u32 (i_was s - i_length s) else 0))) :: Q) (SEPx R))) end.
    { forward. forward.
      assert (EM: i_mode s = COPY).
      { match goal with H: Int.repr (i_mode s) = Int.repr _ |- _ =>
          apply (f_equal Int.unsigned) in H; rewrite !Int.unsigned_repr in H by (unfold HEAD, SYNC in *; rep_lia) end.
        unfold COPY; lia. }
      rewrite EM, Z.eqb_refl. entailer!. }
    { forward.
      assert (EM: i_mode s <> COPY).
      { intro X. match goal with H: Int.repr (i_mode s) <> Int.repr _ |- _ => apply H; rewrite X; reflexivity end. }
      match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
        forward_if (PROPx P (LOCALx (temp _t'2 (Vint (Int.repr (if i_mode s =? COPY then i_length s
          else if i_mode s =? MATCH then u32 (i_was s - i_length s) else 0))) :: Q) (SEPx R))) end.
      { forward. forward. forward. forward.
        assert (EM2: i_mode s = MATCH).
        { match goal with H: Int.repr (i_mode s) = Int.repr _ |- _ =>
            apply (f_equal Int.unsigned) in H; rewrite !Int.unsigned_repr in H by (unfold HEAD, SYNC in *; rep_lia) end.
          unfold MATCH; lia. }
        rewrite (proj2 (Z.eqb_neq _ _) EM), EM2, Z.eqb_refl. entailer!.
        unfold u32. rewrite <- (Int.repr_unsigned (Int.repr (i_was s - i_length s))), Int.unsigned_repr_eq. reflexivity. }
      { forward. forward.
        assert (EM2: i_mode s <> MATCH).
        { intro X. match goal with H: Int.repr (i_mode s) <> Int.repr _ |- _ => apply H; rewrite X; reflexivity end. }
        rewrite (proj2 (Z.eqb_neq _ _) EM), (proj2 (Z.eqb_neq _ _) EM2). entailer!. }
      entailer!. }
    assert (LR: 0 <= (if i_mode s =? COPY then i_length s
                      else if i_mode s =? MATCH then u32 (i_was s - i_length s) else 0) <= Int.max_unsigned).
    { destruct (i_mode s =? COPY); [lia | ]. destruct (i_mode s =? MATCH); [ | rep_lia].
      unfold u32. pose proof (Z.mod_pos_bound (i_was s - i_length s) (2 ^ 32) ltac:(lia)). rep_lia. }
    forward. forward.
    { entailer!. rewrite mark_shl by lia. rewrite Int64.signed_repr by rep_lia. try rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    unfold is_live, istream_opt. rewrite !if_false by auto. cbn [l_s].
    rewrite mark_val_eq by lia.
    unfold istream, state_mem, zstrm_at, strm_rep. cbn [l_sp l_winp l_s l_h l_headp]. rewrite state_rep_misc.
    entailer!.
    rewrite mark_shl by lia. try rewrite Int.unsigned_repr by rep_lia.
    rewrite Int64.add_signed. rewrite !Int64.signed_repr by rep_lia. reflexivity.
Qed.

(* inflateCodesUsed: state->next is a pointer into state->codes *)
Lemma codes_at_isptr: forall sp k, field_compatible t_state (DOT _codes) sp -> 0 <= k <= ENOUGH_CODES ->
  isptr (codes_at sp k).
Proof.
  intros sp k F Hk. unfold codes_at, field_address0.
  rewrite if_true by (eapply field_compatible0_cons_Tarray; [reflexivity | auto | unfold ENOUGH_CODES in Hk; lia]).
  destruct F as [P _]. destruct sp; try contradiction. simpl. auto.
Qed.

Lemma codes_at_eq: forall sp k, field_compatible t_state (DOT _codes) sp -> 0 <= k <= ENOUGH_CODES ->
  codes_at sp k = offset_val (1368 + 4 * k) sp.
Proof.
  intros sp k F Hk. unfold codes_at, field_address0.
  rewrite if_true by (eapply field_compatible0_cons_Tarray; [reflexivity | auto | unfold ENOUGH_CODES in Hk; lia]).
  f_equal.
Qed.

Lemma codes_sub: forall sp k, isptr sp -> 0 <= k <= ENOUGH_CODES ->
  force_val (sem_sub_pp (Tstruct ___gp_code noattr) (offset_val (1368 + 4 * k) sp) (offset_val 1368 sp)) =
  Vlong (Int64.repr k).
Proof.
  intros sp k P Hk. destruct sp; try contradiction.
  unfold sem_sub_pp. simpl. destruct (eq_block b b); [ | congruence]. simpl.
  rewrite (Ptrofs.add_commut i), (Ptrofs.add_commut i), Ptrofs.sub_shifted.
  unfold ENOUGH_CODES in Hk.
  unfold Ptrofs.sub. rewrite !Ptrofs.unsigned_repr by rep_lia.
  replace (1368 + 4 * k - 1368)%Z with (k * 4)%Z by lia.
  unfold Ptrofs.divs. rewrite !Ptrofs.signed_repr by rep_lia. rewrite Z.quot_mul by lia.
  unfold Vptrofs. simpl. unfold Ptrofs.to_int64. rewrite Ptrofs.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma body_inflateCodesUsed {E: OracleKind}:
  semax_body Vprog_inflate Gp_check f_inflateCodesUsed inflateCodesUsed_spec.
Proof.
  start_function.
  unfold istream_opt.
  destruct (eq_dec strmp nullval) as [Hn | Hn].
  - subst strmp.
    forward_call (nullval, shs, default_val t_strm, nullval, 0, false, gv).
    { simpl. cancel. }
    forward_if; [forward | discriminate].
  - destruct st as [L | ].
    2: { unfold istream, zstrm_at, strm_rep. Intros.
    remember (gv _zcalloc) as zca eqn:Hzca. remember (gv _zcfree) as zcf eqn:Hzcf.
    forward_call (strmp, shs, (zf_ni z, (Vint (Int.repr (zf_ai z)), (lv (zf_tin z), (zf_no z,
      (Vint (Int.repr (zf_ao z)), (lv (zf_tout z), (msg_val gv (zf_msg z), (nullval, (zca, (zcf,
      (nullval, (zv (zf_dt z), (lv (zf_adler z), zf_res z))))))))))))), nullval, 0, false, gv).
    { destruct (eq_dec strmp nullval); [contradiction | ]. cancel. }
    { right. split; [auto | ]. subst zca zcf. repeat split. }
    destruct (eq_dec strmp nullval); [contradiction | ].
    forward_if.
    { forward. unfold is_live, istream_opt. rewrite !if_false by auto. unfold istream, zstrm_at, strm_rep. entailer!. }
    { match goal with H: Int.repr 1 = Int.zero |- _ => inversion H end. } }
    destruct L as [sp winp s h headp hsh xb nb cb].
    unfold istream, state_mem, zstrm_at, strm_rep. cbn [l_sp l_winp l_s l_h l_headp]. rewrite state_rep_misc. Intros.
    match goal with H: live_ok _ |- _ => pose proof H as LOK; destruct H as (Hsp & SW & MW & HW & SW3 & HS & WW) end.
    cbn [l_sp l_s l_h] in Hsp, SW, MW, HW, SW3, HS, WW.
    remember (gv _zcalloc) as zca eqn:Hzca. remember (gv _zcfree) as zcf eqn:Hzcf.
    forward_call (strmp, shs, (zf_ni z, (Vint (Int.repr (zf_ai z)), (lv (zf_tin z), (zf_no z,
      (Vint (Int.repr (zf_ao z)), (lv (zf_tout z), (msg_val gv (zf_msg z), (sp, (zca, (zcf,
      (nullval, (zv (zf_dt z), (lv (zf_adler z), zf_res z))))))))))))), sp, i_mode s, true, gv).
    { destruct (eq_dec strmp nullval); [contradiction | ]. cancel. }
    { pose proof (sw_mode _ SW). split; [ | unfold HEAD, SYNC in *; rep_lia].
      right. split; [auto | ]. subst zca zcf. repeat split. }
    destruct (eq_dec strmp nullval) as [Hx | Hx]; [contradiction | ].
    pose proof (sw_mode _ SW) as HMD.
    rewrite (proj2 (Z.leb_le _ _) (proj1 HMD)), (proj2 (Z.leb_le _ _) (proj2 HMD)). simpl andb. cbv iota.
    forward_if; [contradiction | ]. Intros.
    pose proof (sw_next _ SW) as HNX.
    forward. forward. forward.
    { entailer!. assert (IP: isptr (codes_at sp (i_next s))) by (apply codes_at_isptr; auto). destruct (codes_at sp (i_next s)); try contradiction. simpl; auto. }
    forward.
    { entailer!. rewrite codes_at_eq by auto. split; [destruct sp; try contradiction; simpl; auto | ].
      destruct sp; try contradiction. simpl. destruct (peq b b); simpl; auto. }
    unfold is_live, istream_opt. rewrite !if_false by auto. cbn [l_s].
    unfold istream, state_mem, zstrm_at, strm_rep. cbn [l_sp l_winp l_s l_h l_headp]. rewrite state_rep_misc.
    entailer!.
    rewrite codes_at_eq by auto. apply codes_sub; auto.
Qed.

Lemma api5_misc : api_misc_stmt.
Proof.
  intros E. split; [exact body_inflateGetHeader | ]. split; [exact body_inflatePrime | ].
  split; [exact body_inflateValidate | ]. split; [exact body_inflateMark | ].
  split; [exact body_inflateCodesUsed | exact body_inflateSyncPoint].
Qed.
