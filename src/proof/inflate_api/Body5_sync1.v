(* Body of inflateSync, segment 1 (Body5_sync_kit.v): from `if (state->mode != SYNC)` (the first call: the bits of
   the bit buffer go to buf and are searched for the pattern) to the call of syncsearch on the input. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.Body5_sync_kit.
#[local] Existing Instance Zlib.units.Inflate.CS.

Local Open Scope logic.

(* the fields of the state after the first call's work on the bit buffer: mode SYNC, the bit buffer emptied of
   its whole bytes (bits = 0) and have = the progress of the search for the pattern in those bytes *)
Lemma sync_start_vals (s: istate) :
  i_mode (sync_start s) = SYNC /\
  i_hold (sync_start s) = Z.shiftr (Z.shiftr (i_hold s) (Z.land (i_bits s) 7))
                            (8 * ((i_bits s - Z.land (i_bits s) 7) / 8))%Z /\
  i_bits (sync_start s) = 0 /\
  i_have (sync_start s) = fst (ssearch 0 (hold_bytes (Z.to_nat ((i_bits s - Z.land (i_bits s) 7) / 8))
                                            (Z.shiftr (i_hold s) (Z.land (i_bits s) 7)))).
Proof.
  unfold sync_start. ss_simpl. split; [reflexivity | ]. split; [reflexivity | ]. split; [ | reflexivity].
  change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
  replace (i_bits s - i_bits s mod 8) with (8 * (i_bits s / 8))%Z by (pose proof (Z.div_mod (i_bits s) 8); lia).
  rewrite Z.mul_comm. apply Z_mod_mult.
Qed.

Lemma sync_part1 (NEXT: sync_seg2) : sync_seg1.
Proof.
  intros E gv shs strmp z sp winp s h headp hsh xb nb cb ish ip ilo ilen ic inp v_buf.
  intros HY LOK HMD EB.
  assert (Hsp: isptr sp) by (destruct LOK as (X & _); exact X).
  assert (SW: swf s) by (destruct LOK as (_ & X & _); exact X).
  pose proof (sw_bits _ SW) as HBITS. pose proof (sw_hold _ SW) as HHOLD. unfold lrange in HHOLD.
  sync_seg_start.
  remember (gv _zcalloc) as zca eqn:Hzca. remember (gv _zcfree) as zcf eqn:Hzcf.
    set (s1 := if i_mode s =? SYNC then s else sync_start s).
    assert (E7: Z.land (i_bits s) 7 = i_bits s mod 8)
      by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity).
    assert (L7: 0 <= Z.land (i_bits s) 7 <= 7)
      by (rewrite E7; pose proof (Z.mod_pos_bound (i_bits s) 8); lia).
    set (hold0 := Z.shiftr (i_hold s) (Z.land (i_bits s) 7)).
    set (nby := (i_bits s - Z.land (i_bits s) 7) / 8).
    assert (NBY: (i_bits s - Z.land (i_bits s) 7 = 8 * nby /\ 0 <= nby <= 4)%Z).
    { unfold nby. rewrite E7. pose proof (Z.mod_pos_bound (i_bits s) 8 ltac:(lia)).
      pose proof (Z.div_mod (i_bits s) 8 ltac:(lia)).
      replace (i_bits s - i_bits s mod 8)%Z with ((i_bits s / 8) * 8)%Z by lia.
      rewrite Z.div_mul by lia. split; [lia | ]. split; [apply Z.div_pos; lia | ]. lia. }
    assert (H0R: 0 <= hold0 <= Int64.max_unsigned).
    { unfold hold0. split; [apply Z.shiftr_nonneg; lia | ].
      rewrite Z.shiftr_div_pow2 by lia. apply Z.le_trans with (i_hold s); [ | lia].
      apply Z.div_le_upper_bound; [lia | ]. pose proof (Z.pow_pos_nonneg 2 (Z.land (i_bits s) 7)). nia. }
    forward.
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (EX bc: list val, PROPx P (LOCALx [temp _state sp; lvar _buf (tarray tuchar 4) v_buf; gvars gv; temp _strm strmp] (SEPx
        (replace_nth 2 (replace_nth 4 (replace_nth 9 (replace_nth 10 (replace_nth 11 R
          (field_at Ews t_state (DOT _have) (zv (i_have s1)) sp))
          (field_at Ews t_state (DOT _bits) (zv (i_bits s1)) sp))
          (field_at Ews t_state (DOT _hold) (lv (i_hold s1)) sp))
          (data_at Tsh (tarray tuchar 4) bc v_buf))
          (field_at Ews t_state (DOT _mode) (zv (i_mode s1)) sp)))))%assert end.
    { (* first time: the whole bytes of the bit buffer go to buf, which is searched for the pattern *)
      assert (S1: s1 = sync_start s).
      { unfold s1. rewrite (proj2 (Z.eqb_neq _ _)); [reflexivity | ].
        intro EM. match goal with X: Int.repr (i_mode s) <> _ |- _ => apply X end. rewrite EM. reflexivity. }
      destruct (sync_start_vals s) as (SM & SH & SB & SHV). fold hold0 nby in SH, SHV.
      freeze [0;1;3;5;6;7;8;12;13;14;15;16] FR.
      forward. forward. forward. forward.
      { entailer!. change (Int.unsigned Int64.iwordsize') with 64. lia. }
      forward. forward. forward.
      forward.
      assert (EH: Int64.shru (Int64.repr (i_hold s)) (Int64.repr (Int.unsigned (Int.and (Int.repr (i_bits s)) (Int.repr 7))))
                  = Int64.repr hold0).
      { unfold Int.and. rewrite (Int.unsigned_repr (i_bits s)) by rep_lia. rewrite (Int.unsigned_repr 7) by rep_lia.
        rewrite Int.unsigned_repr by rep_lia.
        unfold Int64.shru. rewrite !Int64.unsigned_repr by rep_lia. reflexivity. }
      assert (EB2: Int.sub (Int.repr (i_bits s)) (Int.and (Int.repr (i_bits s)) (Int.repr 7)) = Int.repr (8 * nby)%Z).
      { unfold Int.and. rewrite (Int.unsigned_repr (i_bits s)) by rep_lia. rewrite (Int.unsigned_repr 7) by rep_lia.
        rewrite sub_repr. f_equal. lia. }
      rewrite EH, EB2. clear EH EB2.
      clearbody hold0 nby.
      forward_loop (EX j: Z, PROP ((0 <= j <= nby)%Z) LOCAL (temp _len (Vint (Int.repr j)); temp _state sp;
            lvar _buf (tarray tuchar 4) v_buf; gvars gv; temp _strm strmp) SEP (FRZL FR;
            field_at Ews t_state (DOT _mode) (zv SYNC) sp;
            data_at Tsh (tarray tuchar 4) (byte_vals (hold_bytes (Z.to_nat j) hold0) ++ Zrepeat Vundef (4 - j)) v_buf;
            field_at Ews t_state (DOT _hold) (lv (Z.shiftr hold0 (8 * j)%Z)) sp;
            field_at Ews t_state (DOT _bits) (zv (8 * nby - 8 * j)%Z) sp;
            field_at Ews t_state (DOT _have) (zv (i_have s)) sp))%assert
        break: (PROP () LOCAL (temp _len (Vint (Int.repr nby)); temp _state sp;
            lvar _buf (tarray tuchar 4) v_buf; gvars gv; temp _strm strmp) SEP (FRZL FR;
            field_at Ews t_state (DOT _mode) (zv SYNC) sp;
            data_at Tsh (tarray tuchar 4) (byte_vals (hold_bytes (Z.to_nat nby) hold0) ++ Zrepeat Vundef (4 - nby)) v_buf;
            field_at Ews t_state (DOT _hold) (lv (Z.shiftr hold0 (8 * nby)%Z)) sp;
            field_at Ews t_state (DOT _bits) (zv 0) sp;
            field_at Ews t_state (DOT _have) (zv (i_have s)) sp)).
      { Exists 0. rewrite Z.mul_0_r, Z.shiftr_0_r, Z.sub_0_r, Z.sub_0_r. simpl hold_bytes. entailer!. }
      { Intros j. forward.
        forward_if.
        - assert (J: (j < nby)%Z).
          { lia. }
          forward. forward. forward. forward.
          assert (HR: 0 <= Z.shiftr hold0 (8 * j) <= Int64.max_unsigned) by (apply shiftr_range; [exact H0R | lia]).
          rewrite zext8_byte by exact HR. rewrite buf_upd by lia.
          forward. forward. change (Int.unsigned (Int.repr 8)) with 8. rewrite shru_repr by (first [exact HR | lia]).
          forward. forward.
          Exists (j + 1).
          rewrite Z.shiftr_shiftr by lia.
          replace (8 * j + 8)%Z with (8 * (j + 1))%Z by lia.
          entailer!.
          replace (8 * nby - 8 * j - 8)%Z with (8 * nby - 8 * (j + 1))%Z by lia. cancel.
        - forward. assert (J: j = nby).
          { lia. }
          subst j. replace (8 * nby - 8 * nby)%Z with 0 by lia. entailer!. }
      forward.
      set (data := hold_bytes (Z.to_nat nby) hold0).
      assert (DL: Zlength data = nby) by (unfold data; rewrite hold_bytes_len; lia).
      assert_PROP (isptr v_buf /\ field_compatible t_state (DOT _have) sp) as PF by entailer!.
      destruct PF as [PVB FCH].
      rewrite (field_at_data_at Ews t_state (DOT _have)).
      forward_call (Ews, field_address t_state (DOT _have) sp, 0, Tsh, v_buf, 0, 4,
                    byte_vals data ++ Zrepeat Vundef (4 - nby), data).
      { entailer!. rewrite DL. simpl. f_equal. rewrite field_compatible_field_address by auto. reflexivity. }
      { split; [rewrite Zlength_app, Zlength_byte_vals, Zlength_Zrepeat; lia | ].
        split; [ | apply hold_bytes_ok].
        replace (Zlength data) with (Zlength (byte_vals data)) by apply Zlength_byte_vals.
        rewrite sublist0_app1 by (pose proof (Zlength_nonneg (byte_vals data)); lia). apply sublist_same; reflexivity. }
      Exists (byte_vals data ++ Zrepeat Vundef (4 - nby)). cbn [replace_nth].
      change (data_at Ews tuint) with (data_at Ews (nested_field_type t_state (DOT _have))).
      rewrite <- field_at_data_at.
      thaw FR. rewrite S1, SM, SH, SB, SHV. entailer!. }
    { forward. Exists (default_val (tarray tuchar 4)). cbn [replace_nth].
      assert (EMS: i_mode s = SYNC).
      { match goal with X: Int.repr (i_mode s) = Int.repr _ |- _ =>
          apply repr_inj_signed in X; [exact X | unfold HEAD, SYNC in *; rep_lia | rep_lia] end. }
      assert (s1 = s) as -> by (unfold s1; rewrite (proj2 (Z.eqb_eq _ _)) by exact EMS; reflexivity).
      entailer!. }
    Intros bc. cbn [replace_nth].
    set (L := Live sp winp s h headp hsh xb nb cb) in LOK.
    assert (LOK1: live_ok (set_l_s L s1)).
    { unfold s1. destruct (i_mode s =? SYNC) eqn:EM; [exact LOK | exact (live_sync_start L LOK)]. }
    assert (M1: i_mode s1 = SYNC /\ i_wrap s1 = i_wrap s /\ i_flags s1 = i_flags s /\ i_wbits s1 = i_wbits s).
    { unfold s1. destruct (Z.eqb_spec (i_mode s) SYNC); [auto | apply sync_start_fields]. }
    assert (U1: U_sync gv sp headp winp s1 = U_sync gv sp headp winp s /\ win_rep winp s1 = win_rep winp s).
    { unfold s1. destruct (i_mode s =? SYNC); [auto | rewrite U_sync_start, win_rep_start; auto]. }
    destruct M1 as (M1 & WR1 & FL1 & WB1). destruct U1 as [U1 WI1].
    rewrite <- WR1, <- FL1, <- WB1, <- U1, <- WI1.
    assert (HV1: 0 <= i_have s1 <= 320) by (destruct LOK1 as (_ & W1' & _); exact (sw_have _ W1')).
    assert (SG: sync_s s inp = (if fst (ssearch (i_have s1) inp) =? 4
        then SyncOk (sync_fin (set_i_have s1 (fst (ssearch (i_have s1) inp)))) (snd (ssearch (i_have s1) inp))
        else SyncData (set_i_have s1 (fst (ssearch (i_have s1) inp))) (snd (ssearch (i_have s1) inp)))).
    { rewrite sync_s_go by exact EB. reflexivity. }
    clearbody s1. clear SW HBITS HHOLD E7 L7 NBY H0R. clear hold0 nby.
    subst zca zcf.
    exact (NEXT E gv shs strmp z sp winp s h headp hsh xb nb cb ish ip ilo ilen ic inp v_buf s1 bc
             HY LOK1 M1 HV1 SG).
Qed.
