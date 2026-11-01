(* RT-H: mechanical port of inflate/NeedBits_5.v to the header-external loop state (RTHLoop.v); identifiers whose meaning changes carry the suffix H. *)
(* NeedBits.v's FLAGS site in Delta_cases5 *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Export Zlib.proof.roundtrip.RTHNeedBits.
Require Import Zlib.proof.inflate.Callees5.
Require Export Zlib.proof.roundtrip.RTHCaseCommon.
Require Export Zlib.proof.inflate.NeedBits_5.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Lemma semax_needbits_FLAGS5H {Espec: OracleKind} (F: frame) (m: mst) (n: Z):
  mwf m -> m_leave m = 0 -> 0 <= n <= 32 ->
  semax Delta_cases5 (loop_stateH F m) (needbits_stmt n _t'13 _t'432)
    (normal_ret_assert (loop_stateH F (needbits n m))).
Proof.
  intros W HL Hn.
  pose proof (mw_bits _ W) as WB. pose proof (mw_nx _ W) as WNX. pose proof (mw_inp _ W) as WINP.
  destruct F as [gv shs strmp sp headp winp hsh xb nb cb ib ob gsh tsh dt vres vhere vlast vhbuf flush].
  unfold needbits_stmt, pullbyte_body, loop_stateH. frame_simpl.
  abbreviate_semax.
  forward_loop (EX k: nat,
     PROP ((k <= 4)%nat; needbits_f (4 - k) n (pullk k m) = needbits n m;
           m_bits (pullk k m) = (m_bits m + 8 * Z.of_nat k)%Z;
           (0 < k)%nat -> (m_bits m + 8 * (Z.of_nat k - 1) < n)%Z;
           (m_nx m + Z.of_nat k <= Zlength (m_inp m))%Z;
           in_ok ib (m_inp m); out_ok ob (m_aout m))
     LOCAL (temp _strm strmp; temp _flush (zv flush); temp _state sp;
            temp _next (in_ptr ib (m_nx (pullk k m)));
            temp _put (out_ptr ob (Zlength (m_ow m)));
            temp _have (zv (m_have (pullk k m))); temp _left (zv (m_left m));
            temp _hold (lv (m_hold (pullk k m))); temp _bits (zv (m_bits (pullk k m)));
            temp _in (zv (m_in m)); temp _out (zv (m_out m));
            temp _ret (zv (m_ret m)); temp _leave (zv 0);
            lvar _here t_code vhere; lvar _last t_code vlast;
            lvar _hbuf (tarray tuchar 4) vhbuf; gvars gv)
     SEP (mem_repH (Fr gv shs strmp sp headp winp hsh xb nb cb ib ob gsh tsh dt vres vhere vlast vhbuf flush) m; locals_rep (Fr gv shs strmp sp headp winp hsh xb nb cb ib ob gsh tsh dt vres vhere vlast vhbuf flush)))
    break: (loop_stateH (Fr gv shs strmp sp headp winp hsh xb nb cb ib ob gsh tsh dt vres vhere vlast vhbuf flush) (needbits n m)).
  - Exists 0%nat. simpl pullk. entailer!.
  - Intros k.
    destruct (pullk_fieldsH k m) as (P1&P2&P3&P4&P5&P6&P7&P8&P9&P10).
    assert (HB: 0 <= m_bits (pullk k m) <= 71) by lia.
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROPx ((m_bits (pullk k m) < n)%Z :: P) (LOCALx Q (SEPx R))) end.
    + (* bits < n: go on *)
      forward. entailer!.
    + (* bits >= n: the loop ends *)
      forward.
      assert (E: needbits n m = pullk k m).
      { match goal with H: needbits_f _ _ _ = needbits n m |- _ => rewrite <- H end.
        apply needbits_f_ge. lia. }
      rewrite E. unfold loop_stateH. rewrite mem_rep_pullkH.
      entailer!.
      unfold m_left. rewrite P3, P4, P5. repeat split; auto.
    + (* PULLBYTE *)
      Intros.
      assert (K4: (k < 4)%nat).
      { destruct (Nat.lt_ge_cases k 4); auto. lia. }
      assert (HH: 0 <= m_have (pullk k m) <= Int.max_signed) by (unfold m_have; rewrite P3, P10; lia).
      forward_if.
      * (* no input: leave *)
        forward. forward.
        assert (E: needbits n m = set_leave (pullk k m)).
        { match goal with H: needbits_f _ _ _ = needbits n m |- _ => rewrite <- H end.
          replace (4 - k)%nat with (S (3 - k)) by lia. rewrite needbits_f_S.
          destruct (m_bits (pullk k m) <? n) eqn:Ebn; [ | lia].
          destruct (m_have (pullk k m) =? 0) eqn:Eh; [ reflexivity | lia]. }
        rewrite E. unfold loop_stateH.
        replace (mem_repH (Fr gv shs strmp sp headp winp hsh xb nb cb ib ob gsh tsh dt vres vhere vlast vhbuf flush) (set_leave (pullk k m))) with (mem_repH (Fr gv shs strmp sp headp winp hsh xb nb cb ib ob gsh tsh dt vres vhere vlast vhbuf flush) m)
          by (rewrite <- (mem_rep_pullkH (Fr gv shs strmp sp headp winp hsh xb nb cb ib ob gsh tsh dt vres vhere vlast vhbuf flush) k m); reflexivity).
        entailer!.
        unfold m_left. mnorm_goalH. rewrite P3, P4, P5, P6, P7, P8. repeat split; auto.
      * (* pull a byte *)
        forward.
        destruct ib as [ | ish ip ilo inb ic]; cbn [in_ptr in_rep].
        { (* no input object: have = 0 *)
          exfalso.
          assert (m_have (pullk k m) = 0); [ | lia].
          unfold m_have. rewrite P3, P10.
          match goal with H: in_ok InNull (m_inp m) |- _ => unfold in_ok in H; rewrite H in * end.
          rewrite Zlength_nil in *. lia. }
        assert (Hj: 0 <= m_nx (pullk k m) < Zlength (m_inp m)).
        { match goal with H: m_have (pullk k m) <> 0 |- _ => revert H end. revert HH.
          unfold m_have. rewrite P3, P10. intros. lia. }
        match goal with H: in_ok (InBuf _ _ _ _ _) _ |- _ =>
          pose proof (in_byte _ _ _ _ _ _ (m_nx (pullk k m)) H Hj) as HBYTE;
          pose proof H as HINOK;
          destruct H as (Hish & Hip & Hilo & Hinb & Hic & Hinbm & Hsub & Hbytes) end.
        unfold mem_repH. cbn [in_ptr in_rep f_ib f_gv f_ob]. Intros.
        assert_PROP (field_compatible (tarray tuchar inb) [] ip) by entailer!.
        forward. forward.
        assert (HIX: 0 <= ilo + m_nx (pullk k m) < inb) by lia.
        rewrite (offset_val_field_address_tuchar inb (ilo + m_nx (pullk k m)) ip) by (auto; lia).
        pose proof (bytes_ok_Znth _ _ Hbytes Hj) as HBR.
        forward.
        { rewrite HBYTE. entailer!. rep_lia. }
        rewrite HBYTE.
        forward.
        { entailer!. change (Int.unsigned Int64.iwordsize') with 64. lia. }
        forward.
        Exists (S k).
        rewrite !pullk_S.
        unfold mem_repH. frame_simpl_goal.
        entailer!.
        match goal with H: needbits_f (4 - k) n (pullk k m) = needbits n m |- _ => rename H into HNB end.
        match goal with H: m_bits (pullk k m) = (m_bits m + 8 * Z.of_nat k)%Z |- _ => rename H into HBK end.
        match goal with H: m_have (pullk k m) <> 0 |- _ => rename H into HHV end.
        match goal with H: m_bits (pullk k m) < n |- _ => rename H into HBN end.
        assert (HBX: 0 <= m_bits (pullk k m) + 8 < 2 ^ 32) by lia.
        split; [ | split; [ | split; [ | split; [ | split]]]].
        -- rewrite <- HNB. replace (4 - k)%nat with (S (4 - S k)) by lia. rewrite needbits_f_S.
          rewrite (proj2 (Z.ltb_lt _ _) HBN). rewrite (proj2 (Z.eqb_neq _ _) HHV). reflexivity.
        -- unfold pull. mnorm_goalH. unfold u32. rewrite Z.mod_small by lia. rewrite HBK, Nat2Z.inj_succ. lia.
        -- rewrite <- (offset_val_field_address_tuchar (Zlength ic) (ilo + m_nx (pullk k m)) ip) by (auto; lia).
          unfold pull. mnorm_goalH. rewrite offset_offset_val. f_equal. lia.
        -- unfold m_have, pull. mnorm_goalH. f_equal. f_equal. lia.
        -- unfold pull. mnorm_goalH. rewrite P3. f_equal. apply hold_add_eq; [ | lia].
          pose proof (bytes_ok_Znth _ _ Hbytes Hj). lia.
        -- unfold pull. mnorm_goalH. unfold u32. rewrite Z.mod_small by lia. reflexivity.
  - (* after the loop *)
    unfold loop_stateH. entailer!.
Qed.
