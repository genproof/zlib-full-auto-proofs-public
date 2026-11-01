(* case CODELENS (CLRep5.v): the variable NEEDBITS(here.bits + k) of the repeat codes 16 / 17 / 18, one lemma per
   clightgen temporaries *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate.CLKit5.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* NEEDBITS(here.bits + k): the bound reloaded from here.bits (temporary t0) at each iteration *)
Definition needbits_var (k: Z) (t0 t1 t2: ident) : statement :=
  Sloop
    (Ssequence
      (Ssequence (Sset t0 (Efield (Evar _here (Tstruct ___gp_code noattr)) _bits tuchar))
        (Sifthenelse (Ebinop Olt (Etempvar _bits tuint)
                       (Ecast (Ebinop Oadd (Etempvar t0 tuchar) (Econst_int (Int.repr k) tint) tint) tuint) tint)
          Sskip Sbreak))
      (pullbyte_body t1 t2))
    Sskip.

Definition nbv_inv (F: frame) (m: mst) (here: entry) (k: Z) (j: nat) : environ -> mpred :=
  PROP ((j <= 4)%nat; needbits_f (4 - j) (e_bits here + k) (pullk j m) = needbits (e_bits here + k) m;
        m_bits (pullk j m) = (m_bits m + 8 * Z.of_nat j)%Z;
        (0 < j)%nat -> (m_bits m + 8 * (Z.of_nat j - 1) < e_bits here + k)%Z;
        (m_nx m + Z.of_nat j <= Zlength (m_inp m))%Z;
        in_ok (f_ib F) (m_inp m); out_ok (f_ob F) (m_aout m))
  LOCAL (temp _strm (f_strmp F); temp _flush (zv (f_flush F)); temp _state (f_sp F);
         temp _next (in_ptr (f_ib F) (m_nx (pullk j m)));
         temp _put (out_ptr (f_ob F) (Zlength (m_ow m)));
         temp _have (zv (m_have (pullk j m))); temp _left (zv (m_left m));
         temp _hold (lv (m_hold (pullk j m))); temp _bits (zv (m_bits (pullk j m)));
         temp _in (zv (m_in m)); temp _out (zv (m_out m));
         temp _ret (zv (m_ret m)); temp _leave (zv 0);
         lvar _here t_code (f_vhere F); lvar _last t_code (f_vlast F);
         lvar _hbuf (tarray tuchar 4) (f_vhbuf F); gvars (f_gv F))
  SEP (mem_rep F m; data_at Tsh t_code (ent here) (f_vhere F); data_at_ Tsh t_code (f_vlast F);
       data_at_ Tsh (tarray tuchar 4) (f_vhbuf F)).

Definition nbv_pre (F: frame) (m: mst) (here: entry) (k: Z) : environ -> mpred := EX j: nat, nbv_inv F m here k j.

Lemma semax_needbits_var16 {Espec: OracleKind} (F: frame) (m: mst) (here: entry) (k: Z):
  mwf m -> m_leave m = 0 -> entry_ok here -> 0 <= e_bits here <= 15 -> 0 <= k <= 7 ->
  semax Delta_cases5 (loop_state_h F m (ent here)) (needbits_var k _t'309 _t'65 _t'308)
    (normal_ret_assert (loop_state_h F (needbits (e_bits here + k) m) (ent here))).
Proof.
  intros W HL HE Hb Hk.
  pose proof (mw_bits _ W) as WB. pose proof (mw_nx _ W) as WNX. pose proof (mw_inp _ W) as WINP.
  unfold needbits_var, pullbyte_body.
  abbreviate_semax.
  forward_loop (nbv_pre F m here k)
    break: (loop_state_h F (needbits (e_bits here + k) m) (ent here)).
  - unfold nbv_pre. Exists 0%nat. unfold loop_state_h, nbv_inv, loop_locals. simpl pullk. entailer!.
  - unfold nbv_pre. Intros j.
    destruct (pullk_fields j m) as (P1&P2&P3&P4&P5&P6&P7&P8&P9&P10).
    destruct F as [gv shs strmp sp headp winp hsh xb nb cb ib ob gsh tsh dt vres vhere vlast vhbuf flush].
    unfold nbv_inv. cbn [f_gv f_ib f_ob f_strmp f_flush f_sp f_vhere f_vlast f_vhbuf]. Intros.
    destruct HE as (Eo & Eb & Ev).
    assert (HB: 0 <= m_bits (pullk j m) <= 71) by lia.
    unfold ent. forward.
    { entailer!. rep_lia. }
    match goal with |- semax _ (PROPx ?P (LOCALx (_ :: ?Q) (SEPx ?R))) _ _ =>
      forward_if (PROPx ((m_bits (pullk j m) < e_bits here + k)%Z :: P) (LOCALx Q (SEPx R))) end.
    + (* bits < n: go on *)
      forward. entailer!.
    + (* bits >= n: the loop ends *)
      forward.
      assert (E: needbits (e_bits here + k) m = pullk j m).
      { rewrite <- H0. apply needbits_f_ge. lia. }
      rewrite E. unfold loop_state_h, loop_locals. cbn [f_gv f_ib f_ob f_strmp f_flush f_sp f_vhere f_vlast f_vhbuf].
      rewrite mem_rep_pullk.
      entailer!.
      unfold m_left. rewrite P4, P5. reflexivity.
    + (* PULLBYTE *)
      Intros.
      assert (K4: (j < 4)%nat).
      { destruct (Nat.lt_ge_cases j 4); auto. lia. }
      assert (HH: 0 <= m_have (pullk j m) <= Int.max_signed) by (unfold m_have; rewrite P3, P10; lia).
      forward_if.
      * (* no input: leave *)
        forward. forward.
        assert (E: needbits (e_bits here + k) m = set_leave (pullk j m)).
        { rewrite <- H0.
          replace (4 - j)%nat with (S (3 - j)) by lia. rewrite needbits_f_S.
          destruct (m_bits (pullk j m) <? e_bits here + k) eqn:Ebn; [ | lia].
          destruct (m_have (pullk j m) =? 0) eqn:Eh; [ reflexivity | lia]. }
        rewrite E. unfold loop_state_h, loop_locals. cbn [f_gv f_ib f_ob f_strmp f_flush f_sp f_vhere f_vlast f_vhbuf].
        replace (mem_rep (Fr gv shs strmp sp headp winp hsh xb nb cb ib ob gsh tsh dt vres vhere vlast vhbuf flush) (set_leave (pullk j m))) with (mem_rep (Fr gv shs strmp sp headp winp hsh xb nb cb ib ob gsh tsh dt vres vhere vlast vhbuf flush) m)
          by (rewrite <- (mem_rep_pullk (Fr gv shs strmp sp headp winp hsh xb nb cb ib ob gsh tsh dt vres vhere vlast vhbuf flush) j m); reflexivity).
        entailer!.
        unfold m_left. mnorm_goal. rewrite P3, P4, P5, P6, P7, P8. repeat split; auto.
      * (* pull a byte *)
        forward.
        destruct ib as [ | ish ip ilo inb ic]; cbn [in_ptr in_rep].
        { (* no input object: have = 0 *)
          exfalso.
          assert (m_have (pullk j m) = 0); [ | lia].
          unfold m_have. rewrite P3, P10.
          match goal with H: in_ok InNull (m_inp m) |- _ => unfold in_ok in H; rewrite H in * end.
          rewrite Zlength_nil in *. lia. }
        assert (Hj: 0 <= m_nx (pullk j m) < Zlength (m_inp m)).
        { match goal with H: m_have (pullk j m) <> 0 |- _ => revert H end. revert HH.
          unfold m_have. rewrite P3, P10. intros. lia. }
        match goal with H: in_ok (InBuf _ _ _ _ _) _ |- _ =>
          pose proof (in_byte _ _ _ _ _ _ (m_nx (pullk j m)) H Hj) as HBYTE;
          pose proof H as HINOK;
          destruct H as (Hish & Hip & Hilo & Hinb & Hic & Hinbm & Hsub & Hbytes) end.
        unfold mem_rep. cbn [in_ptr in_rep f_ib f_gv f_ob]. Intros.
        assert_PROP (field_compatible (tarray tuchar inb) [] ip) by entailer!.
        forward. forward.
        assert (HIX: 0 <= ilo + m_nx (pullk j m) < inb) by lia.
        rewrite (offset_val_field_address_tuchar inb (ilo + m_nx (pullk j m)) ip) by (auto; lia).
        pose proof (bytes_ok_Znth _ _ Hbytes Hj) as HBR.
        forward.
        { rewrite HBYTE. entailer!. rep_lia. }
        rewrite HBYTE.
        forward.
        { entailer!. change (Int.unsigned Int64.iwordsize') with 64. lia. }
        forward.
        unfold nbv_pre. Exists (S j).
        unfold nbv_inv. cbn [f_gv f_ib f_ob f_strmp f_flush f_sp f_vhere f_vlast f_vhbuf in_ptr].
        rewrite !pullk_S.
        unfold mem_rep. frame_simpl_goal.
        entailer!.
        match goal with H: needbits_f (4 - j) _ (pullk j m) = needbits _ m |- _ => rename H into HNB end.
        match goal with H: m_bits (pullk j m) = (m_bits m + 8 * Z.of_nat j)%Z |- _ => rename H into HBK end.
        match goal with H: m_have (pullk j m) <> 0 |- _ => rename H into HHV end.
        match goal with H: m_bits (pullk j m) < _ |- _ => rename H into HBN end.
        assert (HBX: 0 <= m_bits (pullk j m) + 8 < 2 ^ 32) by lia.
        split; [ | split; [ | split; [ | split; [ | split]]]].
        -- rewrite <- HNB. replace (4 - j)%nat with (S (4 - S j)) by lia. rewrite needbits_f_S.
          rewrite (proj2 (Z.ltb_lt _ _) HBN). rewrite (proj2 (Z.eqb_neq _ _) HHV). reflexivity.
        -- unfold pull. mnorm_goal. unfold u32. rewrite Z.mod_small by lia. rewrite HBK, Nat2Z.inj_succ. lia.
        -- rewrite <- (offset_val_field_address_tuchar (Zlength ic) (ilo + m_nx (pullk j m)) ip) by (auto; lia).
          unfold pull. mnorm_goal. rewrite offset_offset_val. f_equal. lia.
        -- unfold m_have, pull. mnorm_goal. f_equal. f_equal. lia.
        -- unfold pull. mnorm_goal. rewrite P3. f_equal. apply hold_add_eq; [ | lia].
          pose proof (bytes_ok_Znth _ _ Hbytes Hj). lia.
        -- unfold pull. mnorm_goal. unfold u32. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma semax_needbits_var17 {Espec: OracleKind} (F: frame) (m: mst) (here: entry) (k: Z):
  mwf m -> m_leave m = 0 -> entry_ok here -> 0 <= e_bits here <= 15 -> 0 <= k <= 7 ->
  semax Delta_cases5 (loop_state_h F m (ent here)) (needbits_var k _t'303 _t'66 _t'302)
    (normal_ret_assert (loop_state_h F (needbits (e_bits here + k) m) (ent here))).
Proof.
  intros W HL HE Hb Hk.
  pose proof (mw_bits _ W) as WB. pose proof (mw_nx _ W) as WNX. pose proof (mw_inp _ W) as WINP.
  unfold needbits_var, pullbyte_body.
  abbreviate_semax.
  forward_loop (nbv_pre F m here k)
    break: (loop_state_h F (needbits (e_bits here + k) m) (ent here)).
  - unfold nbv_pre. Exists 0%nat. unfold loop_state_h, nbv_inv, loop_locals. simpl pullk. entailer!.
  - unfold nbv_pre. Intros j.
    destruct (pullk_fields j m) as (P1&P2&P3&P4&P5&P6&P7&P8&P9&P10).
    destruct F as [gv shs strmp sp headp winp hsh xb nb cb ib ob gsh tsh dt vres vhere vlast vhbuf flush].
    unfold nbv_inv. cbn [f_gv f_ib f_ob f_strmp f_flush f_sp f_vhere f_vlast f_vhbuf]. Intros.
    destruct HE as (Eo & Eb & Ev).
    assert (HB: 0 <= m_bits (pullk j m) <= 71) by lia.
    unfold ent. forward.
    { entailer!. rep_lia. }
    match goal with |- semax _ (PROPx ?P (LOCALx (_ :: ?Q) (SEPx ?R))) _ _ =>
      forward_if (PROPx ((m_bits (pullk j m) < e_bits here + k)%Z :: P) (LOCALx Q (SEPx R))) end.
    + (* bits < n: go on *)
      forward. entailer!.
    + (* bits >= n: the loop ends *)
      forward.
      assert (E: needbits (e_bits here + k) m = pullk j m).
      { rewrite <- H0. apply needbits_f_ge. lia. }
      rewrite E. unfold loop_state_h, loop_locals. cbn [f_gv f_ib f_ob f_strmp f_flush f_sp f_vhere f_vlast f_vhbuf].
      rewrite mem_rep_pullk.
      entailer!.
      unfold m_left. rewrite P4, P5. reflexivity.
    + (* PULLBYTE *)
      Intros.
      assert (K4: (j < 4)%nat).
      { destruct (Nat.lt_ge_cases j 4); auto. lia. }
      assert (HH: 0 <= m_have (pullk j m) <= Int.max_signed) by (unfold m_have; rewrite P3, P10; lia).
      forward_if.
      * (* no input: leave *)
        forward. forward.
        assert (E: needbits (e_bits here + k) m = set_leave (pullk j m)).
        { rewrite <- H0.
          replace (4 - j)%nat with (S (3 - j)) by lia. rewrite needbits_f_S.
          destruct (m_bits (pullk j m) <? e_bits here + k) eqn:Ebn; [ | lia].
          destruct (m_have (pullk j m) =? 0) eqn:Eh; [ reflexivity | lia]. }
        rewrite E. unfold loop_state_h, loop_locals. cbn [f_gv f_ib f_ob f_strmp f_flush f_sp f_vhere f_vlast f_vhbuf].
        replace (mem_rep (Fr gv shs strmp sp headp winp hsh xb nb cb ib ob gsh tsh dt vres vhere vlast vhbuf flush) (set_leave (pullk j m))) with (mem_rep (Fr gv shs strmp sp headp winp hsh xb nb cb ib ob gsh tsh dt vres vhere vlast vhbuf flush) m)
          by (rewrite <- (mem_rep_pullk (Fr gv shs strmp sp headp winp hsh xb nb cb ib ob gsh tsh dt vres vhere vlast vhbuf flush) j m); reflexivity).
        entailer!.
        unfold m_left. mnorm_goal. rewrite P3, P4, P5, P6, P7, P8. repeat split; auto.
      * (* pull a byte *)
        forward.
        destruct ib as [ | ish ip ilo inb ic]; cbn [in_ptr in_rep].
        { (* no input object: have = 0 *)
          exfalso.
          assert (m_have (pullk j m) = 0); [ | lia].
          unfold m_have. rewrite P3, P10.
          match goal with H: in_ok InNull (m_inp m) |- _ => unfold in_ok in H; rewrite H in * end.
          rewrite Zlength_nil in *. lia. }
        assert (Hj: 0 <= m_nx (pullk j m) < Zlength (m_inp m)).
        { match goal with H: m_have (pullk j m) <> 0 |- _ => revert H end. revert HH.
          unfold m_have. rewrite P3, P10. intros. lia. }
        match goal with H: in_ok (InBuf _ _ _ _ _) _ |- _ =>
          pose proof (in_byte _ _ _ _ _ _ (m_nx (pullk j m)) H Hj) as HBYTE;
          pose proof H as HINOK;
          destruct H as (Hish & Hip & Hilo & Hinb & Hic & Hinbm & Hsub & Hbytes) end.
        unfold mem_rep. cbn [in_ptr in_rep f_ib f_gv f_ob]. Intros.
        assert_PROP (field_compatible (tarray tuchar inb) [] ip) by entailer!.
        forward. forward.
        assert (HIX: 0 <= ilo + m_nx (pullk j m) < inb) by lia.
        rewrite (offset_val_field_address_tuchar inb (ilo + m_nx (pullk j m)) ip) by (auto; lia).
        pose proof (bytes_ok_Znth _ _ Hbytes Hj) as HBR.
        forward.
        { rewrite HBYTE. entailer!. rep_lia. }
        rewrite HBYTE.
        forward.
        { entailer!. change (Int.unsigned Int64.iwordsize') with 64. lia. }
        forward.
        unfold nbv_pre. Exists (S j).
        unfold nbv_inv. cbn [f_gv f_ib f_ob f_strmp f_flush f_sp f_vhere f_vlast f_vhbuf in_ptr].
        rewrite !pullk_S.
        unfold mem_rep. frame_simpl_goal.
        entailer!.
        match goal with H: needbits_f (4 - j) _ (pullk j m) = needbits _ m |- _ => rename H into HNB end.
        match goal with H: m_bits (pullk j m) = (m_bits m + 8 * Z.of_nat j)%Z |- _ => rename H into HBK end.
        match goal with H: m_have (pullk j m) <> 0 |- _ => rename H into HHV end.
        match goal with H: m_bits (pullk j m) < _ |- _ => rename H into HBN end.
        assert (HBX: 0 <= m_bits (pullk j m) + 8 < 2 ^ 32) by lia.
        split; [ | split; [ | split; [ | split; [ | split]]]].
        -- rewrite <- HNB. replace (4 - j)%nat with (S (4 - S j)) by lia. rewrite needbits_f_S.
          rewrite (proj2 (Z.ltb_lt _ _) HBN). rewrite (proj2 (Z.eqb_neq _ _) HHV). reflexivity.
        -- unfold pull. mnorm_goal. unfold u32. rewrite Z.mod_small by lia. rewrite HBK, Nat2Z.inj_succ. lia.
        -- rewrite <- (offset_val_field_address_tuchar (Zlength ic) (ilo + m_nx (pullk j m)) ip) by (auto; lia).
          unfold pull. mnorm_goal. rewrite offset_offset_val. f_equal. lia.
        -- unfold m_have, pull. mnorm_goal. f_equal. f_equal. lia.
        -- unfold pull. mnorm_goal. rewrite P3. f_equal. apply hold_add_eq; [ | lia].
          pose proof (bytes_ok_Znth _ _ Hbytes Hj). lia.
        -- unfold pull. mnorm_goal. unfold u32. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma semax_needbits_var18 {Espec: OracleKind} (F: frame) (m: mst) (here: entry) (k: Z):
  mwf m -> m_leave m = 0 -> entry_ok here -> 0 <= e_bits here <= 15 -> 0 <= k <= 7 ->
  semax Delta_cases5 (loop_state_h F m (ent here)) (needbits_var k _t'299 _t'67 _t'298)
    (normal_ret_assert (loop_state_h F (needbits (e_bits here + k) m) (ent here))).
Proof.
  intros W HL HE Hb Hk.
  pose proof (mw_bits _ W) as WB. pose proof (mw_nx _ W) as WNX. pose proof (mw_inp _ W) as WINP.
  unfold needbits_var, pullbyte_body.
  abbreviate_semax.
  forward_loop (nbv_pre F m here k)
    break: (loop_state_h F (needbits (e_bits here + k) m) (ent here)).
  - unfold nbv_pre. Exists 0%nat. unfold loop_state_h, nbv_inv, loop_locals. simpl pullk. entailer!.
  - unfold nbv_pre. Intros j.
    destruct (pullk_fields j m) as (P1&P2&P3&P4&P5&P6&P7&P8&P9&P10).
    destruct F as [gv shs strmp sp headp winp hsh xb nb cb ib ob gsh tsh dt vres vhere vlast vhbuf flush].
    unfold nbv_inv. cbn [f_gv f_ib f_ob f_strmp f_flush f_sp f_vhere f_vlast f_vhbuf]. Intros.
    destruct HE as (Eo & Eb & Ev).
    assert (HB: 0 <= m_bits (pullk j m) <= 71) by lia.
    unfold ent. forward.
    { entailer!. rep_lia. }
    match goal with |- semax _ (PROPx ?P (LOCALx (_ :: ?Q) (SEPx ?R))) _ _ =>
      forward_if (PROPx ((m_bits (pullk j m) < e_bits here + k)%Z :: P) (LOCALx Q (SEPx R))) end.
    + (* bits < n: go on *)
      forward. entailer!.
    + (* bits >= n: the loop ends *)
      forward.
      assert (E: needbits (e_bits here + k) m = pullk j m).
      { rewrite <- H0. apply needbits_f_ge. lia. }
      rewrite E. unfold loop_state_h, loop_locals. cbn [f_gv f_ib f_ob f_strmp f_flush f_sp f_vhere f_vlast f_vhbuf].
      rewrite mem_rep_pullk.
      entailer!.
      unfold m_left. rewrite P4, P5. reflexivity.
    + (* PULLBYTE *)
      Intros.
      assert (K4: (j < 4)%nat).
      { destruct (Nat.lt_ge_cases j 4); auto. lia. }
      assert (HH: 0 <= m_have (pullk j m) <= Int.max_signed) by (unfold m_have; rewrite P3, P10; lia).
      forward_if.
      * (* no input: leave *)
        forward. forward.
        assert (E: needbits (e_bits here + k) m = set_leave (pullk j m)).
        { rewrite <- H0.
          replace (4 - j)%nat with (S (3 - j)) by lia. rewrite needbits_f_S.
          destruct (m_bits (pullk j m) <? e_bits here + k) eqn:Ebn; [ | lia].
          destruct (m_have (pullk j m) =? 0) eqn:Eh; [ reflexivity | lia]. }
        rewrite E. unfold loop_state_h, loop_locals. cbn [f_gv f_ib f_ob f_strmp f_flush f_sp f_vhere f_vlast f_vhbuf].
        replace (mem_rep (Fr gv shs strmp sp headp winp hsh xb nb cb ib ob gsh tsh dt vres vhere vlast vhbuf flush) (set_leave (pullk j m))) with (mem_rep (Fr gv shs strmp sp headp winp hsh xb nb cb ib ob gsh tsh dt vres vhere vlast vhbuf flush) m)
          by (rewrite <- (mem_rep_pullk (Fr gv shs strmp sp headp winp hsh xb nb cb ib ob gsh tsh dt vres vhere vlast vhbuf flush) j m); reflexivity).
        entailer!.
        unfold m_left. mnorm_goal. rewrite P3, P4, P5, P6, P7, P8. repeat split; auto.
      * (* pull a byte *)
        forward.
        destruct ib as [ | ish ip ilo inb ic]; cbn [in_ptr in_rep].
        { (* no input object: have = 0 *)
          exfalso.
          assert (m_have (pullk j m) = 0); [ | lia].
          unfold m_have. rewrite P3, P10.
          match goal with H: in_ok InNull (m_inp m) |- _ => unfold in_ok in H; rewrite H in * end.
          rewrite Zlength_nil in *. lia. }
        assert (Hj: 0 <= m_nx (pullk j m) < Zlength (m_inp m)).
        { match goal with H: m_have (pullk j m) <> 0 |- _ => revert H end. revert HH.
          unfold m_have. rewrite P3, P10. intros. lia. }
        match goal with H: in_ok (InBuf _ _ _ _ _) _ |- _ =>
          pose proof (in_byte _ _ _ _ _ _ (m_nx (pullk j m)) H Hj) as HBYTE;
          pose proof H as HINOK;
          destruct H as (Hish & Hip & Hilo & Hinb & Hic & Hinbm & Hsub & Hbytes) end.
        unfold mem_rep. cbn [in_ptr in_rep f_ib f_gv f_ob]. Intros.
        assert_PROP (field_compatible (tarray tuchar inb) [] ip) by entailer!.
        forward. forward.
        assert (HIX: 0 <= ilo + m_nx (pullk j m) < inb) by lia.
        rewrite (offset_val_field_address_tuchar inb (ilo + m_nx (pullk j m)) ip) by (auto; lia).
        pose proof (bytes_ok_Znth _ _ Hbytes Hj) as HBR.
        forward.
        { rewrite HBYTE. entailer!. rep_lia. }
        rewrite HBYTE.
        forward.
        { entailer!. change (Int.unsigned Int64.iwordsize') with 64. lia. }
        forward.
        unfold nbv_pre. Exists (S j).
        unfold nbv_inv. cbn [f_gv f_ib f_ob f_strmp f_flush f_sp f_vhere f_vlast f_vhbuf in_ptr].
        rewrite !pullk_S.
        unfold mem_rep. frame_simpl_goal.
        entailer!.
        match goal with H: needbits_f (4 - j) _ (pullk j m) = needbits _ m |- _ => rename H into HNB end.
        match goal with H: m_bits (pullk j m) = (m_bits m + 8 * Z.of_nat j)%Z |- _ => rename H into HBK end.
        match goal with H: m_have (pullk j m) <> 0 |- _ => rename H into HHV end.
        match goal with H: m_bits (pullk j m) < _ |- _ => rename H into HBN end.
        assert (HBX: 0 <= m_bits (pullk j m) + 8 < 2 ^ 32) by lia.
        split; [ | split; [ | split; [ | split; [ | split]]]].
        -- rewrite <- HNB. replace (4 - j)%nat with (S (4 - S j)) by lia. rewrite needbits_f_S.
          rewrite (proj2 (Z.ltb_lt _ _) HBN). rewrite (proj2 (Z.eqb_neq _ _) HHV). reflexivity.
        -- unfold pull. mnorm_goal. unfold u32. rewrite Z.mod_small by lia. rewrite HBK, Nat2Z.inj_succ. lia.
        -- rewrite <- (offset_val_field_address_tuchar (Zlength ic) (ilo + m_nx (pullk j m)) ip) by (auto; lia).
          unfold pull. mnorm_goal. rewrite offset_offset_val. f_equal. lia.
        -- unfold m_have, pull. mnorm_goal. f_equal. f_equal. lia.
        -- unfold pull. mnorm_goal. rewrite P3. f_equal. apply hold_add_eq; [ | lia].
          pose proof (bytes_ok_Znth _ _ Hbytes Hj). lia.
        -- unfold pull. mnorm_goal. unfold u32. rewrite Z.mod_small by lia. reflexivity.
Qed.

