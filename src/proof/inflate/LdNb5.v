(* LENEXT: NEEDBITS(state->extra) (part of the cases LENEXT/DIST, Cases5_LD.v; definitions and statements in LdKit5.v) *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate.LdKit5.
Require Import Zlib.proof.inflate.NeedBits.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* the state without its extra field *)
Definition ldnb_state_ne (gv: globals) (sp strmp headp winp: val) (s: istate) : mpred :=
  field_at Ews t_state (DOT _strm) strmp sp *
  field_at Ews t_state (DOT _mode) (zv (i_mode s)) sp *
  field_at Ews t_state (DOT _last) (zv (i_last s)) sp *
  field_at Ews t_state (DOT _wrap) (zv (i_wrap s)) sp *
  field_at Ews t_state (DOT _havedict) (zv (i_havedict s)) sp *
  field_at Ews t_state (DOT _flags) (zv (i_flags s)) sp *
  field_at Ews t_state (DOT _dmax) (zv (i_dmax s)) sp *
  field_at Ews t_state (DOT _check) (lv (i_check s)) sp *
  field_at Ews t_state (DOT _total) (lv (i_total s)) sp *
  field_at Ews t_state (DOT _head) (if i_head s then headp else nullval) sp *
  field_at Ews t_state (DOT _wbits) (zv (i_wbits s)) sp *
  field_at Ews t_state (DOT _wsize) (zv (i_wsize s)) sp *
  field_at Ews t_state (DOT _whave) (zv (i_whave s)) sp *
  field_at Ews t_state (DOT _wnext) (zv (i_wnext s)) sp *
  field_at Ews t_state (DOT _window) (if i_win s then winp else nullval) sp *
  field_at Ews t_state (DOT _hold) (lv (i_hold s)) sp *
  field_at Ews t_state (DOT _bits) (zv (i_bits s)) sp *
  field_at Ews t_state (DOT _length) (zv (i_length s)) sp *
  field_at Ews t_state (DOT _offset) (zv (i_offset s)) sp *
  field_at Ews t_state (DOT _lencode) (tref_val gv sp (i_lencode s)) sp *
  field_at Ews t_state (DOT _distcode) (tref_val gv sp (i_distcode s)) sp *
  field_at Ews t_state (DOT _lenbits) (zv (i_lenbits s)) sp *
  field_at Ews t_state (DOT _distbits) (zv (i_distbits s)) sp *
  field_at Ews t_state (DOT _ncode) (zv (i_ncode s)) sp *
  field_at Ews t_state (DOT _nlen) (zv (i_nlen s)) sp *
  field_at Ews t_state (DOT _ndist) (zv (i_ndist s)) sp *
  field_at Ews t_state (DOT _have) (zv (i_have s)) sp *
  field_at Ews t_state (DOT _next) (codes_at sp (i_next s)) sp *
  field_at Ews t_state (DOT _lens) (map (fun z => Vint (Int.repr z)) (i_lens s)) sp *
  field_at_ Ews t_state (DOT _work) sp *
  field_at Ews t_state (DOT _codes) (map ent (i_codes s)) sp *
  field_at Ews t_state (DOT _sane) (zv (i_sane s)) sp *
  field_at Ews t_state (DOT _back) (zv (i_back s)) sp *
  field_at Ews t_state (DOT _was) (zv (i_was s)) sp.

(* the 20th of 35 separating conjuncts to the front (on variables) *)
Lemma ldnb_sepcon_20_35: forall a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35: mpred,
  a1 * a2 * a3 * a4 * a5 * a6 * a7 * a8 * a9 * a10 * a11 * a12 * a13 * a14 * a15 * a16 * a17 * a18 * a19 * a20 * a21 * a22 * a23 * a24 * a25 * a26 * a27 * a28 * a29 * a30 * a31 * a32 * a33 * a34 * a35 =
  a20 * (a1 * a2 * a3 * a4 * a5 * a6 * a7 * a8 * a9 * a10 * a11 * a12 * a13 * a14 * a15 * a16 * a17 * a18 * a19 * a21 * a22 * a23 * a24 * a25 * a26 * a27 * a28 * a29 * a30 * a31 * a32 * a33 * a34 * a35).
Proof.
  intros. apply pred_ext; cancel.
Qed.

Lemma ldnb_state_split: forall gv sp strmp headp winp s,
  state_rep gv sp strmp headp winp s =
  field_at Ews t_state (DOT _extra) (zv (i_extra s)) sp * ldnb_state_ne gv sp strmp headp winp s.
Proof.
  intros. unfold state_rep, ldnb_state_ne. apply ldnb_sepcon_20_35.
Qed.

Definition ldnb_mem_ne (F: frame) (m: mst) : mpred :=
  ldnb_state_ne (f_gv F) (f_sp F) (f_strmp F) (f_headp F) (f_winp F) (m_s m) *
  win_rep (f_winp F) (m_s m) *
  head_part F m *
  strm_rep (f_gv F) (f_shs F) (f_strmp F)
    (in_ptr (f_ib F) (m_snx m)) (zv (Zlength (m_inp m) - m_snx m)) (m_tin m)
    (out_ptr (f_ob F) (m_sow m)) (zv (m_aout m - m_sow m)) (m_tout m)
    (msg_val (f_gv F) (m_msg m)) (f_sp F) (f_dt F) (m_adler m) (f_vres F) *
  in_rep (f_ib F) *
  out_rep (f_ob F) (m_ow m) *
  tables_rep (f_gsh F) (f_gv F) *
  crc_table_at (f_tsh F) (f_gv F).

Lemma ldnb_mem_split: forall F m,
  mem_rep F m = field_at Ews t_state (DOT _extra) (zv (i_extra (m_s m))) (f_sp F) * ldnb_mem_ne F m.
Proof.
  intros. unfold mem_rep, ldnb_mem_ne. rewrite ldnb_state_split.
  apply pred_ext; cancel.
Qed.

Lemma ldnb_le_nb_eq: le_nb =
  Sloop
    (Ssequence
       (Ssequence
          (Sset _t'231 (Efield (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                  (Tstruct _inflate_state noattr)) _extra tuint))
          (Sifthenelse (Ebinop Olt (Etempvar _bits tuint) (Ecast (Etempvar _t'231 tuint) tuint) tint)
             Sskip Sbreak))
       (pullbyte_body _t'77 _t'230))
    Sskip.
Proof. reflexivity. Qed.

Lemma ld_nb_ok : ld_nb_stmt.
Proof.
  intros Espec F m W HMD HL.
  pose proof (mw_bits _ W) as WB. pose proof (mw_nx _ W) as WNX. pose proof (mw_inp _ W) as WINP.
  pose proof (sw_extra _ (mw_s _ W)) as WEX.
  set (n := i_extra (m_s m)).
  assert (Hn: 0 <= n <= 32) by (unfold n; lia).
  rewrite ldnb_le_nb_eq.
  destruct F as [gv shs strmp sp headp winp hsh xb nb cb ib ob gsh tsh dt vres vhere vlast vhbuf flush].
  unfold pullbyte_body, loop_state. frame_simpl.
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
     SEP (mem_rep (Fr gv shs strmp sp headp winp hsh xb nb cb ib ob gsh tsh dt vres vhere vlast vhbuf flush) m; locals_rep (Fr gv shs strmp sp headp winp hsh xb nb cb ib ob gsh tsh dt vres vhere vlast vhbuf flush)))
    break: (loop_state (Fr gv shs strmp sp headp winp hsh xb nb cb ib ob gsh tsh dt vres vhere vlast vhbuf flush) (needbits n m)).
  - Exists 0%nat. simpl pullk. entailer!.
  - Intros k.
    destruct (pullk_fields k m) as (P1&P2&P3&P4&P5&P6&P7&P8&P9&P10).
    assert (HB: 0 <= m_bits (pullk k m) <= 71) by lia.
    rewrite ldnb_mem_split. Intros.
    forward.
    gather_SEP 0 1. rewrite <- ldnb_mem_split.
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROPx ((m_bits (pullk k m) < n)%Z :: P) (LOCALx Q (SEPx R))) end.
    + (* bits < n: go on *)
      forward. entailer!.
    + (* bits >= n: the loop ends *)
      forward.
      assert (E: needbits n m = pullk k m).
      { match goal with H: needbits_f _ _ _ = needbits n m |- _ => rewrite <- H end.
        apply needbits_f_ge. lia. }
      rewrite E. unfold loop_state. rewrite mem_rep_pullk.
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
        rewrite E. unfold loop_state.
        replace (mem_rep (Fr gv shs strmp sp headp winp hsh xb nb cb ib ob gsh tsh dt vres vhere vlast vhbuf flush) (set_leave (pullk k m))) with (mem_rep (Fr gv shs strmp sp headp winp hsh xb nb cb ib ob gsh tsh dt vres vhere vlast vhbuf flush) m)
          by (rewrite <- (mem_rep_pullk (Fr gv shs strmp sp headp winp hsh xb nb cb ib ob gsh tsh dt vres vhere vlast vhbuf flush) k m); reflexivity).
        entailer!.
        unfold m_left. mnorm_goal. rewrite P3, P4, P5, P6, P7, P8. repeat split; auto.
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
        unfold mem_rep. cbn [in_ptr in_rep f_ib f_gv f_ob]. Intros.
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
        unfold mem_rep. frame_simpl_goal.
        entailer!.
        match goal with H: needbits_f (4 - k) n (pullk k m) = needbits n m |- _ => rename H into HNB end.
        match goal with H: m_bits (pullk k m) = (m_bits m + 8 * Z.of_nat k)%Z |- _ => rename H into HBK end.
        match goal with H: m_have (pullk k m) <> 0 |- _ => rename H into HHV end.
        match goal with H: m_bits (pullk k m) < n |- _ => rename H into HBN end.
        assert (HBX: 0 <= m_bits (pullk k m) + 8 < 2 ^ 32) by lia.
        split; [ | split; [ | split; [ | split; [ | split]]]].
        -- rewrite <- HNB. replace (4 - k)%nat with (S (4 - S k)) by lia. rewrite needbits_f_S.
          rewrite (proj2 (Z.ltb_lt _ _) HBN). rewrite (proj2 (Z.eqb_neq _ _) HHV). reflexivity.
        -- unfold pull. mnorm_goal. unfold u32. rewrite Z.mod_small by lia. rewrite HBK, Nat2Z.inj_succ. lia.
        -- rewrite <- (offset_val_field_address_tuchar (Zlength ic) (ilo + m_nx (pullk k m)) ip) by (auto; lia).
          unfold pull. mnorm_goal. rewrite offset_offset_val. f_equal. lia.
        -- unfold m_have, pull. mnorm_goal. f_equal. f_equal. lia.
        -- unfold pull. mnorm_goal. rewrite P3. f_equal. apply hold_add_eq; [ | lia].
          pose proof (bytes_ok_Znth _ _ Hbytes Hj). lia.
        -- unfold pull. mnorm_goal. unfold u32. rewrite Z.mod_small by lia. reflexivity.
  - (* after the loop *)
    unfold loop_state. entailer!.
Qed.
