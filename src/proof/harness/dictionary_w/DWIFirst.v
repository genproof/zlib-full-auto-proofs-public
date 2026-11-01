(* The laws rt_dictionary and api_dict_id: the first inflate() call on a zlib stream with FDICT after
   inflateInit2(strm, wb), wb the stream's window bits (9..15): HEAD (any valid FLG with FDICT), DICTID, DICT,
   Z_NEED_DICT after exactly 6 bytes, for any flush and any input that starts with those 6 bytes.
   roundtrip/RTIZDictFirst.v proves the same after inflateInit2(strm, 0); here HEAD finds state->wbits = wb
   already set, and its test 'len > state->wbits' passes since len = wb. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.roundtrip.RTIZDictDefs.
Require Import Zlib.proof.roundtrip.RTIZDictFirst.
Import ListNotations.
Local Open Scope Z_scope.

(* HEAD's 'if (state->wbits == 0) state->wbits = len' leaves a nonzero wbits unchanged *)
Lemma dwi_keep_wbits m wb : i_wbits (m_s m) = wb -> wb <> 0 ->
  upd_s m (fun s => set_i_wbits s (if i_wbits s =? 0 then wb else i_wbits s)) = upd_s m (fun s => set_i_wbits s wb).
Proof.
  intros H Hw. unfold upd_s. rewrite H. replace (wb =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hw).
  reflexivity.
Qed.

(* HEAD with state->wbits = wb: the header is accepted, wbits stays wb, next DICTID *)
Lemma dwi_head fl fx dx s h wb flg t ao nin adl msg tin tout :
  i_mode s = HEAD -> i_wrap s = 5 -> i_wbits s = wb -> i_head s = false -> 9 <= wb <= 15 ->
  RF.zflg_ok wb true flg ->
  stepf2 fl fx dx (MS s h (RF.zcmf wb :: flg :: t) ao 0 [] 0 0 nin ao Z_OK 0 adl msg tin tout 0 0) =
  IBrk (MS (set_i_mode (set_i_check (set_i_flags (set_i_dmax (set_i_wbits s wb) (2 ^ wb)) 0) 1) DICTID)
           h (RF.zcmf wb :: flg :: t) ao 2 [] 0 0 nin ao Z_OK 0 1 msg tin tout 0 0).
Proof.
  intros Hm Hw Hb Hh Hwb Hf.
  pose proof (rtz_hdr wb flg Hwb Hf) as (H1 & H2 & H3 & H4 & Hc). cbv zeta in H1, H2, H3, H4.
  pose proof Hf as (Hf8 & _).
  unfold stepf2, step2. unfold m_mode. cbn [m_s]. rewrite Hm. change (HEAD =? HEAD) with true. cbv beta iota.
  unfold c_HEAD2. cbn [m_s]. rewrite Hw. change (5 =? 0) with false. cbv beta iota.
  rewrite rtz_nb16 by lia.
  cbn [m_s m_leave m_hold m_bits set_mode upd_s set_m_s set_m_hold set_m_bits set_m_adler dropbits initbits].
  rewrite Hh, Hw. change (0 =? 1) with false. change (Z.land 5 2 =? 0) with true. change (Z.land 5 1 =? 0) with false.
  cbv beta iota.
  cbn [m_s m_leave m_hold m_bits set_mode upd_s set_m_s set_m_hold set_m_bits set_m_adler dropbits initbits negb andb orb].
  rewrite H1, H2. cbn [negb orb]. rewrite H3, Hb.
  replace (wb =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (wb <? wb) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (15 <? wb) with false by (symmetry; apply Z.ltb_ge; lia). cbn [orb negb andb].
  rewrite H4. rewrite dwi_keep_wbits by (first [exact Hb | lia]).
  cbn [m_s m_leave m_hold m_bits set_mode upd_s set_m_s set_m_hold set_m_bits set_m_adler dropbits initbits].
  reflexivity.
Qed.

(* inflateInit2(strm, wb) for 9 <= wb <= 15: the zlib wrapper (wrap 5) with state->wbits = wb *)
Lemma dwi_init_s sp wb : 9 <= wb <= 15 -> l_s (init_live sp wb) = init_s 5 wb.
Proof.
  intros Hwb. unfold init_live, reset2_wb. cbn [l_s].
  replace (wb <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (Z.shiftr wb 4) with 0
    by (symmetry; rewrite Z.shiftr_div_pow2 by lia; apply Z.div_small; change (2 ^ 4) with 16; lia).
  replace (wb <? 48) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (Z.land wb 15) with wb
    by (symmetry; change 15 with (Z.ones 4); rewrite Z.land_ones by lia; apply Z.mod_small; change (2 ^ 4) with 16; lia).
  replace (wb =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  replace ((8 <=? wb) && (wb <=? 15)) with true
    by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.leb_le]; lia).
  reflexivity.
Qed.

(* the state after Z_NEED_DICT, inflateInit2's windowBits wb (9..15): RTIZDictDefs.zd_nd with the zlib wrapper
   5 that inflateInit2(wb) stores (zd_nd has 13, the wrapper of inflateInit2(0) after patch F8) *)
Definition dw_nd (wb id: Z) (s: istate) : Prop :=
  i_mode s = DICT /\ i_wrap s = 5 /\ i_head s = false /\ i_last s = 0 /\ i_havedict s = 0 /\
  i_total s = 0 /\ i_wsize s = 0 /\ i_whave s = 0 /\ i_wnext s = 0 /\ i_win s = false /\ i_wdata s = [] /\
  i_wbits s = wb /\ i_flags s = 0 /\ i_hold s = 0 /\ i_bits s = 0 /\ i_check s = id.

Lemma dwi_first : forall flush wb flg id rest z sp res,
  9 <= wb <= 15 -> RF.zflg_ok wb true flg -> 0 <= id < 2 ^ 32 -> zf_ok z ->
  run2 flush lenfix_list distfix_list (m_init z (init_live sp wb) ([RF.zcmf wb; flg] ++ be_bytes id 4 ++ rest)) res ->
  r_ret res = Z_NEED_DICT /\ m_snx (r_m res) = 6 /\ m_ow (r_m res) = [] /\ m_sow (r_m res) = 0 /\
  m_aout (r_m res) = zf_ao z /\ m_tout (r_m res) = zf_tout z /\ m_adler (r_m res) = id /\
  dw_nd wb id (m_s (r_m res)).
Proof.
  intros flush wb flg id rest z sp res Hwb Hf Hid Hz (o & HL & Ho).
  assert (E : be_bytes id 4 = [Z.shiftr id (8 * 3) mod 256; Z.shiftr id (8 * 2) mod 256; Z.shiftr id (8 * 1) mod 256;
                               Z.shiftr id (8 * 0) mod 256]) by reflexivity.
  rewrite E in HL. cbn [app] in HL.
  pose proof (Z.mod_pos_bound (Z.shiftr id (8 * 3)) 256 ltac:(lia)) as B0.
  pose proof (Z.mod_pos_bound (Z.shiftr id (8 * 2)) 256 ltac:(lia)) as B1.
  pose proof (Z.mod_pos_bound (Z.shiftr id (8 * 1)) 256 ltac:(lia)) as B2.
  pose proof (Z.mod_pos_bound (Z.shiftr id (8 * 0)) 256 ltac:(lia)) as B3.
  pose proof (rtz_id id Hid) as Q.
  set (i0 := Z.shiftr id (8 * 3) mod 256) in *. set (i1 := Z.shiftr id (8 * 2) mod 256) in *.
  set (i2 := Z.shiftr id (8 * 1) mod 256) in *. set (i3 := Z.shiftr id (8 * 0) mod 256) in *.
  clearbody i0 i1 i2 i3. clear E.
  pose proof (dwi_init_s sp wb Hwb) as Hs.
  unfold m_init in HL. rewrite Hs in HL. set (h0 := l_h (init_live sp wb)) in HL. clearbody h0.
  assert (F : i_mode (init_s 5 wb) = HEAD /\ i_wrap (init_s 5 wb) = 5 /\ i_wbits (init_s 5 wb) = wb /\
              i_head (init_s 5 wb) = false /\ i_havedict (init_s 5 wb) = 0 /\ i_hold (init_s 5 wb) = 0 /\
              i_bits (init_s 5 wb) = 0 /\ i_last (init_s 5 wb) = 0 /\ i_total (init_s 5 wb) = 0 /\
              i_wsize (init_s 5 wb) = 0 /\ i_whave (init_s 5 wb) = 0 /\ i_wnext (init_s 5 wb) = 0 /\
              i_win (init_s 5 wb) = false /\ i_wdata (init_s 5 wb) = []).
  { unfold init_s, reset2_s, reset2_wrap. replace (wb =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    repeat split. }
  remember (init_s 5 wb) as s0 eqn:Es. clear Es Hs.
  destruct F as (Fm & Fw & Fb & Fh & Fd & Fho & Fbi & Fl & Ft & Fws & Fwh & Fwn & Fwi & Fwd).
  cbv zeta in HL. rewrite Fm in HL. change (HEAD =? Zlib.proof.inflate.Model.TYPE) with false in HL.
  cbv beta iota in HL. rewrite Fho, Fbi in HL.
  inversion HL as [m r m' S1 | m m' S1 L1 | m m' o' S1 L1 HL2]; clear HL;
    rewrite dwi_head in S1 by assumption.
  - discriminate.
  - injection S1 as <-. cbn in L1. discriminate.
  - injection S1 as <-. clear L1.
    destruct (rtz_dictid flush lenfix_list distfix_list
                (set_i_mode (set_i_check (set_i_flags (set_i_dmax (set_i_wbits s0 wb) (2 ^ wb)) 0) 1) DICTID)
                h0 (RF.zcmf wb) flg i0 i1 i2 i3 rest (zf_ao z) (Zlength (RF.zcmf wb :: flg :: i0 :: i1 :: i2 :: i3 :: rest))
                1 (zf_msg z) (zf_tin z) (zf_tout z)) as (tin' & S2);
      [destruct s0; reflexivity | destruct s0; cbn in Fd |- *; exact Fd | auto.. |].
    rewrite Q in S2.
    inversion HL2 as [n r2 n' S3 | n n' S3 L3 | n n' o'' S3 L3 HL3]; clear HL2; rewrite S2 in S3; try discriminate.
    injection S3 as <- <-. subst. cbn in Ho. subst res. cbn [r_ret r_m m_snx m_ow m_sow m_aout m_tout m_adler m_s].
    do 7 (split; [reflexivity|]).
    unfold dw_nd. destruct s0; cbn in *; subst. repeat split; reflexivity.
Qed.
