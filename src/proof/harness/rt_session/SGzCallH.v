(* Law rt_session, sessions with a gzip header: one inflate() call from a state inside the gzip header
   (SGzDefs.sgz_call_h_stmt): rt_gzip_header's header passes (G2ICases, G2IHLoop) for any flush and output space,
   then, when the header ends in the call, the decode theory (RTIGW) on the data. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.rt_session.SGzDefs.
Require Import Zlib.proof.harness.rt_session.SGzTail.
Require Import Zlib.proof.harness.rt_gzip_header.G2IHLoop.
Require Import Zlib.proof.harness.rt_gzip_header.G2ICases.
Require Import Zlib.proof.harness.rt_gzip_header.G2IBridge.
Require Zlib.proof.uncompr.URunFrame.
Require Zlib.proof.harness.inflate_header.IHTCall.
Import ListNotations.
Local Open Scope Z_scope.

Module DD := Zlib.proof.rfc1951.DecodeDefs.

(* the exit inside the header for any flush (G2IHLoop.g2l_fin is the Z_FINISH form): a machine that wrote nothing,
   has no window and returns Z_OK leaves with Z_OK or Z_BUF_ERROR (Z_BUF_ERROR when it consumed no input), adds the
   bytes it consumed to total_in and keeps the fields of the header passes *)
Lemma sgz_fin flush m : i_wsize (m_s m) = 0 -> m_out m = m_aout m -> m_ow m = [] -> m_tout m = 0 ->
  i_total (m_s m) = 0 -> m_ret m = Z_OK ->
  let res := leave_fin flush m in
  (r_ret res = Z_BUF_ERROR \/ r_ret res = Z_OK) /\
  (u32 (m_in m - m_have m) = 0 -> r_ret res = Z_BUF_ERROR) /\
  m_tin (r_m res) = u64 (m_tin m + u32 (m_in m - m_have m)) /\
  m_ow (r_m res) = [] /\ m_sow (r_m res) = 0 /\ m_aout (r_m res) = m_aout m /\
  m_snx (r_m res) = m_nx m /\ m_inp (r_m res) = m_inp m /\ m_tout (r_m res) = 0 /\ m_h (r_m res) = m_h m /\
  i_mode (m_s (r_m res)) = m_mode m /\ i_last (m_s (r_m res)) = i_last (m_s m) /\
  i_check (m_s (r_m res)) = i_check (m_s m) /\ i_flags (m_s (r_m res)) = i_flags (m_s m) /\
  i_length (m_s (r_m res)) = i_length (m_s m) /\ i_wrap (m_s (r_m res)) = i_wrap (m_s m) /\
  i_head (m_s (r_m res)) = i_head (m_s m) /\ i_wsize (m_s (r_m res)) = 0 /\ i_total (m_s (r_m res)) = 0 /\
  i_wbits (m_s (r_m res)) = i_wbits (m_s m) /\
  i_hold (m_s (r_m res)) = m_hold m /\ i_bits (m_s (r_m res)) = m_bits m.
Proof.
  intros Ws O W T Tt R. cbv zeta. unfold leave_fin.
  rewrite (Zlib.proof.harness.inflate_header.IHTCall.ihl_leave_ok flush m Ws O W).
  cbv zeta.
  assert (Eo: u32 (m_out (restore m) - m_left (restore m)) = 0).
  { unfold m_left. cbn. rewrite O, W, Zlength_nil, Z.sub_0_r, Z.sub_diag. reflexivity. }
  rewrite Eo. rewrite andb_false_r.
  cbn. unfold m_mode. rewrite Ws, Tt, T, W, R. cbn.
  split; [destruct (_ || _)%bool; [left|right]; reflexivity|].
  split; [unfold m_have; intros E; rewrite E; reflexivity|].
  repeat split; auto.
Qed.

(* the TYPE loop head after the header passes, for any input object src and any blocks bs: G2IBridge.g2_type_kd,
   whose proof does not use the stream's shape *)
Lemma sgz_type_kd wb gh xfl bs src h0 pos inp aout tin m :
  9 <= wb <= 15 -> (xfl = 0 \/ xfl = 2 \/ xfl = 4) ->
  g2h_ok (g2_g gh xfl) -> lay2 (g2_g gh xfl) src ->
  ih_nh (g2_g gh xfl) = Zlength (F.gz_bytes (g2_H gh xfl)) ->
  rtigw_ok (g2_G gh xfl wb bs src) ->
  ctx2 src pos inp -> Zlength inp <= 4294967295 -> 0 <= aout <= 4294967295 -> lrange tin ->
  Km2 (g2_g gh xfl) src h0 wb pos inp aout tin m -> m_leave m = 0 ->
  m_mode m = Zlib.proof.inflate.Model.TYPE ->
  Kd (g2_G gh xfl wb bs src) pos inp [] (g2_mc m) /\ mwf3W (g2_mc m).
Proof.
  intros Hwb Hxfl Hg Hl Hnh Hok Hc Hinp Hao Htin Hm Hlv Hmd.
  destruct Hm as [K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11].
  destruct K8 as [C1 C2 C3 C4 C5 C6 C7 C8].
  destruct K11 as (F1 & F2 & F3 & F4 & F5 & F6).
  assert (Hj : i_check (m_s m) = 0 /\ fg (g2_g gh xfl) (m_s m) /\ i_last (m_s m) = 0 /\
               pos + m_nx m = ih_nh (g2_g gh xfl) /\ m_hold m = 0 /\ m_bits m = 0).
  { unfold m_mode in Hmd.
    destruct K9; try (rewrite Hmd in *; discriminate); tauto. }
  destruct Hj as (J1 & J2 & J3 & J4 & J5 & J6).
  destruct Hc as (Hp0 & Hpl & Hpi).
  assert (Hmd' : i_mode (m_s m) = Zlib.proof.inflate.Model.TYPE) by exact Hmd.
  assert (Hc : Zlength (F.gz_bytes (g2_H gh xfl)) <= Zlength src) by lia.
  set (G := g2_G gh xfl wb bs src).
  assert (HD0 : DD.D0 G = 8 * Zlength (F.gz_bytes (g2_H gh xfl))) by reflexivity.
  assert (Hsrc : DD.dc_src G = src) by reflexivity.
  assert (Hpr : DD.produced G [] = []) by reflexivity.
  assert (Hm0 : m_mode (g2_mc m) = Zlib.proof.inflate.Model.TYPE) by exact Hmd.
  assert (Hac : DD.after_check G (m_mode (g2_mc m)) = false) by (rewrite Hm0; reflexivity).
  pose proof (Zlength_nonneg inp).
  split; [|split; [|split]].
  - constructor; cbn [g2_mc set_m_h m_s m_h m_inp m_nx m_hold m_bits m_ow m_tout m_out m_aout m_ret m_leave].
    + exact K1.
    + rewrite J5, J6, K3, J4, Hnh. split.
      * unfold DD.hold_ok. rewrite Hsrc. split; [|split].
        -- pose proof (Zlength_nonneg (F.gz_bytes (g2_H gh xfl))). lia.
        -- exact Hc.
        -- rewrite Z.sub_0_r, sublist_nil. reflexivity.
      * right. right. left. split; [left; exact Hmd'|].
        exists 0. split; [unfold DD.nblk; pose proof (Zlength_nonneg (DD.dc_bs G)); lia|].
        split; [unfold DD.bpos; cbn [Z.to_nat]; rewrite HD0; destruct (DD.dc_bs G); cbn [DD.epos]; lia|].
        split; [reflexivity|]. split; [lia|]. rewrite J3. reflexivity.
    + split; [|split; [reflexivity|split]].
      * exists wb. split.
        { rewrite C1. left.
          transitivity (Some (Zlib.proof.inflate_api.ApiModel.reset2_wrap 6 wb, wb)).
          - apply Zlib.proof.rfc1951.DecodeDefs.init_wrap_wb_of. apply g2_reset2. exact Hwb.
          - unfold Zlib.proof.inflate_api.ApiModel.reset2_wrap.
            destruct (Z.eqb_spec wb 0); [lia | reflexivity]. }
        intros E. rewrite Hmd' in E. discriminate.
      * intros _. rewrite C5. cbn. lia.
      * intros _ _ _. exact J2.
    + intros _. left. split; [exact C3|reflexivity].
    + intros _ N1 N2 N3 N4. rewrite Hmd', K3. cbn -[DD.produced DD.chkv].
      rewrite Hpr. split; [|split].
      * rewrite J1. reflexivity.
      * rewrite C4. reflexivity.
      * exists []. reflexivity.
    + rewrite Hac, K5, Hpr. reflexivity.
    + rewrite Hac. exact K4.
    + rewrite Hm0, Hlv, K6. reflexivity.
  - change Int.max_unsigned with 4294967295.
    constructor; cbn [g2_mc set_m_h m_s m_h m_inp m_nx m_hold m_bits m_ow m_tout m_out m_aout m_ret m_leave
      m_in m_adler m_tin m_snx m_sow]; unfold urange, lrange;
      change Int.max_unsigned with 4294967295; change Int64.max_unsigned with 18446744073709551615.
    + constructor; rewrite Hmd'; unfold decode_mode; intros;
        repeat match goal with E : _ \/ _ |- _ => destruct E end;
        repeat match goal with |- _ /\ _ => split end; try intros;
        match goal with E : _ = _ |- _ => discriminate E end.
    + exact K10.
    + exact g2_hc_hwf.
    + rewrite K1. split; [lia|]. rewrite Hpi. apply Forall_sublist. exact (l2_bytes _ _ Hl).
    + lia.
    + rewrite K1. exact K2.
    + rewrite K3, Zlength_nil. split; [lia | constructor].
    + rewrite J5. lia.
    + rewrite J6. lia.
    + rewrite K1. exact F2.
    + rewrite K4. lia.
    + rewrite K6. cbv; split; discriminate.
    + rewrite Hlv. lia.
    + exact F6.
    + rewrite F3. exact Htin.
    + rewrite K5. lia.
    + rewrite F4, K1. lia.
    + rewrite F5, K3, Zlength_nil. lia.
    + left. exact K4.
  - change (m_s (g2_mc m)) with (m_s m). constructor; rewrite ?Hmd'; unfold decode_mode; intros;
      repeat match goal with E : _ \/ _ |- _ => destruct E end;
      match goal with E : _ = _ |- _ => discriminate E end.
  - split; intros E; rewrite Hm0 in E; discriminate.
Qed.

Lemma sgz_call_h : sgz_call_h_stmt.
Proof.
  intros gh xfl wb bs src h0 pos L z inp flush res W HOK XFL GOK LY NH RW HW8 TZ PH LV SW ZF AOZ LI CX RUN.
  cbv zeta.
  destruct PH as (JC & JJ & PN & NT).
  set (g := g2_g gh xfl) in *. set (h0' := set_h_done h0 0) in *.
  set (m0 := m_init z L inp) in *.
  pose proof (Zlength_nonneg inp) as LI0.
  assert (M0s: m_s m0 = l_s L).
  { unfold m0, m_init. cbv zeta. rewrite (proj2 (Z.eqb_neq _ _) NT). reflexivity. }
  assert (M0m: m_mode m0 <> Zlib.proof.inflate.Model.TYPE) by (unfold m_mode; rewrite M0s; exact NT).
  pose proof ZF as (_ & AO & TI & _ & _ & AD).
  assert (K0: Km2 g src h0' wb pos inp (zf_ao z) (zf_tin z) m0).
  { destruct LV as (_ & SWF & _).
    constructor; unfold m0, m_init; cbv zeta; rewrite (proj2 (Z.eqb_neq _ _) NT);
      cbn [m_s m_h m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave m_adler m_tin m_tout m_snx m_sow].
    - reflexivity.
    - lia.
    - reflexivity.
    - reflexivity.
    - exact TZ.
    - reflexivity.
    - left; reflexivity.
    - exact JC.
    - rewrite Z.add_0_r. exact JJ.
    - exact SWF.
    - unfold lrange. repeat split; auto; lia. }
  pose proof (URunFrame.run2_frame _ _ _ _ _
                ltac:(unfold URunFrame.vmode; rewrite M0s; pose proof (g2_J2_vmode _ _ _ _ _ _ _ _ JJ);
                      unfold BAD, Zlib.proof.inflate.Model.TYPE in *; lia) RUN)
    as (FI & FA & FS & FH & _).
  destruct RUN as (o0 & LP & RO).
  destruct (g2l_loop g2_cases g src h0' wb pos inp (zf_ao z) (zf_tin z) flush m0 o0 GOK HW8 LY CX LP K0 eq_refl M0m)
    as [(m' & -> & K' & L1) | (mT & KT & LT & MT & LPT)].
  - (* the call leaves inside the header *)
    pose proof (jc2_wsize _ _ _ _ (km2_jc _ _ _ _ _ _ _ _ _ K')) as Ws.
    pose proof (jc2_total _ _ _ _ (km2_jc _ _ _ _ _ _ _ _ _ K')) as Tt.
    inversion RO as [U Wn | ]; subst res.
    { exfalso. rewrite (Zlib.proof.harness.inflate_header.IHTCall.ihl_leave_ok flush m' Ws
                          (km2_out _ _ _ _ _ _ _ _ _ K') (km2_ow _ _ _ _ _ _ _ _ _ K')) in U. discriminate. }
    destruct (sgz_fin flush m' Ws (km2_out _ _ _ _ _ _ _ _ _ K') (km2_ow _ _ _ _ _ _ _ _ _ K')
                (km2_tout _ _ _ _ _ _ _ _ _ K') Tt (km2_ret _ _ _ _ _ _ _ _ _ K'))
      as (R1 & R0 & RT & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17 &
          R18 & R19 & R20).
    destruct (km2_lv _ _ _ _ _ _ _ _ _ K') as [E|(_ & NX & PL & NT')]; [rewrite E in L1; discriminate|].
    destruct (km2_fr _ _ _ _ _ _ _ _ _ K') as (FA' & FIN & FTI & _).
    right. rewrite R5, R2, R3, R4, FA', NX.
    split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
    left. split; [tauto|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact R7|].
    pose proof (km2_jc _ _ _ _ _ _ _ _ _ K') as JC'.
    split; [split; [|split; [|split]]|].
    + destruct JC' as [A1 A2 A3 A4 A5 A6 A7 A8].
      constructor; rewrite ?R8, ?R14, ?R15, ?R16, ?R17, ?R18; auto.
    + rewrite R19, R20, R8. rewrite <- NX.
      apply (g2_J2_proj _ _ _ _ _ _ _ _ _ (km2_j _ _ _ _ _ _ _ _ _ K')); auto.
    + rewrite <- NX. exact PL.
    + rewrite R9. exact NT'.
    + intros Z0.
      assert (EI: u32 (m_in m' - m_have m') = 0).
      { unfold m_have. rewrite FIN, (km2_inp _ _ _ _ _ _ _ _ _ K'), NX, Z0. reflexivity. }
      split; [exact (R0 EI)|]. rewrite RT, EI, FTI, Z.add_0_r. unfold u64. apply Z.mod_small.
      change Int64.max_unsigned with 18446744073709551615 in TI. lia.
  - (* the header ends in the call: the rest is a decode call from the TYPE loop head *)
    destruct (km2_fr _ _ _ _ _ _ _ _ _ KT) as (FAT & _).
    set (G := g2_G gh xfl wb bs src) in *.
    destruct (sgz_type_kd wb gh xfl bs src h0' pos inp (zf_ao z) (zf_tin z) mT W XFL GOK LY NH RW CX LI
                ltac:(change Int.max_unsigned with 4294967295 in AO; lia) TI KT LT MT) as (KD & MW).
    assert (HK: SK.hk mT) by (right; rewrite MT; apply g2_hdr_mode_after; lia).
    destruct CX as (P0 & PL & IE).
    destruct (sgz_tail G pos inp [] flush mT o0 res RW P0 PL IE KD MW LT HK
                ltac:(exists []; reflexivity) ltac:(exists (full G); reflexivity) LPT RO)
      as [MEM | (RC & SNX & SOW & AOT & HH & FR & DV & EN)].
    { left. exact MEM. }
    cbn [app] in FR, DV, EN.
    destruct (g2_J2_type _ _ _ _ _ _ _ _ (km2_j _ _ _ _ _ _ _ _ _ KT) MT) as (DN & EP).
    pose proof (km2_nx _ _ _ _ _ _ _ _ _ KT) as NXT.
    pose proof (km2_jc _ _ _ _ _ _ _ _ _ KT) as JCT.
    right. split; [exact SNX|]. split; [exact SOW|]. split; [rewrite AOT; exact FAT|].
    right. split; [intros Z0; lia|]. split; [exact RC|]. split; [exact FR|].
    split; [|exact EN].
    split; [exact DV|]. split; [exact FR|].
    split; [rewrite FH, M0s; exact (jc2_head _ _ _ _ JC)|].
    rewrite HH. split; [exact DN|].
    split; [exact (jc2_xmax _ _ _ _ JCT)|]. split; [exact (jc2_nmax _ _ _ _ JCT)|]. exact (jc2_cmax _ _ _ _ JCT).
Qed.
