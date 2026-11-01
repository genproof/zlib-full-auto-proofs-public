(* Law rt_gzip_header on the round-2 harness, inflate side: entering the decode theory (RTIGW) after the header,
   on the machine whose gz_header is the small G2IDefs.g2_hc (the decode theory's machine invariant InvW.mwf3W holds
   Spec5's header invariant hwf, which caps the buffer sizes at 65536; the passes after the header do not read the
   header model, RTH8SimKit).  At the TYPE loop head where the header passes end (in the middle of a call), and at
   the start of a call that begins after the header. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.rt_gzip_header.G2IDefs.
Import ListNotations.
Local Open Scope Z_scope.

Module DD := Zlib.proof.rfc1951.DecodeDefs.
Module RG := Zlib.proof.roundtrip.RTIGDefs.

(* the small header satisfies Spec5's header invariant *)
Lemma g2_hc_hwf : hwf g2_hc.
Proof.
  constructor; cbn; unfold srange, urange, lrange;
    try (split; [reflexivity | constructor]);
    change Int.min_signed with (-2147483648); change Int.max_signed with 2147483647;
    change Int.max_unsigned with 4294967295; change Int64.max_unsigned with 18446744073709551615; lia.
Qed.

(* inflateInit2(16 + wb): wrap 6 (gzip only, bit 3 off: the window size is given), window bits wb *)
Lemma g2_reset2 wb : 9 <= wb <= 15 -> Zlib.proof.inflate_api.ApiModel.reset2_wb (16 + wb) = Some (6, wb).
Proof.
  intros H. assert (E : wb = 9 \/ wb = 10 \/ wb = 11 \/ wb = 12 \/ wb = 13 \/ wb = 14 \/ wb = 15) by lia.
  repeat destruct E as [E|E]; subst wb; reflexivity.
Qed.

(* the TYPE loop head after the header passes (G2IDefs.J2_TYPE) *)
Definition g2_type_kd_stmt : Prop := forall wb gh xfl bs O h0 pos inp aout tin m,
  9 <= wb <= 15 -> (xfl = 0 \/ xfl = 2 \/ xfl = 4) ->
  O = F.stream_bytes (F.WGzip (g2_H gh xfl)) [] bs ->
  g2h_ok (g2_g gh xfl) -> lay2 (g2_g gh xfl) O ->
  ih_nh (g2_g gh xfl) = Zlength (F.gz_bytes (g2_H gh xfl)) ->
  RTIGW.rtigw_ok (g2_G gh xfl wb bs O) ->
  ctx2 O pos inp -> Zlength inp <= 4294967295 -> 0 <= aout <= 4294967295 -> lrange tin ->
  Km2 (g2_g gh xfl) O h0 wb pos inp aout tin m -> m_leave m = 0 ->
  m_mode m = Zlib.proof.inflate.Model.TYPE ->
  Zlib.proof.roundtrip.RTIGDefs.Kd (g2_G gh xfl wb bs O) pos inp [] (g2_mc m) /\ mwf3W (g2_mc m).

(* a call that starts after the header (from RTIGW.rtigw_init_stmt, on the live part with the small header) *)
Definition g2_canon_init_stmt : Prop := forall G pos L z inp,
  RTIGW.rtigw_ok G -> Zlib.proof.roundtrip.RTIGDefs.dinv G pos [] (l_s L) (zf_tout z) -> live_ok8 L -> zf_ok z ->
  zf_ao z <= 4294967295 -> Zlength inp <= 4294967295 -> bytes_ok inp ->
  Zlib.proof.roundtrip.RTIGDefs.Kd G pos inp [] (g2_mc (m_init z L inp)) /\ mwf3W (g2_mc (m_init z L inp)).

(* the TYPE loop head after the header passes: k = 0 of the decode theory (bpos 0 = D0 = the header's bits),
   nothing produced, no window, check 0; the machine invariant with the small header *)
Lemma g2_type_kd : g2_type_kd_stmt.
Proof.
  intros wb gh xfl bs O h0 pos inp aout tin m Hwb Hxfl HO Hg Hl Hnh Hok Hc Hinp Hao Htin Hm Hlv Hmd.
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
  assert (Hc : Zlength (F.gz_bytes (g2_H gh xfl)) <= Zlength O) by lia.
  set (G := g2_G gh xfl wb bs O).
  assert (HD0 : DD.D0 G = 8 * Zlength (F.gz_bytes (g2_H gh xfl))) by reflexivity.
  assert (Hsrc : DD.dc_src G = O) by reflexivity.
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

(* a call that starts after the header: rtigw_init_stmt on the live part whose header is the small one *)
Lemma g2_canon_init : RTIGW.rtigw_init_stmt -> g2_canon_init_stmt.
Proof.
  intros RI G pos L z inp Hok Hd Hl Hz Hao Hinp Hb.
  set (L' := set_l_head L g2_hc (l_headp L) (l_hsh L) (l_xb L) (l_nb L) (l_cb L)).
  assert (E : g2_mc (m_init z L inp) = m_init z L' inp) by reflexivity.
  rewrite E. eapply RI; [exact Hok | exact Hd | | exact Hz | lia | lia | exact Hb].
  destruct Hl as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
  unfold live_ok; cbn [L' set_l_head l_sp l_s l_h l_hsh l_xb l_nb l_cb].
  split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact g2_hc_hwf|].
  split; [exact A5|]. split; [exact A6|]. split; [exact A7|]. split; [|exact A9].
  intros _. split; [|split]; intros X; discriminate X.
Qed.

Theorem g2_bridge : g2_type_kd_stmt /\ (RTIGW.rtigw_init_stmt -> g2_canon_init_stmt).
Proof. exact (conj g2_type_kd g2_canon_init). Qed.
