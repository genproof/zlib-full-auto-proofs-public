(* RT-H: case EXLEN (index 4) of inflate() with the partial header hd6 framed (RTHCase.case_ok6):
   FEXTRA: NEEDBITS(16), state->length, head->extra_len (phase 4), CRC2, INITBITS; else head->extra = Z_NULL
   (h_xp := false); state->mode = EXTRA; falls into EXTRA. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.roundtrip.RTHSpec.
Require Import Zlib.proof.roundtrip.RTHCase.
Require Import Zlib.proof.roundtrip.RTHEx6Kit.
Require Import Zlib.proof.inflate.MwfLemmas.
Require Import Zlib.proof.inflate.Steps2.
Require Import Zlib.proof.roundtrip.RTHNeedBits1_5.
Require Import Zlib.proof.roundtrip.RTHExHdrCrc5.
Require Import Zlib.proof.roundtrip.RTHModeKit5.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.inflate.CaseEXLEN5.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Lemma exlen_A_ok6 {Espec: OracleKind} (F: frame) (m1: mst) : mwf m1 ->
  semax Delta_cases5 (loop_stateH F m1) exlen_A (normal_ret_assert (loop_stateH F (ex_m2 m1))).
Proof.
  intros W1. unfold exlen_A, ex_m2.
  rewrite loop_state_exH. unfold ex_stateH. abbreviate_semax.
  forward.
  rewrite loop_state_exH. unfold ex_stateH. x_simplH.
  entailer!. cbn [i_length m_s upd_s set_m_s set_i_length].
  pose proof (mw_hold _ W1) as HH. unfold lrange in HH.
  rewrite repr_u32, Int64.Z_mod_modulus_eq, Z.mod_small by rep_lia. cancel.
Qed.

Lemma exlen_C_ok6 {Espec: OracleKind} (F: frame) (m3: mst) : frame_ok F -> mwf m3 ->
  semax Delta_cases5 (loop_stateH F m3) exlen_C
    (normal_ret_assert (loop_stateH F (crc_if m3 (hbytes2 (m_hold m3))))).
Proof. intros FOK W. rewrite exlen_C_eq. apply semax_crcblock_EXLENH; auto. Qed.

Lemma exlen_D_ok6 {Espec: OracleKind} (F: frame) (m: mst) :
  semax Delta_cases5 (loop_stateH F m) exlen_D (normal_ret_assert (loop_stateH F (initbits m))).
Proof.
  unfold exlen_D. apply semax_dowhile0. unfold loop_stateH. abbreviate_semax.
  change (mem_repH F (initbits m)) with (mem_repH F m).
  forward. forward. entailer!. apply derives_refl.
Qed.

Lemma hd6_exlen_set6 (F: frame) (m1: mst) (vt vtm vxf vos vhc: val) (lx ln lc: list val):
  i_mode (m_s m1) = IM.EXLEN -> fextra (m_s m1) = true -> hinv6 (m_s m1) (m_h m1) ->
  (1 <= hph (m_s m1) -> vt = zv (h_text (m_h m1))) ->
  (2 <= hph (m_s m1) -> vtm = lv (h_time (m_h m1))) ->
  (3 <= hph (m_s m1) -> vxf = zv (h_xflags (m_h m1)) /\ vos = zv (h_os (m_h m1))) ->
  bufok6 lx (h_extra_max (m_h m1)) (cx6 (m_s m1) (m_h m1)) (h_xbuf (m_h m1)) ->
  bufok6 ln (h_name_max (m_h m1)) (cn6 (m_s m1) (m_h m1)) (h_nbuf (m_h m1)) ->
  bufok6 lc (h_comm_max (m_h m1)) (cc6 (m_s m1) (m_h m1)) (h_cbuf (m_h m1)) ->
  data_at (f_hsh F) t_head
  (vt, (vtm, (vxf, (vos, (if h_xp (m_h m1) then f_xb F else nullval,
   (Vint (Int.repr (m_hold m1)), (Vint (Int.repr (h_extra_max (m_h m1))),
   (if h_np (m_h m1) then f_nb F else nullval, (Vint (Int.repr (h_name_max (m_h m1))),
   (if h_cp (m_h m1) then f_cb F else nullval, (Vint (Int.repr (h_comm_max (m_h m1))),
   (vhc, Vint (Int.repr (h_done (m_h m1))))))))))))))) (f_headp F) *
  hbuf6 (f_xb F) (h_extra_max (m_h m1)) lx * hbuf6 (f_nb F) (h_name_max (m_h m1)) ln *
  hbuf6 (f_cb F) (h_comm_max (m_h m1)) lc
  |-- hd6 F (set_mode (upd_h (upd_s m1 (fun s => set_i_length s (u32 (m_hold m1))))
                        (fun h => set_h_extra_len h (u32 (m_hold m1)))) IM.EXTRA).
Proof.
  intros HM Hx HI H2 H3 H4 H7 H8 H9.
  assert (P3: hph (m_s m1) = 3) by (unfold hph; rewrite HM; reflexivity).
  assert (C1: cx6 (m_s m1) (m_h m1) = 0) by (unfold cx6; rewrite HM; reflexivity).
  assert (C2: cn6 (m_s m1) (m_h m1) = 0) by (unfold cn6; rewrite HM; reflexivity).
  assert (C3: cc6 (m_s m1) (m_h m1) = 0) by (unfold cc6; rewrite HM; reflexivity).
  rewrite P3 in *. rewrite C1 in H7. rewrite C2 in H8. rewrite C3 in H9.
  destruct (H4 ltac:(lia)) as [E3 E4]. specialize (H2 ltac:(lia)). specialize (H3 ltac:(lia)).
  pose proof (u32_range (m_hold m1)) as U.
  destruct HI as (D0 & _).
  unfold hd6, head_rep6, head_rep6p.
  cbn [set_mode upd_h upd_s set_m_s set_m_h m_s m_h set_i_length set_i_mode set_h_extra_len
       h_xp h_np h_cp h_extra_max h_name_max h_comm_max h_done h_text h_time h_xflags h_os h_extra_len h_hcrc
       h_xbuf h_nbuf h_cbuf i_mode i_flags i_length].
  apply andp_right.
  { apply prop_right. unfold hinv6.
    cbn [set_mode upd_h upd_s set_m_s set_m_h m_s m_h set_i_length set_i_mode set_h_extra_len
       h_xp h_np h_cp h_extra_max h_name_max h_comm_max h_done h_text h_time h_xflags h_os h_extra_len h_hcrc
       h_xbuf h_nbuf h_cbuf i_mode i_flags i_length].
    refine (conj D0 (conj _ (conj _ (conj _ _)))).
    - intros _ _. exact Hx.
    - intros _ _. unfold urange in U; lia.
    - intros E. exfalso. compute in E. discriminate E.
    - intros E. exfalso. compute in E. discriminate E. }
  Exists vt vtm vxf vos (Vint (Int.repr (m_hold m1))) vhc lx ln lc.
  apply andp_right; [ | apply derives_refl].
  apply prop_right.
  set (s4 := set_i_mode (set_i_length (m_s m1) (u32 (m_hold m1))) IM.EXTRA).
  set (h4 := set_h_extra_len (m_h m1) (u32 (m_hold m1))).
  assert (Q4: hph s4 = 4) by reflexivity.
  assert (X4: cx6 s4 h4 = 0).
  { unfold cx6. change (i_mode s4) with IM.EXTRA. rewrite Z.eqb_refl.
    change (h_xp h4) with (h_xp (m_h m1)). change (h_extra_len h4) with (u32 (m_hold m1)).
    change (i_length s4) with (u32 (m_hold m1)). change (h_extra_max h4) with (h_extra_max (m_h m1)).
    destruct H7 as (_ & B7 & _). rewrite Z.sub_diag. destruct (h_xp (m_h m1)); lia. }
  assert (N4: cn6 s4 h4 = 0) by reflexivity.
  assert (K4: cc6 s4 h4 = 0) by reflexivity.
  rewrite Q4, X4, N4, K4.
  refine (conj (fun _ => H2) (conj (fun _ => H3) (conj (fun _ => conj E3 E4) (conj _ (conj _ (conj H7 (conj H8 H9))))))).
  - intros _ _. rewrite repr_u32. reflexivity.
  - intros Hc. lia.
Qed.

Lemma exlen_B_ok6 {Espec: OracleKind} (F: frame) (m1: mst) : frame_ok F -> mwf m1 ->
  m_mode m1 = IM.EXLEN -> i_head (m_s m1) = true -> fextra (m_s m1) = true ->
  semax Delta_cases5 (loop_stateH F (ex_m2 m1) * (fun _ => hd6 F m1)) exlen_B
    (normal_ret_assert (loop_stateH F (ex_m3 m1) * (fun _ => hd6 F (set_mode (ex_m3 m1) IM.EXTRA)))).
Proof.
  intros Hok W1 HM Eh Hx. pose proof Hok as (HS1 & HS2 & HS3 & HS4).
  pose proof (mw_hold _ W1) as HH. unfold lrange in HH.
  unfold exlen_B, ex_m3, ex_m2. rewrite Eh.
  rewrite !loop_state_exH. unfold ex_stateH. x_simplH. xp_simpl.
  rewrite !PQR_tok.
  unfold head_partH. cbn [upd_h upd_s set_m_s set_m_h m_s m_h i_head set_i_length]. rewrite !Eh. unfold hnoneH.
  simpl app.
  abbreviate_semax.
  unfold hd6 at 1; unfold head_rep6, head_rep6p. Intros vt vtm vxf vos vxl vhc lx ln lc.
  forward. forward_if.
  2: { assert_PROP (field_compatible t_head [] (f_headp F)) as FC by entailer!.
       exfalso. destruct FC as [P _]. match goal with E: _ = nullval |- _ => rewrite E in P end. exact P. }
  forward. forward.
  rewrite Int64.Z_mod_modulus_eq, Z.mod_small by rep_lia.
  sep_apply (hd6_exlen_set6 F m1 vt vtm vxf vos vhc lx ln lc HM Hx H1 H2 H3 H4 H7 H8 H9).
  entailer!.
Qed.

Lemma hd6_exlen_skip6 (F: frame) (m: mst) (vt vtm vxf vos vxl vhc: val) (lx ln lc: list val):
  i_mode (m_s m) = IM.EXLEN -> fextra (m_s m) = false -> hinv6 (m_s m) (m_h m) ->
  (1 <= hph (m_s m) -> vt = zv (h_text (m_h m))) ->
  (2 <= hph (m_s m) -> vtm = lv (h_time (m_h m))) ->
  (3 <= hph (m_s m) -> vxf = zv (h_xflags (m_h m)) /\ vos = zv (h_os (m_h m))) ->
  bufok6 lx (h_extra_max (m_h m)) (cx6 (m_s m) (m_h m)) (h_xbuf (m_h m)) ->
  bufok6 ln (h_name_max (m_h m)) (cn6 (m_s m) (m_h m)) (h_nbuf (m_h m)) ->
  bufok6 lc (h_comm_max (m_h m)) (cc6 (m_s m) (m_h m)) (h_cbuf (m_h m)) ->
  data_at (f_hsh F) t_head
  (vt, (vtm, (vxf, (vos, (nullval,
   (vxl, (Vint (Int.repr (h_extra_max (m_h m))),
   (if h_np (m_h m) then f_nb F else nullval, (Vint (Int.repr (h_name_max (m_h m))),
   (if h_cp (m_h m) then f_cb F else nullval, (Vint (Int.repr (h_comm_max (m_h m))),
   (vhc, Vint (Int.repr (h_done (m_h m))))))))))))))) (f_headp F) *
  hbuf6 (f_xb F) (h_extra_max (m_h m)) lx * hbuf6 (f_nb F) (h_name_max (m_h m)) ln *
  hbuf6 (f_cb F) (h_comm_max (m_h m)) lc
  |-- hd6 F (set_mode (upd_h m (fun h => set_h_xp h false)) IM.EXTRA).
Proof.
  intros HM Hx HI H2 H3 H4 H7 H8 H9.
  assert (P3: hph (m_s m) = 3) by (unfold hph; rewrite HM; reflexivity).
  assert (C1: cx6 (m_s m) (m_h m) = 0) by (unfold cx6; rewrite HM; reflexivity).
  assert (C2: cn6 (m_s m) (m_h m) = 0) by (unfold cn6; rewrite HM; reflexivity).
  assert (C3: cc6 (m_s m) (m_h m) = 0) by (unfold cc6; rewrite HM; reflexivity).
  rewrite P3 in *. rewrite C1 in H7. rewrite C2 in H8. rewrite C3 in H9.
  destruct (H4 ltac:(lia)) as [E3 E4]. specialize (H2 ltac:(lia)). specialize (H3 ltac:(lia)).
  destruct HI as (D0 & _).
  unfold hd6, head_rep6, head_rep6p.
  cbn [set_mode upd_h upd_s set_m_s set_m_h m_s m_h set_i_mode set_h_xp
       h_xp h_np h_cp h_extra_max h_name_max h_comm_max h_done h_text h_time h_xflags h_os h_extra_len h_hcrc
       h_xbuf h_nbuf h_cbuf].
  apply andp_right.
  { apply prop_right. unfold hinv6.
    cbn [set_mode upd_h upd_s set_m_s set_m_h m_s m_h set_i_mode set_h_xp h_xp h_done i_mode].
    refine (conj D0 (conj _ (conj _ (conj _ _)))).
    - intros _ E. discriminate E.
    - intros _ E. discriminate E.
    - intros E. exfalso. compute in E. discriminate E.
    - intros E. exfalso. compute in E. discriminate E. }
  Exists vt vtm vxf vos vxl vhc lx ln lc.
  apply andp_right; [ | apply derives_refl].
  apply prop_right.
  set (s4 := set_i_mode (m_s m) IM.EXTRA).
  set (h4 := set_h_xp (m_h m) false).
  assert (Q4: hph s4 = 4) by reflexivity.
  assert (X4: cx6 s4 h4 = 0) by reflexivity.
  assert (N4: cn6 s4 h4 = 0) by reflexivity.
  assert (K4: cc6 s4 h4 = 0) by reflexivity.
  assert (F4: fextra s4 = false) by exact Hx.
  rewrite Q4, X4, N4, K4, F4.
  refine (conj (fun _ => H2) (conj (fun _ => H3) (conj (fun _ => conj E3 E4) (conj _ (conj _ (conj H7 (conj H8 H9))))))).
  - intros _ E. discriminate E.
  - intros Hc. lia.
Qed.

(* the header-frame of a case body *)
Lemma body_frame6 {Espec: OracleKind} (F: frame) (m: mst) (Y: Z) (i: nat):
  semax Delta_cases5 (loop_stateH F m * (fun _ => hd6 F m)) (case_body i)
    (overridePost (fall_post6 F m Y) (switch_ret_assert (case_post6 F m))) ->
  semax Delta_cases5 (loop_stateH F m * (fun _ => hdr_tok F m * hd6 F m)) (case_body i)
    (overridePost (fall_post6 F m Y * (fun _ => hdr_tok F m))
       (frame_ret_assert (switch_ret_assert (case_post6 F m)) (fun _ => hdr_tok F m))).
Proof.
  intros H.
  apply semax_pre with (P' := (loop_stateH F m * (fun _ => hd6 F m)) * (fun _ => hdr_tok F m)).
  { apply andp_left2. intros rho. simpl. cancel. }
  eapply semax_post; [ | | | | apply semax_frame; [ | exact H]].
  - intros rho. simpl. apply andp_left2. apply derives_refl.
  - intros rho. simpl. apply andp_left2. apply derives_refl.
  - intros rho. simpl. apply andp_left2. apply derives_refl.
  - intros vl rho. simpl. apply andp_left2. apply derives_refl.
  - intros rho te _. reflexivity.
Qed.

Definition exlen_mid6 (F: frame) (m: mst) : environ -> mpred :=
  EX m4: mst,
    !! (stepf2 (f_flush F) lenfix_list distfix_list m =
        stepf2 (f_flush F) lenfix_list distfix_list (set_mode m4 IM.EXTRA) /\
        mwf3 (set_mode m4 IM.EXTRA) /\ m_leave m4 = 0 /\ hd_ok F m4 /\ hdr_tok F m4 = hdr_tok F m /\
        i_head (m_s m4) = true) &&
    (loop_stateH F m4 * (fun _ => hd6 F (set_mode m4 IM.EXTRA))).

Lemma crc_if_keep: forall m d,
  i_flags (m_s (crc_if m d)) = i_flags (m_s m) /\ i_length (m_s (crc_if m d)) = i_length (m_s m) /\
  m_h (crc_if m d) = m_h m.
Proof. intros. unfold crc_if. destruct (andb _ _); auto. Qed.

Lemma exlen_rest_ok6 {Espec: OracleKind} (F: frame) (m1: mst) :
  frame_ok F -> mwf m1 -> m_mode m1 = IM.EXLEN -> i_head (m_s m1) = true -> fextra (m_s m1) = true ->
  semax Delta_cases5 (loop_stateH F m1 * (fun _ => hd6 F m1)) exlen_rest
    (normal_ret_assert (loop_stateH F (exlen_fin m1) * (fun _ => hd6 F (set_mode (exlen_fin m1) IM.EXTRA)))).
Proof.
  intros Hok W1 HM1 Eh Hx.
  rewrite exlen_rest_eq.
  eapply semax_seq'; [apply semax_frame_lsH; apply exlen_A_ok6; exact W1 | ].
  eapply semax_seq'; [apply exlen_B_ok6; auto | ].
  assert (E: exlen_fin m1 = initbits (crc_if (ex_m3 m1) (hbytes2 (m_hold (ex_m3 m1))))).
  { unfold exlen_fin, ex_m3, ex_m2. cbv zeta.
    change (i_head (m_s (upd_s m1 (fun s => set_i_length s (u32 (m_hold m1)))))) with (i_head (m_s m1)).
    destruct (i_head (m_s m1)); reflexivity. }
  assert (EH: hd6 F (set_mode (exlen_fin m1) IM.EXTRA) = hd6 F (set_mode (ex_m3 m1) IM.EXTRA)).
  { rewrite E. destruct (crc_if_keep (ex_m3 m1) (hbytes2 (m_hold (ex_m3 m1)))) as (A & B & C).
    apply hd6_ext; [reflexivity | exact A | exact B | exact C]. }
  rewrite EH, E.
  eapply semax_seq'; [apply semax_frame_lsH; apply exlen_C_ok6; auto; apply mwf_ex_m3; auto | ].
  apply semax_frame_lsH; apply exlen_D_ok6.
Qed.

Lemma rth_exlen6 {Espec: OracleKind} (F: frame) : frame_ok5 F -> case_ok6 F IM.EXTRA 5 -> case_ok6 F IM.EXLEN 4.
Proof.
  intros [Hok HF] HY m n HM HL [W W2] HD Eh HP.
  pose proof Hok as (HS1 & HS2 & HS3 & HS4).
  assert (Hhm: hdr_mode (m_mode m) = true) by (rewrite HM; reflexivity).
  apply (case_fallthrough6 F m n IM.EXTRA 4); [lia | reflexivity | exact Hhm | exact HP | exact HY | ].
  apply body_frame6.
  case_body_stmt.
  apply semax_seq with (Q := exlen_mid6 F m).
  2: { unfold exlen_mid6. apply extract_exists_pre. intros m4.
       apply semax_extract_prop. intros (E & W4 & L4 & HD4 & HT4 & Eh4).
       eapply ConseqFacts.semax_post''; [ | apply semax_frame_lsH; apply semax_store_mode5H].
       unfold fall_post6. Exists (set_mode m4 IM.EXTRA).
       apply andp_right; [ | apply andp_left2; apply derives_refl].
       apply prop_right. split; [exact E | ]. split; [reflexivity | ]. split; [exact L4 | ].
       split; [exact W4 | ]. split; [exact HD4 | ]. split; [exact HT4 | exact Eh4]. }
  rewrite loop_state_exH. unfold ex_stateH. rewrite PQR_tok. simpl app. abbreviate_semax.
  forward.
  forward_if.
  - (* FEXTRA *)
    assert (Hf: Z.land (i_flags (m_s m)) 1024 <> 0) by (apply and_repr_nz; [rep_lia | exact H1]).
    destruct (step_exlen_set (f_flush F) m HM Hf) as [EL E0].
    apply semax_pre with (P' := loop_stateH F m * (fun _ => hd6 F m)).
    { rewrite loop_state_exH. unfold ex_stateH. rewrite PQR_tok. simpl app. entailer!. }
    eapply (semax_needbits_seq6 F m 16 (hd6 F m)).
    + apply semax_needbits_EXLEN5H; auto; lia.
    + exact W.
    + lia.
    + intros L1. pose proof (hpass_brk _ _ _ _ Hhm HP (EL L1)) as L0. lia.
    + apply semax_extract_prop. intros HL1.
      specialize (E0 HL1).
      pose proof (mwf_needbits 16 m W ltac:(lia)) as W1.
      destruct (needbits_sh 16 m) as [S1 H1s].
      assert (HM1: m_mode (needbits 16 m) = IM.EXLEN) by (unfold m_mode; rewrite S1; exact HM).
      destruct (mwf3_exlen_fin _ W1 HM1) as [W4 L4].
      assert (K4: hkey (exlen_fin (needbits 16 m)) = hkey m) by (rewrite exlen_fin_hkey; apply hkey_needbits).
      pose proof (hkey_hd_ok F m _ K4 HD) as HD4. pose proof (hkey_hdr_tok F m _ K4) as HT4.
      assert (Eh4: i_head (m_s (exlen_fin (needbits 16 m))) = true).
      { unfold hkey in K4. injection K4. intros. congruence. }
      assert (Eh1: i_head (m_s (needbits 16 m)) = true) by (rewrite S1; exact Eh).
      assert (Hx1: fextra (m_s (needbits 16 m)) = true).
      { unfold fextra. rewrite S1. apply negb_true_iff. apply Z.eqb_neq. exact Hf. }
      rewrite (hd6_ext F m (needbits 16 m)) by (rewrite ?S1, ?H1s; reflexivity).
      set (m1 := needbits 16 m) in *. clearbody m1.
      eapply ConseqFacts.semax_post''; [ | apply (exlen_rest_ok6 F m1 Hok W1 HM1 Eh1 Hx1) ].
      unfold POSTCONDITION, abbreviate. simpl RA_normal.
      unfold exlen_mid6. Exists (exlen_fin m1).
      apply andp_right; [ | apply andp_left2; apply derives_refl].
      apply prop_right. split; [exact E0 | ]. split; [exact W4 | ]. split; [exact (eq_trans L4 HL1) | ].
      split; [exact HD4 | ]. split; [exact HT4 | exact Eh4].
  - (* no FEXTRA *)
    assert (Hf: Z.land (i_flags (m_s m)) 1024 = 0) by (apply and_repr_zero; [rep_lia | exact H1]).
    pose proof (step_exlen_skip (f_flush F) m HM Hf) as E.
    destruct (mwf3_exlen_skip m W HM) as [W4 L4].
    destruct (exlen_skip_hd F m HD) as [HD4 HT4].
    assert (X: exlen_skip m = upd_h m (fun h => set_h_xp h false)) by (unfold exlen_skip; rewrite Eh; reflexivity).
    assert (Hx0: fextra (m_s m) = false) by (unfold fextra; rewrite Hf; reflexivity).
    rewrite Eh. unfold head_partH. rewrite Eh. unfold hnoneH.
    unfold hd6 at 1; unfold head_rep6, head_rep6p. Intros vt vtm vxf vos vxl vhc lx ln lc.
    forward.
    forward_if.
    2: { assert_PROP (field_compatible t_head [] (f_headp F)) as FC by entailer!.
         exfalso. destruct FC as [P _]. match goal with E: _ = nullval |- _ => rewrite E in P end. exact P. }
    forward. forward.
    unfold exlen_mid6. Exists (exlen_skip m).
    apply andp_right.
    { apply prop_right. split; [exact E | ]. split; [exact W4 | ]. split; [exact (eq_trans L4 HL) | ].
      split; [exact HD4 | ]. split; [exact HT4 | ]. rewrite X. exact Eh. }
    rewrite X, loop_state_exH. unfold ex_stateH. rewrite PQR_tok. simpl app. rewrite mem_x_upd_h.
    unfold head_partH. cbn [upd_h set_m_h m_s m_h]. rewrite Eh. unfold hnoneH.
    sep_apply (hd6_exlen_skip6 F m vt vtm vxf vos vxl vhc lx ln lc HM Hx0 H2 H3 H4 H5 H8 H9 H10).
    entailer!.
Qed.
