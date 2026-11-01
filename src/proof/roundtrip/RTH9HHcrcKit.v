(* The breaks of the header case HCRC that round 1 excluded by the header pass (RTH8Spec.hpass8), for the case
   over RTH9WKit.case_ok9v (docs/port-hl/rth9h/hcrc.py patches the ported RTH8CaseHCRC with them): with the flag
   0x0200 set, NEEDBITS(16) runs out of input (the case breaks with leave = 1, still in mode HCRC), or the header
   CRC does not match (the case breaks in mode BAD).  In both the header is the one of the case's start: the
   partial header in mode HCRC, the raw header (done = 0) in mode BAD (RTH9HDefs.hd9a's second disjunct). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.roundtrip.RTHSpec.
Require Import Zlib.proof.roundtrip.RTHCase.
Require Import Zlib.proof.roundtrip.RTH8Spec.
Require Import Zlib.proof.roundtrip.RTH8Defs.
Require Import Zlib.proof.roundtrip.RTH8CaseKit.
Require Import Zlib.proof.roundtrip.RTHCaseHyps5.
Require Import Zlib.proof.inflate.Steps2.
Require Import Zlib.proof.roundtrip.RTHModeKit5.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.adler32.Spec.
Require Import Zlib.proof.inflate.Cases5_HD.
Require Import Zlib.proof.roundtrip.RTHCaseHCRC6.
Require Import Zlib.proof.roundtrip.RTH8CaseHCRC.
Require Import Zlib.proof.roundtrip.RTH9HDefs.
Require Import Zlib.proof.roundtrip.RTH9WKit.
Require Zlib.proof.roundtrip.RTHFTO6.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* the ret_assert of a statement that ends normally in Q or breaks in B (in the combinators Floyd reads) *)
Definition hcrc_ret9 (Q B: environ -> mpred) : ret_assert :=
  overridePost Q (switch_ret_assert (normal_ret_assert B)).

(* the break of HCRC before the header is written, from machine m: the model's machine, with the header of m;
   in a header mode (a leave) the partial header of m is that of the new machine *)
Definition hcrc_brk9 (F: frame) (m: mst) : environ -> mpred :=
  EX m': mst,
    !! (stepf2 (f_flush F) lenfix_list distfix_list m = IBrk m' /\ m_h m' = m_h m /\
        (hdr_mode (m_mode m') = true -> hd6 F m' = hd6 F m)) &&
    loop_stateH F m'.

(* the partial header as the raw one (done is 0: the header is not passed) *)
Lemma hcrc_hd6_raw: forall F m,
  hd6 F m |-- !! (h_done (m_h m) <> 1) && hraw6 (f_hsh F) (f_headp F) (f_xb F) (f_nb F) (f_cb F) (m_h m).
Proof.
  intros F m. unfold hd6, head_rep6, head_rep6p, hraw6, bufok6.
  Intros vt vtm vxf vos vxl vhc lx ln lc.
  Exists vt vtm vxf vos vxl vhc (zv (h_done (m_h m))) lx ln lc.
  match goal with H: hinv6 _ _ |- _ => destruct H as [D _] end.
  entailer!.
Qed.

(* NEEDBITS leaves the partial header alone *)
Lemma hcrc_hd6_needbits: forall F n m, hd6 F (needbits n m) = hd6 F m.
Proof. exact Zlib.proof.roundtrip.RTHFTO6.hd6_needbits. Qed.

(* such a break, with the header of m framed, is the case's break *)
Lemma hcrc_brk9_post: forall F m,
  hcrc_brk9 F m * (fun _ => hd6 F m) |-- RA_normal (case_post9 F m).
Proof.
  intros F m. unfold hcrc_brk9, case_post9, RA_normal, post9.
  rewrite exp_sepcon1. apply exp_left. intros m'. apply exp_right with m'.
  rewrite sepcon_andp_prop'. apply derives_extract_prop. intros (E & Eh & Hd).
  apply andp_right; [apply prop_right; exact E | ].
  apply sepcon_derives; [apply derives_refl | ]. intros rho. unfold hd9.
  destruct (hdr_mode (m_mode m')) eqn:M.
  - rewrite (Hd eq_refl). apply derives_refl.
  - unfold hd9a. apply orp_right2. rewrite Eh. apply hcrc_hd6_raw.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the end of the case: the header written                                                        *)

(* the statements of HCRC after the CRC check: head->hcrc and head->done = 1, check = adler = crc32(0, NULL, 0),
   mode TYPE, break *)
Definition hcrc_rest9 : statement :=
  match case_body 8 with Ssequence _ c => c | _ => Sskip end.

(* from the machine m2 after the CRC check (the model's step of m is hcrc_fin m2), with the partial header of the
   case's start m (done = 0): the case's break in mode TYPE, the header passed (RTH8Spec.head_rep8a, hd9a's first
   disjunct), as round 1's case *)
Lemma hcrc_tail9 {Espec: OracleKind} (F: frame) (m m2: mst):
  frame_ok5 F -> m_mode m = IM.HCRC -> i_head (m_s m) = true -> h_done (m_h m) = 0 ->
  stepf2 (f_flush F) lenfix_list distfix_list m = hcrc_fin m2 -> mwf9 m2 -> m_s m2 = m_s m -> m_h m2 = m_h m ->
  semax Delta_cases5 (loop_stateH F m2 * (fun _ => hd6 F m)) hcrc_rest9
    (overridePost FF (switch_ret_assert (case_post9 F m))).
Proof.
  intros HF0 HM Hh Hdone E W2 Es2 Eh2.
  unfold hcrc_rest9. case_body_stmt.
  assert (Hh2: i_head (m_s m2) = true) by (rewrite Es2; exact Hh).
  assert (ET: stepf2 (f_flush F) lenfix_list distfix_list m =
    IBrk (set_mode (set_m_adler (upd_s (upd_h m2 (fun h => set_h_done (set_h_hcrc h
        (Z.land (Z.shiftr (i_flags (m_s m2)) 9) 1)) 1)) (fun s => set_i_check s 0)) 0) IM.TYPE)).
  { rewrite E; unfold hcrc_fin; rewrite Hh2; reflexivity. }
  assert (HM': i_mode (m_s m) = IM.HCRC) by exact HM.
  assert (Hph: hph (m_s m) = 4) by (unfold hph; rewrite HM'; reflexivity).
  assert (Hcx: cx6 (m_s m) (m_h m) = cxa (m_h m)) by (unfold cx6, cxa; rewrite HM'; reflexivity).
  assert (Hcn: cn6 (m_s m) (m_h m) = cna (m_h m)) by (unfold cn6, cna; rewrite HM'; reflexivity).
  assert (Hcc: cc6 (m_s m) (m_h m) = cca (m_h m)) by (unfold cc6, cca; rewrite HM'; reflexivity).
  rewrite loop_state_hd_eqH. unfold loop_state_hdH. apply start_function_aux1 with (R1 := hd6 F m).
  unfold hd6, head_rep6, head_rep6p.
  rewrite Hph, Hcx, Hcn, Hcc.
  Intros vt vtm vxf vos vxl vhc lx ln lc.
  match goal with X: 1 <= 4 -> _ |- _ => specialize (X ltac:(lia)) end.
  match goal with X: 2 <= 4 -> _ |- _ => specialize (X ltac:(lia)) end.
  match goal with X: 3 <= 4 -> _ |- _ => destruct (X ltac:(lia)) end.
  match goal with X: 4 <= 4 -> _ |- _ => specialize (X ltac:(lia)) end.
  subst vt vtm vxf vos. rewrite Hdone.
  destruct HF0 as [HF HFl]. destruct HF as (Hshs & Hhsh & Hgsh & Htsh).
  destruct F as [gv shs strmp sp headp winp hsh xb nb cb ib ob gsh tsh dt vres vhere vlast vhbuf flush].
  frame_simpl. unfold head_partH. cbn [f_hsh f_headp f_xb f_nb f_cb] in *.
  rewrite Hh2. unfold hnoneH.
  abbreviate_semax.
  freeze FR := (field_at _ _ (DOT _wrap) _ _) (field_at _ _ (DOT _havedict) _ _) (field_at _ _ (DOT _hold) _ _)
    (field_at _ _ (DOT _bits) _ _) (state_rest _ _ _ _ _ _) (win_rep _ _) (in_rep _) (out_rep _ _)
    (tables_rep _ _) (locals_rep _).
  freeze FB := (hbuf6 _ _ _) (hbuf6 _ _ _) (hbuf6 _ _ _).
  forward.
  unfold abbreviate in MORE_COMMANDS. subst MORE_COMMANDS. apply semax_if_seq. forward_if.
  + forward. forward. forward. forward. forward.
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      apply semax_pre with (PROPx P (LOCALx Q (SEPx (emp :: emp :: R)))); [entailer! |] end.
    forward_call (0, nullval, 0, true, Ews, nullval, 0, 0, @nil val, @nil Z, false, Ews, gv, tsh).
    forward. unfold strm_rep. remember (gv _zcalloc) as za eqn:Eza. remember (gv _zcfree) as zf eqn:Ezf.
    forward. forward. forward.
    unfold switch_ret_assert, case_post9. cbn [RA_break RA_normal].
    Exists (set_mode (set_m_adler (upd_s (upd_h m2 (fun h => set_h_done (set_h_hcrc h
        (Z.land (Z.shiftr (i_flags (m_s m2)) 9) 1)) 1)) (fun s => set_i_check s 0)) 0) IM.TYPE).
    apply andp_right; [apply prop_right; exact ET | ].
    unfold post9, hd9. match goal with |- context [hdr_mode ?x] => replace (hdr_mode x) with false by reflexivity end.
    rewrite int_hcrc by (apply (sw_flags _ (mw9_s _ W2))).
    eapply derives_trans; [ | apply sepcon_derives; [apply derives_refl | intro; apply orp_right1, derives_refl]].
    unfold hd8a. cbn [f_hsh f_headp f_xb f_nb f_cb].
    set (m' := set_mode (set_m_adler (upd_s (upd_h m2 (fun h => set_h_done (set_h_hcrc h
        (Z.land (Z.shiftr (i_flags (m_s m2)) 9) 1)) 1)) (fun s => set_i_check s 0)) 0) IM.TYPE).
    assert (Eh': m_h m' = set_h_done (set_h_hcrc (m_h m) (Z.land (Z.shiftr (i_flags (m_s m2)) 9) 1)) 1)
      by (subst m'; cbn [m_h set_mode set_m_adler upd_s upd_h set_m_h set_m_s]; rewrite Eh2; reflexivity).
    thaw FB.
    pose proof (head_rep8a_intro hsh headp xb nb cb (m_s m')
      (set_h_done (set_h_hcrc (m_h m) (Z.land (Z.shiftr (i_flags (m_s m2)) 9) 1)) 1) vxl lx ln lc) as P8.
    simpl in P8.
    assert (Hx: fextra (set_i_mode (set_i_check (m_s m2) 0) IM.TYPE) = true -> vxl = zv (h_extra_len (m_h m))).
    { intros Hx; match goal with X: fextra _ = true -> vxl = _ |- _ => apply X end;
      unfold fextra in Hx |- *; cbn in Hx; rewrite Es2 in Hx; exact Hx. }
    sep_apply (P8 Hx ltac:(assumption) ltac:(assumption) ltac:(assumption)). clear P8.
    replace (head_rep8a hsh headp xb nb cb (set_i_mode (set_i_check (m_s m2) 0) IM.TYPE)
      (set_h_done (set_h_hcrc (m_h m) (Z.land (Z.shiftr (i_flags (m_s m2)) 9) 1)) 1))
      with (head_rep8a hsh headp xb nb cb (m_s m') (m_h m')) by (rewrite Eh'; reflexivity).
    set (HD8 := head_rep8a hsh headp xb nb cb (m_s m') (m_h m')). subst m'.
    rewrite loop_state_hd_eqH. unfold loop_state_hdH. rewrite frame_SEP8.
    frame_simpl_goal. unfold m_have, m_left. mnorm_goalH. cbn [f_gv f_hsh f_headp f_xb f_nb f_cb].
    rewrite Hh2. unfold hnoneH.
    rewrite strm_rep_unfold. rewrite <- Eza, <- Ezf.
    rest_simpl. thaw FR. unfold win_rep. entailer!.
  + match goal with X: headp = nullval |- _ => subst headp end.
    assert_PROP False by (sep_apply (data_at_local_facts hsh t_head); entailer!;
      match goal with X: field_compatible _ _ nullval |- _ => destruct X; contradiction end). contradiction.
Qed.
