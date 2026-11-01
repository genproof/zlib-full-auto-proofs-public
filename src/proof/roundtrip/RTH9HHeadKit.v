(* Case HEAD of inflate() with the partial header attached, for calls of any uInt size: the branches that round 1
   excluded (a call that passes the header takes the gzip branch).  Every branch ends past or in the header modes
   with the header RTH9HDefs.hd9:
   - wrap = 0: mode TYPEDO, the header untouched (done = 0), left raw (RTHSpec.hraw6);
   - NEEDBITS(16) out of input: mode HEAD, the partial header unchanged;
   - the gzip branch: mode FLAGS, the partial header unchanged (RTHHEADKit6.head_rep6_HEAD_FLAGS);
   - the zlib branch: `head->done = -1` (the header's memory is needed for this write), then the zlib header's
     checks (the headless port of inflate/HeadZlib7.v, hl9h/inflate/H9ZHeadZlib7.v): mode BAD, DICTID or TYPE with
     done = -1, the header left raw. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.roundtrip.RTHSpec.
Require Import Zlib.proof.roundtrip.RTHCase.
Require Import Zlib.proof.roundtrip.RTHCaseHyps5.
Require Import Zlib.proof.inflate.Steps2.
Require Import Zlib.proof.inflate.HeadDefs5.
Require Import Zlib.proof.hl9h.roundtrip.H9HRTHNeedKit5 Zlib.proof.hl9h.roundtrip.H9HRTHNeedBits1_5.
Require Import Zlib.proof.hl9h.roundtrip.H9HRTHHEADKit6.
Require Import Zlib.proof.hl9h.inflate.H9ZHeadZlib7.
Require Import Zlib.proof.roundtrip.RTH8Defs.
Require Import Zlib.proof.roundtrip.RTH9HDefs.
Require Import Zlib.proof.roundtrip.RTH9WKit.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* ---------------------------------------------------------------------------------------------- *)
(* the header past the header modes, raw                                                          *)

(* the partial header has done = 0 and the pointer and size fields: it is a raw header *)
Lemma head_rep6_raw: forall hsh headp xb nb cb s h,
  head_rep6 hsh headp xb nb cb s h |-- !! (h_done h = 0) && hraw6 hsh headp xb nb cb h.
Proof.
  intros. unfold head_rep6, head_rep6p, hraw6. Intros vt vtm vxf vos vxl vhc lx ln lc.
  destruct H as (D & _).
  apply andp_right; [apply prop_right; exact D | ].
  Exists vt vtm vxf vos vxl vhc (zv (h_done h)) lx ln lc.
  entailer!. split; [apply H5 | split; [apply H6 | apply H7]].
Qed.

(* the raw header does not record done *)
Lemma hraw6_done: forall hsh headp xb nb cb h d,
  hraw6 hsh headp xb nb cb (set_h_done h d) = hraw6 hsh headp xb nb cb h.
Proof. reflexivity. Qed.

Lemma hd9_of_raw: forall F m,
  hdr_mode (m_mode m) = false -> h_done (m_h m) <> 1 ->
  hraw6 (f_hsh F) (f_headp F) (f_xb F) (f_nb F) (f_cb F) (m_h m) |-- hd9 F m.
Proof.
  intros F m HM HD. unfold hd9. rewrite HM. unfold hd9a. apply orp_right2.
  apply andp_right; [apply prop_right; exact HD | apply derives_refl].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the model                                                                                      *)

Lemma needbits_sh9: forall n m, m_s (needbits n m) = m_s m /\ m_h (needbits n m) = m_h m.
Proof. intros. unfold needbits. apply rthh_nb_sh. Qed.

(* the outcomes of the zlib branch: past the header modes, the header with done = -1 *)
Lemma head_zlib_out_h: forall m1 m',
  i_head (m_s m1) = true -> head_zlib_out m1 = IBrk m' ->
  hdr_mode (m_mode m') = false /\ m_h m' = set_h_done (m_h m1) (-1).
Proof.
  intros m1 m' HI E. unfold head_zlib_out in E. rewrite HI in E. cbv zeta in E.
  repeat match type of E with
  | context [if ?c then _ else _] => destruct c
  end; inversion E; subst m'; split; try reflexivity;
  cbn; reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the headless pieces                                                                             *)

Lemma loop_state_set_mode_mwH: forall F m md, loop_stateH F (set_mode m md) = loop_state_mwH F m (zv md).
Proof. intros. rewrite loop_state_split_mwH. reflexivity. Qed.

(* if (state->wrap == 0) { state->mode = TYPEDO; break; } *)
Lemma head_wrap9H {Espec: OracleKind} (F: frame) (m: mst) (R: ret_assert):
  m_mode m = IM.HEAD -> mwf9 m ->
  RA_break R = RA_normal (case_post2H F m) ->
  semax Delta_cases5 (loop_stateH F m) head_WRAP
    (overridePost (!! (i_wrap (m_s m) <> 0) && loop_stateH F m) R).
Proof.
  intros HM W HR.
  pose proof (sw_wrap_range _ (mw9_s _ W)) as Hw.
  destruct (Z.eq_dec (i_wrap (m_s m)) 0) as [Hw0 | Hw0].
  - assert (E: stepf2 (f_flush F) lenfix_list distfix_list m = IBrk (set_mode m IM.TYPEDO)).
    { rewrite (stepf2_HEAD _ _ _ _ HM). unfold c_HEAD2. rewrite Hw0. reflexivity. }
    rewrite loop_state_split_mwH. unfold loop_state_mwH, head_WRAP.
    abbreviate_semax.
    forward. forward_if; [ | contradiction].
    forward. forward.
    match goal with |- context [RA_break ?X] =>
      replace (RA_break X) with (RA_break R) by (destruct R; reflexivity) end.
    rewrite HR. unfold case_post2H. unfold RA_normal at 1.
    Exists (set_mode m IM.TYPEDO).
    apply andp_right; [apply prop_right; exact E | ].
    rewrite loop_state_set_mode_mwH. unfold loop_state_mwH.
    entailer!.
  - rewrite loop_state_split_mwH. unfold loop_state_mwH, head_WRAP.
    abbreviate_semax.
    forward. forward_if; [ contradiction | ].
    eapply ConseqFacts.semax_post''; [ | apply semax_skip].
    match goal with |- context [RA_normal ?X] =>
      replace (RA_normal X) with (!! (i_wrap (m_s m) <> 0) && loop_state_mwH F m (zv (m_mode m)))
        by (destruct R; reflexivity) end.
    unfold loop_state_mwH.
    entailer!.
Qed.

(* case HEAD, headless, when wrap = 0 or NEEDBITS(16) runs out of input *)
Lemma head_case_lv9H {Espec: OracleKind} (F: frame) (m: mst):
  m_mode m = IM.HEAD -> m_leave m = 0 -> mwf9 m ->
  (i_wrap (m_s m) = 0 \/ m_leave (needbits 16 m) = 1) ->
  semax Delta_cases5 (loop_stateH F m) (seq_of_labeled_statement (ls_drop 0 inflate_LS))
    (switch_ret_assert (case_post2H F m)).
Proof.
  intros HM HL W HC.
  rewrite seq_split by lia.
  eapply semax_seq; [ | apply semax_ff].
  rewrite case_body0_eq.
  apply semax_seq with (Q := !! (i_wrap (m_s m) <> 0) && loop_stateH F m).
  { apply head_wrap9H; [exact HM | exact W | reflexivity]. }
  apply semax_extract_prop; intros Hw.
  pose proof (stepf2_HEAD (f_flush F) lenfix_list distfix_list m HM) as E0.
  eapply (semax_needbits_seq_r5H_h9h F m m 16).
  - apply semax_needbits_HEAD5H_h9h; [exact W | exact HL | lia].
  - exact W.
  - lia.
  - reflexivity.
  - intro E. rewrite E0. unfold c_HEAD2. rewrite (proj2 (Z.eqb_neq _ _) Hw). cbv zeta. rewrite E.
    reflexivity.
  - apply semax_extract_prop; intros HL1. exfalso. destruct HC as [HC | HC]; [exact (Hw HC) | lia].
Qed.

(* if (leave) break; with leave = 0 *)
Lemma head_noleave9H {Espec: OracleKind} (F: frame) (m: mst):
  m_leave m = 0 ->
  semax Delta_cases5 (loop_stateH F m) (Sifthenelse (Etempvar _leave tint) Sbreak Sskip)
    (normal_ret_assert (loop_stateH F m)).
Proof.
  intros HL. unfold loop_stateH. abbreviate_semax.
  forward_if.
  - exfalso. rewrite HL in H. apply H. reflexivity.
  - forward. entailer!.
Qed.

(* t'7 = (state->wrap & 2) && hold == 0x8b1f; if (t'7) <gzip>, the gzip test false *)
Lemma head_w7_false9H {Espec: OracleKind} (F: frame) (m1: mst):
  mwf9 m1 ->
  andb (negb (Z.land (i_wrap (m_s m1)) 2 =? 0)) (m_hold m1 =? 35615) = false ->
  semax Delta_cases5 (loop_stateH F m1) (Ssequence head_W7 (Sifthenelse (Etempvar _t'7 tint) head_GZIP Sskip))
    (normal_ret_assert (loop_stateH F m1)).
Proof.
  intros W G.
  pose proof (sw_wrap_range _ (mw9_s _ W)) as Hw. pose proof (mw9_hold _ W) as Hh.
  rewrite loop_state_split_mwH. unfold loop_state_mwH, head_W7.
  abbreviate_semax.
  forward.
  apply semax_if_seq.
  forward_if.
  - forward.
    forward_if.
    + exfalso.
      assert (G1: Z.land (i_wrap (m_s m1)) 2 <> 0) by (rewrite !Int.unsigned_repr in H1' by rep_lia; exact H1').
      assert (G2: m_hold m1 = 35615).
      { apply Int64.same_if_eq in H2. unfold lrange in Hh.
        apply repr_inj_unsigned64 in H2; [exact H2 | rep_lia | rep_lia]. }
      rewrite (proj2 (Z.eqb_neq _ _) G1), G2 in G. discriminate.
    + forward. entailer!.
  - forward. forward_if; [exfalso; match goal with Hx: _ <> _ |- _ => apply Hx; reflexivity end | ].
    forward. entailer!.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the zlib branch after head->done = -1, headless (HeadZlib7.head_zlib7_w's steps after its first)  *)

Lemma zl_rest9H {Espec: OracleKind} (F: frame) (m0 m1: mst) (R: ret_assert):
  frame_ok5 F -> mwf9 m1 ->
  (i_wbits (m_s m1) = 0 -> i_win (m_s m1) = false) ->
  RA_break R = RA_normal (case_post2H F m0) ->
  stepf2 (f_flush F) lenfix_list distfix_list m0 = head_zlib_out m1 ->
  semax Delta_cases5 (loop_stateH F (zl_mh m1)) zl_rest R.
Proof.
  intros [FOK _] W Hwin HR E.
  rewrite head_zlib_out_eq in E.
  pose proof (mw9_hold _ W) as Hh. pose proof (sw_wrap_range _ (mw9_s _ W)) as Hw.
  pose proof (sw_wbits _ (mw9_s _ W)) as Hwb.
  assert (Hs: m_s (zl_mh m1) = m_s m1) by (unfold zl_mh; destruct (i_head (m_s m1)); reflexivity).
  assert (Hho: m_hold (zl_mh m1) = m_hold m1) by (unfold zl_mh; destruct (i_head (m_s m1)); reflexivity).
  rewrite zl_rest_eq.
  eapply semax_seq.
  { apply (zl_c31_ok_h9z F (zl_mh m1) m0 R FOK); [rewrite Hho; exact Hh | rewrite Hs; exact Hw | exact HR | ].
    intro C. rewrite C in E. exact E. }
  apply semax_extract_prop; intros C31. rewrite C31 in E.
  eapply semax_seq.
  { apply (zl_meth_ok_h9z F (zl_mh m1) m0 R FOK); [rewrite Hho; exact Hh | exact HR | ].
    intro N. rewrite (proj2 (Z.eqb_neq _ _) N) in E. exact E. }
  apply semax_extract_prop; intros M8. rewrite (proj2 (Z.eqb_eq _ _) M8) in E. cbn [negb] in E.
  rewrite zl_r3_eq.
  apply semax_seq' with (P' := loop_stateH F (dropbits 4 (zl_mh m1)));
    [apply zl_drop_ok_h9z; rewrite Hho; exact Hh | ].
  rewrite zl_tail_eq in E. cbv zeta in E.
  assert (Hh2: lrange (m_hold (dropbits 4 (zl_mh m1)))).
  { unfold dropbits. cbn [set_m_bits set_m_hold m_hold]. rewrite Hho. apply zl_shiftr_lrange; [exact Hh | lia]. }
  assert (Hs2: m_s (dropbits 4 (zl_mh m1)) = m_s m1) by (rewrite <- Hs; reflexivity).
  apply (zl_lset_ok_h9z F (dropbits 4 (zl_mh m1)) _ R FOK Hh2).
  pose proof (Z.mod_pos_bound (m_hold (dropbits 4 (zl_mh m1))) 16 ltac:(lia)) as Hl.
  eapply semax_seq.
  { apply (zl_wsz_ok_h9z F _ m0 _ R FOK); [lia | rewrite Hs2; exact Hwb | exact HR | ].
    intro C. rewrite C in E. exact E. }
  apply semax_extract_prop; intros CW. rewrite CW in E.
  unfold zl_wc in CW. apply orb_false_iff in CW. destruct CW as [CW _]. apply Z.ltb_ge in CW.
  eapply semax_seq'.
  { apply zl_wbs_ok_h9z; [exact FOK | lia | rewrite Hs2; exact Hwb | rewrite Hs2; exact Hwin]. }
  apply (zl_fin_ok_h9z F _ m0 _ R FOK); [lia | exact Hh2 | exact HR | exact E].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* head->done = -1, with the raw header                                                            *)

(* the headless loop state with one more item X *)
Definition loop_stateHX (F: frame) (m: mst) (X: mpred) : environ -> mpred :=
  PROP (in_ok (f_ib F) (m_inp m); out_ok (f_ob F) (m_aout m))
  LOCAL (temp _strm (f_strmp F); temp _flush (zv (f_flush F)); temp _state (f_sp F);
         temp _next (in_ptr (f_ib F) (m_nx m)); temp _put (out_ptr (f_ob F) (Zlength (m_ow m)));
         temp _have (zv (m_have m)); temp _left (zv (m_left m)); temp _hold (lv (m_hold m));
         temp _bits (zv (m_bits m)); temp _in (zv (m_in m)); temp _out (zv (m_out m));
         temp _ret (zv (m_ret m)); temp _leave (zv (m_leave m));
         lvar _here t_code (f_vhere F); lvar _last t_code (f_vlast F);
         lvar _hbuf (tarray tuchar 4) (f_vhbuf F); gvars (f_gv F))
  SEP (mem_repH F m; locals_rep F; X).

Lemma loop_stateHX_eq: forall F m X, loop_stateH F m * (fun _ => X) = loop_stateHX F m X.
Proof.
  intros. extensionality rho. unfold loop_stateH, loop_stateHX.
  unfold PROPx, LOCALx, SEPx, local, lift1. simpl. rewrite !sepcon_emp. rewrite !sepcon_andp_prop'.
  rewrite !sepcon_assoc. reflexivity.
Qed.

Lemma zl_hd9 {Espec: OracleKind} (F: frame) (m1: mst) (h: hstate): frame_ok F -> i_head (m_s m1) = true ->
  semax Delta_cases5 (loop_stateHX F m1 (hraw6 (f_hsh F) (f_headp F) (f_xb F) (f_nb F) (f_cb F) h)) zl_hd
    (normal_ret_assert (loop_stateHX F (zl_mh m1) (hraw6 (f_hsh F) (f_headp F) (f_xb F) (f_nb F) (f_cb F) h))).
Proof.
  intros FOK HI. pose proof FOK as (HWS & HWH & HRG & HRT).
  unfold zl_hd, head_ZLIB, zl_mh. rewrite HI.
  unfold loop_stateHX. rewrite !mem_rep_zsplit_h9z.
  unfold head_partH, hnoneH. cbn [upd_h set_m_h m_s m_h m_inp m_aout m_nx m_ow m_have m_left m_hold m_bits m_in
    m_out m_ret m_leave m_snx m_sow m_tin m_tout m_msg m_adler]. rewrite HI.
  unfold hraw6. Intros vt vtm vxf vos vxl vhc vd lx ln lc.
  abbreviate_semax. forward. forward_if.
  - forward. forward.
    Exists vt vtm vxf vos vxl vhc (Vint (Int.neg (Int.repr 1))) lx ln lc.
    unfold strm_z. entailer!; apply derives_refl.
  - assert_PROP (isptr (f_headp F)) by entailer!. match goal with E: f_headp F = nullval, P: isptr (f_headp F) |- _ => rewrite E in P; contradiction end.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the case with the header attached                                                               *)

Lemma semax_frame_n {Espec: OracleKind} (Delta: tycontext) (P Q: environ -> mpred) (c: statement) (X: mpred):
  semax Delta P c (normal_ret_assert Q) ->
  semax Delta (P * (fun _ => X)) c (normal_ret_assert (Q * (fun _ => X))).
Proof.
  intros H.
  eapply semax_post; [ | | | | apply semax_frame; [ | exact H]].
  - intros rho. simpl. apply andp_left2. apply derives_refl.
  - intros rho. simpl. apply andp_left2. normalize.
  - intros rho. simpl. apply andp_left2. normalize.
  - intros vl rho. simpl. apply andp_left2. normalize.
  - intros rho te _. reflexivity.
Qed.

(* a headless case that breaks with the machine m' of the model, with a header that hd9 of m' accepts *)
Lemma head_frame9 {Espec: OracleKind} (F: frame) (m m': mst) (S: statement):
  stepf2 (f_flush F) lenfix_list distfix_list m = IBrk m' ->
  hd6 F m |-- hd9 F m' ->
  semax Delta_cases5 (loop_stateH F m) S (switch_ret_assert (case_post2H F m)) ->
  semax Delta_cases5 (loop_stateH F m * (fun _ => hdr_tok F m * hd6 F m)) S
    (frame_ret_assert (switch_ret_assert (case_post9 F m)) (fun _ => hdr_tok F m)).
Proof.
  intros E Hh HS.
  eapply semax_post; [ | | | | apply semax_frame with (F := fun _ => hdr_tok F m * hd6 F m); [ | exact HS]].
  - intros rho. simpl. apply andp_left2. normalize.
  - intros rho. simpl. apply andp_left2. normalize. rewrite E in H. inversion H; subst x; clear H.
    apply (exp_right m'). unfold post9. simpl. normalize. sep_apply Hh. cancel.
  - intros rho. simpl. apply andp_left2. normalize.
  - intros vl rho. simpl. apply andp_left2. normalize. rewrite E in H. discriminate.
  - intros rho te _. reflexivity.
Qed.

(* the zlib branch: wrap <> 0, NEEDBITS(16) done, the gzip test false *)
Lemma head_case_zlib9 {Espec: OracleKind} (F: frame) (m: mst):
  frame_ok5 F -> m_mode m = IM.HEAD -> m_leave m = 0 -> mwf39 m -> i_head (m_s m) = true ->
  i_wrap (m_s m) <> 0 -> m_leave (needbits 16 m) = 0 ->
  andb (negb (Z.land (i_wrap (m_s (needbits 16 m))) 2 =? 0)) (m_hold (needbits 16 m) =? 35615) = false ->
  semax Delta_cases5 (loop_stateH F m * (fun _ => hdr_tok F m * hd6 F m))
    (seq_of_labeled_statement (ls_drop 0 inflate_LS))
    (frame_ret_assert (switch_ret_assert (case_post9 F m)) (fun _ => hdr_tok F m)).
Proof.
  intros HF HM HL W3 HI Hw HL1 G.
  pose proof (proj1 W3) as W.
  pose proof (mwf9_needbits 16 m W ltac:(lia)) as W1.
  pose proof (head_gzip_nowin9 m W3 HM Hw) as HN.
  destruct (needbits_sh9 16 m) as [S1 H1].
  pose proof (stepf2_HEAD (f_flush F) lenfix_list distfix_list m HM) as E0.
  assert (E1: stepf2 (f_flush F) lenfix_list distfix_list m = head_zlib_out (needbits 16 m)).
  { rewrite E0, (c_HEAD_split m Hw HL1), G. reflexivity. }
  set (m1 := needbits 16 m) in *.
  set (hr := hraw6 (f_hsh F) (f_headp F) (f_xb F) (f_nb F) (f_cb F) (m_h m)).
  rewrite seq_split by lia. eapply semax_seq; [ | apply semax_ff]. rewrite case_body0_eq.
  apply semax_seq' with (P' := loop_stateH F m * (fun _ => hdr_tok F m * hd6 F m)).
  { apply semax_frame_n. exact (head_wrapH_h9h F m (normal_ret_assert (loop_stateH F m)) W Hw). }
  apply semax_seq' with (P' := loop_stateH F m1 * (fun _ => hdr_tok F m * hd6 F m)).
  { apply semax_frame_n. apply semax_needbits_HEAD5H_h9h; [exact W | exact HL | lia]. }
  apply semax_seq' with (P' := loop_stateH F m1 * (fun _ => hdr_tok F m * hd6 F m)).
  { apply semax_frame_n. apply head_noleave9H; exact HL1. }
  apply semax_seq' with (P' := loop_stateH F m1 * (fun _ => hdr_tok F m * hd6 F m)).
  { apply semax_frame_n. apply head_w7_false9H; [exact W1 | exact G]. }
  rewrite head_ZLIB_eq.
  apply semax_pre with (P' := loop_stateHX F m1 hr * (fun _ => hdr_tok F m)).
  { rewrite <- loop_stateHX_eq. intros rho. simpl. apply andp_left2. unfold hd6, hr.
    sep_apply head_rep6_raw. Intros. cancel. }
  apply semax_seq' with (P' := loop_stateHX F (zl_mh m1) hr * (fun _ => hdr_tok F m)).
  { apply semax_frame_n. apply zl_hd9; [exact (proj1 HF) | rewrite S1; exact HI]. }
  rewrite <- loop_stateHX_eq.
  apply semax_pre with (P' := loop_stateH F (zl_mh m1) * (fun _ => hr * hdr_tok F m)).
  { intros rho. simpl. apply andp_left2. cancel. }
  eapply semax_post; [ | | | | apply semax_frame with (F := fun _ => hr * hdr_tok F m);
    [ | apply (zl_rest9H F m m1
          {| RA_normal := FF; RA_break := RA_normal (case_post2H F m); RA_continue := FF;
             RA_return := fun _ _ => FF |} HF W1 HN eq_refl E1)]].
  - intros rho. simpl. apply andp_left2. normalize.
  - intros rho. simpl. apply andp_left2. normalize. rewrite E1 in H.
    destruct (head_zlib_out_h m1 x) as [HMx HHx]; [rewrite S1; exact HI | exact H | ].
    apply (exp_right x). unfold post9. simpl. normalize.
    assert (D: hr |-- hd9 F x).
    { unfold hr. rewrite <- H1, <- (hraw6_done _ _ _ _ _ (m_h m1) (-1)), <- HHx.
      apply hd9_of_raw; [exact HMx | rewrite HHx; cbn; discriminate]. }
    sep_apply D. rewrite E1. apply andp_right; [apply prop_right; exact H | cancel].
  - intros rho. simpl. apply andp_left2. normalize.
  - intros vl rho. simpl. apply andp_left2. normalize.
  - intros rho te _. reflexivity.
Qed.
