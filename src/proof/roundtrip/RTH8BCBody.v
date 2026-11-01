(* inflate()'s body with a partial header, from the loop and exit parts of RTH8BCKit: the prologue
   (RTHPro6.pro_part6 on the stream with the small header RTH8W.lcanon, the header in the frame), then the
   header passes and the loop (hloop8_stmt, for hd8pre_b) or the loop past the header (nhloop8_stmt, for
   hd8pre_c), then the exit (exit8_stmt); as RTHBody6H.rth_body6h. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.roundtrip.RTHSpec.
Require Import Zlib.proof.roundtrip.RTH8Spec.
Require Import Zlib.proof.roundtrip.RTH8BCKit.
Require Import Zlib.proof.inflate_api.Body5Conv.
Require Import Zlib.proof.inflate_api.Body5StepInv.
Require Import Zlib.proof.inflate_api.Body5StepHdr.
Require Import Zlib.proof.inflate_api.LibProof5.
Require Import Zlib.proof.inflate.InvQ5.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.roundtrip.RTHPro6.
Require Import Zlib.proof.inflate_api.Body5Fin.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* the stream error of the prologue does not depend on the live part *)
Lemma inflate_bad_some: forall strmp z L1 L2 ib ob,
  inflate_bad strmp z (Some L1) ib ob -> inflate_bad strmp z (Some L2) ib ob.
Proof.
  unfold inflate_bad, is_live. intros strmp z L1 L2 ib ob H.
  destruct (eq_dec strmp nullval); [left; reflexivity | ].
  destruct H as [H | H]; [discriminate | right; exact H].
Qed.

Lemma istream8_opt_canon: forall gv shs strmp z L, strmp <> nullval ->
  istream8_opt gv shs strmp z (Some L) |-- !! live_ok8 L && istream_opt gv shs strmp z (Some (lcanon L)).
Proof.
  intros. unfold istream8_opt, istream_opt. destruct (eq_dec strmp nullval); [contradiction | ].
  apply istream8_canon.
Qed.

Lemma istream_opt_canon_8: forall gv shs strmp z L, live_ok8 L ->
  istream_opt gv shs strmp z (Some (lcanon L)) |-- istream8_opt gv shs strmp z (Some L).
Proof.
  intros. unfold istream_opt, istream8_opt. destruct (eq_dec strmp nullval); [apply derives_refl | ].
  apply istream_canon_8; assumption.
Qed.

(* the precondition's header part with the tokens is head_mem8's second (hd8pre_b) or third (hd8pre_c)
   disjunct *)
Lemma head_mem8_b: forall L, i_head (l_s L) = true -> hdr_mode (i_mode (l_s L)) = true ->
  head_rep6 (l_hsh L) (l_headp L) (l_xb L) (l_nb L) (l_cb L) (l_s L) (l_h L) * htok6 (Some (lcanon L))
  |-- head_mem8 L.
Proof.
  intros L EH EM. rewrite htok6_lcanon by exact EH. unfold head_mem8, btoks8. rewrite EH, !sepcon_assoc.
  apply sepcon_derives; [ | apply derives_refl].
  apply orp_right1. apply orp_right2. apply andp_right; [apply prop_right; exact EM | apply derives_refl].
Qed.

Lemma head_mem8_c: forall L, i_head (l_s L) = true -> hdr_mode (i_mode (l_s L)) = false ->
  head_rep8a (l_hsh L) (l_headp L) (l_xb L) (l_nb L) (l_cb L) (l_s L) (l_h L) * htok6 (Some (lcanon L))
  |-- head_mem8 L.
Proof.
  intros L EH EM. rewrite htok6_lcanon by exact EH. unfold head_mem8, btoks8. rewrite EH, !sepcon_assoc.
  apply sepcon_derives; [ | apply derives_refl].
  apply orp_right2. apply andp_right; [apply prop_right; exact EM | apply derives_refl].
Qed.

(* TYPE -> TYPEDO keeps the flags and whether the mode is a header mode *)
Lemma fextra_typedo: forall s, fextra (s_typedo s) = fextra s.
Proof.
  intros s. unfold s_typedo. destruct (i_mode s =? Zlib.proof.inflate.Model.TYPE); [destruct s | ]; reflexivity.
Qed.

Lemma hdr_mode_typedo: forall s, hdr_mode (i_mode (s_typedo s)) = hdr_mode (i_mode s).
Proof.
  intros s. unfold s_typedo.
  destruct (Z.eqb_spec (i_mode s) Zlib.proof.inflate.Model.TYPE) as [E | ]; [ | reflexivity].
  rewrite E. destruct s; reflexivity.
Qed.

Lemma body8_b : hloop8_stmt -> exit8_stmt -> rth8_delta_stmt -> body8_stmt hd8pre_b.
Proof.
intros HLOOP HEXIT (_ & _ & DSUB & _) E.
start_function.
rename H7 into HD8.
assert_PROP (exists L, is_live strmp st = Some L /\ i_head (l_s L) = true /\ hdr_mode (i_mode (l_s L)) = true) as HL.
{ unfold hd8pre_b. destruct (is_live strmp st) as [L|]; [destruct (i_head (l_s L)) eqn:EH | ]; entailer!. eauto. }
destruct HL as (L & ISL & EH & EM).
assert (NN: strmp <> nullval /\ st = Some L).
{ unfold is_live in ISL. destruct (eq_dec strmp nullval); [discriminate | split; congruence]. }
destruct NN as [NN ->].
unfold hd8pre_b at 1. rewrite ISL, EH. Intros.
sep_apply (istream8_opt_canon gv shs strmp z L NN). Intros.
rename H7 into LOK8.
set (Hd := head_rep6 (l_hsh L) (l_headp L) (l_xb L) (l_nb L) (l_cb L) (l_s L) (l_h L)).
match goal with |- semax _ _ _ ?R => set (RR := R) end.
assert (RET: forall (F: frame) (Y T X: mpred) (r: Z),
  f_vhere F = v_here -> f_vlast F = v_last -> f_vhbuf F = v_hbuf -> f_gv F = gv ->
  Y * T * X |-- (EX z': zfields, EX st': option live, EX ow: list Z,
          !! (inflate_rel flush strmp z (Some L) ib inp ob r z' st' ow) &&
          (istream8_opt gv shs strmp z' st' * head_opt8 (is_live strmp st') *
           bufs_opt (is_live strmp (Some L)) ib ob ow itok otok *
           tables_rep gsh gv * crc_table_at tsh gv)) ->
  ENTAIL Delta_inflate5_hl, PROPx [] (LOCALx (ret_locals F)
     (SEPx [Y; locals_rep F; T; mem_mgr (f_gv F); zfuncs (f_gv F); X])) |-- RA_return RR (Some (zv r))).
{ intros F Y T X r E1 E2 E3 E4 HX. unfold RR, POSTCONDITION, abbreviate. simpl RA_return.
  unfold ret_locals, locals_rep; rewrite E1, E2, E3, E4. unfold stackframe_of; simpl fn_vars. simpl fold_right. go_lowerx.
  rewrite !var_block_data_at_ by (reflexivity || auto). unfold_lift. erewrite !lvar_eval_lvar by eassumption.
  sep_apply HX.
  Intros z' st' ow. Exists r z' st' ow. entailer!. }
change Delta with Delta_inflate5_hl.
apply body_reshape.
assert (ISLc: is_live strmp (Some (lcanon L)) = Some (lcanon L)).
{ unfold is_live. destruct (eq_dec strmp nullval); [contradiction | reflexivity]. }
eapply semax_seq.
{ eapply semax_Delta_subsumption; [exact DSUB | ].
  eapply semax_pre.
  2: apply (pro_part6 _ gv shs strmp z (Some (lcanon L)) ib inp ob flush gsh tsh itok otok
              v_here v_last v_hbuf Hd RR); try assumption.
  - unfold pro_pre6. rewrite ISLc, htok6_lcanon by exact EH. unfold bufs_opt. entailer!.
  - intros BAD. apply (inflate_bad_some _ _ _ L) in BAD.
    unfold RR, POSTCONDITION, abbreviate. simpl RA_return.
    unfold stackframe_of; simpl fn_vars. simpl fold_right. go_lowerx.
    rewrite !var_block_data_at_ by (reflexivity || auto). unfold_lift. erewrite !lvar_eval_lvar by eassumption.
    Exists Z_STREAM_ERROR z (Some L) (@nil Z). rewrite ISLc, ISL.
    sep_apply (istream_opt_canon_8 gv shs strmp z L LOK8).
    unfold Hd. sep_apply (head_mem8_b L EH EM).
    unfold bufs_opt. entailer!.
    left. auto. }
unfold pro_post6. Intros L' o.
apply semax_extract_prop. intros (EL1 & EO & NBc & LOK & ZOK & WS & _). subst ob.
assert (L' = lcanon L) by congruence. subst L'.
assert (NB: ~ inflate_bad strmp z (Some L) ib (Some o)).
{ intros BAD. apply NBc. apply (inflate_bad_some _ _ L). exact BAD. }
rewrite mkF_lcanon, xfr_lcanon, m_init_lcanon, lstateH_mcanon.
set (F := mkF gv shs strmp L ib o gsh tsh z v_here v_last v_hbuf flush).
set (X := xfr L itok otok ib o).
set (m0 := m_init z L inp).
pose proof LOK8 as (LP & _ & _ & LH8 & _ & LW & _ & LHD & _).
assert (FOK: frame_ok5 F) by (unfold frame_ok5, frame_ok, F, mkF; simpl; auto).
assert (INP: Zlength inp <= Int.max_signed /\ bytes_ok inp).
{ destruct ib as [ | ish ip ilo ilen ic].
  - subst inp. split; [rewrite Zlength_nil; rep_lia | constructor].
  - destruct H3 as [(_ & _ & _ & _ & _ & _ & _ & HB) HA]. split; [lia | exact HB]. }
assert (MW: mwf3_8 m0).
{ split; [ | exact LH8]. unfold m0. rewrite <- m_init_lcanon. apply m_init_mwf3; tauto. }
assert (OI: out_inv m0).
{ apply m_init_out_inv. destruct ZOK as (_ & ? & _); lia. }
assert (WI0: win_inv5 (m_s m0)).
{ unfold m0. rewrite m_init_s. apply s_typedo_win_inv5. exact (live_win_inv5 _ LOK). }
assert (HD0: hd_ok F m0).
{ unfold hd_ok, m0, F, mkF. rewrite m_init_s. cbn [f_xb f_nb f_cb m_h m_init].
  unfold s_typedo. destruct (i_mode (l_s L) =? Zlib.proof.inflate.Model.TYPE); exact LHD. }
assert (DT: srange (zf_dt z)) by (destruct ZOK as (_&_&_&_&?&_); assumption).
assert (WIN0: i_win (m_s m0) = i_win (l_s L)).
{ unfold m0. rewrite m_init_s. unfold s_typedo.
  destruct (i_mode (l_s L) =? Zlib.proof.inflate.Model.TYPE); reflexivity. }
assert (MS0: m_s m0 = l_s L).
{ unfold m0. rewrite m_init_s. unfold s_typedo.
  destruct (Z.eqb_spec (i_mode (l_s L)) Zlib.proof.inflate.Model.TYPE) as [ET | ]; [ | reflexivity].
  rewrite ET in EM. discriminate. }
assert (HD6m: Hd = hd6 F m0).
{ unfold Hd, hd6, F, mkF. cbn [f_hsh f_headp f_xb f_nb f_cb]. rewrite MS0. reflexivity. }
rewrite HD6m.
assert (HPm: exists n, hpass8 flush n m0).
{ unfold hd8_ok in HD8. rewrite ISL in HD8. apply HD8; auto. }
destruct HPm as [n HPm].
eapply semax_seq.
{ apply (HLOOP _ F X m0 RR FOK) with (n := n).
  - intros r m' HL' [HW3 HW8] HDm HM' HI' (HWin & HWV & HIP).
    apply RET; [reflexivity | reflexivity | reflexivity | reflexivity | ].
    destruct (fin_ok8_live F m' (mwf3_fin_ok5 _ HW3 HWV) HW8 HDm) as [HLV HZV];
      [exact LP | exact LW | exact DT | ].
    Exists (z_of F m') (Some (live_of F m')) (m_ow m').
    apply andp_right.
    + apply prop_right. right. split; [exact NB | ].
      exists L, o, (Res r m' None), (l_winp L).
      split; [reflexivity | ]. split; [reflexivity | ].
      split; [exists (IRet r m'); split; [exact HL' | reflexivity] | ].
      split; [simpl; replace inp with (m_inp m') by (rewrite HIP; reflexivity); exact (mw_snx _ (mwf3_mwf _ HW3)) | ].
      split; [reflexivity | ]. split; [reflexivity | ]. split; [reflexivity | ].
      split; [auto | reflexivity].
    + rewrite ISL. unfold X, xfr. sep_apply (mem_rep_istream8 F m' HLV HZV WS NN HI' HM').
      unfold bufs_opt, F; cbn [f_gv f_shs f_strmp f_ib f_ob f_gsh f_tsh mkF]. cancel.
  - exact HPm.
  - unfold m_mode. rewrite MS0. exact EM.
  - rewrite MS0. exact EH.
  - exact MW.
  - reflexivity.
  - exact HD0.
  - split; [exact OI | split; [reflexivity | split; [exact WI0 | reflexivity]]].
  - auto. }
unfold loop_exit8. apply semax_extract_exists. intro m. apply semax_extract_prop.
intros (LP' & MW' & HDm & ML & HMm & HIm & (OI' & WI & WV & IPm)).
apply (HEXIT _ F X m RR FOK MW' ML OI' WV HMm).
intros res winp HIL (FO & DTr & EH' & EHd & EI & HMr) HWP.
set (F' := set_f_winp_dt F winp (res_dt F res)).
assert (HD': hd_ok F' (r_m res)).
{ unfold hd_ok. rewrite EH', EHd. exact HDm. }
assert (TK: hdr_tok F m = hdr_tok F' (r_m res)).
{ unfold hdr_tok. rewrite EH', EHd. reflexivity. }
assert (HIr: i_head (m_s (r_m res)) = true) by (rewrite EHd; exact HIm).
assert (HW8r: hwf8 (m_h (r_m res))) by (rewrite EH'; exact (proj2 MW')).
rewrite TK.
change (hd8a F (r_m res)) with (hd8a F' (r_m res)).
apply (RET F'); [reflexivity | reflexivity | reflexivity | reflexivity | ].
destruct (fin_ok8_live F' (r_m res) FO HW8r HD') as [HLV HZV].
{ exact LP. }
{ exact LW. }
{ unfold F', res_dt. simpl. destruct (r_dtype res) eqn:ED; [apply DTr; reflexivity | exact DT]. }
Exists (z_of F' (r_m res)) (Some (live_of F' (r_m res))) (m_ow (r_m res)).
apply andp_right.
- apply prop_right. right. split; [exact NB | ].
  exists L, o, res, winp.
  split; [reflexivity | ]. split; [reflexivity | ].
  split; [exists (IBrk m); split; [exact LP' | exact HIL] | ].
  split; [destruct FO as (_ & _ & _ & _ & _ & FS & _); cbn [mcanon set_m_h m_snx m_inp] in FS;
          rewrite EI, IPm in FS; exact FS | ].
  split; [reflexivity | ]. split; [reflexivity | ]. split; [reflexivity | ].
  split; [ | reflexivity].
  intros HW1. apply HWP. rewrite WI, WIN0. exact HW1.
- rewrite ISL. unfold X, xfr. sep_apply (mem_rep_istream8 F' (r_m res) HLV HZV WS NN HIr HMr).
  unfold bufs_opt, F', F; cbn [f_gv f_shs f_strmp f_ib f_ob f_gsh f_tsh mkF set_f_winp_dt]. cancel.
Qed.

Lemma body8_c : nhloop8_stmt -> exit8_stmt -> rth8_delta_stmt -> body8_stmt hd8pre_c.
Proof.
intros HNL HEXIT (_ & _ & DSUB & _) E.
start_function.
rename H7 into HD8.
assert_PROP (exists L, is_live strmp st = Some L /\ i_head (l_s L) = true /\ hdr_mode (i_mode (l_s L)) = false) as HL.
{ unfold hd8pre_c. destruct (is_live strmp st) as [L|]; [destruct (i_head (l_s L)) eqn:EH | ]; entailer!. eauto. }
destruct HL as (L & ISL & EH & EM).
assert (NN: strmp <> nullval /\ st = Some L).
{ unfold is_live in ISL. destruct (eq_dec strmp nullval); [discriminate | split; congruence]. }
destruct NN as [NN ->].
unfold hd8pre_c at 1. rewrite ISL, EH. Intros.
sep_apply (istream8_opt_canon gv shs strmp z L NN). Intros.
rename H7 into LOK8.
set (Hd := head_rep8a (l_hsh L) (l_headp L) (l_xb L) (l_nb L) (l_cb L) (l_s L) (l_h L)).
match goal with |- semax _ _ _ ?R => set (RR := R) end.
assert (RET: forall (F: frame) (Y T X: mpred) (r: Z),
  f_vhere F = v_here -> f_vlast F = v_last -> f_vhbuf F = v_hbuf -> f_gv F = gv ->
  Y * T * X |-- (EX z': zfields, EX st': option live, EX ow: list Z,
          !! (inflate_rel flush strmp z (Some L) ib inp ob r z' st' ow) &&
          (istream8_opt gv shs strmp z' st' * head_opt8 (is_live strmp st') *
           bufs_opt (is_live strmp (Some L)) ib ob ow itok otok *
           tables_rep gsh gv * crc_table_at tsh gv)) ->
  ENTAIL Delta_inflate5_hl, PROPx [] (LOCALx (ret_locals F)
     (SEPx [Y; locals_rep F; T; mem_mgr (f_gv F); zfuncs (f_gv F); X])) |-- RA_return RR (Some (zv r))).
{ intros F Y T X r E1 E2 E3 E4 HX. unfold RR, POSTCONDITION, abbreviate. simpl RA_return.
  unfold ret_locals, locals_rep; rewrite E1, E2, E3, E4. unfold stackframe_of; simpl fn_vars. simpl fold_right. go_lowerx.
  rewrite !var_block_data_at_ by (reflexivity || auto). unfold_lift. erewrite !lvar_eval_lvar by eassumption.
  sep_apply HX.
  Intros z' st' ow. Exists r z' st' ow. entailer!. }
change Delta with Delta_inflate5_hl.
apply body_reshape.
assert (ISLc: is_live strmp (Some (lcanon L)) = Some (lcanon L)).
{ unfold is_live. destruct (eq_dec strmp nullval); [contradiction | reflexivity]. }
eapply semax_seq.
{ eapply semax_Delta_subsumption; [exact DSUB | ].
  eapply semax_pre.
  2: apply (pro_part6 _ gv shs strmp z (Some (lcanon L)) ib inp ob flush gsh tsh itok otok
              v_here v_last v_hbuf Hd RR); try assumption.
  - unfold pro_pre6. rewrite ISLc, htok6_lcanon by exact EH. unfold bufs_opt. entailer!.
  - intros BAD. apply (inflate_bad_some _ _ _ L) in BAD.
    unfold RR, POSTCONDITION, abbreviate. simpl RA_return.
    unfold stackframe_of; simpl fn_vars. simpl fold_right. go_lowerx.
    rewrite !var_block_data_at_ by (reflexivity || auto). unfold_lift. erewrite !lvar_eval_lvar by eassumption.
    Exists Z_STREAM_ERROR z (Some L) (@nil Z). rewrite ISLc, ISL.
    sep_apply (istream_opt_canon_8 gv shs strmp z L LOK8).
    unfold Hd. sep_apply (head_mem8_c L EH EM).
    unfold bufs_opt. entailer!.
    left. auto. }
unfold pro_post6. Intros L' o.
apply semax_extract_prop. intros (EL1 & EO & NBc & LOK & ZOK & WS & _). subst ob.
assert (L' = lcanon L) by congruence. subst L'.
assert (NB: ~ inflate_bad strmp z (Some L) ib (Some o)).
{ intros BAD. apply NBc. apply (inflate_bad_some _ _ L). exact BAD. }
rewrite mkF_lcanon, xfr_lcanon, m_init_lcanon, lstateH_mcanon.
set (F := mkF gv shs strmp L ib o gsh tsh z v_here v_last v_hbuf flush).
set (X := xfr L itok otok ib o).
set (m0 := m_init z L inp).
pose proof LOK8 as (LP & _ & _ & LH8 & _ & LW & _ & LHD & _).
assert (FOK: frame_ok5 F) by (unfold frame_ok5, frame_ok, F, mkF; simpl; auto).
assert (INP: Zlength inp <= Int.max_signed /\ bytes_ok inp).
{ destruct ib as [ | ish ip ilo ilen ic].
  - subst inp. split; [rewrite Zlength_nil; rep_lia | constructor].
  - destruct H3 as [(_ & _ & _ & _ & _ & _ & _ & HB) HA]. split; [lia | exact HB]. }
assert (MW: mwf3_8 m0).
{ split; [ | exact LH8]. unfold m0. rewrite <- m_init_lcanon. apply m_init_mwf3; tauto. }
assert (OI: out_inv m0).
{ apply m_init_out_inv. destruct ZOK as (_ & ? & _); lia. }
assert (WI0: win_inv5 (m_s m0)).
{ unfold m0. rewrite m_init_s. apply s_typedo_win_inv5. exact (live_win_inv5 _ LOK). }
assert (HD0: hd_ok F m0).
{ unfold hd_ok, m0, F, mkF. rewrite m_init_s. cbn [f_xb f_nb f_cb m_h m_init].
  unfold s_typedo. destruct (i_mode (l_s L) =? Zlib.proof.inflate.Model.TYPE); exact LHD. }
assert (DT: srange (zf_dt z)) by (destruct ZOK as (_&_&_&_&?&_); assumption).
assert (WIN0: i_win (m_s m0) = i_win (l_s L)).
{ unfold m0. rewrite m_init_s. unfold s_typedo.
  destruct (i_mode (l_s L) =? Zlib.proof.inflate.Model.TYPE); reflexivity. }
assert (HD8m: Hd = hd8a F m0).
{ unfold Hd, hd8a, head_rep8a, F, mkF. cbn [f_hsh f_headp f_xb f_nb f_cb].
  unfold m0. rewrite m_init_s, fextra_typedo. reflexivity. }
rewrite HD8m.
eapply semax_seq.
{ apply (HNL _ F X m0 m0 RR FOK).
  - intros r m' HL' [HW3 HW8] HDm HM' HI' (HWin & HWV & HIP).
    apply RET; [reflexivity | reflexivity | reflexivity | reflexivity | ].
    destruct (fin_ok8_live F m' (mwf3_fin_ok5 _ HW3 HWV) HW8 HDm) as [HLV HZV];
      [exact LP | exact LW | exact DT | ].
    Exists (z_of F m') (Some (live_of F m')) (m_ow m').
    apply andp_right.
    + apply prop_right. right. split; [exact NB | ].
      exists L, o, (Res r m' None), (l_winp L).
      split; [reflexivity | ]. split; [reflexivity | ].
      split; [exists (IRet r m'); split; [exact HL' | reflexivity] | ].
      split; [simpl; replace inp with (m_inp m') by (rewrite HIP; reflexivity); exact (mw_snx _ (mwf3_mwf _ HW3)) | ].
      split; [reflexivity | ]. split; [reflexivity | ]. split; [reflexivity | ].
      split; [auto | reflexivity].
    + rewrite ISL. unfold X, xfr. sep_apply (mem_rep_istream8 F m' HLV HZV WS NN HI' HM').
      unfold bufs_opt, F; cbn [f_gv f_shs f_strmp f_ib f_ob f_gsh f_tsh mkF]. cancel.
  - auto.
  - exact MW.
  - reflexivity.
  - exact HD0.
  - unfold m_mode, m0. rewrite m_init_s, hdr_mode_typedo. exact EM.
  - unfold m0. rewrite m_init_s. unfold s_typedo.
    destruct (i_mode (l_s L) =? Zlib.proof.inflate.Model.TYPE); exact EH.
  - split; [exact OI | split; [reflexivity | split; [exact WI0 | reflexivity]]]. }
unfold loop_exit8. apply semax_extract_exists. intro m. apply semax_extract_prop.
intros (LP' & MW' & HDm & ML & HMm & HIm & (OI' & WI & WV & IPm)).
apply (HEXIT _ F X m RR FOK MW' ML OI' WV HMm).
intros res winp HIL (FO & DTr & EH' & EHd & EI & HMr) HWP.
set (F' := set_f_winp_dt F winp (res_dt F res)).
assert (HD': hd_ok F' (r_m res)).
{ unfold hd_ok. rewrite EH', EHd. exact HDm. }
assert (TK: hdr_tok F m = hdr_tok F' (r_m res)).
{ unfold hdr_tok. rewrite EH', EHd. reflexivity. }
assert (HIr: i_head (m_s (r_m res)) = true) by (rewrite EHd; exact HIm).
assert (HW8r: hwf8 (m_h (r_m res))) by (rewrite EH'; exact (proj2 MW')).
rewrite TK.
change (hd8a F (r_m res)) with (hd8a F' (r_m res)).
apply (RET F'); [reflexivity | reflexivity | reflexivity | reflexivity | ].
destruct (fin_ok8_live F' (r_m res) FO HW8r HD') as [HLV HZV].
{ exact LP. }
{ exact LW. }
{ unfold F', res_dt. simpl. destruct (r_dtype res) eqn:ED; [apply DTr; reflexivity | exact DT]. }
Exists (z_of F' (r_m res)) (Some (live_of F' (r_m res))) (m_ow (r_m res)).
apply andp_right.
- apply prop_right. right. split; [exact NB | ].
  exists L, o, res, winp.
  split; [reflexivity | ]. split; [reflexivity | ].
  split; [exists (IBrk m); split; [exact LP' | exact HIL] | ].
  split; [destruct FO as (_ & _ & _ & _ & _ & FS & _); cbn [mcanon set_m_h m_snx m_inp] in FS;
          rewrite EI, IPm in FS; exact FS | ].
  split; [reflexivity | ]. split; [reflexivity | ]. split; [reflexivity | ].
  split; [ | reflexivity].
  intros HW1. apply HWP. rewrite WI, WIN0. exact HW1.
- rewrite ISL. unfold X, xfr. sep_apply (mem_rep_istream8 F' (r_m res) HLV HZV WS NN HIr HMr).
  unfold bufs_opt, F', F; cbn [f_gv f_shs f_strmp f_ib f_ob f_gsh f_tsh mkF set_f_winp_dt]. cancel.
Qed.

Lemma body8_bc_of : hloop8_stmt -> nhloop8_stmt -> exit8_stmt -> rth8_delta_stmt ->
  body8_stmt hd8pre_b /\ body8_stmt hd8pre_c.
Proof.
  intros HL HN HE HD. split; [apply body8_b | apply body8_c]; assumption.
Qed.
