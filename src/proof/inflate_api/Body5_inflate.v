(* The body of inflate(), version 5 (Bodies5.v body_inflate_from_cases5). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.Body5Parts.
Require Import Zlib.proof.inflate_api.Body5Conv.
Require Import Zlib.proof.inflate_api.Body5Pro.
Require Import Zlib.proof.inflate_api.Body5Loop.
Require Import Zlib.proof.inflate_api.Body5Exit.
Require Import Zlib.proof.inflate_api.Body5StepInv.
Require Import Zlib.proof.inflate_api.Body5StepHdr.
Require Import Zlib.proof.inflate_api.Body5Fin.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Lemma body_inflate_proof5 : body_inflate_from_cases5.
Proof.
intros HC HS HD E.
start_function.
match goal with |- semax _ _ _ ?R => set (RR := R) end.
assert (RET: forall (F: frame) (Y T X: mpred) (r: Z),
  f_vhere F = v_here -> f_vlast F = v_last -> f_vhbuf F = v_hbuf -> f_gv F = gv ->
  Y * T * X |-- (EX z': zfields, EX st': option live, EX ow: list Z,
          !! (inflate_rel flush strmp z st ib inp ob r z' st' ow) &&
          (istream_opt gv shs strmp z' st' * head_opt (is_live strmp st') *
           bufs_opt (is_live strmp st) ib ob ow itok otok *
           tables_rep gsh gv * crc_table_at tsh gv)) ->
  ENTAIL Delta_inflate5, PROPx [] (LOCALx (ret_locals F)
     (SEPx [Y; locals_rep F; T; mem_mgr (f_gv F); zfuncs (f_gv F); X])) |-- RA_return RR (Some (zv r))).
{ intros F Y T X r E1 E2 E3 E4 HX. unfold RR, POSTCONDITION, abbreviate. simpl RA_return.
  unfold ret_locals, locals_rep; rewrite E1, E2, E3, E4. unfold stackframe_of; simpl fn_vars. simpl fold_right. go_lowerx.
  rewrite !var_block_data_at_ by (reflexivity || auto). unfold_lift. erewrite !lvar_eval_lvar by eassumption.
  sep_apply HX.
  Intros z' st' ow. Exists r z' st' ow. entailer!. }
change Delta with Delta_inflate5.
apply body_reshape.
eapply semax_seq.
{ apply (pro_part5 _ gv shs strmp z st ib inp ob flush gsh tsh itok otok v_here v_last v_hbuf RR); auto.
  intros BAD. unfold RR, POSTCONDITION, abbreviate. simpl RA_return.
  unfold stackframe_of; simpl fn_vars. simpl fold_right. go_lowerx.
  rewrite !var_block_data_at_ by (reflexivity || auto). unfold_lift. erewrite !lvar_eval_lvar by eassumption.
  Exists Z_STREAM_ERROR z st (@nil Z). entailer!.
  left. auto. }
unfold pro_post. Intros L o.
apply semax_extract_prop. intros (EL & EO & NB & LOK & ZOK & WS & NN). subst st ob.
set (F := mkF gv shs strmp L ib o gsh tsh z v_here v_last v_hbuf flush).
set (X := xfr L itok otok ib o).
set (m0 := m_init z L inp).
pose proof LOK as (LP & LS & LM & LH & LS3 & LW & LW0 & LHD & LWIN).
assert (FOK: frame_ok5 F) by (unfold frame_ok5, frame_ok, F, mkF; simpl; auto).
assert (INP: Zlength inp <= Int.max_signed /\ bytes_ok inp).
{ destruct ib as [ | ish ip ilo ilen ic].
  - subst inp. split; [rewrite Zlength_nil; rep_lia | constructor].
  - destruct H3 as [(_ & _ & _ & _ & _ & _ & _ & HB) HA]. split; [lia | exact HB]. }
assert (MW: mwf3 m0).
{ apply m_init_mwf3; tauto. }
assert (OI: out_inv m0).
{ apply m_init_out_inv. destruct ZOK as (_ & ? & _); lia. }
assert (WI0: win_inv5 (m_s m0)).
{ unfold m0. rewrite m_init_s. apply s_typedo_win_inv5, live_win_inv5, LOK. }
assert (HD0: hd_ok F m0).
{ unfold hd_ok, m0, F, mkF. rewrite m_init_s. cbn [f_xb f_nb f_cb m_h m_init].
  unfold s_typedo. destruct (i_mode (l_s L) =? Zlib.proof.inflate.Model.TYPE); exact LHD. }
assert (DT: srange (zf_dt z)) by (destruct ZOK as (_&_&_&_&?&_); exact H7).
assert (ISL: is_live strmp (Some L) = Some L).
{ unfold is_live. destruct (eq_dec strmp nullval); [contradiction | reflexivity]. }
assert (WIN0: i_win (m_s m0) = i_win (l_s L)).
{ unfold m0. rewrite m_init_s. unfold s_typedo.
  destruct (i_mode (l_s L) =? Zlib.proof.inflate.Model.TYPE); reflexivity. }
eapply semax_seq.
{ apply (loop_part5 _ F X m0
           (fun m => out_inv m /\ i_win (m_s m) = i_win (m_s m0) /\ win_inv5 (m_s m) /\ m_inp m = inp)
           (fun m => i_win (m_s m) = i_win (m_s m0) /\ win_inv5 (m_s m) /\ m_inp m = inp)
           RR HC HS HD stepf2_hdr FOK).
  - intros m HW HL0 _ (OIm & WIm & WVm & IPm).
    pose proof (stepf_inv5 (f_flush F) m HW HL0 OIm WVm) as HSI.
    pose proof (stepf2_hdr (f_flush F) m HW HL0) as HSH.
    destruct (stepf2 (f_flush F) lenfix_list distfix_list m); intuition congruence.
  - exact MW.
  - reflexivity.
  - exact HD0.
  - split; [exact OI | split; [reflexivity | split; [exact WI0 | reflexivity]]].
  - intros r m' HL HW HDm (HWin & HWV & HIP).
    apply RET; [reflexivity | reflexivity | reflexivity | reflexivity | ].
    destruct (fin_ok5_live F m' (mwf3_fin_ok5 m' HW HWV) HDm) as [HLV HZV]; [exact LP | exact LW | exact DT | ].
    Exists (z_of F m') (Some (live_of F m')) (m_ow m').
    apply andp_right.
    + apply prop_right. right. split; [exact NB | ].
      exists L, o, (Res r m' None), (l_winp L).
      split; [reflexivity | ]. split; [reflexivity | ].
      split; [exists (IRet r m'); split; [exact HL | reflexivity] | ].
      split; [simpl; rewrite <- HIP; apply (mw_snx _ (mwf3_mwf _ HW)) | ].
      split; [reflexivity | ]. split; [reflexivity | ]. split; [reflexivity | ].
      split; [auto | reflexivity].
    + rewrite ISL. unfold X, xfr. sep_apply (mem_rep_istream5 F m' HLV HZV WS NN).
      unfold bufs_opt, F; cbn [f_gv f_shs f_strmp f_ib f_ob f_gsh f_tsh mkF]. cancel. }
unfold loop_exit. apply semax_extract_exists. intro m. apply semax_extract_prop.
intros (LP' & MW' & HDm & ML & (OI' & WI & WV & IPm)).
apply (exit_part5 _ F X m RR FOK MW' ML OI' WV).
intros res winp HIL HWP.
destruct (leave_fin5 flush m res MW' OI' WV HIL) as (FO & DTr & EH & EHd & EI).
set (F' := set_f_winp_dt F winp (res_dt F res)).
assert (HD': hd_ok F' (r_m res)).
{ unfold hd_ok. rewrite EH, EHd. exact HDm. }
assert (TK: hdr_tok F m = hdr_tok F' (r_m res)).
{ unfold hdr_tok. rewrite EH, EHd. reflexivity. }
rewrite TK.
apply (RET F'); [reflexivity | reflexivity | reflexivity | reflexivity | ].
destruct (fin_ok5_live F' (r_m res) FO HD') as [HLV HZV].
{ exact LP. }
{ exact LW. }
{ unfold F', res_dt. simpl. destruct (r_dtype res) eqn:ED; [apply DTr; reflexivity | exact DT]. }
Exists (z_of F' (r_m res)) (Some (live_of F' (r_m res))) (m_ow (r_m res)).
apply andp_right.
- apply prop_right. right. split; [exact NB | ].
  exists L, o, res, winp.
  split; [reflexivity | ]. split; [reflexivity | ].
  split; [exists (IBrk m); split; [exact LP' | exact HIL] | ].
  split; [destruct FO as (_ & _ & _ & _ & _ & FS & _); rewrite EI, IPm in FS; exact FS | ].
  split; [reflexivity | ]. split; [reflexivity | ]. split; [reflexivity | ].
  split; [ | reflexivity].
  intros HW1. apply HWP. rewrite WI, WIN0. exact HW1.
- rewrite ISL. unfold X, xfr. sep_apply (mem_rep_istream5 F' (r_m res) HLV HZV WS NN).
  unfold bufs_opt, F', F; cbn [f_gv f_shs f_strmp f_ib f_ob f_gsh f_tsh mkF set_f_winp_dt]. cancel.
Qed.
