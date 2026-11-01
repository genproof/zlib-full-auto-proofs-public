(* inflate()'s body against RTH9Spec.inflate_spec9 from the prologue (RTH9Parts.pro_part9_stmt), the main loop
   (RTH9AKit.loop9_for) and the exit (RTH9AKit.exit9_for).

   A stream that is not live only gets Z_STREAM_ERROR from the prologue.  On a live stream L the prologue runs on
   the stream with the small header RTH8W.lcanon L, the header part of head_mem9 L in the frame; that part is the
   header RTH9HDefs.hd9 of the first machine m_init z L inp (RTH9ABodyKit.head9_init).  Then ONE main loop over the
   machines of the call, whatever the mode, and the exit; a final machine with its header hd9 is inflate_spec9's
   postcondition (RTH9ABodyKit.mem_rep_istream9).  As RTH8BCBody.body8_b. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.roundtrip.RTHSpec.
Require Import Zlib.proof.roundtrip.RTH8Spec.
Require Import Zlib.proof.roundtrip.RTH9AKit.
Require Import Zlib.proof.inflate_api.Body5Conv.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.roundtrip.RTH8BCBody.
Require Import Zlib.proof.roundtrip.RTH9ABodyKit.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Lemma body9_from (fast: funspec) :
  funspec_sub fast (snd inflate_fast_spec3_hl) -> pro_part9_stmt -> loop9_for fast -> exit9_for ->
  forall {Espec: OracleKind}, semax_body Vprog_inflate (Gprog_inflate8 fast) f_inflate inflate_spec9.
Proof.
intros FS PRO LOOP EXIT E.
start_function.
rename H5 into HD9.
match goal with |- semax _ _ _ ?R => set (RR := R) end.
change Delta with (Delta_inflate9 fast).
apply body_reshape.
destruct (is_live strmp st) as [L | ] eqn:ISL.
2: {
  rewrite (istream8_opt_nolive gv shs strmp z st ISL).
  eapply semax_seq.
  { eapply semax_Delta_subsumption; [exact (rth9_sub_5 fast FS) | ].
    eapply semax_pre.
    2: apply (PRO _ gv shs strmp z st ib inp ob flush gsh tsh itok otok v_here v_last v_hbuf emp RR);
       try assumption.
    - unfold pro_pre6. rewrite ISL. unfold head_opt9, htok6, bufs_opt. entailer!.
    - intros BAD.
      unfold RR, POSTCONDITION, abbreviate. simpl RA_return.
      unfold stackframe_of; simpl fn_vars. simpl fold_right. go_lowerx.
      rewrite !var_block_data_at_ by (reflexivity || auto). unfold_lift. erewrite !lvar_eval_lvar by eassumption.
      Exists Z_STREAM_ERROR z st (@nil Z). rewrite (istream8_opt_nolive gv shs strmp z st ISL), ISL.
      unfold head_opt9, htok6, bufs_opt. entailer!.
      left. auto. }
  unfold pro_post6. Intros L o.
  apply semax_extract_prop. intros (EL & _ & _ & _ & _ & _ & NN). exfalso.
  unfold is_live in ISL. destruct (eq_dec strmp nullval); congruence. }
assert (NN: strmp <> nullval /\ st = Some L).
{ unfold is_live in ISL. destruct (eq_dec strmp nullval); [discriminate | split; congruence]. }
destruct NN as [NN ->].
destruct HD9 as [EH SW].
unfold head_opt9 at 1. rewrite head_mem9_split.
sep_apply (istream8_opt_canon gv shs strmp z L NN). Intros.
match goal with HL8: live_ok8 L |- _ => rename HL8 into LOK8 end.
assert (RET: forall (D: tycontext) (F: frame) (Y T X: mpred) (r: Z),
  f_vhere F = v_here -> f_vlast F = v_last -> f_vhbuf F = v_hbuf -> f_gv F = gv ->
  Y * T * X |-- (EX z': zfields, EX st': option live, EX ow: list Z,
          !! (inflate_rel flush strmp z (Some L) ib inp ob r z' st' ow /\ hd9_ok st') &&
          (istream8_opt gv shs strmp z' st' * head_opt9 (is_live strmp st') *
           bufs_opt (is_live strmp (Some L)) ib ob ow itok otok *
           tables_rep gsh gv * crc_table_at tsh gv)) ->
  ENTAIL D, PROPx [] (LOCALx (ret_locals F)
     (SEPx [Y; locals_rep F; T; mem_mgr (f_gv F); zfuncs (f_gv F); X])) |-- RA_return RR (Some (zv r))).
{ intros D F Y T X r E1 E2 E3 E4 HX. unfold RR, POSTCONDITION, abbreviate. simpl RA_return.
  unfold ret_locals, locals_rep; rewrite E1, E2, E3, E4. unfold stackframe_of; simpl fn_vars. simpl fold_right. go_lowerx.
  rewrite !var_block_data_at_ by (reflexivity || auto). unfold_lift. erewrite !lvar_eval_lvar by eassumption.
  sep_apply HX.
  Intros z' st' ow. rewrite ISL. Exists r z' st' ow. unfold bufs_opt. entailer!. }
assert (ISLc: is_live strmp (Some (lcanon L)) = Some (lcanon L)).
{ unfold is_live. destruct (eq_dec strmp nullval); [contradiction | reflexivity]. }
eapply semax_seq.
{ eapply semax_Delta_subsumption; [exact (rth9_sub_5 fast FS) | ].
  eapply semax_pre.
  2: apply (PRO _ gv shs strmp z (Some (lcanon L)) ib inp ob flush gsh tsh itok otok
              v_here v_last v_hbuf (hdm9 L) RR); try assumption.
  - unfold pro_pre6. rewrite ISLc, htok6_lcanon by exact EH. unfold bufs_opt. entailer!.
  - intros BAD. apply (inflate_bad_some _ _ _ L) in BAD.
    unfold RR, POSTCONDITION, abbreviate. simpl RA_return.
    unfold stackframe_of; simpl fn_vars. simpl fold_right. go_lowerx.
    rewrite !var_block_data_at_ by (reflexivity || auto). unfold_lift. erewrite !lvar_eval_lvar by eassumption.
    Exists Z_STREAM_ERROR z (Some L) (@nil Z). rewrite ISLc, ISL.
    sep_apply (istream_opt_canon_8 gv shs strmp z L LOK8).
    rewrite htok6_lcanon by exact EH. unfold head_opt9. rewrite head_mem9_split.
    unfold bufs_opt. entailer!.
    split; [left; auto | split; assumption]. }
unfold pro_post6. Intros L' o.
apply semax_extract_prop. intros (EL1 & EO & NBc & LOK & ZOK & WS & _). subst ob.
assert (L' = lcanon L) by congruence. subst L'.
assert (NB: ~ inflate_bad strmp z (Some L) ib (Some o)).
{ intros BAD. apply NBc. apply (inflate_bad_some _ _ L). exact BAD. }
rewrite mkF_lcanon, xfr_lcanon, m_init_lcanon, lstateH_mcanon.
set (F := mkF gv shs strmp L ib o gsh tsh z v_here v_last v_hbuf flush).
set (X := xfr L itok otok ib o).
set (m0 := m_init z L inp).
eapply semax_pre with (P' := lstateH F (X * hd9 F m0) m0).
{ apply andp_left2. apply lstateH_X_derives. apply sepcon_derives; [apply derives_refl | apply head9_init]. }
pose proof LOK8 as (LP & _ & _ & LH8 & _ & LW & _ & LHD & _).
assert (FOK: frame_ok5 F) by (unfold frame_ok5, frame_ok, F, mkF; simpl; auto).
assert (INP: Zlength inp <= Int.max_unsigned /\ bytes_ok inp).
{ destruct ib as [ | ish ip ilo ilen ic].
  - subst inp. split; [rewrite Zlength_nil; rep_lia | constructor].
  - destruct H3 as [(_ & _ & _ & _ & _ & _ & _ & HB) HA]. destruct ZOK as ((_ & ZA) & _).
    split; [lia | exact HB]. }
assert (MW: mwf3_9 m0).
{ split; [ | exact LH8]. unfold m0. rewrite <- m_init_lcanon. apply m_init_mwf3W; first [exact SW | tauto]. }
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
assert (HI0: i_head (m_s m0) = true).
{ unfold m0. rewrite m_init_s. unfold s_typedo.
  destruct (i_mode (l_s L) =? Zlib.proof.inflate.Model.TYPE); exact EH. }
eapply semax_seq.
{ apply (LOOP _ F X m0 RR FOK).
  - intros r m' HL' MW' HDm HM' HI' (HWin & HWV & HIP) SW'.
    apply RET; [reflexivity | reflexivity | reflexivity | reflexivity | ].
    replace (hd9a F m') with (hd9 F m') by (unfold hd9; rewrite HM'; reflexivity).
    pose proof (mwf3W_fin_ok9 (mcanon m') (proj1 MW') HWV) as FO.
    destruct (fin_ok9_live8 F m' FO (proj2 MW') HDm) as [HLV HZV]; [exact LP | exact LW | exact DT | ].
    Exists (z_of F m') (Some (live_of F m')) (m_ow m').
    apply andp_right.
    + apply prop_right. split; [ | split; [exact HI' | exact SW']].
      right. split; [exact NB | ].
      exists L, o, (Res r m' None), (l_winp L).
      split; [reflexivity | ]. split; [reflexivity | ].
      split; [exists (IRet r m'); split; [exact HL' | reflexivity] | ].
      split; [destruct FO as (_ & _ & _ & _ & _ & FSN & _); cbn [mcanon set_m_h m_snx m_inp] in FSN;
              simpl; rewrite HIP in FSN; exact FSN | ].
      split; [reflexivity | ]. split; [reflexivity | ]. split; [reflexivity | ].
      split; [auto | reflexivity].
    + rewrite ISL. unfold X, xfr. sep_apply (mem_rep_istream9 F m' HLV HZV WS NN HI').
      unfold bufs_opt, F; cbn [f_gv f_shs f_strmp f_ib f_ob f_gsh f_tsh mkF]. cancel.
  - exact MW.
  - reflexivity.
  - exact HD0.
  - exact HI0.
  - split; [exact OI | split; [reflexivity | split; [exact WI0 | reflexivity]]]. }
unfold loop_exit9. apply semax_extract_exists. intro m. apply semax_extract_prop.
intros (LP' & MW' & HDm & ML & HIm & (OI' & WI & WV & IPm)).
eapply semax_Delta_subsumption; [exact (rth9_sub_hl fast FS) | ].
apply (EXIT _ F X m RR FOK MW' ML OI' WV HIm).
intros res winp HIL (FO & SWr & DTr & EH' & EHd & EI) HWP.
set (F' := set_f_winp_dt F winp (res_dt F res)).
assert (HD': hd_ok F' (r_m res)).
{ unfold hd_ok. rewrite EH', EHd. exact HDm. }
assert (TK: hdr_tok F m = hdr_tok F' (r_m res)).
{ unfold hdr_tok. rewrite EH', EHd. reflexivity. }
assert (HIr: i_head (m_s (r_m res)) = true) by (rewrite EHd; exact HIm).
assert (HW8r: hwf8 (m_h (r_m res))) by (rewrite EH'; exact (proj2 MW')).
rewrite TK.
change (hd9 F (r_m res)) with (hd9 F' (r_m res)).
apply (RET _ F'); [reflexivity | reflexivity | reflexivity | reflexivity | ].
destruct (fin_ok9_live8 F' (r_m res) FO HW8r HD') as [HLV HZV].
{ exact LP. }
{ exact LW. }
{ unfold F', res_dt. simpl. destruct (r_dtype res) eqn:ED; [apply DTr; reflexivity | exact DT]. }
Exists (z_of F' (r_m res)) (Some (live_of F' (r_m res))) (m_ow (r_m res)).
apply andp_right.
- apply prop_right. split; [ | split; [exact HIr | exact SWr]].
  right. split; [exact NB | ].
  exists L, o, res, winp.
  split; [reflexivity | ]. split; [reflexivity | ].
  split; [exists (IBrk m); split; [exact LP' | exact HIL] | ].
  split; [destruct FO as (_ & _ & _ & _ & _ & FSN & _); cbn [mcanon set_m_h m_snx m_inp] in FSN;
          rewrite EI, IPm in FSN; exact FSN | ].
  split; [reflexivity | ]. split; [reflexivity | ]. split; [reflexivity | ].
  split; [ | reflexivity].
  intros HW1. apply HWP. rewrite WI, WIN0. exact HW1.
- rewrite ISL. unfold X, xfr. sep_apply (mem_rep_istream9 F' (r_m res) HLV HZV WS NN HIr).
  unfold bufs_opt, F', F; cbn [f_gv f_shs f_strmp f_ib f_ob f_gsh f_tsh mkF set_f_winp_dt]. cancel.
Qed.
