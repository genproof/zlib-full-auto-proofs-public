(* inflateEnd's body against the v5 spec (Spec5.v inflateEnd_spec), for Body5_reset.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.ResetSplit5.
Require Import Zlib.proof.inflate_api.ResetKit5.
#[local] Existing Instance Zlib.units.Inflate.CS.

Local Open Scope logic.

Lemma zfuncs_isptr_end: forall gv zcf, zcf = gv _zcfree -> zfuncs gv |-- !! isptr zcf.
Proof.
  intros. subst. unfold zfuncs, func_ptr'.
  eapply derives_trans; [apply sepcon_derives; apply andp_left1; apply func_ptr_isptr | ].
  rewrite sepcon_prop_prop. apply prop_derives. tauto.
Qed.

Lemma state_free_end: forall gv sp strmp headp winp s,
  field_at Ews t_state (DOT _strm) strmp sp *
  field_at Ews t_state (DOT _mode) (zv (i_mode s)) sp *
  field_at Ews t_state (DOT _window) (if i_win s then winp else nullval) sp *
  U_end gv sp headp winp s * state_pad sp |-- data_at_ Ews t_state sp.
Proof. intros. rewrite <- state_rep_end. apply state_free. Qed.

Lemma body5_inflateEnd {E: OracleKind}: semax_body Vprog_inflate Gp_end f_inflateEnd inflateEnd_spec.
Proof.
  start_function.
  unfold istream_opt.
  destruct (eq_dec strmp nullval) as [Hn | Hn].
  - subst strmp.
    forward_call (nullval, shs, default_val t_strm, nullval, 0, false, gv).
    { simpl. cancel. }
    forward_if; [forward; cancel | discriminate].
  - destruct st as [L | ].
    2: { unfold istream, zstrm_at, strm_rep. Intros.
    remember (gv _zcalloc) as zca eqn:Hzca. remember (gv _zcfree) as zcf eqn:Hzcf.
    forward_call (strmp, shs, (zf_ni z, (Vint (Int.repr (zf_ai z)), (lv (zf_tin z), (zf_no z,
      (Vint (Int.repr (zf_ao z)), (lv (zf_tout z), (msg_val gv (zf_msg z), (nullval, (zca, (zcf,
      (nullval, (zv (zf_dt z), (lv (zf_adler z), zf_res z))))))))))))), nullval, 0, false, gv).
    { destruct (eq_dec strmp nullval); [contradiction | ]. cancel. }
    { right. split; [auto | ]. subst zca zcf. repeat split. }
    destruct (eq_dec strmp nullval); [contradiction | ].
    forward_if.
    { forward. unfold is_live, istream_opt, istream, zstrm_at, strm_rep.
      rewrite !if_false by auto. entailer!. }
    { match goal with H: Int.repr 1 = Int.zero |- _ => inversion H end. } }
    destruct L as [sp winp s h headp hsh xb nb cb].
    unfold istream, state_mem. cbn [l_sp l_winp l_s l_h l_headp]. rewrite state_rep_end. Intros.
    unfold zstrm_at, strm_rep.
    remember (gv _zcalloc) as zca eqn:Hzca. remember (gv _zcfree) as zcf eqn:Hzcf.
    assert (HMD: HEAD <= i_mode s <= SYNC) by (destruct H1 as (_ & SW & _); exact (sw_mode _ SW)).
    assert (HSP: isptr sp) by (destruct H1 as (P & _); exact P).
    forward_call (strmp, shs, (zf_ni z, (Vint (Int.repr (zf_ai z)), (lv (zf_tin z), (zf_no z,
      (Vint (Int.repr (zf_ao z)), (lv (zf_tout z), (msg_val gv (zf_msg z), (sp, (zca, (zcf,
      (nullval, (zv (zf_dt z), (lv (zf_adler z), zf_res z))))))))))))), sp, i_mode s, true, gv).
    { destruct (eq_dec strmp nullval); [contradiction | ]. cancel. }
    { split; [ | unfold HEAD, SYNC in *; rep_lia].
      right. split; [auto | ]. subst zca zcf. repeat split. }
    destruct (eq_dec strmp nullval) as [Hx | Hx]; [contradiction | ].
    rewrite (proj2 (Z.leb_le _ _) (proj1 HMD)), (proj2 (Z.leb_le _ _) (proj2 HMD)). simpl andb. cbv iota.
    forward_if; [contradiction | ]. Intros.
    forward. (* t'9 = strm->state *)
    forward. (* state = cast *)
    forward. (* t'5 = state->window *)
    { unfold win_rep; destruct (i_win s); entailer!. }
    match goal with |- semax _ (PROPx ?P (LOCALx (_ :: ?Q) (SEPx [?A; ?B; ?C; ?D; ?E2; ?F; ?G; win_rep winp s; ?I; ?J]))) _ _ =>
      forward_if (PROPx P (LOCALx Q (SEPx [A; B; C; D; E2; F; G; I; J]))) end.
    { unfold win_rep; destruct (i_win s); entailer!. }
    { (* free the window *)
      destruct (i_win s) eqn:EW; [ | contradiction].
      unfold win_rep at 1. rewrite EW. Intros.
      assert_PROP (isptr zcf).
      { go_lower. rewrite (add_andp (zfuncs gv) _ (zfuncs_isptr_end gv zcf Hzcf)). normalize; try (apply prop_right; auto). }
      forward. forward. forward.
      assert_PROP (isptr winp) by entailer!.
      unfold zfuncs. rewrite <- Hzcf, <- Hzca. flatten_sepcon_in_SEP.
      forward_call (tarray tuchar (2 ^ i_wbits s), winp, gv, nullval).
      { rewrite if_false by (destruct winp; try contradiction; discriminate).
        sep_apply (data_at_data_at_ Ews (tarray tuchar (2 ^ i_wbits s))). cancel. }
      unfold zfuncs. rewrite <- Hzcf, <- Hzca. entailer!. }
    { forward. destruct (i_win s) eqn:EW.
      - assert_PROP (isptr winp) by (unfold win_rep; rewrite EW; entailer!). subst; contradiction.
      - unfold win_rep; rewrite EW. entailer!. }
    assert_PROP (isptr zcf).
    { go_lower. rewrite (add_andp (zfuncs gv) _ (zfuncs_isptr_end gv zcf Hzcf)). normalize; try (apply prop_right; auto). }
    forward. forward. forward.
    unfold zfuncs. rewrite <- Hzcf, <- Hzca. flatten_sepcon_in_SEP.
    forward_call (t_state, sp, gv, nullval).
    { rewrite if_false by (destruct sp; try contradiction; discriminate).
      sep_apply (state_free_end gv sp strmp headp winp s). cancel. }
    forward. (* strm->state = Z_NULL *)
    forward. (* return Z_OK *)
    unfold is_live, istream_opt, istream, zstrm_at, strm_rep, zfuncs. rewrite !if_false by auto.
    entailer!.
Qed.
