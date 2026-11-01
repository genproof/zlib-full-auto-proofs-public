(* inflate()'s exit inf_leave, the window update (Body5ExitKit.v ex_win), for calls of any uInt size:
   if (state->wsize || (out != strm->avail_out && state->mode < BAD && (state->mode < CHECK || flush != Z_FINISH)))
     if (updatewindow(strm, strm->next_out, out - strm->avail_out)) { state->mode = MEM; return Z_MEM_ERROR; }
   This file: the condition (semax_ex_cond9); RTH9ExitCall.v: the call and the whole update.
   The proof scripts are those of the headless port src/proof/hl/inflate_api/HlBody5ExitWin.v (copied by hand,
   with Body5ExitWin.v's win_data_len / win_data_slice / swf_restore); only the bounds change: the output space
   is up to Int.max_unsigned and the machine invariant is InvW.mwf3W.  updatewindow's specification
   (Callees3.updatewindow_spec3) takes any uInt length. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.hl.inflate_api.HlBody5Parts.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.hl.inflate_api.HlBody5ExitKit.
Require Import Zlib.proof.hl.inflate_api.HlBody5ExitWin.
Require Import Zlib.proof.inflate.InvW.

#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Lemma mwfW_left: forall m, mwfW m -> 0 <= m_left m <= Int.max_unsigned.
Proof. intros m H. destruct H. unfold m_left. pose proof (Zlength_nonneg (m_ow m)). lia. Qed.

Lemma semax_ex_cond9 {Espec: OracleKind} (F: frame) (X: mpred) (m: mst):
  0 <= i_wsize (m_s m) <= Int.max_unsigned -> HEAD <= i_mode (m_s m) <= SYNC ->
  m_sow m = Zlength (m_ow m) -> urange (m_out m) -> 0 <= m_left m <= Int.max_unsigned ->
  Int.min_signed <= f_flush F <= Int.max_signed -> writable_share (f_shs F) ->
  semax Delta_inflate5_hl (lstate_hl F X m) ex_cond
    (normal_ret_assert (lstate_t_hl F X m (Vint (Int.repr (b2z (leave_ok (f_flush F) m)))))).
Proof.
  intros RWS RM ESOW RO RL RF HWS.
  cbv beta iota zeta delta [ex_cond ex_win inflate_exit f_inflate fn_body].
  rewrite lstate_esplit_hl. unfold lstate_t_hl. rewrite mem_rep_esplit_hl. unfold lstate_e_hl, strm_e, strm_rep, state_f9.
  rewrite ESOW.
  abbreviate_semax.
  remember (f_gv F _zcalloc) as zca eqn:Hzca. remember (f_gv F _zcfree) as zcf eqn:Hzcf.
  forward.
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?S))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _t'97 (Vint (Int.repr (b2z (leave_ok (f_flush F) m)))) :: L) (SEPx S))) end.
  - forward. entailer!.
    apply int_repr_nz in H1; [ | rep_lia].
    unfold leave_ok, b2z. rewrite (proj2 (Z.eqb_neq _ _) H1). reflexivity.
  - apply int_repr_z in H1; [ | rep_lia].
    forward.
    match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?S))) _ _ =>
      forward_if (PROPx P (LOCALx (temp _t'98 (Vint (Int.repr (b2z (negb (m_out m =? m_left m) && (m_mode m <? BAD))%bool))) :: L) (SEPx S))) end.
    + forward. forward. entailer!.
      assert (Ne: m_out m <> m_left m) by (intro E; apply H2; rewrite E; reflexivity).
      rewrite (proj2 (Z.eqb_neq _ _) Ne). cbn [negb andb].
      rewrite lt_val by (unfold HEAD, SYNC in *; rep_lia). reflexivity.
    + forward. entailer!.
      apply repr_inj_u in H2; [ | unfold urange in RO; rep_lia | unfold m_left in RL; rep_lia].
      change (m_aout m - Zlength (m_ow m)) with (m_left m) in H2.
      rewrite H2, Z.eqb_refl. reflexivity.
    + forward_if.
      * forward.
        forward_if.
        -- rewrite Int.signed_repr in H3 by (unfold HEAD, SYNC in *; rep_lia).
           forward. forward. entailer!.
           unfold leave_ok, m_mode in *. rewrite H1, H2.
           assert (H3': (i_mode (m_s m) <? CHECK) = true) by (apply Z.ltb_lt; unfold CHECK; lia).
           rewrite H3'. reflexivity.
        -- rewrite Int.signed_repr in H3 by (unfold HEAD, SYNC in *; rep_lia).
           forward. forward. forward. entailer!.
           unfold leave_ok, m_mode in *. rewrite H1, H2.
           assert (H3': (i_mode (m_s m) <? CHECK) = false) by (apply Z.ltb_ge; unfold CHECK; lia).
           rewrite H3'. cbn [orb negb andb].
           unfold Z_FINISH. rewrite ne_val by rep_lia. reflexivity.
      * forward. entailer!.
        unfold leave_ok, m_mode in *. rewrite H1, H2. reflexivity.
  - entailer!.
Qed.
