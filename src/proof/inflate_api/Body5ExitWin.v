(* inflate()'s exit inf_leave: the window update (Body5ExitKit.v ex_win):
   if (state->wsize || (out != strm->avail_out && state->mode < BAD && (state->mode < CHECK || flush != Z_FINISH)))
     if (updatewindow(strm, strm->next_out, out - strm->avail_out)) { state->mode = MEM; return Z_MEM_ERROR; } *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate_api.Body5Parts.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.inflate_api.Body5ExitKit.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Definition ex_cond : statement := match ex_win with Ssequence c _ => c | _ => Sskip end.
Definition ex_call : statement := match ex_win with Ssequence _ (Sifthenelse _ c _) => c | _ => Sskip end.

Lemma ex_win_eq: ex_win = Ssequence ex_cond (Sifthenelse (Etempvar _t'97 tint) ex_call Sskip).
Proof. reflexivity. Qed.

(* lstate with the condition's value in _t'97 *)
Definition lstate_t (F: frame) (X: mpred) (m: mst) (v: val) : environ -> mpred :=
  PROP (in_ok (f_ib F) (m_inp m); out_ok (f_ob F) (m_aout m))
  LOCAL (temp _t'97 v; temp _strm (f_strmp F); temp _flush (zv (f_flush F)); temp _state (f_sp F);
         temp _next (in_ptr (f_ib F) (m_nx m)); temp _put (out_ptr (f_ob F) (Zlength (m_ow m)));
         temp _have (zv (m_have m)); temp _left (zv (m_left m)); temp _hold (lv (m_hold m));
         temp _bits (zv (m_bits m)); temp _in (zv (m_in m)); temp _out (zv (m_out m));
         temp _ret (zv (m_ret m)); temp _leave (zv (m_leave m));
         lvar _here t_code (f_vhere F); lvar _last t_code (f_vlast F);
         lvar _hbuf (tarray tuchar 4) (f_vhbuf F); gvars (f_gv F))
  SEP (mem_rep F m; locals_rep F; hdr_tok F m; mem_mgr (f_gv F); zfuncs (f_gv F); X).

Definition b2z (b: bool) : Z := if b then 1 else 0.

Lemma int_repr_nz: forall x, 0 <= x <= Int.max_unsigned -> Int.repr x <> Int.zero -> x <> 0.
Proof. intros x R H E. subst. apply H. reflexivity. Qed.

Lemma int_repr_z: forall x, 0 <= x <= Int.max_unsigned -> Int.repr x = Int.zero -> x = 0.
Proof.
  intros x R H. apply (f_equal Int.unsigned) in H. rewrite Int.unsigned_repr in H by rep_lia. exact H.
Qed.

Lemma repr_inj_u: forall x y, 0 <= x <= Int.max_unsigned -> 0 <= y <= Int.max_unsigned ->
  Int.repr x = Int.repr y -> x = y.
Proof.
  intros x y Rx Ry H. apply (f_equal Int.unsigned) in H. rewrite !Int.unsigned_repr in H by rep_lia. exact H.
Qed.

Lemma lt_val: forall x y, Int.min_signed <= x <= Int.max_signed -> Int.min_signed <= y <= Int.max_signed ->
  bool2val (Int.lt (Int.repr x) (Int.repr y)) = Vint (Int.repr (b2z (x <? y))).
Proof.
  intros x y Rx Ry. unfold Int.lt. rewrite !Int.signed_repr by rep_lia.
  destruct (zlt x y), (Z.ltb_spec x y); try reflexivity; lia.
Qed.

Lemma ne_val: forall x y, Int.min_signed <= x <= Int.max_signed -> Int.min_signed <= y <= Int.max_signed ->
  bool2val (negb (Int.eq (Int.repr x) (Int.repr y))) = Vint (Int.repr (b2z (negb (x =? y)))).
Proof.
  intros x y Rx Ry. destruct (Z.eqb_spec x y).
  - subst. rewrite Int.eq_true. reflexivity.
  - rewrite Int.eq_false; [reflexivity | ]. intro E. apply (f_equal Int.signed) in E.
    rewrite !Int.signed_repr in E by rep_lia. contradiction.
Qed.

Lemma b2z_true: forall b, Int.repr (b2z b) <> Int.zero -> b = true.
Proof. intros [ | ] H; [reflexivity | exfalso; apply H; reflexivity]. Qed.

Lemma b2z_false: forall b, Int.repr (b2z b) = Int.zero -> b = false.
Proof. intros [ | ] H; [discriminate | reflexivity]. Qed.

Lemma semax_ex_cond {Espec: OracleKind} (F: frame) (X: mpred) (m: mst):
  0 <= i_wsize (m_s m) <= Int.max_unsigned -> HEAD <= i_mode (m_s m) <= SYNC ->
  m_sow m = Zlength (m_ow m) -> urange (m_out m) -> 0 <= m_left m <= Int.max_signed ->
  Int.min_signed <= f_flush F <= Int.max_signed -> writable_share (f_shs F) ->
  semax Delta_inflate5 (lstate F X m) ex_cond
    (normal_ret_assert (lstate_t F X m (Vint (Int.repr (b2z (leave_ok (f_flush F) m)))))).
Proof.
  intros RWS RM ESOW RO RL RF HWS.
  cbv beta iota zeta delta [ex_cond ex_win inflate_exit f_inflate fn_body].
  rewrite lstate_esplit. unfold lstate_t. rewrite mem_rep_esplit. unfold lstate_e, strm_e, strm_rep, state_f9.
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

(* ---------------------------------------------------------------------------------------------- *)
(* the call                                                                                       *)

Lemma state_rep_wp: forall gv sp strmp headp winp s,
  state_rep gv sp strmp headp winp s = state_rep gv sp strmp headp (if i_win s then winp else nullval) s.
Proof. intros. unfold state_rep. destruct (i_win s); reflexivity. Qed.

Lemma win_rep_wp: forall winp s, win_rep winp s = win_rep (if i_win s then winp else nullval) s.
Proof. intros. unfold win_rep. destruct (i_win s); reflexivity. Qed.

Lemma win_data_len: forall m, m_left m <= m_out m <= m_aout m -> Zlength (m_ow m) <= m_aout m <= Int.max_signed ->
  Zlength (win_data m) = m_out m - m_left m.
Proof.
  intros m A B. pose proof (Zlength_nonneg (m_ow m)). unfold win_data, u32, m_left in *.
  rewrite Z.mod_small by rep_lia. rewrite Zlength_sublist; lia.
Qed.

Lemma win_data_slice: forall m (oc: list val) olo on,
  m_left m <= m_out m <= m_aout m -> Zlength (m_ow m) <= m_aout m <= Int.max_signed ->
  0 <= olo -> olo + Zlength (m_ow m) <= on -> Zlength oc = on ->
  sublist (olo + Zlength (m_ow m) - Zlength (win_data m)) (olo + Zlength (m_ow m))
    (sublist 0 olo oc ++ byte_vals (m_ow m) ++ sublist (olo + Zlength (m_ow m)) on oc) = byte_vals (win_data m).
Proof.
  intros m oc olo on A B C D E. rewrite (win_data_len m A B).
  pose proof (Zlength_nonneg (m_ow m)).
  unfold win_data, u32, m_left in *. rewrite Z.mod_small by rep_lia.
  unfold byte_vals. list_solve.
Qed.

Lemma win_data_bytes: forall m, bytes_ok (m_ow m) -> bytes_ok (win_data m).
Proof. intros m H. unfold win_data, bytes_ok in *. apply Forall_sublist. exact H. Qed.

Lemma semax_ret_const {Espec: OracleKind} (P: environ -> mpred) (R: ret_assert) (r: Z) (e: expr):
  (forall rho, eval_expr (Ecast e tint) rho = Vint (Int.repr r)) ->
  ENTAIL Delta_inflate5, P |-- tc_expr Delta_inflate5 (Ecast e tint) ->
  ENTAIL Delta_inflate5, P |-- RA_return R (Some (Vint (Int.repr r))) ->
  semax Delta_inflate5 P (Sreturn (Some e)) R.
Proof.
  intros He Htc HP.
  eapply semax_pre; [ | apply semax_return ].
  change (ret_type Delta_inflate5) with tint.
  apply andp_right; [ exact Htc | ].
  intro rho. specialize (HP rho). cbv beta in HP.
  assert (E: cast_expropt (Some e) tint rho = Some (Vint (Int.repr r))).
  { change (cast_expropt (Some e) tint rho) with (Some (eval_expr (Ecast e tint) rho)). rewrite He. reflexivity. }
  change (liftx (RA_return R) (cast_expropt (Some e) tint) id rho)
    with (RA_return R (cast_expropt (Some e) tint rho) (id rho)).
  rewrite E. exact HP.
Qed.

Lemma state_rep_e_set_mode: forall gv sp strmp headp w s v,
  state_rep_e gv sp strmp headp w (set_i_mode s v) = state_rep_e gv sp strmp headp w s.
Proof. reflexivity. Qed.
Lemma win_rep_set_mode: forall w s v, win_rep w (set_i_mode s v) = win_rep w s.
Proof. reflexivity. Qed.
Lemma head_part_set_mode: forall F m v, head_part F (set_mode m v) = head_part F m.
Proof. reflexivity. Qed.

Lemma head_part_winp: forall F w d m, head_part (set_f_winp_dt F w d) m = head_part F m.
Proof. reflexivity. Qed.

Definition mupd (m: mst) : mst := upd_s m (fun s => set_i_win (updatewindow s (win_data m)) true).

Lemma head_part_mupd: forall F m, head_part F (mupd m) = head_part F m.
Proof.
  intros. unfold head_part.
  change (i_head (m_s (mupd m))) with (i_head (updatewindow (m_s m) (win_data m))).
  destruct (updatewindow_keep (m_s m) (win_data m)) as (_ & _ & _ & _ & _ & _ & _ & _ & E). rewrite E.
  reflexivity.
Qed.

Lemma hdr_tok_mupd: forall F m, hdr_tok F (mupd m) = hdr_tok F m.
Proof.
  intros. unfold hdr_tok.
  change (i_head (m_s (mupd m))) with (i_head (updatewindow (m_s m) (win_data m))).
  destruct (updatewindow_keep (m_s m) (win_data m)) as (_ & _ & _ & _ & _ & _ & _ & _ & E). rewrite E.
  reflexivity.
Qed.

Lemma hdr_tok_winp: forall F w d m, hdr_tok (set_f_winp_dt F w d) m = hdr_tok F m.
Proof. reflexivity. Qed.
Lemma locals_rep_winp: forall F w d, locals_rep (set_f_winp_dt F w d) = locals_rep F.
Proof. reflexivity. Qed.
Lemma m_have_mupd: forall m, m_have (mupd m) = m_have m.
Proof. reflexivity. Qed.
Lemma m_left_mupd: forall m, m_left (mupd m) = m_left m.
Proof. reflexivity. Qed.

Lemma semax_ex_call {Espec: OracleKind} (F: frame) (X: mpred) (m: mst) (v: val) (R: ret_assert):
  frame_ok5 F -> swf (m_s m) -> m_sow m = Zlength (m_ow m) -> m_left m <= m_out m <= m_aout m ->
  Zlength (m_ow m) <= m_aout m <= Int.max_signed -> bytes_ok (m_ow m) ->
  (i_win (m_s m) = false ->
   ENTAIL Delta_inflate5,
     PROPx [] (LOCALx (ret_locals F)
       (SEPx [mem_rep (set_f_winp_dt F nullval (f_dt F)) (set_mode m MEM); locals_rep F; hdr_tok F m;
              mem_mgr (f_gv F); zfuncs (f_gv F); X]))
     |-- RA_return R (Some (zv Z_MEM_ERROR))) ->
  semax Delta_inflate5 (lstate_t F X m v) ex_call
    (overridePost (EX winp: val, !! (i_win (m_s m) = true -> winp = f_winp F) &&
                     lstate (set_f_winp_dt F winp (f_dt F)) X (mupd m)) R).
Proof.
  intros [FOK FL] SW ESOW RO RA BO HMEM. pose proof FOK as (HWS & HWH & HRG & HRT).
  cbv beta iota zeta delta [ex_call ex_win inflate_exit f_inflate fn_body].
  unfold lstate_t, mem_rep.
  rewrite state_rep_wp, win_rep_wp.
  destruct F as [gv shs strmp sp headp winp hsh xb nb cb ib ob gsh tsh dt vres vhere vlast vhbuf flush].
  destruct ob as [osh op olo on oc].
  frame_simpl. unfold strm_rep. rewrite ESOW.
  set (wp := if i_win (m_s m) then winp else nullval).
  abbreviate_semax.
  remember (gv _zcalloc) as zca eqn:Hzca. remember (gv _zcfree) as zcf eqn:Hzcf.
  Intros.
  pose proof (win_data_len m RO RA) as HL.
  destruct H0 as (Hosh & Hop & Holo & Haout & Hlo & Hoc & Hon).
  pose proof (win_data_slice m oc olo on RO RA Holo ltac:(lia) Hoc) as HS.
  pose proof (win_data_bytes m BO) as HB.
  forward. forward.
  forward_call (gv, shs, strmp, (in_ptr ib (m_snx m),
      (Vint (Int.repr (Zlength (m_inp m) - m_snx m)),
       (Vlong (Int64.repr (m_tin m)),
        (offset_val (olo + Zlength (m_ow m)) op,
         (Vint (Int.repr (m_aout m - Zlength (m_ow m))),
          (Vlong (Int64.repr (m_tout m)),
           (msg_val gv (m_msg m),
            (sp, (zca, (zcf, (nullval, (Vint (Int.repr dt), (Vlong (Int64.repr (m_adler m)), vres))))))))))))),
     sp, headp, wp, m_s m, osh, op, on, sublist 0 olo oc ++ byte_vals (m_ow m) ++ sublist (olo + Zlength (m_ow m)) on oc,
     olo + Zlength (m_ow m), win_data m).
  { rewrite HL. unfold m_left. entailer!. }
  { split; [unfold stream_ok_val2; auto | ].
    rewrite HL. unfold m_left in *.
    split; [lia | ]. split; [rep_lia | ].
    split; [unfold byte_vals; autorewrite with sublist; lia | ].
    intro E. unfold wp. rewrite E. reflexivity. }
  Intros vret. destruct vret as [r winp']. cbn [fst snd] in *.
  destruct H0 as [[R0 HW] | (R1 & HWF & HWN)].
  - subst r. cbn [Z.eqb].
    forward_if; [contradiction | ].
    forward.
    assert (HWW: i_win (m_s m) = true -> winp' = winp) by (intro E; rewrite (HW E); unfold wp; rewrite E; reflexivity).
    destruct R as [Rn Rb Rc Rr]; cbn [RA_normal].
    Exists winp'.
    unfold lstate, mem_rep.
    rewrite head_part_winp, head_part_mupd, hdr_tok_winp, hdr_tok_mupd, locals_rep_winp, m_have_mupd, m_left_mupd.
    unfold set_f_winp_dt. frame_simpl_goal.
    cbn [mupd upd_s set_m_s m_s m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave m_snx m_sow m_tin
         m_tout m_msg m_adler].
    unfold strm_rep. rewrite <- Hzca, <- Hzcf. rewrite ?ESOW.
    entailer!.
    unfold out_ok. split; [exact Hosh | ]. split; [exact Hop | ]. repeat split; lia.
  - subst r winp'. cbn [Z.eqb].
    forward_if; [ | discriminate].
    rewrite state_rep_esplit. unfold state_f9. Intros.
    forward.
    apply semax_ret_const with (r := Z_MEM_ERROR); [intro rho; reflexivity | entailer! | ].
    unfold abbreviate in POSTCONDITION; subst POSTCONDITION.
    replace (RA_return (overridePost _ R)) with (RA_return R) by (destruct R; reflexivity).
    eapply derives_trans; [ | apply (HMEM HWF)].
    apply andp_right; [apply andp_left1, derives_refl | ].
    unfold ret_locals, mem_rep. rewrite head_part_set_mode, head_part_winp, state_rep_esplit. unfold state_f9, strm_rep.
    unfold set_f_winp_dt. frame_simpl_goal.
    cbn [set_mode upd_s set_m_s m_s m_snx m_inp m_tin m_sow m_aout m_tout m_msg m_adler m_ow].
    rewrite state_rep_e_set_mode, win_rep_set_mode.
    cbn [i_mode i_last i_wrap i_flags i_check i_total i_wsize i_hold i_bits set_i_mode].
    rewrite <- Hzca, <- Hzcf. rewrite ?ESOW. unfold MEM.
    entailer!.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the window update after RESTORE                                                                *)

Lemma swf_restore: forall m, mwf m -> swf (m_s (restore m)).
Proof.
  intros m W. pose proof (mw_hold _ W). pose proof (mw_bits _ W).
  destruct (mw_s _ W); constructor; cbn [restore upd_s set_m_s m_s set_i_bits set_i_hold i_mode i_last i_wrap
    i_havedict i_flags i_dmax i_check i_total i_wbits i_wsize i_whave i_wnext i_win i_wdata i_hold i_bits
    i_length i_offset i_extra i_lencode i_distcode i_lenbits i_distbits i_ncode i_nlen i_ndist i_have i_next
    i_lens i_codes i_sane i_back i_was]; auto.
Qed.

Lemma wsize_range: forall s, swf s -> 0 <= i_wsize s <= Int.max_unsigned.
Proof.
  intros s S. pose proof (sw_wbits _ S). destruct (sw_wsize _ S) as [E | [_ E]]; rewrite E; [rep_lia | ].
  assert (2 ^ i_wbits s <= 2 ^ 23) by (apply Z.pow_le_mono_r; lia).
  assert (0 < 2 ^ i_wbits s) by (apply Z.pow_pos_nonneg; lia). rep_lia.
Qed.

Lemma set_f_winp_dt_id: forall F, set_f_winp_dt F (f_winp F) (f_dt F) = F.
Proof. intros []. reflexivity. Qed.

Lemma semax_ex_win {Espec: OracleKind} (F: frame) (X: mpred) (m: mst) (R: ret_assert):
  frame_ok5 F -> mwf3 m -> out_inv m ->
  (leave_ok (f_flush F) m = true -> i_win (m_s m) = false ->
   ENTAIL Delta_inflate5,
     PROPx [] (LOCALx (ret_locals F)
       (SEPx [mem_rep (set_f_winp_dt F nullval (f_dt F)) (set_mode (restore m) MEM); locals_rep F; hdr_tok F m;
              mem_mgr (f_gv F); zfuncs (f_gv F); X]))
     |-- RA_return R (Some (zv Z_MEM_ERROR))) ->
  semax Delta_inflate5 (lstate F X (restore m)) ex_win
    (overridePost (EX winp: val, !! (i_win (m_s m) = true -> winp = f_winp F) &&
                     lstate (set_f_winp_dt F winp (f_dt F)) X (mwin (f_flush F) m)) R).
Proof.
  intros FO [W W3] [O1 [O2 _]] HMEM. pose proof FO as [(HWS & _) FL].
  pose proof (swf_restore m W) as SR.
  rewrite ex_win_eq.
  eapply semax_seq'.
  { apply semax_ex_cond; auto.
    - apply wsize_range. exact SR.
    - exact (sw_mode _ SR).
    - exact (mw_out _ W).
    - exact (mwf_left _ W). }
  change (leave_ok (f_flush F) (restore m)) with (leave_ok (f_flush F) m).
  destruct (leave_ok (f_flush F) m) eqn:HB.
  - unfold lstate_t. abbreviate_semax. forward_if; [ | exfalso; exact (Int.one_not_zero H)].
    unfold abbreviate in POSTCONDITION; subst POSTCONDITION.
    replace (mwin (f_flush F) m) with (mupd (restore m)) by (unfold mwin; rewrite HB; reflexivity).
    change (i_win (m_s m)) with (i_win (m_s (restore m))).
    pose proof (mw_ow _ W) as [OW BO]. pose proof (mw_aout _ W) as AO.
    change Delta with Delta_inflate5. specialize (HMEM eq_refl).
    eapply semax_pre; [ | apply (semax_ex_call F X (restore m) (Vint (Int.repr (b2z true))) R); auto;
                          exact (conj OW (proj2 AO))].
    unfold lstate_t. entailer!.
  - unfold lstate_t. abbreviate_semax. forward_if; [exfalso; exact (H eq_refl) | ].
    forward.
    destruct R as [Rn Rb Rc Rr]; cbn [RA_normal overridePost].
    Exists (f_winp F). rewrite set_f_winp_dt_id.
    replace (mwin (f_flush F) m) with (restore m) by (unfold mwin; rewrite HB; reflexivity).
    unfold lstate. entailer!.
Qed.
