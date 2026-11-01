(** * deflate(): the entry stage for any witness of the weak validity of next_out

    StageEntry.stage_entry with the caller's witness [wv_at W pout] replaced by an arbitrary frame [Wm] that,
    with the output space, gives the weak validity of [pout] (the test [strm->next_out == Z_NULL]); the witness
    is used nowhere else in the stage.  [stage_entryV] instantiates it with DSpecV's witnesses ([wv2_at]). *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.DeflateKit.
Require Import Zlib.proof.deflate.StageEntry.
Require Import Zlib.proof.deflate.DSpecV.
#[export] Existing Instance DCS.CS.
Open Scope cmodel_scope.

(** DSpecV's witnesses give the weak validity of next_out when nothing is written and there is no output
    space; a readable byte at [pout] makes it valid. *)
Lemma out_wv2 z pout R W : z_out z = [] -> (Zlength R = 0 -> wv2_ok W) ->
  out_space z pout R * wv2_at W pout |-- weak_valid_pointer pout.
Proof.
  intros Hz HW. destruct W as [w|sh v]; [apply (out_wv z pout R w Hz HW)|].
  unfold out_space. Intros. rewrite Hz, Zlength_nil, Z.add_0_l. cbn [map app].
  destruct (Z.eq_dec (Zlength R) 0) as [E|E].
  - specialize (HW E). cbn in HW |- *. apply sepcon_weak_valid_pointer2.
    apply valid_pointer_weak'. apply data_at_valid_ptr.
    + apply readable_nonidentity; auto.
    + simpl. lia.
  - apply sepcon_weak_valid_pointer1. apply valid_pointer_weak'. apply data_at_valid_ptr; auto.
    simpl. pose proof (Zlength_nonneg R). rewrite Z.max_r by lia. lia.
Qed.

(** The entry stage with the witness frame [Wm]. *)
Lemma stage_entry_g (Espec : OracleKind) p pin pout ish R msgv gv flush s z (Wm X : mpred) res :
  0 <= flush <= 5 -> z_out z = [] -> (out_space z pout R * Wm |-- weak_valid_pointer pout) ->
  c_entry2 flush s z = Some res ->
  @semax DCS.CS Espec Delta_df (stage_pre p pin pout ish R msgv gv flush s z (X * Wm))%logic S_entry
    (stage_post p pin pout ish R gv flush z (X * Wm)%logic res).
Proof.
Proof.
  intros Hfl Hz0 HW Hc.
  destruct res as [[s' z'] o].
  unfold c_entry2, c_deflate_entry in Hc.
  unfold S_entry. apply <- seq_assoc.
  apply semax_seq with (PROP (((d_status s =? DState.FINISH_STATE) && negb (flush =? DState.Z_FINISH))%bool = false;
      z_avail_out z <> 0)
    LOCAL (temp _strm (p_strm p); temp _s (p_s p); temp _flush (vi flush); gvars gv)
    SEP (dfull s z p pin pout ish R msgv gv; deflate_globals gv; (X * Wm)%logic)).
  2: { Intros.
       match goal with Hx : (_ && _)%bool = false |- _ => rewrite Hx in Hc end.
       match goal with Hx : z_avail_out z <> 0 |- _ => rewrite (proj2 (Z.eqb_neq _ _) Hx) in Hc end.
       cbv beta iota in Hc.
       eapply semax_pre; [| apply (part_rest Espec p pin pout ish R msgv gv flush s z (X * Wm)%logic
         (s', z', o) Hfl Hc)].
       unfold df_locals. entailer!. }
  unfold stage_pre, stage_post, df_locals.
  cbv [nth_stmt df_body f_deflate fn_body].
  sep_apply (dfull_flush_open s z p pin pout ish R msgv gv). Intros.
  unfold flush_frame. Intros.
  rewrite strm_at_open. Intros.
  sep_apply (out_isptr z pout R). Intros. sep_apply (in_isptr ish z pin). Intros.
  assert (Eo : offset_val (Zlength (z_out z)) pout = pout)
    by (rewrite Hz0, Zlength_nil; apply isptr_offset_val_zero; auto).
  freeze [4;6;7;8;9;10;11;12;13;14;15;16;17;18;19;20;21;22;23;24;25;26;27;28;29;30;31;32;33;34] FR.
  forward.
  forward_if_temp _t'6 (Vint Int.zero).
  { rewrite Eo. apply wv_test_eq; auto. eapply derives_trans; [|apply (extend_weak_valid_pointer _ TT)].
    sep_apply HW. cancel. }
  { rewrite Eo in *. subst pout. contradiction. }
  { forward.
    forward_if.
    - forward.
      forward.
      { entailer!. assert (Ha : z_avail_in z <> 0) by (intro E; rewrite E in *; contradiction).
        apply wv_test_eq; [destruct pin; try contradiction; simpl; auto|].
        eapply derives_trans; [|apply (extend_weak_valid_pointer _ TT)].
        sep_apply (in_wv ish z pin H2 H Ha). cancel. }
      forward. entailer!. destruct pin; try contradiction. reflexivity.
    - forward. entailer!. }
  thaw FR.
  freeze F1 := (ltree_at _ _) (dtree_at _ _) (sym_at _ _ _) (dtype_at _ _ _) (lvl_at _ _) (trees_rest _ _ _ _)
    (win_at _ _) (hash_at _ _) (match_at _ _) (cfg_at _ _).
  freeze F2 := (strm_zfuncs _ _) Wm (in_obj _ _ _) (out_space _ _ _) (field_at _ _ (DOT _total_in) _ _)
    (field_at _ _ (DOT _total_out) _ _) (field_at _ _ (DOT _state) _ _) (field_at _ _ (DOT _opaque) _ _)
    (field_at _ _ (DOT _adler) _ _) (field_at_ _ _ (DOT _reserved) _).
  freeze F3 := X (field_at _ _ (DOT _pending_buf_size) _ _) (field_at _ _ (DOT _gzhead) _ _)
    (field_at _ _ (DOT _gzindex) _ _) (field_at _ _ (DOT _method) _ _) (field_at _ _ (DOT _pending_out) _ _).
  destruct (dr_facts s H1) as (Hpo0 & Hst & Hlf & Hwr). unfold s32_ok in Hst, Hlf, Hwr.
  forward_if_temp _t'7 (Val.of_bool ((d_status s =? DState.FINISH_STATE) && negb (flush =? DState.Z_FINISH))).
  { contradiction. }
  { forward.
    forward_if.
    - forward. forward. entailer!.
      unfold DState.FINISH_STATE, DState.Z_FINISH.
      match goal with Hx : d_status s = 666 |- _ => rewrite Hx, Z.eqb_refl end.
      simpl. destruct (zeq flush 4), (Z.eqb_spec flush 4); try lia; reflexivity.
    - forward. entailer!.
      unfold DState.FINISH_STATE, DState.Z_FINISH.
      match goal with Hx : d_status s <> 666 |- _ => rewrite (proj2 (Z.eqb_neq _ _) Hx) end. reflexivity. }
  forward_if (PROP (((d_status s =? DState.FINISH_STATE) && negb (flush =? DState.Z_FINISH))%bool = false)
    LOCAL (temp _strm (p_strm p); temp _s (p_s p); temp _flush (vi flush); gvars gv)
    SEP (FRZL F3; FRZL F2; FRZL F1;
      field_at Ews t_strm (DOT _avail_out) (vi (z_avail_out z)) (p_strm p);
      field_at Ews t_strm (DOT _msg) msgv (p_strm p);
      out_at (tr_out (d_tr s)) (d_pbm s) (p_s p) (p_pbuf p);
      field_at Ews t_ds (DOT _status) (vi (d_status s)) (p_s p);
      field_at Ews t_ds (DOT _wrap) (vi (d_wrap s)) (p_s p);
      field_at Ews t_ds (DOT _last_flush) (vi (d_last_flush s)) (p_s p);
      deflate_globals gv;
      field_at Ews t_strm (DOT _next_in) (offset_val (z_next_in z) pin) (p_strm p);
      field_at Ews t_strm (DOT _avail_in) (vi (z_avail_in z)) (p_strm p);
      field_at Ews t_strm (DOT _next_out) (offset_val (Zlength (z_out z)) pout) (p_strm p))).
  { (* ERR_RETURN(strm, Z_STREAM_ERROR) *)
    forward_if_temp _t'4 (Vint Int.zero).
    { match goal with Hx : Int.lt _ _ = true |- _ => vm_compute in Hx; discriminate end. }
    { forward. entailer!. }
    forward_if_temp _t'5 (Vint (Int.repr 4)).
    { contradiction. }
    { forward. entailer!. }
    unfold deflate_globals, errmsg_at. Intros vs.
    assert (Hpn : is_pointer_or_null (Znth 4 vs)) by (apply Forall_Znth; auto; lia).
    forward.
    forward.
    match goal with Hx : typed_true _ (if ?b then _ else _) |- _ => destruct b eqn:Ecnd; [clear Hx | inversion Hx] end.
    cbn [then_stage bind] in Hc. inversion Hc; subst s' z' o; clear Hc.
    unfold POSTCONDITION, abbreviate. clear POSTCONDITION.
    thaw F3. thaw F2. thaw F1.
    eapply semax_pre; [| apply semax_return].
    apply andp_right; [entailer!|].
    go_lowerx. simpl RA_return. Exists (Znth 4 vs).
    rewrite (rest_after_same z (set_z_msg z _) R) by reflexivity.
    sep_apply (gen_close s z z (Some DState.Z_STREAM_ERROR) (Znth 4 vs) (tr_out (d_tr s)) (d_pbm s) (d_po s)
      (d_status s) (d_last_flush s) p pin pout ish R gv); auto.
    rewrite st_id. apply andp_right; [apply prop_right; split; [reflexivity | auto] |].
    unfold deflate_globals, errmsg_at. Exists vs. entailer!. }
  { cond_false. forward. entailer!. }
  Intros.
  forward.
  destruct (zr_facts z H) as [Hai Hao].
  forward_if (PROP (z_avail_out z <> 0)
    LOCAL (temp _strm (p_strm p); temp _s (p_s p); temp _flush (vi flush); gvars gv)
    SEP (FRZL F3; FRZL F2; FRZL F1;
      field_at Ews t_strm (DOT _avail_out) (vi (z_avail_out z)) (p_strm p);
      field_at Ews t_strm (DOT _msg) msgv (p_strm p);
      out_at (tr_out (d_tr s)) (d_pbm s) (p_s p) (p_pbuf p);
      field_at Ews t_ds (DOT _status) (vi (d_status s)) (p_s p);
      field_at Ews t_ds (DOT _wrap) (vi (d_wrap s)) (p_s p);
      field_at Ews t_ds (DOT _last_flush) (vi (d_last_flush s)) (p_s p);
      deflate_globals gv;
      field_at Ews t_strm (DOT _next_in) (offset_val (z_next_in z) pin) (p_strm p);
      field_at Ews t_strm (DOT _avail_in) (vi (z_avail_in z)) (p_strm p);
      field_at Ews t_strm (DOT _next_out) (offset_val (Zlength (z_out z)) pout) (p_strm p))).
  { (* ERR_RETURN(strm, Z_BUF_ERROR) *)
    err_prefix _t'8 _t'9 7. err_read 7.
    match goal with Hx : (_ && _)%bool = false |- _ => rewrite Hx in Hc end.
    match goal with Hx : z_avail_out z = 0 |- _ => rewrite (proj2 (Z.eqb_eq _ _) Hx) in Hc end.
    cbn [then_stage bind] in Hc. inversion Hc; subst s' z' o; clear Hc.
    unfold POSTCONDITION, abbreviate. clear POSTCONDITION.
    thaw F3. thaw F2. thaw F1.
    eapply semax_pre; [| apply semax_return].
    apply andp_right; [entailer!|].
    go_lowerx. simpl RA_return. Exists (Znth 7 vs).
    rewrite (rest_after_same z (set_z_msg z _) R) by reflexivity.
    sep_apply (gen_close s z z (Some DState.Z_BUF_ERROR) (Znth 7 vs) (tr_out (d_tr s)) (d_pbm s) (d_po s)
      (d_status s) (d_last_flush s) p pin pout ish R gv); auto.
    rewrite st_id. apply andp_right; [apply prop_right; split; [reflexivity | auto] |].
    unfold deflate_globals, errmsg_at. Exists vs. entailer!. }
  { forward. entailer!. }
  Intros.
  thaw F3. thaw F2. thaw F1.
  sep_apply (gen_close s z z (z_msg z) msgv (tr_out (d_tr s)) (d_pbm s) (d_po s)
    (d_status s) (d_last_flush s) p pin pout ish R gv); auto.
  rewrite st_id, z_msg_self.
  entailer!.
Qed.

(** The entry stage with DSpecV's witness [W]. *)
Lemma stage_entryV (Espec : OracleKind) p pin pout ish R msgv gv flush s z W X res :
  0 <= flush <= 5 -> z_out z = [] -> (Zlength R = 0 -> wv2_ok W) -> c_entry2 flush s z = Some res ->
  @semax DCS.CS Espec Delta_df (stage_pre p pin pout ish R msgv gv flush s z (X * wv2_at W pout))%logic S_entry
    (stage_post p pin pout ish R gv flush z (X * wv2_at W pout)%logic res).
Proof.
  intros Hfl Hz0 HW Hc. apply stage_entry_g; auto. apply out_wv2; auto.
Qed.
