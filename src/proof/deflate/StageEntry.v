(** * deflate(): the entry stage (e2 .. e8, after [s = strm->state]) against its model [c_entry2] (DeflateKit.v). *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.DeflateKit.
#[export] Existing Instance DCS.CS.
Open Scope cmodel_scope.

(** ** Validity of next_out / next_in for the NULL tests *)
Lemma out_isptr z pout R : out_space z pout R |-- !! isptr pout && out_space z pout R.
Proof. unfold out_space. Intros. entailer!. Qed.

Lemma in_isptr ish z pin : in_obj ish z pin |-- !! isptr pin && in_obj ish z pin.
Proof. unfold in_obj. entailer!. Qed.

Lemma out_wv z pout R W : z_out z = [] -> (Zlength R = 0 -> wv_ok W) ->
  out_space z pout R * wv_at W pout |-- weak_valid_pointer pout.
Proof.
  intros Hz HW. unfold out_space. Intros. rewrite Hz, Zlength_nil, Z.add_0_l. cbn [map app].
  destruct (Z.eq_dec (Zlength R) 0) as [E|E].
  - specialize (HW E). apply sepcon_weak_valid_pointer2.
    destruct W as [|t|sh v]; cbn in HW |- *; [contradiction| |].
    + apply valid_pointer_weak'. apply library.malloc_token_valid_pointer; auto.
    + assert_PROP (isptr (offset_val (-1) pout)) by entailer!.
      destruct pout; try contradiction.
      sep_apply data_at_memory_block.
      eapply derives_trans; [apply (memory_block_weak_valid_pointer sh (sizeof tuchar) _ 1); simpl; try lia|].
      { apply readable_nonidentity; auto. }
      simpl. rewrite Ptrofs.add_assoc.
      replace (Ptrofs.add (Ptrofs.repr (-1)) (Ptrofs.repr 1)) with Ptrofs.zero
        by (rewrite Ptrofs.add_signed; rewrite !Ptrofs.signed_repr by rep_lia; reflexivity).
      rewrite Ptrofs.add_zero. auto.
  - apply sepcon_weak_valid_pointer1. apply valid_pointer_weak'. apply data_at_valid_ptr; auto.
    simpl. pose proof (Zlength_nonneg R). rewrite Z.max_r by lia. lia.
Qed.

Lemma in_wv ish z pin : readable_share ish -> strm_ranges z -> z_avail_in z <> 0 ->
  in_obj ish z pin |-- weak_valid_pointer (offset_val (z_next_in z) pin).
Proof.
  intros Hsh Hz Ha. open_zranges Hz. unfold in_obj.
  sep_apply data_at_memory_block.
  apply memory_block_weak_valid_pointer.
  - simpl. rewrite Z.max_r by (apply Zlength_nonneg). lia.
  - simpl. rewrite Z.max_r by (apply Zlength_nonneg). lia.
  - apply readable_nonidentity; auto.
Qed.

Local Transparent denote_tc_test_eq.
Lemma wv_test_eq (P : mpred) q : isptr q -> (P |-- weak_valid_pointer q) ->
  P |-- denote_tc_test_eq q (Vlong (Int64.repr 0)).
Proof.
  intros Hq H. destruct q; try contradiction.
  unfold denote_tc_test_eq. cbv [Archi.ptr64].
  apply andp_right; [apply prop_right; reflexivity | exact H].
Qed.
Local Opaque denote_tc_test_eq.

(** ** Back to [dfull] from the opened pieces: any status [st], last_flush [lf], bit output / pending_out, msg. *)
Lemma gen_close s z0 z e m ob mm po st lf p pin pout ish R gv :
  strm_ranges z -> msg_ok e m -> z_in z = z_in z0 -> 0 <= po -> dstate_ranges s -> s32_ok st -> s32_ok lf ->
  readable_share ish ->
  in_obj ish z0 pin * out_space z pout R *
  @field_at DCS.CS Ews t_strm (DOT _next_in) (offset_val (z_next_in z) pin) (p_strm p) *
  @field_at DCS.CS Ews t_strm (DOT _avail_in) (vi (z_avail_in z)) (p_strm p) *
  @field_at DCS.CS Ews t_strm (DOT _total_in) (vl (z_total_in z)) (p_strm p) *
  @field_at DCS.CS Ews t_strm (DOT _next_out) (offset_val (Zlength (z_out z)) pout) (p_strm p) *
  @field_at DCS.CS Ews t_strm (DOT _avail_out) (vi (z_avail_out z)) (p_strm p) *
  @field_at DCS.CS Ews t_strm (DOT _total_out) (vl (z_total_out z)) (p_strm p) *
  @field_at DCS.CS Ews t_strm (DOT _msg) m (p_strm p) *
  @field_at DCS.CS Ews t_strm (DOT _state) (p_s p) (p_strm p) *
  strm_zfuncs (p_strm p) gv *
  @field_at DCS.CS Ews t_strm (DOT _opaque) nullval (p_strm p) *
  @field_at DCS.CS Ews t_strm (DOT _adler) (vl (z_adler z)) (p_strm p) *
  @field_at_ DCS.CS Ews t_strm (DOT _reserved) (p_strm p) *
  @field_at DCS.CS Ews t_ds (DOT _pending_out) (offset_val po (p_pbuf p)) (p_s p) *
  out_at ob mm (p_s p) (p_pbuf p) *
  ltree_at (tr_ltree (d_tr s)) (p_s p) * dtree_at (tr_dtree (d_tr s)) (p_s p) *
  sym_at (d_tr s) (p_s p) (p_pbuf p) * dtype_at (d_tr s) (p_s p) (p_strm p) * lvl_at (d_tr s) (p_s p) *
  trees_rest (d_tr s) (p_s p) (p_strm p) gv *
  win_at s p * hash_at s p * match_at s p * cfg_at s p *
  @field_at DCS.CS Ews t_ds (DOT _status) (vi st) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _pending_buf_size) (vl (d_pending_buf_size s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _wrap) (vi (d_wrap s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _gzhead) (p_gzhead p) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _gzindex) (vl (d_gzindex s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _method) (vi (d_method s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _last_flush) (vi lf) (p_s p)
  |-- dfull (set_d_po (set_d_out (set_d_status (set_d_last_flush s lf) st) (ob, mm)) po) (set_z_msg z e)
        p pin pout ish R m gv.
Proof.
  intros Hz Hm Ein Hpo Hd Hst Hlf Hsh.
  set (s1 := set_d_status (set_d_last_flush s lf) st).
  assert (Hd1 : dstate_ranges s1) by (unfold s1, dstate_ranges in *; dsimpl; tauto).
  eapply derives_trans; [| apply (dfull_out_close s1 z0 (set_z_msg z e) ob mm po p pin pout ish R m gv); auto].
  rewrite strm_at_open. unfold flush_frame.
  change (win_at s1 p) with (win_at s p). change (hash_at s1 p) with (hash_at s p).
  change (match_at s1 p) with (match_at s p). change (cfg_at s1 p) with (cfg_at s p).
  change (d_tr s1) with (d_tr s).
  change (d_status s1) with st. change (d_pending_buf_size s1) with (d_pending_buf_size s).
  change (d_wrap s1) with (d_wrap s). change (d_gzindex s1) with (d_gzindex s).
  change (d_method s1) with (d_method s). change (d_last_flush s1) with lf.
  cbn [z_next_in z_avail_in z_total_in z_out z_avail_out z_total_out z_adler set_z_msg].
  change (out_space (set_z_msg z e) pout R) with (out_space z pout R).
  entailer!.
Qed.

Lemma st_id s : set_d_po (set_d_out (set_d_status (set_d_last_flush s (d_last_flush s)) (d_status s))
  (tr_out (d_tr s), d_pbm s)) (d_po s) = s.
Proof. destruct s as [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? t ?]; destruct t; reflexivity. Qed.

Lemma dr_facts s : dstate_ranges s ->
  0 <= d_po s /\ s32_ok (d_status s) /\ s32_ok (d_last_flush s) /\ s32_ok (d_wrap s).
Proof. unfold dstate_ranges. tauto. Qed.

Lemma st_set s st : set_d_po (set_d_out (set_d_status (set_d_last_flush s (d_last_flush s)) st)
  (tr_out (d_tr s), d_pbm s)) (d_po s) = set_d_status s st.
Proof. destruct s as [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? t ?]; destruct t; reflexivity. Qed.

Lemma z_msg_self z : set_z_msg z (z_msg z) = z.
Proof. destruct z; reflexivity. Qed.

Lemma init_busy_eq s : init_busy s = set_d_status s (d_status (init_busy s)).
Proof. unfold init_busy. destruct (_ && _)%bool; [reflexivity | destruct s; reflexivity]. Qed.

Lemma init_busy_ranges s : dstate_ranges s -> s32_ok (d_status (init_busy s)).
Proof.
  intros H. unfold init_busy. destruct (_ && _)%bool; [cbn; unfold s32_ok, BUSY_STATE; rep_lia | apply H].
Qed.

Lemma zr_facts z : strm_ranges z ->
  0 <= z_avail_in z <= Int.max_unsigned /\ 0 <= z_avail_out z <= Int.max_unsigned.
Proof. unfold strm_ranges, u32_ok. tauto. Qed.

Lemma ne_eqb_val a : 0 <= a <= Int.max_unsigned ->
  Val.of_bool (negb (a =? 0)) = bool2val (negb (Int.eq (Int.repr a) (Int.repr 0))).
Proof.
  intros Ha. destruct (Z.eqb_spec a 0) as [E|E]; [subst; reflexivity|].
  rewrite Int.eq_false; [reflexivity|]. intro Hx. apply repr_inj_unsigned in Hx; rep_lia.
Qed.

Lemma eqb_val_s a : Int.min_signed <= a <= Int.max_signed ->
  Val.of_bool (a =? 0) = bool2val (Int.eq (Int.repr a) (Int.repr 0)).
Proof.
  intros Ha. destruct (Z.eqb_spec a 0) as [E|E]; [subst; reflexivity|].
  rewrite Int.eq_false; [reflexivity|]. intro Hx. apply repr_inj_signed in Hx; rep_lia.
Qed.

Lemma init_busy_t s : ((d_status s =? DState.INIT_STATE) && (d_wrap s =? 0))%bool = true ->
  init_busy s = set_d_status s 113.
Proof.
  intros E. unfold init_busy.
  match goal with |- context [if ?b then _ else _] => replace b with true by (rewrite <- E; reflexivity) end.
  reflexivity.
Qed.

Lemma init_busy_f s : ((d_status s =? DState.INIT_STATE) && (d_wrap s =? 0))%bool = false -> init_busy s = s.
Proof.
  intros E. unfold init_busy.
  match goal with |- context [if ?b then _ else _] => replace b with false by (rewrite <- E; reflexivity) end.
  reflexivity.
Qed.

Lemma in_int_range x : in_int x = true -> Int.min_signed <= x <= Int.max_signed.
Proof. unfold in_int. intros H. apply andb_prop in H. destruct H as [A B]. apply Z.leb_le in A, B. rep_lia. Qed.

Lemma rank_val f o : 0 <= f <= 5 -> Int.min_signed <= o * 2 <= Int.max_signed ->
  bool2val (negb (Int.lt (Int.repr (o * 2 - (if o >? 4 then 9 else 0)))
                         (Int.repr (f * 2 - (if f >? 4 then 9 else 0))))) =
  Val.of_bool (rank f <=? rank o).
Proof.
  intros Hf Ho. unfold Int.lt, rank.
  destruct (Z.gtb_spec f 4), (Z.gtb_spec o 4); rewrite !Int.signed_repr by rep_lia;
  destruct (zlt _ _); zfin.
Qed.

Lemma e6_zero_cases s z flush (e6 : option dres) :
  e6 = (if z_avail_in z =? 0 then
         let* _ := guard (in_int (d_last_flush s * 2)) in
         if ((rank flush <=? rank (d_last_flush s)) && negb (flush =? DState.Z_FINISH))%bool then
           Some (set_d_last_flush s flush, set_z_msg z (Some DState.Z_BUF_ERROR), Some DState.Z_BUF_ERROR)
         else Some (set_d_last_flush s flush, z, None)
       else Some (set_d_last_flush s flush, z, None)) ->
  e6 <> None ->
  ((((z_avail_in z =? 0) && (rank flush <=? rank (d_last_flush s))) && negb (flush =? 4))%bool = true ->
     e6 = Some (set_d_last_flush s flush, set_z_msg z (Some DState.Z_BUF_ERROR), Some DState.Z_BUF_ERROR)) /\
  ((((z_avail_in z =? 0) && (rank flush <=? rank (d_last_flush s))) && negb (flush =? 4))%bool = false ->
     e6 = Some (set_d_last_flush s flush, z, None)).
Proof.
  intros -> Hn. unfold DState.Z_FINISH.
  destruct (z_avail_in z =? 0); cbn [andb]; [|split; [discriminate | auto]].
  destruct (in_int (d_last_flush s * 2)); cbn [guard bind] in Hn |- *; [|contradiction].
  destruct (rank flush <=? rank (d_last_flush s)), (flush =? 4); cbn; split; auto; discriminate.
Qed.

Ltac cond_true := match goal with Hx : typed_true _ (if ?b then _ else _) |- _ =>
  let E := fresh "Ecnd" in destruct b eqn:E; [clear Hx | inversion Hx] end.
Ltac cond_false := match goal with Hx : typed_false _ (if ?b then _ else _) |- _ =>
  let E := fresh "Ecnd" in destruct b eqn:E; [inversion Hx | clear Hx] end.

(** ** ERR_RETURN(strm, err): the message index, z_errmsg[k], strm->msg = ..; up to the return. *)
Ltac err_prefix ta tb k :=
  forward_if_temp ta (Vint Int.zero);
  [ match goal with Hx : Int.lt _ _ = true |- _ => vm_compute in Hx; discriminate end
  | forward; entailer!
  | forward_if_temp tb (Vint (Int.repr k));
    [ contradiction | forward; entailer! | ] ].

Ltac err_read k :=
  unfold deflate_globals, errmsg_at;
  let vs := fresh "vs" in Intros vs;
  let Hpn := fresh "Hpn" in
  assert (Hpn : is_pointer_or_null (Znth k vs)) by (apply Forall_Znth; auto; lia);
  forward; forward.

(** ** e7; e8 *)
Lemma part_e78 Espec p pin pout ish R msgv gv flush s2 z z2 X res :
  0 <= flush <= 5 ->
  (if ((d_status s2 =? DState.FINISH_STATE) && negb (z_avail_in z2 =? 0))%bool
   then Some (s2, set_z_msg z2 (Some DState.Z_BUF_ERROR), Some DState.Z_BUF_ERROR)
   else Some (init_busy s2, z2, None)) = Some res ->
  @semax DCS.CS Espec Delta_df
    (PROPx [] (LOCALx (df_locals p flush gv)
     (SEPx [dfull s2 z2 p pin pout ish (rest_after z z2 R) msgv gv; deflate_globals gv; X])))
    (Ssequence (nth_stmt df_body 7) (nth_stmt df_body 8))
    (stage_post p pin pout ish R gv flush z X res).
Proof.
  intros Hfl Hc. destruct res as [[s' z'] o].
  unfold stage_post, df_locals.
  cbv [nth_stmt df_body f_deflate fn_body].
  sep_apply (dfull_flush_open s2 z2 p pin pout ish (rest_after z z2 R) msgv gv). Intros.
  unfold flush_frame. Intros.
  rewrite strm_at_open. Intros.
  destruct (dr_facts s2 H1) as (Hpo0 & Hst & Hlf & Hwr). unfold s32_ok in Hst, Hlf, Hwr.
  freeze F1 := (ltree_at _ _) (dtree_at _ _) (sym_at _ _ _) (dtype_at _ _ _) (lvl_at _ _) (trees_rest _ _ _ _)
    (win_at _ _) (hash_at _ _) (match_at _ _) (cfg_at _ _).
  freeze F2 := (strm_zfuncs _ _) (in_obj _ _ _) (out_space _ _ _) (field_at _ _ (DOT _total_in) _ _)
    (field_at _ _ (DOT _total_out) _ _) (field_at _ _ (DOT _state) _ _) (field_at _ _ (DOT _opaque) _ _)
    (field_at _ _ (DOT _adler) _ _) (field_at_ _ _ (DOT _reserved) _) (field_at _ _ (DOT _next_in) _ _).
  freeze F3 := X (field_at _ _ (DOT _pending_buf_size) _ _) (field_at _ _ (DOT _gzhead) _ _)
    (field_at _ _ (DOT _gzindex) _ _) (field_at _ _ (DOT _method) _ _) (field_at _ _ (DOT _pending_out) _ _)
    (out_at _ _ _ _) (field_at _ _ (DOT _next_out) _ _) (field_at _ _ (DOT _avail_out) _ _)
    (field_at _ _ (DOT _last_flush) _ _).
  forward.
  forward_if_temp _t'18 (Val.of_bool ((d_status s2 =? DState.FINISH_STATE) && negb (z_avail_in z2 =? 0))).
  { forward. forward. entailer!.
    unfold DState.FINISH_STATE. match goal with Hx : d_status s2 = 666 |- _ => rewrite Hx, Z.eqb_refl end.
    simpl. destruct (zr_facts z2 H) as [Hai _]. apply ne_eqb_val; auto. }
  { forward. entailer!.
    unfold DState.FINISH_STATE. match goal with Hx : d_status s2 <> 666 |- _ => rewrite (proj2 (Z.eqb_neq _ _) Hx) end.
    reflexivity. }
  forward_if (PROP (((d_status s2 =? DState.FINISH_STATE) && negb (z_avail_in z2 =? 0))%bool = false)
    LOCAL (temp _strm (p_strm p); temp _s (p_s p); temp _flush (vi flush); gvars gv)
    SEP (FRZL F3; FRZL F2; FRZL F1;
      field_at Ews t_strm (DOT _avail_in) (vi (z_avail_in z2)) (p_strm p);
      field_at Ews t_strm (DOT _msg) msgv (p_strm p);
      field_at Ews t_ds (DOT _status) (vi (d_status s2)) (p_s p);
      field_at Ews t_ds (DOT _wrap) (vi (d_wrap s2)) (p_s p);
      deflate_globals gv)).
  { err_prefix _t'16 _t'17 7. err_read 7.
    cond_true. inversion Hc; subst s' z' o; clear Hc.
    unfold POSTCONDITION, abbreviate. clear POSTCONDITION.
    thaw F3. thaw F2. thaw F1.
    eapply semax_pre; [| apply semax_return].
    apply andp_right; [entailer!|].
    go_lowerx. simpl RA_return. Exists (Znth 7 vs).
    change (rest_after z (set_z_msg z2 ?e) R) with (rest_after z z2 R).
    sep_apply (gen_close s2 z2 z2 (Some DState.Z_BUF_ERROR) (Znth 7 vs) (tr_out (d_tr s2)) (d_pbm s2) (d_po s2)
      (d_status s2) (d_last_flush s2) p pin pout ish (rest_after z z2 R) gv); auto.
    rewrite st_id. apply andp_right; [apply prop_right; split; [reflexivity | auto] |].
    unfold deflate_globals, errmsg_at. Exists vs. entailer!. }
  { forward. cond_false. entailer!. }
  Intros. rewrite H3 in Hc. inversion Hc; subst s' z' o; clear Hc.
  forward.
  forward_if_temp _t'19 (Val.of_bool ((d_status s2 =? DState.INIT_STATE) && (d_wrap s2 =? 0))).
  { forward. forward. entailer!.
    unfold DState.INIT_STATE. match goal with Hx : d_status s2 = 42 |- _ => rewrite Hx, Z.eqb_refl end.
    apply eqb_val_s; auto. }
  { forward. entailer!.
    unfold DState.INIT_STATE. match goal with Hx : d_status s2 <> 42 |- _ => rewrite (proj2 (Z.eqb_neq _ _) Hx) end.
    reflexivity. }
  forward_if (PROP ()
    LOCAL (temp _strm (p_strm p); temp _s (p_s p); temp _flush (vi flush); gvars gv)
    SEP (FRZL F3; FRZL F2; FRZL F1;
      field_at Ews t_strm (DOT _avail_in) (vi (z_avail_in z2)) (p_strm p);
      field_at Ews t_strm (DOT _msg) msgv (p_strm p);
      field_at Ews t_ds (DOT _status) (vi (d_status (init_busy s2))) (p_s p);
      field_at Ews t_ds (DOT _wrap) (vi (d_wrap s2)) (p_s p);
      deflate_globals gv)).
  { cond_true. forward. rewrite (init_busy_t s2 Ecnd). entailer!. }
  { cond_false. forward. rewrite (init_busy_f s2 Ecnd). entailer!. }
  thaw F3. thaw F2. thaw F1.
  Exists msgv.
  sep_apply (gen_close s2 z2 z2 (z_msg z2) msgv (tr_out (d_tr s2)) (d_pbm s2) (d_po s2) (d_status (init_busy s2))
    (d_last_flush s2) p pin pout ish (rest_after z z2 R) gv); auto using init_busy_ranges.
  rewrite st_set, z_msg_self, <- init_busy_eq. entailer!.
Qed.

Lemma out_at_fold o m sp pbp : out_ok o m ->
  @field_at DCS.CS Ews t_ds (DOT Zlib.trees.code._pending) (vl (o_pending o)) sp *
  @field_at DCS.CS Ews t_ds (DOT Zlib.trees.code._pending_buf) pbp sp *
  @field_at DCS.CS Ews t_ds (DOT Zlib.trees.code._bi_buf) (vi (o_bi_buf o)) sp *
  @field_at DCS.CS Ews t_ds (DOT Zlib.trees.code._bi_valid) (vi (o_bi_valid o)) sp *
  @field_at DCS.CS Ews t_ds (DOT Zlib.trees.code._bi_used) (vi (o_bi_used o)) sp *
  @data_at DCS.CS Ews (tarray tuchar (Zlength (o_buf o))) (pb_vals (o_buf o) m) pbp
  |-- out_at o m sp pbp.
Proof. intros. unfold out_at. entailer!. Qed.

Lemma strm_at_fold z sp strmp pin pout msgv gv :
  @field_at DCS.CS Ews t_strm (DOT _next_in) (offset_val (z_next_in z) pin) strmp *
  @field_at DCS.CS Ews t_strm (DOT _avail_in) (vi (z_avail_in z)) strmp *
  @field_at DCS.CS Ews t_strm (DOT _total_in) (vl (z_total_in z)) strmp *
  @field_at DCS.CS Ews t_strm (DOT _next_out) (offset_val (Zlength (z_out z)) pout) strmp *
  @field_at DCS.CS Ews t_strm (DOT _avail_out) (vi (z_avail_out z)) strmp *
  @field_at DCS.CS Ews t_strm (DOT _total_out) (vl (z_total_out z)) strmp *
  @field_at DCS.CS Ews t_strm (DOT _msg) msgv strmp *
  @field_at DCS.CS Ews t_strm (DOT _state) sp strmp *
  strm_zfuncs strmp gv *
  @field_at DCS.CS Ews t_strm (DOT _opaque) nullval strmp *
  @field_at DCS.CS Ews t_strm (DOT _adler) (vl (z_adler z)) strmp *
  @field_at_ DCS.CS Ews t_strm (DOT _reserved) strmp
  |-- strm_at z sp strmp pin pout msgv gv.
Proof. rewrite strm_at_open. cancel. Qed.

Lemma st_lf s lf : set_d_po (set_d_out (set_d_status (set_d_last_flush s lf) (d_status s))
  (tr_out (d_tr s), d_pbm s)) (d_po s) = set_d_last_flush s lf.
Proof. destruct s as [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? t ?]; destruct t; reflexivity. Qed.

Lemma st_flush s o po lf lf' : set_d_last_flush (set_d_po (set_d_out (set_d_last_flush s lf') o) po) lf =
  set_d_po (set_d_out (set_d_status (set_d_last_flush s lf) (d_status s)) o) po.
Proof. destruct s as [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? t ?]; destruct t, o; reflexivity. Qed.

Lemma st_flush2 s o po lf : set_d_po (set_d_out (set_d_last_flush s lf) o) po =
  set_d_po (set_d_out (set_d_status (set_d_last_flush s lf) (d_status s)) o) po.
Proof. destruct s as [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? t ?]; destruct t, o; reflexivity. Qed.

(** ** e4 .. e8 *)
Lemma part_rest Espec p pin pout ish R msgv gv flush s z X res :
  0 <= flush <= 5 ->
  then_stage
    (let* r :=
      (if negb (d_pending (set_d_last_flush s flush) =? 0) then
         let* (s0, z0) := c_flush_pending (set_d_last_flush s flush) z in
         if z_avail_out z0 =? 0 then Some (set_d_last_flush s0 (-1), z0, Some DState.Z_OK) else Some (s0, z0, None)
       else if z_avail_in z =? 0 then
         let* _ := guard (in_int (d_last_flush s * 2)) in
         if ((rank flush <=? rank (d_last_flush s)) && negb (flush =? DState.Z_FINISH))%bool then
           Some (set_d_last_flush s flush, set_z_msg z (Some DState.Z_BUF_ERROR), Some DState.Z_BUF_ERROR)
         else Some (set_d_last_flush s flush, z, None)
       else Some (set_d_last_flush s flush, z, None)) in
     then_stage (Some r) (fun s0 z0 =>
       if ((d_status s0 =? DState.FINISH_STATE) && negb (z_avail_in z0 =? 0))%bool then
         Some (s0, set_z_msg z0 (Some DState.Z_BUF_ERROR), Some DState.Z_BUF_ERROR)
       else Some (s0, z0, None)))
    (fun s0 z0 => Some (init_busy s0, z0, None)) = Some res ->
  @semax DCS.CS Espec Delta_df
    (PROPx [] (LOCALx (df_locals p flush gv)
     (SEPx [dfull s z p pin pout ish R msgv gv; deflate_globals gv; X])))
    (Ssequence (nth_stmt df_body 4) (Ssequence (nth_stmt df_body 5) (Ssequence (nth_stmt df_body 6)
      (Ssequence (nth_stmt df_body 7) (nth_stmt df_body 8)))))
    (stage_post p pin pout ish R gv flush z X res).
Proof.
  intros Hfl Hc.
  match type of Hc with then_stage (bind ?E _) _ = _ => remember E as e6 eqn:He6 end.
  apply <- seq_assoc. apply <- seq_assoc.
  apply semax_seq with (EX s2 z2 : _, PROPx [e6 = Some (s2, z2, None)] (LOCALx (df_locals p flush gv)
     (SEPx [dfull s2 z2 p pin pout ish (rest_after z z2 R) msgv gv; deflate_globals gv; X]))).
  2: { Intros s2 z2. rewrite H in Hc. cbn [bind then_stage] in Hc.
       apply part_e78; auto.
       revert Hc. destruct ((d_status s2 =? DState.FINISH_STATE) && negb (z_avail_in z2 =? 0))%bool; cbn; auto. }
  destruct res as [[s' z'] o].
  unfold stage_post, df_locals.
  cbv [nth_stmt df_body f_deflate fn_body].
  sep_apply (dfull_flush_open s z p pin pout ish R msgv gv). Intros.
  unfold flush_frame. Intros.
  destruct (dr_facts s H1) as (Hpo0 & Hst & Hlf & Hwr). unfold s32_ok in Hst, Hlf, Hwr.
  destruct (zr_facts z H) as [Hai Hao].
  freeze F1 := (ltree_at _ _) (dtree_at _ _) (sym_at _ _ _) (dtype_at _ _ _) (lvl_at _ _) (trees_rest _ _ _ _)
    (win_at _ _) (hash_at _ _) (match_at _ _) (cfg_at _ _).
  freeze F2 := X (in_obj _ _ _) (field_at _ _ (DOT _pending_buf_size) _ _) (field_at _ _ (DOT _gzhead) _ _)
    (field_at _ _ (DOT _gzindex) _ _) (field_at _ _ (DOT _method) _ _) (field_at _ _ (DOT _wrap) _ _)
    (field_at _ _ (DOT _status) _ _).
  forward. forward.
  unfold out_at. Intros.
  forward.
  set (s1 := set_d_last_flush s flush).
  forward_if (EX s2 z2 : _, PROP (e6 = Some (s2, z2, None))
     LOCAL (temp _strm (p_strm p); temp _s (p_s p); temp _flush (vi flush); gvars gv)
     SEP (dfull s2 z2 p pin pout ish (rest_after z z2 R) msgv gv; deflate_globals gv; X)).
  { (* pending != 0: flush_pending *)
    assert (Ep : negb (d_pending (set_d_last_flush s flush) =? 0) = true).
    { unfold d_pending; cbn. rewrite negb_true_iff, Z.eqb_neq. intro E. rewrite E in *. contradiction. }
    rewrite Ep in He6.
    destruct (c_flush_pending (set_d_last_flush s flush) z) as [[s2 z2]|] eqn:Ef;
      cbn [bind] in He6; [| subst e6; cbn in Hc; discriminate].
    sep_apply (out_at_fold (tr_out (d_tr s)) (d_pbm s) (p_s p) (p_pbuf p)); auto.
    change (out_at (tr_out (d_tr s)) (d_pbm s)) with (out_at (tr_out (d_tr s1)) (d_pbm s1)).
    change (offset_val (d_po s) (p_pbuf p)) with (offset_val (d_po s1) (p_pbuf p)).
    forward_call (p_strm p, p_s p, p_pbuf p, pin, pout, msgv, R, s1, z, (s2, z2), gv).
    cbn [fst snd].
    destruct (c_flush_pending_same _ _ _ _ Ef) as (Ein & Emsg & _).
    destruct (c_flush_pending_inv _ _ _ _ H Ef) as ([ob2 m2] & po2 & -> & Hpo & Hr).
    assert (Hpo2 : 0 <= po2) by (apply Hpo; exact Hpo0).
    change (tr_out (d_tr (set_d_po (set_d_out s1 (ob2, m2)) po2))) with ob2.
    change (d_pbm (set_d_po (set_d_out s1 (ob2, m2)) po2)) with m2.
    change (d_po (set_d_po (set_d_out s1 (ob2, m2)) po2)) with po2.
    unfold out_at. Intros.
    destruct (Hr ltac:(auto)) as [Hz2 _].
    sep_apply (out_at_fold ob2 m2 (p_s p) (p_pbuf p)); auto.
    rewrite strm_at_open. Intros.
    destruct (zr_facts z2 Hz2) as [Hai2 Hao2].
    forward.
    subst s1.
    forward_if.
    - (* avail_out == 0: return Z_OK *)
      forward.
      match goal with Hx : z_avail_out z2 = 0 |- _ => rewrite (proj2 (Z.eqb_eq _ _) Hx) in He6 end. subst e6. cbn in Hc. inversion Hc; subst s' z' o; clear Hc.
      unfold POSTCONDITION, abbreviate. clear POSTCONDITION.
      thaw F2. thaw F1.
      eapply semax_pre; [| apply semax_return].
      apply andp_right; [entailer!|].
      go_lowerx. simpl RA_return. Exists msgv.
      change (Vint (Int.neg (Int.repr 1))) with (vi (-1)).
      sep_apply (gen_close s z z2 (z_msg z2) msgv ob2 m2 po2 (d_status s) (-1) p pin pout ish (rest_after z z2 R) gv); auto.
      { rewrite Emsg; auto. }
      { unfold s32_ok; rep_lia. }
      rewrite z_msg_self, <- (st_flush s (ob2, m2) po2 (-1) flush).
      apply andp_right; [apply prop_right; split; [reflexivity | auto] |].
      entailer!.
    - (* continue *)
      forward.
      match goal with Hx : z_avail_out z2 <> 0 |- _ => rewrite (proj2 (Z.eqb_neq _ _) Hx) in He6 end.
      Exists (set_d_po (set_d_out (set_d_last_flush s flush) (ob2, m2)) po2) z2.
      thaw F2. thaw F1.
      sep_apply (gen_close s z z2 (z_msg z2) msgv ob2 m2 po2 (d_status s) flush p pin pout ish (rest_after z z2 R) gv); auto.
      { rewrite Emsg; auto. }
      { unfold s32_ok; rep_lia. }
      rewrite z_msg_self, <- (st_flush2 s (ob2, m2) po2 flush).
      entailer!. }
  { (* pending == 0 *)
    assert (Ep : negb (d_pending (set_d_last_flush s flush) =? 0) = false).
    { unfold d_pending; cbn. destruct H3 as (_ & _ & Hp & _).
      change Int64.zero with (Int64.repr 0) in H4. apply repr_inj_unsigned64 in H4; [|rep_lia|rep_lia]. rewrite H4. reflexivity. }
    rewrite Ep in He6.
    rewrite strm_at_open. Intros.
    forward.
    forward_if_temp _t'12 (Val.of_bool ((z_avail_in z =? 0) && (rank flush <=? rank (d_last_flush s)))).
    { assert (Ea : z_avail_in z = 0) by assumption.
      rewrite Ea, Z.eqb_refl in He6.
      destruct (in_int (d_last_flush s * 2)) eqn:Hg; cbn [guard bind] in He6; [| subst e6; cbn in Hc; discriminate].
      forward_if_temp _t'13 (vi (if flush >? 4 then 9 else 0)).
      { forward. entailer!. destruct (Z.gtb_spec flush 4); try lia; reflexivity. }
      { forward. entailer!. destruct (Z.gtb_spec flush 4); try lia; reflexivity. }
      forward_if_temp _t'14 (vi (if d_last_flush s >? 4 then 9 else 0)).
      { forward. entailer!. destruct (Z.gtb_spec (d_last_flush s) 4); try lia; reflexivity. }
      { forward. entailer!. destruct (Z.gtb_spec (d_last_flush s) 4); try lia; reflexivity. }
      apply in_int_range in Hg.
      forward.
      { entailer!. destruct (Z.gtb_spec flush 4), (Z.gtb_spec (d_last_flush s) 4);
          rewrite !Int.signed_repr by rep_lia; rep_lia. }
      entailer!. rewrite Ea, Z.eqb_refl. cbn [andb].
      symmetry. apply rank_val; auto. }
    { forward. entailer!. rewrite (proj2 (Z.eqb_neq _ _)) by auto. reflexivity. }
    destruct (e6_zero_cases s z flush e6 He6) as [Ht Hf].
    { intro E. rewrite E in Hc. discriminate. }
    forward_if_temp _t'15 (Val.of_bool ((((z_avail_in z =? 0) && (rank flush <=? rank (d_last_flush s)))
      && negb (flush =? 4))%bool)).
    { cond_true. forward. entailer!. try rewrite Ecnd. cbn [andb].
      destruct (zeq flush 4), (Z.eqb_spec flush 4); try lia; reflexivity. }
    { cond_false. forward. entailer!. }
    forward_if.
    { cond_true. rewrite (Ht eq_refl) in Hc. cbn in Hc. inversion Hc; subst s' z' o; clear Hc.
      err_prefix _t'10 _t'11 7. err_read 7.
      unfold POSTCONDITION, abbreviate. clear POSTCONDITION.
      thaw F2. thaw F1.
      sep_apply (out_at_fold (tr_out (d_tr s)) (d_pbm s) (p_s p) (p_pbuf p)); auto.
      eapply semax_pre; [| apply semax_return].
      apply andp_right; [entailer!|].
      go_lowerx. simpl RA_return. Exists (Znth 7 vs).
      rewrite (rest_after_same z (set_z_msg z _) R) by reflexivity.
      sep_apply (gen_close s z z (Some DState.Z_BUF_ERROR) (Znth 7 vs) (tr_out (d_tr s)) (d_pbm s) (d_po s)
        (d_status s) flush p pin pout ish R gv); auto.
      { unfold s32_ok; rep_lia. }
      rewrite st_lf. apply andp_right; [apply prop_right; split; [reflexivity | auto] |].
      unfold deflate_globals, errmsg_at. Exists vs. entailer!. }
    { cond_false. specialize (Hf eq_refl). forward.
      Exists (set_d_last_flush s flush) z.
      thaw F2. thaw F1.
      sep_apply (out_at_fold (tr_out (d_tr s)) (d_pbm s) (p_s p) (p_pbuf p)); auto.
      sep_apply (gen_close s z z (z_msg z) msgv (tr_out (d_tr s)) (d_pbm s) (d_po s)
        (d_status s) flush p pin pout ish R gv); auto.
      { unfold s32_ok; rep_lia. }
      rewrite st_lf, z_msg_self, rest_after_refl.
      entailer!. } }
Qed.

Lemma stage_entry : stage_ok_entry.
Proof.
  intros Espec p pin pout ish R msgv gv flush s z W X res Hfl Hz0 HW Hc.
  destruct res as [[s' z'] o].
  unfold c_entry2, c_deflate_entry in Hc.
  unfold S_entry. apply <- seq_assoc.
  apply semax_seq with (PROP (((d_status s =? DState.FINISH_STATE) && negb (flush =? DState.Z_FINISH))%bool = false;
      z_avail_out z <> 0)
    LOCAL (temp _strm (p_strm p); temp _s (p_s p); temp _flush (vi flush); gvars gv)
    SEP (dfull s z p pin pout ish R msgv gv; deflate_globals gv; (X * wv_at W pout)%logic)).
  2: { Intros.
       match goal with Hx : (_ && _)%bool = false |- _ => rewrite Hx in Hc end.
       match goal with Hx : z_avail_out z <> 0 |- _ => rewrite (proj2 (Z.eqb_neq _ _) Hx) in Hc end.
       cbv beta iota in Hc.
       eapply semax_pre; [| apply (part_rest Espec p pin pout ish R msgv gv flush s z (X * wv_at W pout)%logic
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
    sep_apply (out_wv z pout R W Hz0 HW). cancel. }
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
  freeze F2 := (strm_zfuncs _ _) (wv_at _ _) (in_obj _ _ _) (out_space _ _ _) (field_at _ _ (DOT _total_in) _ _)
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
