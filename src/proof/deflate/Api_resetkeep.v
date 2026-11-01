(** * Body proof of deflateResetKeep. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.Obligations.
Require Import Zlib.proof.deflate.DModel3 Zlib.proof.deflate.DSpec Zlib.proof.deflate.DCS.
Require Import Zlib.deflate.code.
Require Zlib.trees.code.
Require Import Zlib.proof.deflate.ApiKit.

(** ** The model: the shape of a successful deflateResetKeep. *)
Definition rk_T1 (s : dstate) : tstate :=
  let o := tr_out (d_tr s) in
  set_out (set_data_type (d_tr s) Z_UNKNOWN) (mkOut (o_buf o) 0 (o_bi_buf o) (o_bi_valid o) (o_bi_used o)).
Definition rk_w (s : dstate) : Z := if d_wrap s <? 0 then - d_wrap s else d_wrap s.
Definition rk_S (s : dstate) (t : tstate) : dstate :=
  set_d_trm (set_d_last_flush (set_d_status (set_d_wrap (set_d_po s 0) (rk_w s))
     (if rk_w s =? 2 then GZIP_STATE else INIT_STATE)) (-2)) (t, d_pbm s).

Lemma rk_model s z r :
  status_ok (d_status s) = true -> on_state c_deflateResetKeep (Some s) z = Some r ->
  (d_wrap s < 0 -> in_int (- d_wrap s) = true) /\
  exists t, c_tr_init (rk_T1 s, d_pbm s) = Some (t, d_pbm s) /\
  r = (Some (rk_S s t),
       set_z_adler (set_z_msg (set_z_total_out (set_z_total_in z 0) 0) None) (if rk_w s =? 2 then 0 else 1), Z_OK).
Proof.
  intros Hst H. cbn in H. unfold c_deflateResetKeep, bad_state, c_deflateStateCheck in H.
  rewrite Hst in H; cbn in H. unfold rk_S, rk_w, rk_T1.
  destruct (d_wrap s <? 0) eqn:Hw.
  - destruct (in_int (- d_wrap s)) eqn:Hi; cbn in H; [|discriminate].
    split; [auto|].
    unfold c_tr_init in *; cbn in H |- *.
    destruct (c_init_block _) as [t|] eqn:Hc; cbn in H; [|discriminate].
    exists t. split; [reflexivity|]. inv H. destruct s; reflexivity.
  - split; [intro; lia|].
    unfold c_tr_init in *; cbn in H |- *.
    destruct (c_init_block _) as [t|] eqn:Hc; cbn in H; [|discriminate].
    exists t. split; [reflexivity|]. inv H. destruct s; reflexivity.
Qed.

(** _tr_init keeps the level, strategy, data_type, the pending buffer and the mask. *)
Lemma rk_init_keep T m t m' :
  c_tr_init (T, m) = Some (t, m') ->
  tr_level t = tr_level T /\ tr_strategy t = tr_strategy T /\ tr_data_type t = tr_data_type T /\
  o_buf (tr_out t) = o_buf (tr_out T) /\ tr_lit_bufsize t = tr_lit_bufsize T /\ m' = m.
Proof.
  unfold c_tr_init, c_init_block. intro H.
  repeat match type of H with
  | context [bind (c_zero_fc ?a ?b ?c ?d) _] =>
      destruct (c_zero_fc a b c d); cbn [bind] in H; [|discriminate]
  | context [bind (c_set_fc ?a ?b ?c) _] =>
      destruct (c_set_fc a b c); cbn [bind] in H; [|discriminate]
  end.
  inv H. repeat split; reflexivity.
Qed.

(** ** Level-generic open / close of the state: the trees part flat, the groups the body does not touch
    ([rk_rest]) and [stat_at]. *)
Definition rk_hpart (lvl : Z) (s : dstate) (p : dptrs) : mpred :=
  if lvl =? 2 then hash_at s p else hash_at_h0 s p.
Definition rk_rest (lvl : Z) (s : dstate) (p : dptrs) : mpred :=
  (win_at s p * rk_hpart lvl s p * match_at s p * cfg_at s p)%logic.

(** v7: at level 0, strm->data_type and s->pending_out are any values: the open state has only those. *)
Definition rk_dt (T : tstate) (sp strmp : val) : mpred :=
  (!! (Int.min_signed <= tr_data_type T <= Int.max_signed) &&
   (@field_at DCS.CS Ews t_ds (DOT _strm) strmp sp *
    EX dt : val, @field_at DCS.CS Ews t_strm (DOT _data_type) dt strmp))%logic.

Lemma rk_dt_of T sp strmp : dtype_at T sp strmp |-- rk_dt T sp strmp.
Proof. unfold dtype_at, rk_dt. Intros. Exists (vi (tr_data_type T)). entailer!. Qed.

Lemma rk_stat_d0 s p : stat_at s p |-- stat_at_d0 s p.
Proof. unfold stat_at, stat_at_d0. cancel. Qed.

Lemma rk_open lvl s p gv :
  dstate_at' lvl s p gv |-- !! dstate_ranges s &&
  EX lp : val, EX ls : val, EX dp : val, EX ds : val, EX bp : val, EX bs : val,
  (ltree_at (tr_ltree (d_tr s)) (p_s p) * dtree_at (tr_dtree (d_tr s)) (p_s p) *
   bltree_at (tr_bltree (d_tr s)) (p_s p) *
   ldesc_at lp (tr_lmax (d_tr s)) ls (p_s p) * ddesc_at dp (tr_dmax (d_tr s)) ds (p_s p) *
   bldesc_at bp (tr_blmax (d_tr s)) bs (p_s p) * work_at (tr_wk (d_tr s)) (p_s p) *
   out_at (tr_out (d_tr s)) (d_pbm s) (p_s p) (p_pbuf p) * sym_at (d_tr s) (p_s p) (p_pbuf p) *
   lvl_at (d_tr s) (p_s p) * rk_dt (d_tr s) (p_s p) (p_strm p) * rk_rest lvl s p * stat_at_d0 s p)%logic.
Proof.
  unfold dstate_at', rk_rest, rk_hpart.
  destruct (lvl =? 2); [|destruct (lvl =? 1)];
    unfold dstate_at, dstate_at_h0, dstate_at_d0, trees_at, trees_at_d0, d_trm; cbn [fst snd]; Intros.
  - Exists (field_address t_ds (DOT Zlib.trees.code._dyn_ltree) (p_s p)) (gv Zlib.trees.code._static_l_desc)
           (field_address t_ds (DOT Zlib.trees.code._dyn_dtree) (p_s p)) (gv Zlib.trees.code._static_d_desc)
           (field_address t_ds (DOT Zlib.trees.code._bl_tree) (p_s p)) (gv Zlib.trees.code._static_bl_desc).
    apply andp_right; [apply prop_right; auto|]. sep_apply rk_dt_of. sep_apply rk_stat_d0. cancel.
  - Exists (field_address t_ds (DOT Zlib.trees.code._dyn_ltree) (p_s p)) (gv Zlib.trees.code._static_l_desc)
           (field_address t_ds (DOT Zlib.trees.code._dyn_dtree) (p_s p)) (gv Zlib.trees.code._static_d_desc)
           (field_address t_ds (DOT Zlib.trees.code._bl_tree) (p_s p)) (gv Zlib.trees.code._static_bl_desc).
    apply andp_right; [apply prop_right; auto|]. sep_apply rk_dt_of. sep_apply rk_stat_d0. cancel.
  - Intros lp ls dp ds bp bs. Exists lp ls dp ds bp bs.
    apply andp_right; [apply prop_right; auto|]. unfold rk_dt. cancel.
    apply andp_right; [apply prop_right; auto|]. cancel.
Qed.

Lemma rk_close lvl s T m p gv sl sd sb :
  sl = gv Zlib.trees.code._static_l_desc -> sd = gv Zlib.trees.code._static_d_desc ->
  sb = gv Zlib.trees.code._static_bl_desc ->
  dstate_ranges s -> d_tr s = T -> d_pbm s = m ->
  (ltree_at (tr_ltree T) (p_s p) * dtree_at (tr_dtree T) (p_s p) * bltree_at (tr_bltree T) (p_s p) *
   ldesc_at (field_address t_ds (DOT Zlib.trees.code._dyn_ltree) (p_s p)) (tr_lmax T) sl (p_s p) *
   ddesc_at (field_address t_ds (DOT Zlib.trees.code._dyn_dtree) (p_s p)) (tr_dmax T) sd (p_s p) *
   bldesc_at (field_address t_ds (DOT Zlib.trees.code._bl_tree) (p_s p)) (tr_blmax T) sb (p_s p) *
   work_at (tr_wk T) (p_s p) * out_at (tr_out T) m (p_s p) (p_pbuf p) * sym_at T (p_s p) (p_pbuf p) *
   lvl_at T (p_s p) * dtype_at T (p_s p) (p_strm p) * rk_rest lvl s p * stat_at s p)%logic
  |-- dstate_at' (Z.max lvl 1) s p gv.
Proof.
  intros -> -> -> Hr <- <-. unfold dstate_at', rk_rest, rk_hpart.
  destruct (Z.eqb_spec lvl 2).
  - subst lvl. cbn. unfold dstate_at, trees_at, d_trm; cbn [fst snd].
    apply andp_right; [apply prop_right; auto|]. cancel.
  - assert (Z.max lvl 1 =? 2 = false) as -> by (apply Z.eqb_neq; lia).
    destruct (Z.max lvl 1 =? 1).
    + unfold dstate_at_h0, trees_at, d_trm; cbn [fst snd].
      apply andp_right; [apply prop_right; auto|]. cancel.
    + unfold dstate_at_d0, trees_at_d0, d_trm; cbn [fst snd].
      Exists (field_address t_ds (DOT Zlib.trees.code._dyn_ltree) (p_s p)) (gv Zlib.trees.code._static_l_desc)
             (field_address t_ds (DOT Zlib.trees.code._dyn_dtree) (p_s p)) (gv Zlib.trees.code._static_d_desc)
             (field_address t_ds (DOT Zlib.trees.code._bl_tree) (p_s p)) (gv Zlib.trees.code._static_bl_desc).
      apply andp_right; [apply prop_right; auto|]. cancel.
      sep_apply rk_dt_of. sep_apply rk_stat_d0. unfold rk_dt. cancel.
Qed.

Lemma rk_rest_S lvl s t p : rk_rest lvl (rk_S s t) p = rk_rest lvl s p.
Proof. reflexivity. Qed.

(** out_at again after [s->pending = 0]. *)
Lemma rk_out_fold o m sp pbp :
  out_ok o m ->
  (@field_at DCS.CS Ews t_ds (DOT Zlib.trees.code._pending) (Vlong (Int64.repr (Int.signed (Int.repr 0)))) sp *
   @field_at DCS.CS Ews t_ds (DOT Zlib.trees.code._pending_buf) pbp sp *
   @field_at DCS.CS Ews t_ds (DOT Zlib.trees.code._bi_buf) (vi (o_bi_buf o)) sp *
   @field_at DCS.CS Ews t_ds (DOT Zlib.trees.code._bi_valid) (vi (o_bi_valid o)) sp *
   @field_at DCS.CS Ews t_ds (DOT Zlib.trees.code._bi_used) (vi (o_bi_used o)) sp *
   @data_at DCS.CS Ews (tarray tuchar (Zlength (o_buf o))) (pb_vals (o_buf o) m) pbp)%logic
  |-- out_at (mkOut (o_buf o) 0 (o_bi_buf o) (o_bi_valid o) (o_bi_used o)) m sp pbp.
Proof.
  intros [? [? [? ?]]]. unfold out_at; cbn [o_buf o_pending o_bi_buf o_bi_valid o_bi_used].
  apply andp_right; [apply prop_right; unfold out_ok; cbn [o_buf o_pending o_bi_buf o_bi_valid o_bi_used];
                     refine (conj H (conj H0 (conj _ H2))); rep_lia|].
  change (Vlong (Int64.repr (Int.signed (Int.repr 0)))) with (vl 0). cancel.
Qed.

(** Folding the final state. *)
Lemma rk_dtype_fold T sp strmp :
  tr_data_type T = 2 ->
  (@field_at DCS.CS Ews t_ds (DOT Zlib.trees.code._strm) strmp sp *
   @field_at DCS.CS Ews t_strm (DOT Zlib.trees.code._data_type) (Vint (Int.repr 2)) strmp)%logic
  |-- dtype_at T sp strmp.
Proof.
  intros E. unfold dtype_at. rewrite E. apply andp_right; [apply prop_right; rep_lia|]. unfold vi. cancel.
Qed.

Lemma rk_lvl_eq a b sp :
  tr_level a = tr_level b -> tr_strategy a = tr_strategy b -> lvl_at a sp = lvl_at b sp.
Proof. intros E1 E2. unfold lvl_at. rewrite E1, E2. reflexivity. Qed.

Lemma rk_stat_fold s t p :
  isptr (p_pbuf p) ->
  (@field_at DCS.CS Ews t_ds (DOT _status) (Vint (Int.repr (if rk_w s =? 2 then GZIP_STATE else INIT_STATE))) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _pending_buf_size) (vl (d_pending_buf_size s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _pending_out) (p_pbuf p) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _wrap) (vi (rk_w s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _gzhead) (p_gzhead p) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _gzindex) (vl (d_gzindex s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _method) (vi (d_method s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _last_flush) (Vint (Int.neg (Int.repr 2))) (p_s p))%logic
  |-- stat_at (rk_S s t) p.
Proof.
  intros Hp. unfold stat_at, rk_S, set_d_trm. dcbn.
  rewrite isptr_offset_val_zero by auto. unfold vi. cancel.
Qed.

Lemma rk_dtokens s t p :
  tr_lit_bufsize t = tr_lit_bufsize (d_tr s) -> dtokens (rk_S s t) p = dtokens s p.
Proof. intros E. unfold dtokens, rk_S, set_d_trm. dcbn. rewrite E. reflexivity. Qed.

Lemma rk_ranges s t :
  dstate_ranges s -> s32_ok (rk_w s) -> dstate_ranges (rk_S s t).
Proof.
  intros Hr Hw. unfold dstate_ranges in *. unfold rk_S, set_d_trm. dcbn. unfold s32_ok in *.
  destruct (rk_w s =? 2); unfold GZIP_STATE, INIT_STATE; intuition rep_lia.
Qed.

Lemma rk_sizes s t :
  dsizes s -> o_buf (tr_out t) = o_buf (tr_out (d_tr s)) -> tr_lit_bufsize t = tr_lit_bufsize (d_tr s) ->
  dsizes (rk_S s t).
Proof.
  unfold dsizes, rk_S, set_d_trm. dcbn. intros (? & ? & ? & ?) E1 E2. rewrite E1, E2. auto.
Qed.

(** The call deflateStateCheck(strm) with next_in taken from [api_fields] (forward_call leaves the frame
    goal with the wand in SEP: closed by [cancel]). *)
Ltac rk_check os strmp gv :=
  lazymatch goal with |- context [api_fields strmp ?ni ?a ?b ?c ?d ?e ?f ?h] =>
    sep_apply (api_fields_ni strmp ni a b c d e f h);
    lazymatch os with
    | Some ?s =>
      lazymatch goal with |- context [dstream ?l (Some s) strmp ?g gv] =>
        sep_apply (dstream_check_some l s strmp g gv) end;
      let pc := fresh "pc" in let za := fresh "za" in let zf := fresh "zf" in
      Intros pc; forget (gv _zcalloc) as za; forget (gv _zcfree) as zf;
      forward_call (Some s, strmp, p_s pc, za, zf, ni, gv); try match goal with |- _ |-- _ => cancel end;
      sep_apply mp_wand; sep_apply (mp_wand (@field_at DCS.CS Ews t_strm (DOT _next_in) ni strmp)
                                     (api_fields strmp ni a b c d e f h));
      clear dependent pc; clear dependent za; clear dependent zf
    | None =>
      lazymatch goal with |- context [dstream ?l None strmp ?g gv] =>
        sep_apply (dstream_check_none l strmp g gv) end;
      let za := fresh "za" in let zf := fresh "zf" in
      Intros za zf;
      forward_call (@None dstate, strmp, nullval, za, zf, ni, gv); try match goal with |- _ |-- _ => cancel end;
      sep_apply mp_wand; sep_apply (mp_wand (@field_at DCS.CS Ews t_strm (DOT _next_in) ni strmp)
                                     (api_fields strmp ni a b c d e f h));
      clear dependent za; clear dependent zf
    end
  end.

Ltac rk_err msgv := forward_if; [forward; Exists msgv; change (Z_STREAM_ERROR =? Z_OK) with false; cbv iota;
  cbn [z_avail_in z_total_in z_avail_out z_total_out z_adler z_msg zmk]; entailer! | discriminate].

Ltac rk_fi_temp id v :=
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp id v :: Q) (SEPx R))) end.

Ltac rk_eq_then Hw :=
  match goal with Hx : Int.repr ?w = Int.repr 2 |- _ =>
    apply repr_inj_signed in Hx; [|unfold s32_ok in Hw; rep_lia|rep_lia];
    rewrite (proj2 (Z.eqb_eq _ _) Hx) end.
Ltac rk_eq_else :=
  match goal with Hx : Int.repr ?w <> Int.repr 2 |- _ =>
    destruct (Z.eqb_spec w 2) as [He|]; [rewrite He in Hx; contradiction|] end.

Lemma body_deflateResetKeep : ob_deflateResetKeep.
Proof.
  unfold ob_deflateResetKeep. start_function.
  destruct os as [s|].
  2:{ cbn in H0. inv H0. rk_check (@None dstate) strmp gv. rk_err msgv. }
  rk_check (Some s) strmp gv.
  destruct (status_ok (d_status s)) eqn:Hst.
  2:{ cbn in H0. unfold c_deflateResetKeep, bad_state, c_deflateStateCheck in H0. rewrite Hst in H0.
      cbn in H0. inv H0. unfold c_deflateStateCheck. rewrite Hst. rk_err msgv. }
  apply rk_model in H0; auto. destruct H0 as [Hin [t [Hti ->]]].
  unfold c_deflateStateCheck. rewrite Hst.
  forward_if; [contradiction|].
  unfold api_fields. Intros.
  forward. forward. forward.
  rewrite dstream_some_eq. Intros p. subst strmp.
  sep_apply rk_open. Intros lp ls dp ds bp bs.
  unfold rk_dt. Intros dt.
  forward.
  forward.
  unfold out_at. Intros.
  assert_PROP (isptr (p_pbuf p)) as Hpb by entailer!.
  forward. forward.
  unfold stat_at_d0. Intros.
  forward. forward.
  change (let (_, p_s, _, _, _, _, _) := p in p_s) with (p_s p).
  forward. forward.
  set (wv := vi (d_wrap s)).
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    let R' := eval pattern wv in R in
    match R' with ?F _ =>
      forward_if (PROPx P (LOCALx Q (SEPx (F (vi (rk_w s)))))) end end.
  - subst wv. forward. assert (s32_ok (d_wrap s)) by drange H7. unfold s32_ok in *.
    rewrite Int.signed_repr in H11 by rep_lia. specialize (Hin H11). unfold in_int in Hin.
    apply andb_prop in Hin; destruct Hin as [Hin1 Hin2]; apply Z.leb_le in Hin1, Hin2.
    forward; try (rewrite Int.signed_zero; rep_lia).
    unfold rk_w. replace (d_wrap s <? 0) with true by lia. rewrite Int.neg_repr. entailer!.
  - subst wv. forward. assert (s32_ok (d_wrap s)) by drange H7. unfold s32_ok in *.
    rewrite Int.signed_repr in H11 by rep_lia. unfold rk_w. replace (d_wrap s <? 0) with false by lia.
    entailer!.
  - cbv beta. subst wv.
    assert (Hw : s32_ok (rk_w s)).
    { assert (s32_ok (d_wrap s)) by drange H7. unfold rk_w, s32_ok in *.
      destruct (Z.ltb_spec (d_wrap s) 0) as [Hneg|]; [|lia]. specialize (Hin Hneg). unfold in_int in Hin.
      apply andb_prop in Hin; destruct Hin as [Hin1 Hin2]; apply Z.leb_le in Hin1, Hin2. rep_lia. }
    forward.
    rk_fi_temp _t'3 (vi (if rk_w s =? 2 then GZIP_STATE else INIT_STATE)).
    + forward. rk_eq_then Hw. apply ENTAIL_refl.
    + forward. rk_eq_else. apply ENTAIL_refl.
    + forward. forward. unfold deflate_globals. Intros.
      rk_fi_temp _t'4 (Vlong (Int64.repr (if rk_w s =? 2 then 0 else 1))).
      * forward_call (0, nullval, 0, true, Ews, nullval, 0, 0, @nil val, @nil Z, false, Ews, gv, Ers).
        { rewrite !emp_sepcon; cancel. }
        forward. rk_eq_then Hw. entailer!.
      * forward_call (0, nullval, 0, true, Ews, nullval, 0, 0, @nil val, @nil Z, false, Ews).
        { rewrite !emp_sepcon; cancel. }
        forward. rk_eq_else. entailer!.
      * forward. forward.
        sep_apply (rk_out_fold (tr_out (d_tr s)) (d_pbm s) (p_s p) (p_pbuf p)); auto.
        change (mkOut _ 0 _ _ _) with (tr_out (fst (rk_T1 s, d_pbm s))).
        change (tr_ltree (d_tr s)) with (tr_ltree (fst (rk_T1 s, d_pbm s))).
        change (tr_dtree (d_tr s)) with (tr_dtree (fst (rk_T1 s, d_pbm s))).
        change (tr_bltree (d_tr s)) with (tr_bltree (fst (rk_T1 s, d_pbm s))).
        change (tr_lmax (d_tr s)) with (tr_lmax (fst (rk_T1 s, d_pbm s))).
        change (tr_dmax (d_tr s)) with (tr_dmax (fst (rk_T1 s, d_pbm s))).
        change (tr_blmax (d_tr s)) with (tr_blmax (fst (rk_T1 s, d_pbm s))).
        change (tr_wk (d_tr s)) with (tr_wk (fst (rk_T1 s, d_pbm s))).
        change (sym_at (d_tr s)) with (sym_at (fst (rk_T1 s, d_pbm s))).
        forward_call (p_s p, p_pbuf p, p_strm p, (rk_T1 s, d_pbm s), (t, d_pbm s), lp, ls, dp, ds, bp, bs, gv);
          try (cbn [fst snd]; cancel).
        cbn [fst snd].
        remember (gv Zlib.trees.code._static_l_desc) as sl eqn:Esl.
        remember (gv Zlib.trees.code._static_d_desc) as sd eqn:Esd.
        remember (gv Zlib.trees.code._static_bl_desc) as sb eqn:Esb.
        pose proof (rk_init_keep _ _ _ _ Hti) as (Kl & Ks & Kd & Kb & Kbs & _).
        change (tr_data_type (rk_T1 s)) with Z_UNKNOWN in Kd.
        change (tr_lit_bufsize (rk_T1 s)) with (tr_lit_bufsize (d_tr s)) in Kbs.
        change (o_buf (tr_out (rk_T1 s))) with (o_buf (tr_out (d_tr s))) in Kb.
        change (tr_level (rk_T1 s)) with (tr_level (d_tr s)) in Kl.
        change (tr_strategy (rk_T1 s)) with (tr_strategy (d_tr s)) in Ks.
        sep_apply (rk_dtype_fold t (p_s p) (p_strm p)); auto.
        rewrite (rk_lvl_eq (d_tr s) t (p_s p)) by auto.
        sep_apply (rk_stat_fold s t p); auto.
        rewrite <- (rk_rest_S lvl s t p), <- (rk_dtokens s t p) by auto.
        sep_apply (rk_close lvl (rk_S s t) t (d_pbm s) p gv sl sd sb); auto.
        { apply rk_ranges; auto. }
        sep_apply (dstream_some_fold (Z.max lvl 1) (rk_S s t) p (p_strm p) ghp gv); auto.
        { apply rk_sizes; auto. }
        clear Esl Esd Esb sl sd sb.
        forward. Exists nullval.
        cbn [fst snd z_avail_in z_total_in z_avail_out z_total_out z_adler z_msg zmk set_z_adler set_z_msg
             set_z_total_out set_z_total_in].
        change (Z_OK =? Z_OK) with true. cbv iota. unfold api_fields, deflate_globals.
        entailer!. unfold u64_ok. destruct (rk_w s =? 2); rep_lia.
Qed.
