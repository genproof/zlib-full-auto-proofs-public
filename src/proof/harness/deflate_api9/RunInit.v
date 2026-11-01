(* Law deflate_api, deflate_run: stream_defaults, deflateInit2 and its checks, R->wrap, R->wb (RunKit.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec Zlib.proof.deflate.DSpec9 Zlib.proof.deflate.InitStrm.
Require Import Zlib.proof.deflate.LawFacts Zlib.proof.deflate.HarnessLib Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.harness.deflate_api.ApiCS Zlib.proof.harness.deflate_api9.RunSpec
               Zlib.proof.harness.deflate_api9.ApiConv Zlib.proof.harness.deflate_api9.RunKit.
Require Import Zlib.harness.x_deflate_api.code.
#[local] Existing Instance ApiCS.CS.
Local Open Scope logic.

Lemma ri_keep s z s' z' r :
  c_deflateResetKeep s z = Some (s', z', r) -> bad_state s = false -> r = Z_OK.
Proof.
  unfold c_deflateResetKeep. intros H Hb. rewrite Hb in H.
  destruct (if d_wrap _ <? 0 then _ else _) as [s1|]; [|discriminate].
  simpl in H.
  do 4 (try match type of H with context [bind ?x _] =>
    lazymatch x with Some _ => fail | None => fail | _ => destruct x; simpl in H; try discriminate end end).
  inversion H; reflexivity.
Qed.

Lemma ri_reset s z s' z' r :
  c_deflateReset s z = Some (s', z', r) -> bad_state s = false -> r = Z_OK.
Proof.
  unfold c_deflateReset. intros H Hb.
  destruct (c_deflateResetKeep s z) as [[[a b] c]|] eqn:E; [|discriminate].
  pose proof (ri_keep _ _ _ _ _ E Hb); subst c. simpl in H.
  destruct (c_lm_init a); [|discriminate]. inversion H; reflexivity.
Qed.

Lemma ri_bs_init w b h l t m : bad_state (set_d_method (set_d_tr (init_dstate w b h l) t) m) = false.
Proof. reflexivity. Qed.

Lemma ri_bs_fin s : bad_state (set_d_status s FINISH_STATE) = false.
Proof. reflexivity. Qed.

Lemma ri_reset_bind S Z os z' code :
  bad_state S = false ->
  bind (c_deflateReset S Z) (fun p => let '(s, z0, r) := p in Some (Some s, z0, r)) = Some (os, z', code) ->
  code = Z_OK.
Proof.
  intros Hb H. destruct (c_deflateReset S Z) as [[[a b] c]|] eqn:E; [|discriminate].
  apply ri_reset in E; [|exact Hb]. simpl in H. injection H as <- <- <-. exact E.
Qed.

Lemma ri_end_bind S Z os z' code :
  bind (c_deflateEnd (set_d_status S FINISH_STATE) Z)
    (fun p => let '(os0, z1, _) := p in Some (os0, z1, Z_MEM_ERROR)) = Some (os, z', code) ->
  os = None.
Proof.
  intros H. unfold c_deflateEnd in H. rewrite ri_bs_fin in H. simpl in H.
  injection H as <- <- <-. reflexivity.
Qed.

Lemma ri_reset_bind' S Z f os z' code :
  bad_state S = false -> (forall s z0 r, f (s, z0, r) = Some (Some s, z0, r)) ->
  bind (c_deflateReset S Z) f = Some (os, z', code) -> code = Z_OK.
Proof.
  intros Hb Hf H. destruct (c_deflateReset S Z) as [[[a b] c]|] eqn:E; [|discriminate].
  apply ri_reset in E; [|exact Hb]. simpl in H. rewrite Hf in H. injection H as <- <- <-. exact E.
Qed.

(* deflateInit2_ returns a state only on Z_OK *)
Local Opaque c_deflateReset c_deflateEnd init_dstate.
Lemma ri_init_none level method wbits mem strategy a1 a2 a3 a4 a5 z os z' code :
  c_deflateInit2_ true true false level method wbits mem strategy a1 a2 a3 a4 a5 z = Some (os, z', code) ->
  code <> Z_OK -> os = None.
Proof.
  intros H Hc. unfold c_deflateInit2_ in H. cbn [negb orb] in H.
  destruct (if wbits <? 0 then _ else _) as [[wb wr]|]; [|injection H as <- _ _; reflexivity].
  destruct (_ || _)%bool; [injection H as <- _ _; reflexivity|].
  destruct a1; cbn [negb] in H; [|injection H as <- _ _; reflexivity].
  destruct (a2 && a3 && a4 && a5)%bool; cbn [negb] in H.
  - apply ri_reset_bind' in H; [contradiction|apply ri_bs_init|intros; reflexivity].
  - apply ri_end_bind in H. exact H.
Qed.

Lemma ri_params_wbits l m w me st : params_ok l m w me st = true -> -15 <= w.
Proof.
  unfold params_ok. intros H. destruct (w <? -15) eqn:E; [discriminate | lia].
Qed.

(* the z_stream's memory from the fields deflateInit2_ leaves on failure, the caller's fields and the padding *)
Lemma ri_strm_fold (sp st za zf op dt nin : val) ain tin nout aout tout msgv adler :
  @field_at_ DCS.CS Ews t_strm (DOT deflate.code._reserved) sp *
  @field_at DCS.CS Ews t_strm (DOT deflate.code._state) st sp *
  @field_at DCS.CS Ews t_strm (DOT deflate.code._zalloc) za sp *
  @field_at DCS.CS Ews t_strm (DOT deflate.code._zfree) zf sp *
  @field_at DCS.CS Ews t_strm (DOT deflate.code._opaque) op sp *
  @field_at DCS.CS Ews t_strm (DOT deflate.code._data_type) dt sp *
  api_fields sp nin ain tin nout aout tout msgv adler *
  spacer Ews 12 16 sp * spacer Ews 36 40 sp * spacer Ews 92 96 sp
  |-- @data_at_ DCS.CS Ews t_strm sp.
Proof.
  unfold api_fields. Intros.
  unfold_data_at (@data_at_ DCS.CS Ews t_strm sp).
  cancel. unfold field_at_. apply derives_refl.
Qed.

(* v9: the same from deflateInit2__spec_v9's failure postcondition (any values in the caller's fields) *)
Lemma ri_strm_fold9 (sp st za zf op dt nin tin tout msgv adler ain nout aout : val) :
  @field_at_ DCS.CS Ews t_strm (DOT deflate.code._reserved) sp *
  @field_at DCS.CS Ews t_strm (DOT deflate.code._state) st sp *
  @field_at DCS.CS Ews t_strm (DOT deflate.code._zalloc) za sp *
  @field_at DCS.CS Ews t_strm (DOT deflate.code._zfree) zf sp *
  @field_at DCS.CS Ews t_strm (DOT deflate.code._opaque) op sp *
  @field_at DCS.CS Ews t_strm (DOT deflate.code._data_type) dt sp *
  @field_at DCS.CS Ews t_strm (DOT deflate.code._next_in) nin sp *
  reset_fields sp tin tout msgv adler *
  @field_at DCS.CS Ews t_strm (DOT deflate.code._avail_in) ain sp *
  @field_at DCS.CS Ews t_strm (DOT deflate.code._next_out) nout sp *
  @field_at DCS.CS Ews t_strm (DOT deflate.code._avail_out) aout sp *
  spacer Ews 12 16 sp * spacer Ews 36 40 sp * spacer Ews 92 96 sp
  |-- @data_at_ DCS.CS Ews t_strm sp.
Proof.
  unfold reset_fields.
  sep_apply (@field_at_field_at_ DCS.CS Ews t_strm (DOT deflate.code._state) st sp).
  sep_apply (@field_at_field_at_ DCS.CS Ews t_strm (DOT deflate.code._zalloc) za sp).
  sep_apply (@field_at_field_at_ DCS.CS Ews t_strm (DOT deflate.code._zfree) zf sp).
  sep_apply (@field_at_field_at_ DCS.CS Ews t_strm (DOT deflate.code._opaque) op sp).
  sep_apply (@field_at_field_at_ DCS.CS Ews t_strm (DOT deflate.code._data_type) dt sp).
  sep_apply (@field_at_field_at_ DCS.CS Ews t_strm (DOT deflate.code._next_in) nin sp).
  sep_apply (@field_at_field_at_ DCS.CS Ews t_strm (DOT deflate.code._total_in) tin sp).
  sep_apply (@field_at_field_at_ DCS.CS Ews t_strm (DOT deflate.code._total_out) tout sp).
  sep_apply (@field_at_field_at_ DCS.CS Ews t_strm (DOT deflate.code._msg) msgv sp).
  sep_apply (@field_at_field_at_ DCS.CS Ews t_strm (DOT deflate.code._adler) adler sp).
  sep_apply (@field_at_field_at_ DCS.CS Ews t_strm (DOT deflate.code._avail_in) ain sp).
  sep_apply (@field_at_field_at_ DCS.CS Ews t_strm (DOT deflate.code._next_out) nout sp).
  sep_apply (@field_at_field_at_ DCS.CS Ews t_strm (DOT deflate.code._avail_out) aout sp).
  unfold_data_at (@data_at_ DCS.CS Ews t_strm sp). cancel.
  unfold field_at_. simpl. cancel.
Qed.

Lemma ri_override_normal Delta (P Q : environ -> mpred) (R : ret_assert) :
  ENTAIL Delta, P |-- Q -> ENTAIL Delta, P |-- RA_normal (overridePost Q R).
Proof. intros H. destruct R. exact H. Qed.

Ltac ri_end := first [apply ri_override_normal | idtac]; entailer!.

Ltac ri_wb :=
  try (match goal with Hw : s32 ?w |- context [wrap_of ?w] =>
    rewrite ?Int.signed_repr in * by (unfold s32 in Hw; rep_lia) end);
  try (match goal with Hw : s32 ?w |- context [wb_of ?w] =>
    rewrite ?Int.signed_repr in * by (unfold s32 in Hw; rep_lia) end);
  unfold wrap_of, wb_of; rewrite ?Z.gtb_ltb;
  repeat match goal with |- context [?a <? ?b] => destruct (Z.ltb_spec a b) end;
  try lia; try reflexivity;
  try (unfold vi; rewrite ?Int.neg_repr, ?sub_repr; reflexivity).

Ltac ri_ovf :=
  rewrite ?Int.signed_repr in * by (unfold s32 in *; rep_lia);
  rewrite ?Int.signed_zero; unfold s32 in *; rep_lia.

Ltac ri_cases Hc3 :=
  destruct Hc3 as [-> | [-> | ->] ];
  try (match goal with H : @eq int _ _ |- _ =>
         apply (f_equal Int.unsigned) in H; vm_compute in H; discriminate end);
  try (match goal with H : ?a <> ?a |- _ => contradiction end);
  try reflexivity.

Lemma run_init_ok {Espec : OracleKind} I Iend Rp sp api vosn gv rs :
  (forall s tin tout adler ain aout msg msgv,
     semax Delta_r (A2 I Iend Rp sp api vosn gv rs s tin tout adler nullval ain nullval aout msg msgv) rsuf51
       (POST_r Iend Rp sp gv)) ->
  semax Delta_r (A1 I Iend Rp sp api vosn gv rs) rsuf45 (POST_r Iend Rp sp gv).
Proof.
  intros HK.
  unfold rsuf45, A1, allobjs.
  abbreviate_semax.
  Intros.
  match goal with H : api_facts _ _ |- _ => pose proof H as AF;
    destruct H as [Finit Ftune Fdict Fhead Fdeflate Fparams Fend1 Fend2 Fend3 Fend4] end.
  rewrite <- strm_data_at__cs.
  forward_call (sp, Ews, Vundef, Vundef).
  Intros vret. destruct vret as [[[[tin tout] adler] dt] rsv]. cbn [fst snd] in *.
  match goal with H : rs_ok rs |- _ => pose proof H as RS;
    destruct H as (Hlev & Hmeth & Hwb & Hmem & Hstr & _) end.
  unfold drun_rest. Intros.
  forward. forward. forward. forward. forward.
  unfold version_at.
  unfold_data_at (@data_at DCS.CS Ews t_strm _ sp).
  assert (FIN := Finit (rs_level rs) (rs_method rs) (rs_wbits rs) (rs_mem rs) (rs_strategy rs)).
  clear Finit Ftune Fdict Fhead Fdeflate Fparams Fend1 Fend2 Fend3 Fend4.
  forward_call (sp, rs_level rs, rs_method rs, rs_wbits rs, rs_mem rs, rs_strategy rs, gv vlit, Ers,
                [49; 46; 51; 46; 50; 0], 112, nullval, vl tin, vl tout, Vundef, vl adler, nullval, vi dt,
                Vundef, gv).
  { unfold reset_fields. cancel. }
  { split; [unfold s32_ok; rep_lia|]. split; [list_solve|]. split; [cbn; rep_lia|].
    intros a1 a2 a3 a4 a5. exact (proj1 (FIN a1 a2 a3 a4 a5 _ Hlev Hmeth Hwb Hmem Hstr)). }
  Intros vret. destruct vret as [[[[[a1 a2] a3] a4] a5] [[os z'] code]]. cbn [fst snd] in *.
  match goal with H : c_deflateInit2_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _ |- _ => rename H into HI end.
  change (Znth 0 [49; 46; 51; 46; 50; 0] =? 49) with true in HI. change (112 =? 112) with true in HI.
  destruct (proj2 (FIN a1 a2 a3 a4 a5 _ Hlev Hmeth Hwb Hmem Hstr) _ _ _ HI) as (Hcode & Hse & Hok).
  Intros msgv'.
  forward.
  assert (Hmsg : msg_ok (z_msg z') msgv') by (destruct Hcode as [-> | [-> | ->] ]; exact H).
  clear H.
  assert (Hc3 : code = 0 \/ code = -2 \/ code = -4) by exact Hcode.
  assert (Hse' : code = -2 <-> params_ok (rs_level rs) (rs_method rs) (rs_wbits rs) (rs_mem rs) (rs_strategy rs) = false)
    by exact Hse.
  clear Hcode Hse.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx Q (SEPx R))) end.
  { forward.
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp _t'39 (vi (if code =? Z_MEM_ERROR then 0 else 1)) :: Q) (SEPx R))) end.
    { forward. entailer!; ri_cases Hc3. }
    { forward. forward. entailer!; ri_cases Hc3. }
    match goal with |- semax _ (PROPx ?P (LOCALx (_ :: ?Q) (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp _t'40 (vi 1) :: Q) (SEPx R))) end.
    { forward. entailer!. }
    { forward. forward. entailer!; ri_cases Hc3. }
    forward_call (Int.one).
    forward. forward. forward. forward. forward.
    forward_call (rs_level rs, rs_method rs, rs_wbits rs, rs_mem rs, rs_strategy rs).
    forward.
    forward_call (Int.one).
    { apply prop_right.
      destruct (params_ok _ _ _ _ _) eqn:Hp; destruct Hc3 as [-> | [-> | ->] ];
        first [reflexivity
              | exfalso; destruct Hse' as [Ha Hb];
                first [specialize (Ha eq_refl); congruence | specialize (Hb eq_refl); lia] ]. }
    apply ri_override_normal. entailer!. }
  { apply semax_skip. }
  forward.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx ((code = 0) :: P) (LOCALx Q (SEPx R))) end.
  { assert (Hc0 : code <> 0) by assumption.
    assert (os = None) by (eapply ri_init_none; [exact HI | exact Hc0]). subst os.
    Intros st za zf op' dt'.
    sep_apply (ri_strm_fold9 sp st za zf op' dt' nullval (rfv (code =? Z_OK) (z_total_in z') (vl tin))
                 (rfv (code =? Z_OK) (z_total_out z') (vl tout)) msgv' (rfv (code =? Z_OK) (z_adler z') (vl adler))
                 (vi 0) nullval (vi 0)).
    rewrite strm_data_at__cs.
    forward.
    Exists 1.
    rewrite prop_true_andp by (split; [right; reflexivity | reflexivity]).
    unfold run_post. change (1 =? 0) with false. cbv iota.
    Exists code. rewrite (proj2 (Z.eqb_neq code 0) Hc0). Exists rs.
    rewrite prop_true_andp by (unfold s32; destruct Hc3 as [-> | [-> | ->] ]; lia).
    unfold drun_rest. cancel. }
  { eapply semax_pre; [| apply semax_skip]. apply ri_override_normal. entailer!. }
  Intros. subst code.
  destruct (Hok eq_refl) as (s & -> & Hgz & HIs). clear Hok.
  destruct (init_ok_strm _ _ _ _ _ _ _ _ _ _ _ _ _ HI) as (T1 & T2 & T3 & T4 & T5 & T6).
  change (0 =? Z_OK) with true in *. unfold rfv.
  assert (Hp : params_ok (rs_level rs) (rs_method rs) (rs_wbits rs) (rs_mem rs) (rs_strategy rs) = true)
    by (destruct (params_ok _ _ _ _ _) eqn:E; [reflexivity | exfalso; destruct Hse' as [_ Hb]; specialize (Hb eq_refl); discriminate]).
  pose proof (ri_params_wbits _ _ _ _ _ Hp) as Hwbr.
  forward.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _t'42 (vi (wrap_of (rs_wbits rs))) :: Q) (SEPx R))) end.
  { forward. ri_end; ri_wb. }
  { forward. forward_if.
    { forward. forward. ri_end; ri_wb. }
    { forward. forward. ri_end; ri_wb. } }
  forward.
  forward.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _t'43 (vi (wb_of (rs_wbits rs))) :: Q) (SEPx R))) end.
  { forward. forward. 1: (entailer!; ri_ovf). ri_end; ri_wb. }
  { forward. forward_if.
    { forward. forward. 1: (entailer!; ri_ovf). forward. ri_end; ri_wb. }
    { forward. forward. forward. ri_end; ri_wb. } }
  forward.
  eapply semax_pre;
    [| apply (HK s (z_total_in z') (z_total_out z') (z_adler z') 0 0 (z_msg z') msgv')].
  unfold A2, allobjs, drun_rest, strm_pad, api_fields, reset_fields. rewrite T1, T2. entailer!.
  unfold u32_ok, u64_ok. destruct T3 as [-> | ->]; repeat split; rep_lia.
Qed.
