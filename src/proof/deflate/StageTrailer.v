(** * deflate(): the end (e16 .. e22: [if (flush != Z_FINISH) return Z_OK; ...; the trailer; return]) against its model (DeflateKit.v). *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.DeflateKit.
#[export] Existing Instance DCS.CS.
Open Scope cmodel_scope.

(** ** Helpers (from StageGzip.v) *)
(** ** put_byte of a list on the output part of the state *)
Fixpoint c_put_bytes (om : cout) (l : list Z) : option cout :=
  match l with
  | [] => Some om
  | c :: l => let* om := c_put_byte om c in c_put_bytes om l
  end.

Lemma c_dput_bytes_inv s l s' : c_dput_bytes s l = Some s' ->
  exists om, c_put_bytes (d_out s) l = Some om /\ s' = set_d_out s om.
Proof.
  revert s; induction l as [|c l IH]; intros s H; cbn [c_dput_bytes c_put_bytes] in H |- *.
  - inversion H; subst s'. exists (d_out s). rewrite set_d_out_self. auto.
  - unfold c_dput_byte in H. inv_bind H. inv_bind Ha. inversion Ha; subst x; clear Ha.
    rewrite Ha0. cbn [bind]. destruct (IH _ H) as [om [E1 E2]].
    rewrite d_out_set_d_out in E1. exists om. rewrite E2, set_d_out_out. auto.
Qed.

(** The fields after the C store of one put_byte, folded back into [out_at] of the model's result. *)
Lemma out_at_put_byte_x om c x sp pbp : c_put_byte om c = Some x -> out_ok (fst om) (snd om) ->
  @field_at DCS.CS Ews t_ds (DOT _pending) (Vlong (Int64.repr (o_pending (fst om) + 1))) sp *
  @field_at DCS.CS Ews t_ds (DOT _pending_buf) pbp sp *
  @field_at DCS.CS Ews t_ds (DOT _bi_buf) (vi (o_bi_buf (fst om))) sp *
  @field_at DCS.CS Ews t_ds (DOT _bi_valid) (vi (o_bi_valid (fst om))) sp *
  @field_at DCS.CS Ews t_ds (DOT _bi_used) (vi (o_bi_used (fst om))) sp *
  @data_at DCS.CS Ews (tarray tuchar (Zlength (o_buf (fst om))))
     (upd_Znth (o_pending (fst om)) (pb_vals (o_buf (fst om)) (snd om)) (Vint (Int.repr (u8 c)))) pbp
  |-- out_at (fst x) (snd x) sp pbp.
Proof.
  intros H Hok. destruct (c_put_byte_inv' _ _ _ H) as [Hr ->].
  apply (out_at_put_byte (fst om) (snd om) c sp pbp Hok Hr).
Qed.

Lemma c_put_byte_range om c x : c_put_byte om c = Some x -> 0 <= o_pending (fst om) < Zlength (o_buf (fst om)).
Proof. intros H. apply (c_put_byte_inv' _ _ _ H). Qed.

(** [out_at] opened, with the pending field's value as the forward steps need it. *)
Lemma out_at_open o m sp pbp : out_at o m sp pbp =
  (!! out_ok o m &&
  (@field_at DCS.CS Ews t_ds (DOT _pending) (Vlong (Int64.repr (o_pending o))) sp *
   @field_at DCS.CS Ews t_ds (DOT _pending_buf) pbp sp *
   @field_at DCS.CS Ews t_ds (DOT _bi_buf) (vi (o_bi_buf o)) sp *
   @field_at DCS.CS Ews t_ds (DOT _bi_valid) (vi (o_bi_valid o)) sp *
   @field_at DCS.CS Ews t_ds (DOT _bi_used) (vi (o_bi_used o)) sp *
   @data_at DCS.CS Ews (tarray tuchar (Zlength (o_buf o))) (pb_vals (o_buf o) m) pbp))%logic.
Proof. reflexivity. Qed.

Lemma deflate_globals_fold gv :
  trees_globals gv * errmsg_at gv *
  @data_at DCS.CS Ers (tarray t_config 10) (config_vals gv) (gv _configuration_table) *
  @data_at DCS.CS Ers (tarray tschar 6) (map vi [49; 46; 51; 46; 50; 0]) (gv _my_version) *
  Zlib.proof.crc32.Spec.crc_table_at Ers gv |-- deflate_globals gv.
Proof. unfold deflate_globals. cancel. Qed.

Lemma out_at_fold o m sp pbp : out_ok o m ->
  @field_at DCS.CS Ews t_ds (DOT _pending) (Vlong (Int64.repr (o_pending o))) sp *
  @field_at DCS.CS Ews t_ds (DOT _pending_buf) pbp sp *
  @field_at DCS.CS Ews t_ds (DOT _bi_buf) (vi (o_bi_buf o)) sp *
  @field_at DCS.CS Ews t_ds (DOT _bi_valid) (vi (o_bi_valid o)) sp *
  @field_at DCS.CS Ews t_ds (DOT _bi_used) (vi (o_bi_used o)) sp *
  @data_at DCS.CS Ews (tarray tuchar (Zlength (o_buf o))) (pb_vals (o_buf o) m) pbp
  |-- out_at o m sp pbp.
Proof. intros. rewrite out_at_open. entailer!. Qed.

(** [return c;] against an abstract postcondition (floyd's forward refuses it). *)
Lemma semax_ret_const {Espec: OracleKind} (P: environ -> mpred) (R: ret_assert) (r: Z) (e: expr):
  (forall rho, eval_expr (Ecast e tint) rho = Vint (Int.repr r)) ->
  ENTAIL Delta_df, P |-- tc_expr Delta_df (Ecast e tint) ->
  ENTAIL Delta_df, P |-- RA_return R (Some (Vint (Int.repr r))) ->
  semax Delta_df P (Sreturn (Some e)) R.
Proof.
  intros He Htc HP.
  eapply semax_pre; [ | apply semax_return ].
  change (ret_type Delta_df) with tint.
  apply andp_right; [ exact Htc | ].
  intro rho. specialize (HP rho). cbv beta in HP.
  assert (E: cast_expropt (Some e) tint rho = Some (Vint (Int.repr r))).
  { change (cast_expropt (Some e) tint rho) with (Some (eval_expr (Ecast e tint) rho)). rewrite He. reflexivity. }
  change (liftx (RA_return R) (cast_expropt (Some e) tint) id rho)
    with (RA_return R (cast_expropt (Some e) tint rho) (id rho)).
  rewrite E. exact HP.
Qed.

(** [Int.repr a = Int.zero] for a signed [a] in range: [a = 0]. *)
Ltac int_zero := match goal with Hx : Int.repr ?a = Int.zero |- _ =>
  change Int.zero with (Int.repr 0) in Hx; apply repr_inj_signed in Hx; [|rep_lia|rep_lia] end.

(** One put_byte: open [out_at], the C steps, fold the result. *)
Ltac pb_open Hp :=
  let Hr := fresh "Hr" in pose proof (c_put_byte_range _ _ _ Hp) as Hr;
  rewrite out_at_open; Intros.
Ltac pb_close Hp :=
  try (change (Int.signed (Int.repr 1)) with 1; rewrite add64_repr);
  norm_byte_val;
  match type of Hp with c_put_byte ?om ?c = Some ?x =>
    match goal with Hok : out_ok (fst om) (snd om) |- _ =>
    match goal with |- context [@field_at _ _ _ (DOT _pending_buf) ?pbp ?sp] =>
      sep_apply (out_at_put_byte_x om c x sp pbp Hp Hok) end end end.
Ltac pb_const Hp := pb_open Hp; forward; forward; forward; forward; pb_close Hp.
Lemma zmm64 a : 0 <= a <= Int64.max_unsigned -> Int64.Z_mod_modulus a = a.
Proof. intros. rewrite Int64.Z_mod_modulus_eq. apply Z.mod_small. rep_lia. Qed.

Lemma land_range8 a : 0 <= a -> 0 <= Z.land a 255 < 256.
Proof.
  intros. change 255 with (Z.ones 8). rewrite Z.land_ones by lia.
  apply Z.mod_pos_bound. reflexivity.
Qed.

Lemma byte_long a : 0 <= a <= Int64.max_unsigned ->
  Int64.Z_mod_modulus (Z.land (Int64.Z_mod_modulus a) 255) = Z.land a 255.
Proof. intros. rewrite (zmm64 a) by auto. pose proof (land_range8 a ltac:(lia)). apply zmm64. rep_lia. Qed.

Lemma shiftr_range a k : 0 <= a -> 0 <= k -> 0 <= Z.shiftr a k <= a.
Proof.
  intros Ha Hk. rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia]|].
  apply Z.div_le_upper_bound; [apply Z.pow_pos_nonneg; lia|].
  assert (1 <= 2 ^ k) by (apply Z.pow_le_mono_r with (a := 2) (b := 0) in Hk; [simpl in Hk; lia | lia]). nia.
Qed.


(** ** The z_stream folded back unchanged *)
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

(** ** The final state: wrap negated *)
Lemma dstate_ranges_wrap s w : dstate_ranges s -> s32_ok w -> dstate_ranges (set_d_wrap s w).
Proof. intros H Hw. destruct s. unfold dstate_ranges in *. cbn in *. tauto. Qed.

Lemma wrap_frame_fold s w z p pin ish gv :
  dstate_ranges s -> readable_share ish -> s32_ok w ->
  ltree_at (tr_ltree (d_tr s)) (p_s p) * dtree_at (tr_dtree (d_tr s)) (p_s p) *
  sym_at (d_tr s) (p_s p) (p_pbuf p) * dtype_at (d_tr s) (p_s p) (p_strm p) * lvl_at (d_tr s) (p_s p) *
  trees_rest (d_tr s) (p_s p) (p_strm p) gv *
  win_at s p * hash_at s p * match_at s p * cfg_at s p *
  @field_at DCS.CS Ews t_ds (DOT _status) (vi (d_status s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _pending_buf_size) (vl (d_pending_buf_size s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _wrap) (vi w) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _gzhead) (p_gzhead p) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _gzindex) (vl (d_gzindex s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _method) (vi (d_method s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _last_flush) (vi (d_last_flush s)) (p_s p) *
  in_obj ish z pin
  |-- flush_frame (set_d_wrap s w) z p pin ish gv.
Proof.
  intros Hs Hi Hw. pose proof (dstate_ranges_wrap s w Hs Hw).
  unfold flush_frame.
  change (d_tr (set_d_wrap s w)) with (d_tr s). change (win_at (set_d_wrap s w) p) with (win_at s p).
  change (hash_at (set_d_wrap s w) p) with (hash_at s p). change (match_at (set_d_wrap s w) p) with (match_at s p).
  change (cfg_at (set_d_wrap s w) p) with (cfg_at s p).
  entailer!.
Qed.

Lemma wrap_state_eq s o1 o2 po w :
  set_d_wrap (set_d_po (set_d_out (set_d_out s o1) o2) po) w = set_d_po (set_d_out (set_d_wrap s w) o2) po.
Proof. destruct s as [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? t ?]; destruct t; reflexivity. Qed.

Lemma byte_long_sh a k : 0 <= a <= Int64.max_unsigned -> 0 <= k ->
  Int64.Z_mod_modulus (Z.land (Int64.Z_mod_modulus (Z.shiftr (Int64.Z_mod_modulus a) k)) 255) =
  Z.land (Z.shiftr a k) 255.
Proof.
  intros Ha Hk. rewrite (zmm64 a) by auto. pose proof (shiftr_range a k ltac:(lia) Hk).
  apply byte_long. lia.
Qed.

Lemma byte_shru a k : 0 <= a <= Int64.max_unsigned -> 0 <= k < 64 ->
  Int64.Z_mod_modulus (Z.land (Int64.unsigned (Int64.shru (Int64.repr a) (Int64.repr (Int.unsigned (Int.repr k))))) 255) =
  Z.land (Z.shiftr a k) 255.
Proof.
  intros Ha Hk. rewrite (Int.unsigned_repr k) by rep_lia. unfold Int64.shru.
  rewrite (Int64.unsigned_repr a) by rep_lia. rewrite (Int64.unsigned_repr k) by rep_lia.
  pose proof (shiftr_range a k ltac:(lia) ltac:(lia)).
  rewrite (Int64.unsigned_repr (Z.shiftr a k)) by rep_lia.
  pose proof (land_range8 (Z.shiftr a k) ltac:(lia)). apply zmm64. rep_lia.
Qed.

Ltac byte_norm :=
  first [ rewrite byte_shru by (auto; lia) | rewrite byte_long_sh by (auto; lia) | rewrite byte_long by auto ].
(** Stores of a shifted 64-bit value: keep [Int64.shru] folded (simpl on [Z.shiftr _ 24] blows up). *)
Ltac fwd_sh := with_strategy opaque [Int64.shru] forward.

Lemma land_range16 a : 0 <= a -> 0 <= Z.land a 65535 < 65536.
Proof.
  intros. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia.
  apply Z.mod_pos_bound. reflexivity.
Qed.

(** [return e;] whose value [v] is known from the precondition, against an abstract postcondition. *)
Lemma semax_ret_val {Espec: OracleKind} (P: environ -> mpred) (R: ret_assert) (v: val) (e: expr):
  ENTAIL Delta_df, P |-- tc_expr Delta_df (Ecast e tint) ->
  ENTAIL Delta_df, P |-- (fun rho => !! (eval_expr (Ecast e tint) rho = v)) ->
  ENTAIL Delta_df, P |-- RA_return R (Some v) ->
  semax Delta_df P (Sreturn (Some e)) R.
Proof.
  intros Htc Hv HP.
  eapply semax_pre; [ | apply semax_return ].
  change (ret_type Delta_df) with tint.
  apply andp_right; [ exact Htc | ].
  intro rho. specialize (HP rho). specialize (Hv rho). cbv beta in HP, Hv.
  change (liftx (RA_return R) (cast_expropt (Some e) tint) id rho)
    with (RA_return R (cast_expropt (Some e) tint rho) (id rho)).
  change (cast_expropt (Some e) tint rho) with (Some (eval_expr (Ecast e tint) rho)).
  apply derives_trans with (!! (eval_expr (Ecast e tint) rho = v) && RA_return R (Some v) rho).
  { apply andp_right; auto. }
  normalize. apply derives_refl.
Qed.

Lemma stage_trailer : stage_ok S_trailer (fun f s z => c_trailer2 s z f).
Proof.
  intros Espec p pin pout ish R msgv gv flush s z X res Hfl Hc. cbv beta in Hc.
  unfold stage_pre, stage_post, df_locals.
  cbv [S_trailer chain_from df_body f_deflate fn_body].
  sep_apply (dfull_flush_open s z p pin pout ish R msgv gv). Intros.
  unfold flush_frame. Intros.
  destruct res as [[s' z'] o].
  unfold c_trailer2, c_deflate_trailer in Hc.
  forward_if.
  { (* flush <> Z_FINISH *)
    rewrite (proj2 (Z.eqb_neq _ _)) in Hc by (intro E; subst flush; contradiction).
    cbn [negb bind] in Hc. inversion Hc; subst s' z' o; clear Hc.
    unfold MORE_COMMANDS, abbreviate. apply semax_seq with (Q := FF); [| apply semax_ff].
    apply semax_ret_const with (r := 0); [intro rho; reflexivity | entailer! | ].
    unfold abbreviate in POSTCONDITION; subst POSTCONDITION.
    cbn [RA_return overridePost stage_post].
    Exists msgv. rewrite rest_after_refl.
    sep_apply (flush_frame_fold s z p pin ish gv); auto.
    sep_apply (dfull_flush_back s z p pin pout ish R msgv gv); auto.
    entailer!. }
  subst flush. rewrite (proj2 (Z.eqb_eq _ _)) in Hc by reflexivity. cbn [negb] in Hc.
  forward.
  forward_if.
  { (* wrap <= 0 *)
    assert (Hw : d_wrap s <= 0) by (open_dranges H1; unfold s32_ok in *; rewrite Int.signed_repr in H3 by rep_lia; lia).
    rewrite (proj2 (Z.leb_le _ _)) in Hc by lia.
    cbn [bind] in Hc. inversion Hc; subst s' z' o; clear Hc.
    unfold MORE_COMMANDS, abbreviate. apply semax_seq with (Q := FF); [| apply semax_ff].
    apply semax_ret_const with (r := 1); [intro rho; reflexivity | entailer! | ].
    unfold abbreviate in POSTCONDITION; subst POSTCONDITION.
    cbn [RA_return overridePost stage_post].
    Exists msgv. rewrite rest_after_refl.
    sep_apply (flush_frame_fold s z p pin ish gv); auto.
    sep_apply (dfull_flush_back s z p pin pout ish R msgv gv); auto.
    entailer!. }
  assert (Hw : 0 < d_wrap s) by (open_dranges H1; unfold s32_ok in *; rewrite Int.signed_repr in H3 by rep_lia; lia).
  rewrite (proj2 (Z.leb_gt _ _)) in Hc by lia.
  inv_bind Hc. destruct x as [[s3 z3] rc]. inversion Hc; subst s' z' o; clear Hc. rename Ha into Hc.
  inv_bind Hc. rename x into s1, Ha into Hs1.
  inv_bind Hc. destruct x as [s2 z2]. rename Ha into Hf.
  forward.
  sep_apply (flush_frame_fold s z p pin ish gv); auto.
  forward_if (EX om : cout,
    PROP (s1 = set_d_out s om)
    LOCAL (temp _strm (p_strm p); temp _s (p_s p); temp _flush (vi 4); gvars gv)
    SEP (strm_at z (p_s p) (p_strm p) pin pout msgv gv; out_space z pout R;
         @field_at DCS.CS Ews t_ds (DOT _pending_out) (offset_val (d_po s) (p_pbuf p)) (p_s p);
         out_at (fst om) (snd om) (p_s p) (p_pbuf p); flush_frame s z p pin ish gv; deflate_globals gv; X)).
  { (* gzip trailer *)
    assert (E2 : d_wrap s = 2) by (open_dranges H1; unfold s32_ok in *; apply repr_inj_signed; auto; rep_lia).
    rewrite E2, Z.eqb_refl in Hs1.
    apply c_dput_bytes_inv in Hs1. destruct Hs1 as [om [Hp ->]].
    cbn [c_put_bytes] in Hp.
    inv_bind Hp. rename x into q1, Ha into Hq1.
    inv_bind Hp. rename x into q2, Ha into Hq2.
    inv_bind Hp. rename x into q3, Ha into Hq3.
    inv_bind Hp. rename x into q4, Ha into Hq4.
    inv_bind Hp. rename x into q5, Ha into Hq5.
    inv_bind Hp. rename x into q6, Ha into Hq6.
    inv_bind Hp. rename x into q7, Ha into Hq7.
    inv_bind Hp. rename x into q8, Ha into Hq8. inversion Hp; subst q8; clear Hp.
    rewrite strm_at_open. Intros.
    assert (Had : 0 <= z_adler z <= Int64.max_unsigned) by (open_zranges H; auto).
    assert (Hti : 0 <= z_total_in z <= Int64.max_unsigned) by (open_zranges H; auto).
    pb_open Hq1.
    match goal with Hk : out_ok (tr_out (d_tr s)) (d_pbm s) |- _ =>
      assert (Hok : out_ok (fst (d_out s)) (snd (d_out s))) by exact Hk end.
    forward. forward. forward. forward. forward. byte_norm. pb_close Hq1.
    pb_open Hq2. forward. forward. forward. forward. fwd_sh. byte_norm. pb_close Hq2.
    pb_open Hq3. forward. forward. forward. forward. fwd_sh. byte_norm. pb_close Hq3.
    pb_open Hq4. forward. forward. forward. forward. fwd_sh. byte_norm. pb_close Hq4.
    pb_open Hq5. forward. forward. forward. forward. forward. byte_norm. pb_close Hq5.
    pb_open Hq6. forward. forward. forward. forward. fwd_sh. byte_norm. pb_close Hq6.
    pb_open Hq7. forward. forward. forward. forward. fwd_sh. byte_norm. pb_close Hq7.
    pb_open Hq8. forward. forward. forward. forward. fwd_sh. byte_norm. pb_close Hq8.
    sep_apply (strm_at_fold z (p_s p) (p_strm p) pin pout msgv gv).
    Exists om. entailer!. }
  { (* zlib trailer *)
    assert (E2 : d_wrap s <> 2) by (intro E; rewrite E in *; contradiction).
    rewrite (proj2 (Z.eqb_neq _ _) E2) in Hs1.
    inv_bind Hs1. rename x into s1a, Ha into Hs1a.
    rewrite c_putShortMSB_eq in Hs1a. inv_bind Hs1a. rename x into om2, Ha into Hp2.
    inversion Hs1a; subst s1a; clear Hs1a.
    rewrite c_putShortMSB_eq, d_out_set_d_out in Hs1. inv_bind Hs1. rename x into om3, Ha into Hp3.
    inversion Hs1; subst s1; clear Hs1.
    rewrite strm_at_open. Intros.
    assert (Had : 0 <= z_adler z <= Int64.max_unsigned) by (open_zranges H; auto).
    pose proof (shiftr_range (z_adler z) 16 ltac:(lia) ltac:(lia)) as Hsh.
    pose proof (land_range16 (z_adler z) ltac:(lia)) as Hla.
    forward.
    forward_call (p_s p, p_pbuf p, tr_out (d_tr s), d_pbm s, u32 (Z.shiftr (z_adler z) 16), om2).
    { entailer!. simpl.
      rewrite (zmm64 (z_adler z)) by rep_lia. rewrite zmm64 by rep_lia. unfold vi. rewrite repr_u32. reflexivity. }
    { pose proof (u32_range (Z.shiftr (z_adler z) 16)). repeat split; try lia; exact Hp2. }
    forward.
    forward_call (p_s p, p_pbuf p, fst om2, snd om2, u32 (Z.land (z_adler z) 65535), om3).
    { entailer!. simpl. rewrite zmm64 by rep_lia. unfold vi. rewrite repr_u32. reflexivity. }
    { pose proof (u32_range (Z.land (z_adler z) 65535)). destruct om2. repeat split; try lia; exact Hp3. }
    sep_apply (strm_at_fold z (p_s p) (p_strm p) pin pout msgv gv).
    Exists om3. entailer!. }
  Intros om. subst s1.
  change (out_at (fst om) (snd om)) with (out_at (tr_out (d_tr (set_d_out s om))) (d_pbm (set_d_out s om))).
  change (offset_val (d_po s) (p_pbuf p)) with (offset_val (d_po (set_d_out s om)) (p_pbuf p)).
  forward_call (p_strm p, p_s p, p_pbuf p, pin, pout, msgv, R, set_d_out s om, z, (s2, z2), gv).
  cbn [fst snd].
  destruct (c_flush_pending_same _ _ _ _ Hf) as (Ein2 & Emsg2 & _).
  destruct (c_flush_pending_inv _ _ _ _ H Hf) as ([ob2 m2] & po2 & -> & Hpo2 & Hg2).
  change (tr_out (d_tr (set_d_po (set_d_out (set_d_out s om) (ob2, m2)) po2))) with ob2.
  change (d_pbm (set_d_po (set_d_out (set_d_out s om) (ob2, m2)) po2)) with m2.
  change (d_po (set_d_po (set_d_out (set_d_out s om) (ob2, m2)) po2)) with po2.
  change (d_wrap (set_d_po (set_d_out (set_d_out s om) (ob2, m2)) po2)) with (d_wrap s) in Hc.
  replace (d_wrap s >? 0) with true in Hc by (symmetry; apply Z.gtb_lt; lia).
  change (d_pending (set_d_wrap (set_d_po (set_d_out (set_d_out s om) (ob2, m2)) po2) (- d_wrap s)))
    with (o_pending ob2) in Hc.
  inversion Hc; subst s3 z3 rc; clear Hc.
  rewrite out_at_open. Intros.
  destruct (Hg2 ltac:(assumption)) as [Hz2 Hgr2].
  assert (Hpo2' : 0 <= po2) by (apply Hpo2; open_dranges H1; auto).
  assert (Hm2 : msg_ok (z_msg z2) msgv) by (rewrite Emsg2; assumption).
  unfold flush_frame. Intros.
  forward.
  forward_if_sep (@field_at DCS.CS Ews t_ds (DOT _wrap) (vi (d_wrap s)) (p_s p))
                 (@field_at DCS.CS Ews t_ds (DOT _wrap) (vi (- d_wrap s)) (p_s p)).
  { forward. forward.
    { open_dranges H1. unfold s32_ok in *. entailer!. change (Int.signed Int.zero) with 0. rep_lia. }
    rewrite neg_repr. entailer!. }
  { exfalso. open_dranges H1. unfold s32_ok in *. rewrite Int.signed_repr in * by rep_lia. lia. }
  forward.
  forward_if_temp _t'88 (vi (if negb (o_pending ob2 =? 0) then DState.Z_OK else DState.Z_STREAM_END)).
  { forward. entailer!.
    assert (Hp0 : o_pending ob2 <> 0).
    { intro E. match goal with Hn : Int64.repr (o_pending ob2) <> _ |- _ => apply Hn; rewrite E; reflexivity end. }
    rewrite (proj2 (Z.eqb_neq _ _) Hp0). reflexivity. }
  { forward. entailer!.
    assert (Hp0 : o_pending ob2 = 0).
    { match goal with Hk : out_ok ob2 m2 |- _ => destruct Hk as (_ & _ & Hpr & _) end.
      match goal with Hx : Int64.repr (o_pending ob2) = _ |- _ =>
        apply (f_equal Int64.unsigned) in Hx; rewrite !Int64.unsigned_repr in Hx by rep_lia; exact Hx end. }
    rewrite Hp0. reflexivity. }
  sep_apply (out_at_fold ob2 m2 (p_s p) (p_pbuf p)); auto.
  apply semax_ret_val with (v := vi (if negb (o_pending ob2 =? 0) then DState.Z_OK else DState.Z_STREAM_END)).
  { entailer!. }
  { go_lowerx. apply prop_right. destruct H7 as [Hx _].
    change (vi (if negb (o_pending ob2 =? 0) then DState.Z_OK else DState.Z_STREAM_END) = eval_id _t'88 rho) in Hx.
    change (force_val1 (sem_cast_i2i I32 Signed) (eval_id _t'88 rho) =
            vi (if negb (o_pending ob2 =? 0) then DState.Z_OK else DState.Z_STREAM_END)).
    rewrite <- Hx. destruct (negb _); reflexivity. }
  unfold abbreviate in POSTCONDITION; subst POSTCONDITION.
  cbn [RA_return stage_post].
  Exists msgv.
  rewrite wrap_state_eq.
  sep_apply (wrap_frame_fold s (- d_wrap s) z p pin ish gv); auto.
  { open_dranges H1. unfold s32_ok in *. rep_lia. }
  sep_apply (dfull_out_close (set_d_wrap s (- d_wrap s)) z z2 ob2 m2 po2 p pin pout ish (rest_after z z2 R) msgv gv); auto.
  entailer!.
Qed.
