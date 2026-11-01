(* inflate()'s exit inf_leave, the tail after the window update (Body5ExitKit.v ex_tail_stmt). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate_api.Body5Parts.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.inflate_api.Body5ExitKit.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* ---------------------------------------------------------------------------------------------- *)
(* the statement cut into its pieces                                                              *)

(* in -= avail_in; out -= avail_out; total_in, total_out, state->total *)
Definition et_cnt : statement :=
  match ex_tail with Ssequence a (Ssequence b (Ssequence c (Ssequence d (Ssequence e _)))) =>
    Ssequence a (Ssequence b (Ssequence c (Ssequence d e))) | _ => Sskip end.
(* if ((wrap & 4) && out) strm->adler = state->check = UPDATE_CHECK(...) *)
Definition et_chk : statement :=
  match ex_tail with Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence k _))))) => k
  | _ => Sskip end.
(* data_type; the return code; return *)
Definition et_end : statement :=
  match ex_tail with Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ r))))) => r
  | _ => Sskip end.

Lemma ex_tail_split: forall {Espec: OracleKind} Delta P Q R S,
  semax Delta P et_cnt (normal_ret_assert Q) ->
  semax Delta Q et_chk (normal_ret_assert S) ->
  semax Delta S et_end R ->
  semax Delta P ex_tail R.
Proof.
  intros Espec Delta P Q R S H1 H2 H3.
  eapply semax_unfold_Ssequence; [ | eapply semax_seq'; [exact H1 | eapply semax_seq'; [exact H2 | exact H3]]].
  reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the model cut along the pieces                                                                 *)

Definition lt_inn (m: mst) : Z := u32 (m_in m - m_have m).
Definition lt_out (m: mst) : Z := u32 (m_out m - m_left m).
Definition lt_m1 (m: mst) : mst :=
  upd_s (set_m_tout (set_m_tin m (u64 (m_tin m + lt_inn m))) (u64 (m_tout m + lt_out m)))
        (fun s => set_i_total s (u64 (i_total s + lt_out m))).
Definition lt_cond (m: mst) : bool := (negb (Z.land (i_wrap (m_s m)) 4 =? 0) && negb (lt_out m =? 0))%bool.
Definition lt_c (m: mst) : Z :=
  update_check (i_flags (m_s m)) (i_check (m_s m))
    (sublist (Zlength (m_ow m) - lt_out m) (Zlength (m_ow m)) (m_ow m)).
Definition lt_m2 (m: mst) : mst :=
  if lt_cond m then set_m_adler (upd_s (lt_m1 m) (fun s => set_i_check s (lt_c m))) (lt_c m) else lt_m1 m.
Definition lt_dt (m2: mst) : Z :=
  m_bits m2 + (if i_last (m_s m2) =? 0 then 0 else 64) +
  (if i_mode (m_s m2) =? Zlib.proof.inflate.Model.TYPE then 128 else 0) +
  (if ((i_mode (m_s m2) =? LEN_) || (i_mode (m_s m2) =? COPY_))%bool then 256 else 0).
Definition lt_ret (flush: Z) (m: mst) : Z :=
  if ((((lt_inn m =? 0) && (lt_out m =? 0)) || (flush =? Z_FINISH)) && (m_ret m =? Z_OK))%bool
  then Z_BUF_ERROR else m_ret m.

Lemma leave_tail_eq: forall flush m,
  leave_tail flush m = Res (lt_ret flush m) (lt_m2 m) (Some (lt_dt (lt_m2 m))).
Proof.
  intros. unfold leave_tail, lt_ret, lt_m2, lt_dt, lt_cond, lt_c, lt_m1, lt_inn, lt_out.
  cbv zeta. cbn [upd_s set_m_s set_m_tout set_m_tin m_s set_i_total i_wrap i_flags i_check m_ow].
  destruct (negb (Z.land (i_wrap (m_s m)) 4 =? 0) && negb (u32 (m_out m - m_left m) =? 0))%bool; reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the assertion between the pieces                                                               *)

Definition tst (F: frame) (X: mpred) (m0 m: mst) (vin vout: Z) : environ -> mpred :=
  PROP (out_ok (f_ob F) (m_aout m))
  LOCAL (temp _strm (f_strmp F); temp _flush (zv (f_flush F)); temp _state (f_sp F);
         temp _in (zv vin); temp _out (zv vout); temp _ret (zv (m_ret m));
         lvar _here t_code (f_vhere F); lvar _last t_code (f_vlast F);
         lvar _hbuf (tarray tuchar 4) (f_vhbuf F); gvars (f_gv F))
  SEP (field_at Ews t_state (DOT _mode) (zv (i_mode (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _last) (zv (i_last (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _wrap) (zv (i_wrap (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _flags) (zv (i_flags (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _check) (lv (i_check (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _total) (lv (i_total (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _wsize) (zv (i_wsize (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _hold) (lv (i_hold (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _bits) (zv (i_bits (m_s m))) (f_sp F);
       strm_e F m; out_rep (f_ob F) (m_ow m); crc_table_at (f_tsh F) (f_gv F); mem_rep_e F m;
       locals_rep F; hdr_tok F m0; mem_mgr (f_gv F); zfuncs (f_gv F); X).

Lemma ck_add_u64: forall a b, Int64.add (Int64.repr a) (Int64.repr b) = Int64.repr (u64 (a + b)).
Proof.
  intros. unfold Int64.add. apply Int64.eqm_samerepr. unfold u64.
  change (2 ^ 64) with Int64.modulus.
  apply Int64.eqm_trans with (a + b).
  - apply Int64.eqm_add; apply Int64.eqm_sym; apply Int64.eqm_unsigned_repr.
  - unfold Int64.eqm. apply Zbits.eqmod_mod. apply Int64.modulus_pos.
Qed.

Lemma lt_inn_eq: forall m, tail_facts m -> lt_inn m = m_nx m.
Proof.
  intros m TF. destruct TF as (T1 & T2 & T3 & T4 & T5 & T6 & _). unfold lt_inn, m_have, u32.
  rewrite T4. replace (Zlength (m_inp m) - (Zlength (m_inp m) - m_nx m)) with (m_nx m) by lia.
  apply Z.mod_small. rep_lia.
Qed.

Lemma lt_out_eq: forall m, tail_facts m -> lt_out m = m_out m - m_left m /\ 0 <= lt_out m <= Zlength (m_ow m).
Proof.
  intros m TF. destruct TF as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & _). unfold lt_out, m_left, u32 in *.
  rewrite Z.mod_small by rep_lia. split; [reflexivity | lia].
Qed.

Lemma et_cnt_ok {Espec: OracleKind} (F: frame) (X: mpred) (m: mst):
  frame_ok5 F -> tail_facts m ->
  semax Delta_inflate5 (lstate F X m) et_cnt
    (normal_ret_assert (tst F X m (lt_m1 m) (lt_inn m) (lt_out m))).
Proof.
  intros FOK TF.
  pose proof (lt_inn_eq m TF) as EI. pose proof (lt_out_eq m TF) as [EO RO].
  pose proof TF as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & T10 & T11 & T12 & T13 & _).
  pose proof FOK as ((HWS & HWH & HRG & HRT) & HFL).
  cbv beta iota zeta delta [et_cnt ex_tail inflate_exit f_inflate fn_body].
  rewrite lstate_esplit. unfold lstate_e, strm_e, strm_rep.
  abbreviate_semax.
  remember (f_gv F _zcalloc) as zca eqn:Hzca. remember (f_gv F _zcfree) as zcf eqn:Hzcf.
  forward. forward. forward. forward. forward. forward. forward. forward. forward. forward.
  assert (SI: Int.sub (Int.repr (m_in m)) (Int.repr (Zlength (m_inp m) - m_snx m)) = Int.repr (lt_inn m))
    by (rewrite sub_repr, EI; f_equal; lia).
  assert (SO: Int.sub (Int.repr (m_out m)) (Int.repr (m_aout m - m_sow m)) = Int.repr (lt_out m))
    by (rewrite sub_repr, EO; f_equal; unfold m_left; lia).
  assert (UI: Int.unsigned (Int.repr (lt_inn m)) = lt_inn m) by (rewrite Int.unsigned_repr; rep_lia).
  assert (UO: Int.unsigned (Int.repr (lt_out m)) = lt_out m) by (rewrite Int.unsigned_repr; rep_lia).
  rewrite SI, SO, UI, UO, !ck_add_u64.
  unfold tst, strm_e, strm_rep.
  change (mem_rep_e F (lt_m1 m)) with (mem_rep_e F m).
  unfold lt_m1, upd_s.
  cbn [m_s set_m_s set_m_tout set_m_tin set_i_total i_mode i_last i_wrap i_flags i_check i_total i_wsize i_hold
       i_bits m_tin m_tout m_snx m_sow m_inp m_aout m_msg m_adler m_ret m_ow].
  rewrite <- Hzca, <- Hzcf.
  entailer!.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* UPDATE_CHECK (after CaseCHECK5.v ck_upd_ok, CKKit5.v)                                          *)

Lemma ck_land_range: forall a b, 0 <= b -> 0 <= Z.land a b <= b.
Proof.
  intros a b H. split.
  - apply Z.land_nonneg; auto.
  - apply Zbits.Ztestbit_le; auto. intros i _ T. rewrite Z.land_spec in T. apply andb_prop in T. tauto.
Qed.

Lemma ck_and_repr: forall a b, Int.and (Int.repr a) (Int.repr b) = Int.repr (Z.land a b).
Proof.
  intros. apply Int.same_bits_eq; intros i Hi.
  rewrite Int.bits_and by auto. rewrite !Int.testbit_repr by auto. rewrite Z.land_spec. reflexivity.
Qed.

Lemma ck_flagbit: forall a b, Int.and (Int.repr a) (Int.repr b) <> Int.zero -> (Z.land a b =? 0) = false.
Proof.
  intros a b H. rewrite ck_and_repr in H. apply Z.eqb_neq. intro E. rewrite E in H. apply H. reflexivity.
Qed.

Lemma ck_flagbit0: forall a b, Int.and (Int.repr a) (Int.repr b) = Int.zero -> 0 <= b <= Int.max_signed ->
  (Z.land a b =? 0) = true.
Proof.
  intros a b H Hb. rewrite ck_and_repr in H. apply Z.eqb_eq.
  pose proof (ck_land_range a b ltac:(lia)).
  apply (f_equal Int.unsigned) in H. rewrite Int.unsigned_repr in H by rep_lia. exact H.
Qed.

Lemma ck_int_zero: forall x, Int.min_signed <= x <= Int.max_signed -> Int.repr x = Int.zero -> x = 0.
Proof.
  intros x R H. apply (f_equal Int.signed) in H. rewrite Int.signed_repr in H by rep_lia. exact H.
Qed.

Lemma ck_tbool: forall x, 0 <= x <= Int.max_unsigned ->
  Vint (if Int.eq (Int.repr x) Int.zero then Int.zero else Int.one) = Vint (Int.repr (if x =? 0 then 0 else 1)).
Proof.
  intros x H. destruct (Z.eqb_spec x 0).
  - subst. reflexivity.
  - rewrite Int.eq_false; [reflexivity | ]. intro E. apply (f_equal Int.unsigned) in E.
    rewrite Int.unsigned_repr in E by rep_lia. apply n. exact E.
Qed.

(* the adler32/crc32 specs' buffer is stated in their units' compspecs *)
Lemma ck_da_cs_crc: forall sh n (v: list val) p,
  @data_at Zlib.units.Inflate.CS sh (tarray tuchar n) v p = @data_at Zlib.units.Crc32.CS sh (tarray tuchar n) v p.
Proof.
  intros.
  assert (E: @data_at Zlib.units.Crc32.CS sh (tarray tuchar n) v = @data_at Zlib.units.Inflate.CS sh (tarray tuchar n) v).
  { apply (@data_at_change_composite _ _ CCE_crc32); [apply JMeq_refl | reflexivity]. }
  rewrite E. reflexivity.
Qed.
Lemma ck_da_cs_adler: forall sh n (v: list val) p,
  @data_at Zlib.units.Inflate.CS sh (tarray tuchar n) v p = @data_at Zlib.units.Adler32.CS sh (tarray tuchar n) v p.
Proof.
  intros.
  assert (E: @data_at Zlib.units.Adler32.CS sh (tarray tuchar n) v = @data_at Zlib.units.Inflate.CS sh (tarray tuchar n) v).
  { apply (@data_at_change_composite _ _ CCE_adler32); [apply JMeq_refl | reflexivity]. }
  rewrite E. reflexivity.
Qed.

Lemma et_chk_ok {Espec: OracleKind} (F: frame) (X: mpred) (m: mst):
  frame_ok5 F -> tail_facts m ->
  semax Delta_inflate5 (tst F X m (lt_m1 m) (lt_inn m) (lt_out m)) et_chk
    (normal_ret_assert (tst F X m (lt_m2 m) (lt_inn m) (lt_out m))).
Proof.
  intros FOK TF.
  pose proof (lt_out_eq m TF) as [EO RO].
  pose proof TF as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & T10 & T11 & T12 & T13 & T14 & T15 & _).
  pose proof FOK as ((HWS & HWH & HRG & HRT) & HFL).
  cbv beta iota zeta delta [et_chk ex_tail inflate_exit f_inflate fn_body].
  unfold lt_m2. destruct (lt_cond m) eqn:Ec.
  2: { unfold tst. abbreviate_semax. Intros.
       forward.
       forward_if (temp _t'103 (Vint Int.zero)).
       - forward. entailer!.
         unfold lt_cond in Ec.
         match goal with HA: Int.and _ _ <> Int.zero |- _ => rewrite (ck_flagbit _ _ HA) in Ec end.
         cbn [negb andb] in Ec.
         apply negb_false_iff, Z.eqb_eq in Ec. rewrite Ec. reflexivity.
       - forward. entailer!.
       - forward_if.
         + exfalso. match goal with HA: 0 <> 0 |- _ => apply HA; reflexivity end.
         + forward. entailer!. }
  unfold lt_cond in Ec. apply andb_prop in Ec. destruct Ec as [Ec1 Ec2].
  apply negb_true_iff, Z.eqb_neq in Ec1. apply negb_true_iff, Z.eqb_neq in Ec2.
  set (c := lt_c m). set (o := lt_out m) in *.
  destruct F as [gv shs strmp sp headp winp hsh xb nb cb ib ob gsh tsh dt vres vhere vlast vhbuf flush].
  destruct ob as [osh op olo on oc].
  unfold tst, strm_e, strm_rep. cbn [f_ob f_gv f_sp f_strmp f_shs f_ib f_tsh f_dt f_vres f_vhere f_vlast f_vhbuf f_flush] in *.
  abbreviate_semax. Intros.
  assert (P1: m_ow (lt_m1 m) = m_ow m /\ m_aout (lt_m1 m) = m_aout m /\ m_sow (lt_m1 m) = Zlength (m_ow m) /\
              i_check (m_s (lt_m1 m)) = i_check (m_s m) /\ i_flags (m_s (lt_m1 m)) = i_flags (m_s m) /\
              i_wrap (m_s (lt_m1 m)) = i_wrap (m_s m))
    by (unfold lt_m1, upd_s; cbn; rewrite T2; repeat split; reflexivity).
  assert (Hc: c = update_check (i_flags (m_s m)) (i_check (m_s m)) (sublist (Zlength (m_ow m) - o) (Zlength (m_ow m)) (m_ow m)))
    by reflexivity.
  clearbody c.
  set (m1 := lt_m1 m) in *. clearbody m1.
  destruct P1 as (P1 & P2 & P3 & P4 & P5 & P6).
  rewrite P1, P2, P3, P4, P5, P6 in *.
  destruct H as (Hosh & Hop & Holo & Haout & Hlo & Hoc & Hon).
  unfold out_rep, out_ptr.
  remember (gv _zcalloc) as zca eqn:Hzca. remember (gv _zcfree) as zcf eqn:Hzcf.
  forward.
  forward_if (temp _t'103 (Vint Int.one)).
  { forward. entailer!. rewrite ck_tbool by rep_lia. rewrite (proj2 (Z.eqb_neq _ _) Ec2). reflexivity. }
  { exfalso. apply Ec1. apply Z.eqb_eq.
    match goal with HA: Int.and _ _ = Int.zero |- _ => apply (ck_flagbit0 _ _ HA); rep_lia end. }
  forward_if; [ | exfalso; match goal with HA: Int.one = Int.zero |- _ => exact (Int.one_not_zero HA) end].
  forward.
  set (ct := sublist 0 olo oc ++ byte_vals (m_ow m) ++ sublist (olo + Zlength (m_ow m)) on oc).
  set (d := sublist (Zlength (m_ow m) - o) (Zlength (m_ow m)) (m_ow m)) in Hc.
  assert (CB: cbuf_ok false (offset_val (olo + Zlength (m_ow m) - o) op) osh op (olo + Zlength (m_ow m) - o) on o ct d).
  { unfold cbuf_ok. split; [reflexivity | ]. split; [auto | ]. split; [lia | ]. split; [lia | ].
    split; [unfold d; rewrite Zlength_sublist by lia; lia | ]. split.
    { unfold d. apply Forall_sublist. exact T9. }
    unfold ct, d, bytes_rep, byte_vals. autorewrite with sublist. list_solve. }
  assert (PT: force_val (sem_sub_pi tuchar Unsigned (offset_val (olo + Zlength (m_ow m)) op) (Vint (Int.repr o))) =
              offset_val (olo + Zlength (m_ow m) - o) op).
  { destruct op; try contradiction. simpl. unfold sem_sub_pi. simpl.
    rewrite Ptrofs.mul_commut, Ptrofs.mul_one. unfold Ptrofs.of_intu, Ptrofs.of_int.
    rewrite Int.unsigned_repr by rep_lia. f_equal.
    rewrite Ptrofs.sub_add_opp, Ptrofs.add_assoc. f_equal.
    rewrite Ptrofs.neg_repr, ptrofs_add_repr. f_equal; lia. }
  forward_if (temp _t'99 (Vlong (Int64.repr c))).
  { (* crc32 *)
    forward. forward.
    forward_call (i_check (m_s m), offset_val (olo + Zlength (m_ow m) - o) op, o, false, osh, op,
                  olo + Zlength (m_ow m) - o, on, ct, d, false, Ews, gv, tsh).
    { rewrite <- ck_da_cs_crc. cancel. }
    { apply cbuf_valid_pos. lia. }
    forward.
    rewrite Hc. unfold update_check. rewrite (proj2 (Z.eqb_neq _ _) H0'). rewrite <- ck_da_cs_crc.
    entailer!. }
  { (* adler32 *)
    forward. forward.
    forward_call (i_check (m_s m), offset_val (olo + Zlength (m_ow m) - o) op, o, false, osh, op,
                  olo + Zlength (m_ow m) - o, on, ct, d, false, Ews).
    { rewrite <- ck_da_cs_adler. cancel. }
    { apply cbuf_valid_pos. lia. }
    forward.
    assert (F0: i_flags (m_s m) = 0) by (apply ck_int_zero; [unfold srange in T15; rep_lia | assumption]).
    rewrite Hc. unfold update_check. rewrite F0, Z.eqb_refl. rewrite <- ck_da_cs_adler.
    entailer!. }
  forward. forward. forward.
  match goal with |- context [mem_rep_e ?F0 (set_m_adler (upd_s m1 ?f) c)] =>
    change (mem_rep_e F0 (set_m_adler (upd_s m1 f) c)) with (mem_rep_e F0 m1) end.
  unfold upd_s, out_rep, out_ptr.
  cbn [m_s set_m_s set_m_adler set_i_check i_mode i_last i_wrap i_flags i_check i_total i_wsize i_hold i_bits
       m_tin m_tout m_snx m_sow m_inp m_aout m_msg m_adler m_ret m_ow].
  rewrite P1, P2, P3, P5, P6.
  subst ct.
  entailer!.
  unfold out_ok. split; [exact Hosh | ]. split; [exact Hop | ]. repeat split; auto; lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* data_type, the return code, return                                                             *)

Lemma semax_ret_tmp {Espec: OracleKind} (P: environ -> mpred) (R: ret_assert) (r: Z):
  ENTAIL Delta_inflate5, P |-- tc_expr Delta_inflate5 (Ecast (Etempvar _ret tint) tint) ->
  ENTAIL Delta_inflate5, P |-- local (locald_denote (temp _ret (Vint (Int.repr r)))) ->
  ENTAIL Delta_inflate5, P |-- RA_return R (Some (Vint (Int.repr r))) ->
  semax Delta_inflate5 P (Sreturn (Some (Etempvar _ret tint))) R.
Proof.
  intros Htc Hl HP.
  eapply semax_pre; [ | apply semax_return ].
  change (ret_type Delta_inflate5) with tint.
  apply andp_right; [ exact Htc | ].
  intro rho. specialize (HP rho). specialize (Hl rho). cbv beta in HP, Hl.
  apply derives_trans with (local (locald_denote (temp _ret (Vint (Int.repr r)))) rho && RA_return R (Some (Vint (Int.repr r))) rho).
  { apply andp_right; assumption. }
  unfold local, lift1, locald_denote. apply derives_extract_prop. intros E0.
  assert (E1: Vint (Int.repr r) = eval_id _ret rho /\ Vint (Int.repr r) <> Vundef) by exact E0.
  destruct E1 as [E _].
  change (liftx (RA_return R) (cast_expropt (Some (Etempvar _ret tint)) tint) id rho)
    with (RA_return R (cast_expropt (Some (Etempvar _ret tint)) tint rho) (id rho)).
  assert (C: cast_expropt (Some (Etempvar _ret tint)) tint rho = Some (Vint (Int.repr r))).
  { unfold cast_expropt. simpl.
    change (liftx Some (liftx (force_val1 (sem_cast_i2i I32 Signed)) (eval_id _ret)) rho)
      with (Some (force_val1 (sem_cast_i2i I32 Signed) (eval_id _ret rho))).
    rewrite <- E. reflexivity. }
  rewrite C. apply derives_refl.
Qed.

Lemma mem_rep_e_dt: forall F w dt m, w = f_winp F -> mem_rep_e (set_f_winp_dt F w dt) m = mem_rep_e F m.
Proof. intros. subst. destruct F. reflexivity. Qed.

Definition lt_r (flush inn o ret: Z) : Z :=
  if ((((inn =? 0) && (o =? 0)) || (flush =? Z_FINISH)) && (ret =? Z_OK))%bool then Z_BUF_ERROR else ret.

Lemma int_eq_b: forall x y, repable_signed x -> repable_signed y ->
  bool2val (Int.eq (Int.repr x) (Int.repr y)) = Vint (Int.repr (if x =? y then 1 else 0)).
Proof.
  intros x y Hx Hy. destruct (Z.eqb_spec x y).
  - subst. rewrite Int.eq_true. reflexivity.
  - rewrite Int.eq_false; [reflexivity | ]. intro E. apply n. apply repr_inj_signed; auto.
Qed.

Ltac zfix :=
  unfold Zlib.proof.inflate.Model.TYPE, LEN_, COPY_, Z_FINISH, Z_OK, Z_BUF_ERROR;
  repeat match goal with
  | H: Int.repr ?x = Int.zero |- _ =>
      let E := fresh "E" in assert (E: x = 0) by (apply ck_int_zero; [rep_lia | exact H]); clear H
  | H: Int.repr ?x = Int.repr ?y |- _ =>
      apply repr_inj_signed in H; [ | unfold repable_signed; rep_lia | unfold repable_signed; rep_lia]
  | H: Int.repr ?x <> Int.repr ?y |- _ =>
      apply repr_inj_signed' in H; [ | unfold repable_signed; rep_lia | unfold repable_signed; rep_lia]
  end;
  repeat match goal with
  | H: ?x <> ?y |- context [?x =? ?y] => rewrite (proj2 (Z.eqb_neq x y) H)
  | H: ?x = ?y |- context [?x =? ?y] => rewrite (proj2 (Z.eqb_eq x y) H)
  end; cbn [orb andb]; try reflexivity.

Ltac bcase :=
  match goal with |- context [if ?b then _ else _] =>
    let EB := fresh "EB" in destruct b eqn:EB; rewrite ?EB in * end;
  try reflexivity; exfalso;
  match goal with
  | H: Int.repr 0 <> Int.zero |- _ => apply H; reflexivity
  | H: Int.repr 1 = Int.zero |- _ => exact (Int.one_not_zero H)
  | H: Int.zero <> Int.zero |- _ => apply H; reflexivity
  | H: Int.one = Int.zero |- _ => exact (Int.one_not_zero H)
  end.

Ltac zeqfix :=
  unfold Z_FINISH, Z_OK;
  rewrite ?int_eq_b by (unfold repable_signed; rep_lia);
  try match goal with |- context [zeq ?a ?b] =>
    let E := fresh "E" in destruct (zeq a b) as [E|E];
    [rewrite (proj2 (Z.eqb_eq a b) E) | rewrite (proj2 (Z.eqb_neq a b) E)] end;
  rewrite ?Z.eqb_refl; cbn [orb andb]; try reflexivity.

Ltac bsplit t :=
  let bb := fresh "bb" in set (bb := t) in *; clearbody bb; destruct bb; cbn [orb andb].

Ltac bctr :=
  exfalso;
  match goal with
  | H: Int.repr _ <> Int.zero |- _ => apply H; reflexivity
  | H: Int.repr _ = Int.zero |- _ => apply Int.one_not_zero; rewrite <- H; reflexivity
  end.

Lemma et_end_ok {Espec: OracleKind} (F: frame) (X: mpred) (m0 m2: mst) (inn o: Z) (R: ret_assert):
  frame_ok5 F -> i_bits (m_s m2) = m_bits m2 -> 0 <= m_bits m2 <= 39 -> 0 <= i_last (m_s m2) <= 1 ->
  HEAD <= i_mode (m_s m2) <= SYNC -> -5 <= m_ret m2 <= 2 -> 0 <= inn <= Int.max_signed -> 0 <= o <= Int.max_signed ->
  ENTAIL Delta_inflate5,
    PROPx [] (LOCALx (ret_locals F)
      (SEPx [mem_rep (set_f_winp_dt F (f_winp F) (lt_dt m2)) m2;
             locals_rep F; hdr_tok F m0; mem_mgr (f_gv F); zfuncs (f_gv F); X]))
    |-- RA_return R (Some (zv (lt_r (f_flush F) inn o (m_ret m2)))) ->
  semax Delta_inflate5 (tst F X m0 m2 inn o) et_end R.
Proof.
  intros FOK HB RB RL RM RR RI RO HRET.
  unfold HEAD, SYNC in RM.
  destruct R as [Rn Rb Rc Rr]. cbn [RA_return] in HRET.
  pose proof FOK as ((HWS & HWH & HRG & HRT) & HFL).
  cbv beta iota zeta delta [et_end ex_tail inflate_exit f_inflate fn_body].
  unfold tst, strm_e, strm_rep.
  abbreviate_semax. Intros.
  remember (f_gv F _zcalloc) as zca eqn:Hzca. remember (f_gv F _zcfree) as zcf eqn:Hzcf.
  forward.
  forward_if (temp _t'104 (Vint (Int.repr (if i_last (m_s m2) =? 0 then 0 else 64)))).
  { forward. entailer!. zfix. }
  { forward. entailer!. zfix. }
  forward.
  forward_if (temp _t'105 (Vint (Int.repr (if i_mode (m_s m2) =? Zlib.proof.inflate.Model.TYPE then 128 else 0)))).
  { forward. entailer!. zfix. }
  { forward. entailer!. zfix. }
  forward.
  forward_if (temp _t'106 (Vint (Int.repr (if ((i_mode (m_s m2) =? LEN_) || (i_mode (m_s m2) =? COPY_))%bool then 1 else 0)))).
  { forward. entailer!. zfix. }
  { forward. forward. entailer!. zfix.
    destruct (zeq (i_mode (m_s m2)) 16194) as [E|E];
      [rewrite E; reflexivity | rewrite (proj2 (Z.eqb_neq _ _) E); reflexivity]. }
  forward_if (temp _t'107 (Vint (Int.repr (if ((i_mode (m_s m2) =? LEN_) || (i_mode (m_s m2) =? COPY_))%bool then 256 else 0)))).
  { forward. entailer!. bcase. }
  { forward. entailer!. bcase. }
  forward. forward.
  { entailer!.
    destruct (i_last (m_s m2) =? 0), (i_mode (m_s m2) =? Zlib.proof.inflate.Model.TYPE),
      ((i_mode (m_s m2) =? LEN_) || (i_mode (m_s m2) =? COPY_))%bool;
      rewrite !Int.signed_repr by rep_lia; rep_lia. }
  forward_if (temp _t'108 (Vint (Int.repr (if ((inn =? 0) && (o =? 0))%bool then 1 else 0)))).
  { forward. entailer!. zeqfix. }
  { forward. entailer!. zfix. }
  forward_if (temp _t'109 (Vint (Int.repr (if (((inn =? 0) && (o =? 0)) || (f_flush F =? Z_FINISH))%bool then 1 else 0)))).
  { forward. entailer!. bsplit ((inn =? 0) && (o =? 0))%bool; [reflexivity | bctr]. }
  { forward. entailer!. bsplit ((inn =? 0) && (o =? 0))%bool; [bctr | zeqfix]. }
  forward_if (temp _t'110 (Vint (Int.repr (if ((((inn =? 0) && (o =? 0)) || (f_flush F =? Z_FINISH)) && (m_ret m2 =? Z_OK))%bool then 1 else 0)))).
  { forward. entailer!. bsplit (((inn =? 0) && (o =? 0)) || (f_flush F =? Z_FINISH))%bool; [zeqfix | bctr]. }
  { forward. entailer!. bsplit (((inn =? 0) && (o =? 0)) || (f_flush F =? Z_FINISH))%bool; [bctr | reflexivity]. }
  forward_if (temp _ret (Vint (Int.repr (lt_r (f_flush F) inn o (m_ret m2))))).
  { forward. entailer!. unfold lt_r.
    bsplit ((((inn =? 0) && (o =? 0)) || (f_flush F =? Z_FINISH)) && (m_ret m2 =? Z_OK))%bool; [reflexivity | bctr]. }
  { forward. entailer!. unfold lt_r.
    bsplit ((((inn =? 0) && (o =? 0)) || (f_flush F =? Z_FINISH)) && (m_ret m2 =? Z_OK))%bool; [bctr | reflexivity]. }
  apply semax_ret_tmp with (r := lt_r (f_flush F) inn o (m_ret m2)).
  { entailer!. }
  { apply andp_left2. unfold PROPx, LOCALx. apply andp_left2. apply andp_left1.
    intro rho. unfold local, lift1. apply prop_derives. intros HL. exact (proj1 HL). }
  cbn [RA_return].
  eapply derives_trans; [ | exact HRET].
  apply andp_right; [apply andp_left1, derives_refl | ].
  unfold ret_locals. rewrite mem_rep_esplit, mem_rep_e_dt by reflexivity.
  unfold strm_e, strm_rep, set_f_winp_dt, lt_dt, state_f9.
  cbn [f_gv f_shs f_strmp f_sp f_ib f_ob f_tsh f_dt f_vres f_flush].
  rewrite <- HB, <- Hzca, <- Hzcf.
  entailer!.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the assembly                                                                                   *)

Lemma lt_m2_keep: forall m,
  i_bits (m_s (lt_m2 m)) = i_bits (m_s m) /\ m_bits (lt_m2 m) = m_bits m /\
  i_last (m_s (lt_m2 m)) = i_last (m_s m) /\ i_mode (m_s (lt_m2 m)) = i_mode (m_s m) /\
  m_ret (lt_m2 m) = m_ret m.
Proof. intros. unfold lt_m2. destruct (lt_cond m); repeat split; reflexivity. Qed.

Lemma ex_tail_ok : ex_tail_stmt.
Proof.
  intros Espec F X m R FOK TF HRET.
  rewrite leave_tail_eq in HRET. cbn [r_m r_ret] in HRET.
  change (res_dt F (Res (lt_ret (f_flush F) m) (lt_m2 m) (Some (lt_dt (lt_m2 m))))) with (lt_dt (lt_m2 m)) in HRET.
  pose proof (lt_inn_eq m TF) as EI. pose proof (lt_out_eq m TF) as [EO RO].
  pose proof (lt_m2_keep m) as (K1 & K2 & K3 & K4 & K5).
  pose proof TF as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & T10 & T11 & T12 & T13 & T14 & T15 & T16 & T17 & T18 & T19).
  apply ex_tail_split with (Q := tst F X m (lt_m1 m) (lt_inn m) (lt_out m))
                           (S := tst F X m (lt_m2 m) (lt_inn m) (lt_out m)).
  - apply et_cnt_ok; auto.
  - apply et_chk_ok; auto.
  - apply et_end_ok; auto.
    + rewrite K1, K2. exact T3.
    + rewrite K2. exact T16.
    + rewrite K3. exact T17.
    + rewrite K4. exact T18.
    + rewrite K5. exact T19.
    + rep_lia.
    + rep_lia.
    + rewrite K5. unfold lt_ret, lt_r in *. exact HRET.
Qed.
