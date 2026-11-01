(* case LENLENS after the loops: inflate_table(CODES, state->lens, 19, &state->next, &state->lenbits, state->work),
   BAD on an error, else CODELENS (falls through). (LLDefs5.ll_tail; TLFacts.v tl_s0 / tl_s1 / tl_r / tl_table_ok) *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate.CaseHyps5.
Require Import Zlib.proof.inflate.NeedKit5 Zlib.proof.inflate.NeedBits Zlib.proof.inflate.NeedBits3_5.
Require Import Zlib.proof.inflate.Model2 Zlib.proof.inflate.Steps2 Zlib.proof.inflate.MwfLemmas.
Require Import Zlib.proof.inflate.TLFacts Zlib.proof.inflate.TLKit5 Zlib.proof.inflate.LLDefs5.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.
(* the cross-compspecs call of inflate_table: the SEP is converted by hand (da_cs_* below); Floyd's own
   change_compspecs makes forward_call hang (as in Body5_dict) *)
Local Ltac change_compspecs cs ::= idtac.

(* the state after the zero loop *)
Lemma ll_sZ: forall m1, mwf m1 -> m_mode m1 = LENLENS -> i_ncode (m_s m1) <= i_have (m_s m1) ->
  swf (lenlens_zero 19 (m_s m1)) /\ tl_zok (lenlens_zero 19 (m_s m1)) /\ i_have (lenlens_zero 19 (m_s m1)) = 19 /\
  exists L, lenlens_zero 19 (m_s m1) = set_i_have (set_i_lens (m_s m1) L) 19.
Proof.
  intros m1 W M X.
  pose proof (mw_md _ W) as MD. pose proof (mw_s _ W) as S.
  destruct (md_lenlens _ MD M) as (Hc & H0 & Hnl & Hnd & LE).
  destruct (sw_lens _ S) as [ZL FL].
  assert (Z0: tl_zok (m_s m1)) by (split; [lia | split; [exact ZL | split; [exact FL | exact LE]]]).
  destruct (tl_zero_ok 19 (m_s m1) Z0 ltac:(simpl; lia)) as (Z1 & H19 & L & EL).
  split; [ | split; [exact Z1 | split; [exact H19 | exists L; exact EL]]].
  destruct Z1 as (_ & ZL1 & FL1 & _). rewrite EL in ZL1, FL1 |- *. simpl in ZL1, FL1.
  destruct S; constructor; simpl; auto; lia.
Qed.

Lemma codes_at0: forall sp, field_compatible t_state [] sp ->
  field_address t_state (DOT _codes) sp = codes_at sp 0.
Proof.
  intros sp H. unfold codes_at. rewrite field_address0_offset by auto with field_compatible.
  rewrite field_address_offset by auto with field_compatible. simpl. reflexivity.
Qed.

Lemma codes_at_offset: forall sp k, field_compatible t_state [] sp -> 0 <= k <= ENOUGH_CODES ->
  offset_val (4 * k) (codes_at sp 0) = codes_at sp k.
Proof.
  intros sp k H Hk. unfold codes_at. unfold ENOUGH_CODES in Hk.
  rewrite !field_address0_offset by auto with field_compatible.
  simpl. rewrite offset_offset_val. f_equal; try lia.
Qed.

Lemma codes_at_off: forall sp k, field_compatible t_state [] sp -> 0 <= k <= ENOUGH_CODES ->
  codes_at sp k = offset_val (1368 + 4 * k) sp.
Proof.
  intros sp k H Hk. unfold codes_at. unfold ENOUGH_CODES in Hk.
  rewrite field_address0_offset by auto with field_compatible. reflexivity.
Qed.

Lemma lens_split: forall sp L, Zlength L = 320 ->
  field_at Ews t_state (DOT _lens) (map (fun z => Vint (Int.repr z)) L) sp =
  data_at Ews (tarray tushort 19) (map (fun z => Vint (Int.repr z)) (sublist 0 19 L)) (field_address t_state (DOT _lens) sp) *
  data_at Ews (tarray tushort 301) (map (fun z => Vint (Int.repr z)) (sublist 19 320 L))
    (field_address0 (tarray tushort 320) (SUB 19) (field_address t_state (DOT _lens) sp)).
Proof.
  intros sp L HL. rewrite field_at_data_at. simpl nested_field_type.
  replace (map (fun z => Vint (Int.repr z)) L) with
    (map (fun z => Vint (Int.repr z)) (sublist 0 19 L) ++ map (fun z => Vint (Int.repr z)) (sublist 19 320 L))
    by (rewrite <- map_app, <- sublist_split, sublist_same; auto; lia).
  apply (split2_data_at_Tarray_app 19 320); rewrite Zlength_map, Zlength_sublist; lia.
Qed.

Lemma work_split: forall sp,
  field_at_ Ews t_state (DOT _work) sp =
  data_at_ Ews (tarray tushort 19) (field_address t_state (DOT _work) sp) *
  data_at_ Ews (tarray tushort 269) (field_address0 (tarray tushort 288) (SUB 19) (field_address t_state (DOT _work) sp)).
Proof.
  intros sp. rewrite field_at__data_at_. simpl nested_field_type. rewrite !data_at__eq.
  assert (D: default_val (tarray tushort 288) = Zrepeat Vundef 19 ++ Zrepeat Vundef 269) by reflexivity.
  assert (D1: default_val (tarray tushort 19) = Zrepeat Vundef 19) by reflexivity.
  assert (D2: default_val (tarray tushort 269) = Zrepeat Vundef 269) by reflexivity.
  rewrite D, D1, D2.
  apply (split2_data_at_Tarray_app 19 288); reflexivity.
Qed.

Definition tables_rest_it (gsh: share) (gv: globals) : mpred :=
  data_at gsh (tarray t_code 512) (map ent lenfix_list) (gv g_lenfix) *
  data_at gsh (tarray t_code 32) (map ent distfix_list) (gv g_distfix) *
  data_at gsh (tarray tushort 19) (map (fun z => Vint (Int.repr z)) order) (gv _order).

Lemma tables_rep_it: forall gsh gv, tables_rep gsh gv = Zlib.proof.inftrees.spec.itables gsh gv * tables_rest_it gsh gv.
Proof. intros. unfold tables_rep, tables_rest_it. apply pred_ext; cancel. Qed.

(* inflate_table's specification is stated in Inftrees.CS *)
Lemma da_cs_us: forall sh n (v: list val) p,
  @data_at Zlib.units.Inflate.CS sh (tarray tushort n) v p = @data_at Zlib.units.Inftrees.CS sh (tarray tushort n) v p.
Proof. intros. symmetry. revert p. apply equal_f. apply (@data_at_change_composite _ _ CCE_inftrees); [apply JMeq_refl | reflexivity]. Qed.

Lemma da__cs_us: forall sh n p,
  @data_at_ Zlib.units.Inflate.CS sh (tarray tushort n) p = @data_at_ Zlib.units.Inftrees.CS sh (tarray tushort n) p.
Proof. intros. symmetry. revert p. apply equal_f. apply (@data_at__change_composite _ _ CCE_inftrees). reflexivity. Qed.

Lemma da_cs_uint: forall sh (v: val) p,
  @data_at Zlib.units.Inflate.CS sh tuint v p = @data_at Zlib.units.Inftrees.CS sh tuint v p.
Proof. intros. symmetry. revert p. apply equal_f. apply (@data_at_change_composite _ _ CCE_inftrees); [apply JMeq_refl | reflexivity]. Qed.

Lemma da_cs_ptr: forall sh (v: val) p,
  @data_at Zlib.units.Inflate.CS sh (tptr t_code) v p = @data_at Zlib.units.Inftrees.CS sh (tptr t_code) v p.
Proof. intros. symmetry. revert p. apply equal_f. apply (@data_at_change_composite _ _ CCE_inftrees); [apply JMeq_refl | reflexivity]. Qed.

Lemma da_cs_codes: forall sh (v: list (val * (val * val))) p,
  @data_at Zlib.units.Inflate.CS sh (tarray t_code 1444) v p = @data_at Zlib.units.Inftrees.CS sh (tarray t_code 1444) v p.
Proof. intros. symmetry. revert p. apply equal_f. apply (@data_at_change_composite _ _ CCE_inftrees); [apply JMeq_refl | reflexivity]. Qed.

(* a final entailment without entailer! (too slow on these 20-item SEPs) *)
(* the codes table across the two compspecs (the reptype conversion, once, in this small lemma) *)
Lemma da_cs_codes2: forall sh (l: list entry) p,
  @data_at Zlib.units.Inflate.CS sh (tarray t_code 1444) (map ent l) p =
  @data_at Zlib.units.Inftrees.CS sh (tarray t_code 1444) (map spec.entry_rep l) p.
Proof.
  intros. symmetry. revert p. apply equal_f.
  apply (@data_at_change_composite _ _ CCE_inftrees); [apply JMeq_refl | reflexivity].
Qed.

(* the typecheck of forward_call's arguments needs no SEP (as in CLDists5.v) *)
Lemma tl_sep_TT: forall (Delta: tycontext) P Q (R: list mpred) (S: environ -> mpred),
  ENTAIL Delta, PROPx P (LOCALx Q (SEPx [TT])) |-- S -> ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- S.
Proof.
  intros Delta P Q R S H. eapply derives_trans; [ | exact H]. apply andp_derives; [apply derives_refl | ].
  unfold PROPx, LOCALx, SEPx. apply andp_derives; [apply derives_refl | ]. apply andp_derives; [apply derives_refl | ].
  intro rho. simpl. rewrite sepcon_emp. apply TT_right.
Qed.

Local Ltac check_typecheck ::=
  try delete_FRZR_from_SEP;
  first [goal_has_evars; idtac |
         try apply local_True_right; apply tl_sep_TT; entailer!;
         match goal with
         | |- typecheck_error (deref_byvalue ?T) => error (Function_arguments_include_a_memory_load_of_type T)
         | |- _ => idtac
         end].

Lemma tl_entail: forall (Delta: tycontext) (P2: list Prop) (L1 L2: list localdef) (S1 S2: list mpred),
  fold_right and True P2 -> (forall q, In q L2 -> In q L1) ->
  fold_right_sepcon S1 |-- fold_right_sepcon S2 ->
  ENTAIL Delta, PROPx [] (LOCALx L1 (SEPx S1)) |-- PROPx P2 (LOCALx L2 (SEPx S2)).
Proof.
  intros Delta P2 L1 L2 S1 S2 HP HL HS.
  apply andp_left2. eapply derives_trans; [apply (LOCALx_shuffle_derives [] L1 L2 S1 HL) | ].
  unfold PROPx, LOCALx, SEPx. simpl. intro rho. normalize.
  apply andp_derives; [apply derives_refl | exact HS].
Qed.

Ltac tl_in := let q := fresh "q" in let Hq := fresh "Hq" in intros q Hq; cbn [In] in Hq |- *;
  repeat (destruct Hq as [<- | Hq]; [repeat (first [left; reflexivity | right]) | ]); contradiction.

(* cancel on opaque atoms (unifying the data_at items directly compares reptypes across compspecs: slow) *)
Ltac tl_cancel :=
  unfold fold_right_sepcon;
  change spec.code_t with t_code; change (Tstruct ___gp_code noattr) with t_code;
  repeat match goal with |- context [@data_at ?cs ?sh ?t ?v ?p] => let x := fresh "D" in set (x := @data_at cs sh t v p) end;
  repeat match goal with |- context [@data_at_ ?cs ?sh ?t ?p] => let x := fresh "D" in set (x := @data_at_ cs sh t p) end;
  repeat match goal with |- context [@field_at ?cs ?sh ?t ?g ?v ?p] => let x := fresh "D" in set (x := @field_at cs sh t g v p) end;
  cancel.

(* the state after the call (both branches of `if (ret)` start from it) *)
Definition ll_rest_stmt : statement :=
  match ll_tail with Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ x))) => x | _ => Sskip end.

Definition ll_mid (F: frame) (m1: mst) (sZ: istate) (Ls: list Z) (old: list entry) (r: model.result)
    : environ -> mpred :=
  PROPx []
  (LOCALx [temp _ret (Vint (Int.repr (it_ret r))); temp _t'61 (offset_val 1368 (f_sp F));
     temp _t'327 (offset_val 1368 (f_sp F)); temp _strm (f_strmp F);
     temp _flush (Vint (Int.repr (f_flush F))); temp _state (f_sp F);
     temp _next (in_ptr (f_ib F) (m_nx (set_m_s m1 sZ)));
     temp _put (out_ptr (f_ob F) (Zlength (m_ow (set_m_s m1 sZ))));
     temp _have (Vint (Int.repr (m_have (set_m_s m1 sZ))));
     temp _left (Vint (Int.repr (m_left (set_m_s m1 sZ))));
     temp _hold (Vlong (Int64.repr (m_hold (set_m_s m1 sZ))));
     temp _bits (Vint (Int.repr (m_bits (set_m_s m1 sZ))));
     temp _in (Vint (Int.repr (m_in (set_m_s m1 sZ))));
     temp _out (Vint (Int.repr (m_out (set_m_s m1 sZ))));
     temp _leave (Vint (Int.repr (m_leave (set_m_s m1 sZ))));
     lvar _here t_code (f_vhere F); lvar _last t_code (f_vlast F);
     lvar _hbuf (tarray tuchar 4) (f_vhbuf F); gvars (f_gv F)]
  (SEPx [spec.itables (f_gsh F) (f_gv F);
     data_at Ews (tarray tushort 19) (map (fun x => Vint (Int.repr x)) Ls)
       (field_address t_state (DOT _lens) (f_sp F));
     data_at_ Ews (tarray tushort 19) (field_address t_state (DOT _work) (f_sp F));
     data_at Ews (tarray t_code 1444) (map ent (it_tab old r)) (offset_val 1368 (f_sp F));
     data_at Ews (tptr t_code) (codes_at (f_sp F) (it_adv r)) (field_address t_state (DOT _next) (f_sp F));
     data_at Ews tuint (Vint (Int.repr (it_bits 7 r))) (field_address t_state (DOT _lenbits) (f_sp F));
     field_at Ews t_state (DOT _mode) (Vint (Int.repr (i_mode sZ))) (f_sp F);
     field_at Ews t_state (DOT _nlen) (Vint (Int.repr (i_nlen sZ))) (f_sp F);
     field_at Ews t_state (DOT _ndist) (Vint (Int.repr (i_ndist sZ))) (f_sp F);
     field_at Ews t_state (DOT _ncode) (Vint (Int.repr (i_ncode sZ))) (f_sp F);
     field_at Ews t_state (DOT _have) (Vint (Int.repr (i_have sZ))) (f_sp F);
     tl_strm F (set_m_s m1 sZ); mem_rest_tl F (set_m_s m1 sZ); locals_rep F;
     data_at Ews (tarray tushort 301) (map (fun z => Vint (Int.repr z)) (sublist 19 320 (i_lens sZ)))
       (field_address0 (tarray tushort 320) [ArraySubsc 19] (field_address t_state (DOT _lens) (f_sp F)));
     field_at Ews t_state (DOT _lencode) (offset_val 1368 (f_sp F)) (f_sp F);
     field_at Ews t_state (DOT _distcode) (offset_val 1368 (f_sp F)) (f_sp F);
     data_at_ Ews (tarray tushort 269)
       (field_address0 (tarray tushort 288) [ArraySubsc 19] (field_address t_state (DOT _work) (f_sp F)));
     tables_rest_it (f_gsh F) (f_gv F)])).

Ltac ll_rest_start :=
  unfold ll_mid; cbv beta iota zeta delta [ll_rest_stmt ll_tail ll_rest1 ll_body case_body inflate_LS find_switch
    f_inflate fn_body ls_drop]; abbreviate_semax.

Section Branches.
Context {Espec: OracleKind} (F: frame) (m0 m1: mst) (sZ: istate) (Ls: list Z) (old: list entry) (r: model.result).
Hypotheses (Hshs: writable_share (f_shs F)) (C3: cover3_stmt) (W1: mwf m1) (M1: m_mode m1 = LENLENS)
  (L1: m_leave m1 = 0) (X1: i_ncode (m_s m1) <= i_have (m_s m1))
  (E0: stepf2 (f_flush F) lenfix_list distfix_list m0 =
       (if negb (it_ret r =? 0)
        then IBrk (set_bad (set_m_ret (set_m_s m1 (tl_s1 sZ)) (it_ret r)) M_cl_set)
        else c_CODELENS (f_flush F) lenfix_list distfix_list (fast lenfix_list distfix_list) (tl_mcl m1)))
  (SZ: swf sZ)
  (ES1: tl_s1 sZ = set_i_lenbits (set_i_next (set_i_codes (tl_s0 sZ) (it_tab old r)) (it_adv r)) (it_bits 7 r))
  (HIDE: r = inflate_table_model CODES Ls 7 old /\ old = sublist 0 ENOUGH_CODES (i_codes sZ) /\
         Ls = sublist 0 19 (i_lens sZ) /\ sZ = lenlens_zero 19 (m_s m1))
  (H: in_ok (f_ib F) (m_inp (set_m_s m1 sZ))) (H0: out_ok (f_ob F) (m_aout (set_m_s m1 sZ)))
  (FC: field_compatible t_state [] (f_sp F)) (RR: -1 <= it_ret r <= 1) (RA: 0 <= it_adv r <= ENOUGH_CODES).

Lemma ll_rest_bad: it_ret r <> 0 ->
  semax Delta_cases5 (ll_mid F m1 sZ Ls old r) ll_rest_stmt
    (overridePost (fall_post5 F m0 CODELENS) (switch_ret_assert (case_post2 F m0))).
Proof using All.
  intros R0. ll_rest_start.
    forward_if; [ | match goal with X: Int.repr (it_ret r) = Int.zero |- _ =>
                      exfalso; apply R0; apply repr_inj_signed; [rep_lia | rep_lia | exact X] end].
    unfold tl_strm, strm_rep.
    remember (f_gv F _zcalloc) as za eqn:Eza. remember (f_gv F _zcfree) as zf eqn:Ezf.
    freeze [0;1;2;3;4;5;7;8;9;10;12;13;14;15;16;17;18] FR3.
    forward. forward. forward.
    unfold switch_ret_assert, case_post2. cbn [RA_break RA_normal].
    Exists (set_bad (set_m_ret (set_m_s m1 (tl_s1 sZ)) (it_ret r)) M_cl_set).
    apply andp_right; [apply prop_right; rewrite E0, (proj2 (Z.eqb_neq _ _) R0); reflexivity | ].
    assert (MR: mem_rest_tl F (set_bad (set_m_ret (set_m_s m1 (tl_s1 sZ)) (it_ret r)) M_cl_set) =
                mem_rest_tl F (set_m_s m1 sZ)) by (rewrite ES1; reflexivity).
    thaw FR3. rewrite loop_state_tl_eq. unfold loop_state_tl, tl_sep, tl_locals, tl_strm, strm_rep. rewrite MR.
    rewrite ES1. unfold tl_s0, m_have, m_left. mnorm_goal. cbn [tref_val msg_val msg_ident].
    cbn [m_inp m_aout set_m_s] in H, H0.
    rewrite (lens_split (f_sp F) (i_lens sZ)) by (destruct (sw_lens _ SZ); auto).
    rewrite work_split, tables_rep_it, (field_at_data_at Ews t_state (DOT _next)),
      (field_at_data_at Ews t_state (DOT _lenbits)), (field_at_data_at Ews t_state (DOT _codes)).
    simpl nested_field_type.
    rewrite codes_at0 by auto.
    rewrite (codes_at_off _ 0) by (auto; unfold ENOUGH_CODES; lia). change (1368 + 4 * 0) with 1368.
    replace (sublist 0 19 (i_lens sZ)) with Ls by exact (proj1 (proj2 (proj2 HIDE))).
    rewrite <- Eza, <- Ezf.
    apply tl_entail; [exact (conj H (conj H0 I)) | tl_in | ].
    change BAD with 16209. tl_cancel.
Qed.

(* the pure facts of the CODELENS branch, apart (Qed speed) *)
Lemma ll_cl_TR: it_ret r = 0 -> tl_r (lenlens_zero 19 (m_s m1)) = 0.
Proof using All.
  intros R0. destruct HIDE as (Er & EOld & ELs & EsZ).
  rewrite tl_r_eq, <- EsZ, <- ELs, <- EOld, <- Er. exact R0.
Qed.

Lemma ll_cl_EM: it_ret r = 0 ->
  tl_mcl m1 = set_mode (upd_s (set_m_ret (set_m_s m1 (tl_s1 sZ)) 0) (fun s => set_i_have s 0)) CODELENS.
Proof using All.
  intros R0. pose proof (ll_cl_TR R0) as TR. destruct HIDE as (_ & _ & _ & EsZ).
  unfold tl_mcl. cbv zeta. rewrite TR, <- EsZ. reflexivity.
Qed.

Lemma ll_cl_step: it_ret r = 0 ->
  stepf2 (f_flush F) lenfix_list distfix_list m0 = stepf2 (f_flush F) lenfix_list distfix_list (tl_mcl m1).
Proof using All.
  intros R0. rewrite E0, R0. change (negb (0 =? 0)) with false. cbv iota. symmetry.
  exact (stepf2_CODELENS (f_flush F) lenfix_list distfix_list (tl_mcl m1) eq_refl).
Qed.

Lemma ll_cl_fall: it_ret r = 0 ->
  stepf2 (f_flush F) lenfix_list distfix_list m0 = stepf2 (f_flush F) lenfix_list distfix_list (tl_mcl m1) /\
  m_mode (tl_mcl m1) = CODELENS /\ m_leave (tl_mcl m1) = 0 /\ mwf3 (tl_mcl m1).
Proof using All.
  intros R0. split; [exact (ll_cl_step R0) | ].
  rewrite (ll_cl_EM R0). split; [reflexivity | split; [exact L1 | ]].
  rewrite <- (ll_cl_EM R0). exact (tl_mwf3_cl m1 C3 W1 M1 X1 (ll_cl_TR R0)).
Qed.

Lemma ll_cl_MR:
  mem_rest_tl F (set_mode (upd_s (set_m_ret (set_m_s m1 (tl_s1 sZ)) 0) (fun s => set_i_have s 0)) CODELENS) =
  mem_rest_tl F (set_m_s m1 sZ).
Proof using All. rewrite ES1. reflexivity. Qed.

Lemma ll_cl_SR:
  tl_strm F (set_mode (upd_s (set_m_ret (set_m_s m1 (tl_s1 sZ)) 0) (fun s => set_i_have s 0)) CODELENS) =
  tl_strm F (set_m_s m1 sZ).
Proof. reflexivity. Qed.

Lemma ll_rest_cl: it_ret r = 0 ->
  semax Delta_cases5 (ll_mid F m1 sZ Ls old r) ll_rest_stmt
    (overridePost (fall_post5 F m0 CODELENS) (switch_ret_assert (case_post2 F m0))).
Proof using All.
  intros R0. ll_rest_start.
  forward_if; [ exfalso; match goal with X: Int.repr (it_ret r) <> Int.zero |- _ => apply X; rewrite R0; reflexivity end | ].
  freeze [0;1;2;3;4;5;7;8;9;11;12;13;14;15;16;17;18] FR3.
  forward. forward.
  unfold switch_ret_assert, case_post2. cbn [RA_normal]. unfold fall_post5.
  Exists (tl_mcl m1). apply andp_right; [apply prop_right; exact (ll_cl_fall R0) | ].
  rewrite (ll_cl_EM R0).
  thaw FR3. rewrite loop_state_tl_eq. unfold loop_state_tl, tl_sep, tl_locals. rewrite ll_cl_MR, ll_cl_SR.
  rewrite ES1. unfold tl_s0, m_have, m_left. mnorm_goal. cbn [tref_val].
  cbn [m_inp m_aout set_m_s] in H, H0.
  rewrite (lens_split (f_sp F) (i_lens sZ)) by (destruct (sw_lens _ SZ); auto).
  rewrite work_split, tables_rep_it, (field_at_data_at Ews t_state (DOT _next)),
    (field_at_data_at Ews t_state (DOT _lenbits)), (field_at_data_at Ews t_state (DOT _codes)).
  simpl nested_field_type.
  rewrite codes_at0 by auto.
  rewrite (codes_at_off _ 0) by (auto; unfold ENOUGH_CODES; lia). change (1368 + 4 * 0) with 1368.
  replace (sublist 0 19 (i_lens sZ)) with Ls by exact (proj1 (proj2 (proj2 HIDE))).
  rewrite R0. apply tl_entail; [exact (conj H (conj H0 I)) | tl_in | ].
  change CODELENS with 16198. tl_cancel.
Qed.

End Branches.

Lemma ll_tail_ok {Espec: OracleKind} (F: frame) (m0 m1: mst) :
  frame_ok5 F -> cover3_stmt -> mwf m1 -> m_mode m1 = LENLENS -> m_leave m1 = 0 ->
  i_ncode (m_s m1) <= i_have (m_s m1) ->
  stepf2 (f_flush F) lenfix_list distfix_list m0 =
    (let sZ := lenlens_zero 19 (m_s m1) in
     let mm := set_m_ret (set_m_s m1 (tl_s1 sZ)) (tl_r sZ) in
     if negb (tl_r sZ =? 0) then IBrk (set_bad mm M_cl_set) else
     c_CODELENS (f_flush F) lenfix_list distfix_list (fast lenfix_list distfix_list) (tl_mcl m1)) ->
  semax Delta_cases5 (loop_state F (set_m_s m1 (lenlens_zero 19 (m_s m1)))) ll_tail
    (overridePost (fall_post5 F m0 CODELENS) (switch_ret_assert (case_post2 F m0))).
Proof.
  intros [HF Hfl] C3 W1 M1 L1 X1 E0.
  destruct (ll_sZ m1 W1 M1 X1) as (SZ & ZZ & H19 & L & EL).
  destruct (tl_table_ok _ C3 SZ ZZ H19) as (ZL19 & IN0 & CAP0 & FO & ZO & EO & ZT & FT & RA & RB & RR & ES1 & OK).
  cbv zeta in E0. rewrite tl_r_eq in E0.
  set (sZ := lenlens_zero 19 (m_s m1)) in *.
  set (Ls := sublist 0 19 (i_lens sZ)) in *. set (old := sublist 0 ENOUGH_CODES (i_codes sZ)) in *.
  set (r := inflate_table_model CODES Ls 7 old) in *.
  (* keep the model terms opaque: lenlens_zero 19 / inflate_table_model unfold explosively *)
  assert (Er: r = inflate_table_model CODES Ls 7 old) by reflexivity. clearbody r.
  assert (EOld: old = sublist 0 ENOUGH_CODES (i_codes sZ)) by reflexivity. clearbody old.
  assert (ELs: Ls = sublist 0 19 (i_lens sZ)) by reflexivity. clearbody Ls.
  assert (EsZ: sZ = lenlens_zero 19 (m_s m1)) by reflexivity. clearbody sZ.
  (* hidden from Floyd's subst (it would substitute and simpl the model terms) *)
  pose proof (conj Er (conj EOld (conj ELs EsZ))) as HIDE. clear Er EOld ELs EsZ.
  pose proof (mw_s _ W1) as S1.
  ll_stmt. rewrite loop_state_tl_eq. unfold loop_state_tl, tl_sep, tl_locals. cbn [m_s set_m_s].
  abbreviate_semax.
  freeze [0;1;2;3;4;12;14;15] FR.
  forward. forward. forward. forward. forward. forward.
  assert_PROP (field_compatible t_state [] (f_sp F)) as FC.
  { entailer!. match goal with H: field_compatible t_state (DOT _codes) _ |- _ => destruct H as (A1 & A2 & A3 & A4 & A5) end.
    repeat split; auto. }
  rewrite (lens_split (f_sp F) (i_lens sZ)) by (destruct (sw_lens _ SZ); auto).
  rewrite work_split.
  rewrite (field_at_data_at Ews t_state (DOT _next)), (field_at_data_at Ews t_state (DOT _lenbits)),
    (field_at_data_at Ews t_state (DOT _codes)).
  simpl nested_field_type.
  rewrite tables_rep_it.
  rewrite codes_at0 by auto. rewrite (codes_at_off _ 0) by (auto; unfold ENOUGH_CODES; lia).
  change (1368 + 4 * 0) with 1368.
  rewrite <- EO. replace (sublist 0 19 (i_lens sZ)) with Ls by apply HIDE.
  Intros.
  destruct HF as (Hshs & Hhsh & Hgsh & Htsh).
  freeze [0;2;4;5;9;11] FR2.
  rewrite (da_cs_us Ews 19), (da__cs_us Ews 19), da_cs_uint, da_cs_ptr, da_cs_codes2.
  forward_call (0, Ls, 7, old, f_gv F, f_gsh F, Ews, Ews, field_address t_state (DOT _lens) (f_sp F),
    field_address t_state (DOT _work) (f_sp F), field_address t_state (DOT _next) (f_sp F),
    offset_val 1368 (f_sp F), field_address t_state (DOT _lenbits) (f_sp F)).
  { apply prop_right. rewrite ZL19.
    rewrite !field_address_offset by auto with field_compatible. reflexivity. }
  { rewrite ZL19, ZO. unfold spec.zs_rep, ENOUGH_CODES. cancel. }
  replace (inflate_table_model 0 Ls 7 old) with r by exact (proj1 HIDE).
  rewrite ZL19, ZO. unfold ENOUGH_CODES. change spec.code_t with t_code.
  rewrite <- (da_cs_us Ews 19), <- (da__cs_us Ews 19), <- da_cs_uint, <- da_cs_ptr, <- da_cs_codes2.
  rewrite offset_offset_val. rewrite <- (codes_at_off (f_sp F) (it_adv r)) by auto.
  unfold spec.zs_rep.
  thaw FR2.
  thaw FR.
  destruct (Z.eq_dec (it_ret r) 0) as [R0 | R0].
  - exact (ll_rest_cl F m0 m1 sZ Ls old r Hshs C3 W1 M1 L1 X1 E0 SZ ES1 HIDE H H0 FC RR RA R0).
  - exact (ll_rest_bad F m0 m1 sZ Ls old r Hshs C3 W1 M1 L1 X1 E0 SZ ES1 HIDE H H0 FC RR RA R0).
Qed.
