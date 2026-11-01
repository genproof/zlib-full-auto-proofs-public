(* case CODELENS: next = codes; lencode = next; lenbits = 9; inflate_table(LENS, ...); BAD on error (CLKit5.cl_tables; model cl_lens_m) *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate.CLKit5.
Require Import Zlib.proof.crc32.Spec.
Require Zlib.proof.inftrees.ref Zlib.proof.inftrees.facts Zlib.proof.inftrees.part_result Zlib.proof.inftrees.part_sorted
  Zlib.proof.inftrees.part_rfc Zlib.proof.inftrees.part_bits Zlib.proof.inftrees.part_subbits
  Zlib.proof.inftrees.part_size.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.
(* the cross-compspecs call of inflate_table: the SEP is converted by hand (cl_da_cs_* below); Floyd's own
   change_compspecs makes forward_call hang (LLTail5.v, Body3_dict) *)
Local Ltac change_compspecs cs ::= idtac.

Lemma cl_fact_result : Zlib.proof.inftrees.facts.fact_result.
Proof.
  exact (Zlib.proof.inftrees.part_result.fact_result_ok Zlib.proof.inftrees.part_sorted.sorted_ok2
           Zlib.proof.inftrees.part_rfc.rfc_ok2 Zlib.proof.inftrees.part_bits.bits_ok2
           Zlib.proof.inftrees.part_subbits.subbits_ok2
           (Zlib.proof.inftrees.part_size.size_ok2 Zlib.proof.inftrees.part_sorted.sorted_ok2
              Zlib.proof.inftrees.part_rfc.rfc_ok2 Zlib.proof.inftrees.part_bits.bits_ok2)).
Qed.

(* the model of the call, with the opaque pieces named *)
Definition cl_sT (s: istate) : istate := set_i_lenbits (set_i_lencode (set_i_next s 0) (TCodes 0)) 9.

Lemma cl_lens_m_eq: forall m1,
  cl_lens_m m1 =
  let r := inflate_table_model LENS (sublist 0 (i_nlen (m_s m1)) (i_lens (m_s m1))) 9
             (sublist 0 ENOUGH_CODES (i_codes (m_s m1))) in
  (it_ret r, set_m_ret (set_m_s m1 (set_i_lenbits (set_i_next (set_i_codes (cl_sT (m_s m1))
      (it_tab (sublist 0 ENOUGH_CODES (i_codes (m_s m1))) r)) (it_adv r)) (it_bits 9 r))) (it_ret r)).
Proof.
  intros. unfold cl_lens_m, call_table, cl_sT.
  cbn [i_next i_nlen i_lens i_codes set_i_lenbits set_i_lencode set_i_next].
  rewrite sublist_nil. reflexivity.
Qed.

Lemma cl_lens_facts: forall m1, mwf m1 -> m_mode m1 = CODELENS ->
  i_nlen (m_s m1) + i_ndist (m_s m1) <= i_have (m_s m1) ->
  let L := sublist 0 (i_nlen (m_s m1)) (i_lens (m_s m1)) in
  let old := sublist 0 ENOUGH_CODES (i_codes (m_s m1)) in
  let r := inflate_table_model LENS L 9 old in
  Zlength L = i_nlen (m_s m1) /\ inputs_ok LENS L 9 /\ cap_ok LENS L 9 (Zlength old) /\ Forall entry_ok old /\
  Zlength old = ENOUGH_CODES /\ old = i_codes (m_s m1) /\ 0 <= it_adv r <= ENOUGH_CODES /\ -1 <= it_ret r <= 1 /\
  257 <= i_nlen (m_s m1) <= 286.
Proof.
  intros m1 W M X. cbv zeta.
  pose proof (mw_s _ W) as S. pose proof (mw_md _ W) as MD.
  destruct (md_codelens _ MD M) as (HH & HN & HD & _ & _ & LE).
  destruct (sw_lens _ S) as [ZL FL]. destruct (sw_codes _ S) as [ZC FC].
  set (L := sublist 0 (i_nlen (m_s m1)) (i_lens (m_s m1))).
  set (old := sublist 0 ENOUGH_CODES (i_codes (m_s m1))).
  assert (EO: old = i_codes (m_s m1)) by (unfold old; rewrite sublist_same; auto).
  assert (ZO: Zlength old = ENOUGH_CODES) by (rewrite EO; auto).
  assert (FO: Forall entry_ok old) by (rewrite EO; auto).
  assert (ZLL: Zlength L = i_nlen (m_s m1)) by (unfold L; rewrite Zlength_sublist; lia).
  assert (IN: inputs_ok LENS L 9).
  { unfold inputs_ok. rewrite ZLL. split; [unfold LENS; lia | ].
    split; [unfold max_codes, LENS, CODES; simpl; lia | ]. split; [ | lia].
    rewrite Forall_forall. intros x Hx. apply In_Znth in Hx. destruct Hx as (i & Hi & <-).
    rewrite ZLL in Hi. unfold L. rewrite Znth_sublist by lia. rewrite Z.add_0_r.
    rewrite Forall_forall in FL. split.
    - apply (FL (Znth i (i_lens (m_s m1)))). apply Znth_In. lia.
    - unfold MAXBITS. apply LE. lia. }
  assert (CAP: cap_ok LENS L 9 (Zlength old)).
  { rewrite ZO. unfold cap_ok, LENS, CODES, DISTS, ENOUGH_LENS, ENOUGH_CODES. split; [intros; lia | ].
    split; intros; lia. }
  pose proof (cl_fact_result LENS L 9 old IN CAP FO) as FR.
  destruct (Zlib.proof.inftrees.ref.expected_call LENS L 9) as [[want root] size].
  do 6 (split; [assumption | ]).
  destruct (inflate_table_model LENS L 9 old) as [ | t | root' used t]; cbn [it_ret it_adv].
  - unfold ENOUGH_CODES; lia.
  - unfold ENOUGH_CODES; lia.
  - destruct FR as (_ & _ & _ & U1 & _). rewrite ZO in U1. lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the memory of the call (LLTail5.v's, for n code lengths)                                       *)

Lemma cl_codes_at_off: forall sp k, field_compatible t_state [] sp -> 0 <= k <= ENOUGH_CODES ->
  codes_at sp k = offset_val (1368 + 4 * k) sp.
Proof.
  intros sp k H Hk. unfold codes_at. unfold ENOUGH_CODES in Hk.
  rewrite field_address0_offset by auto with field_compatible. reflexivity.
Qed.

Lemma cl_lens_split: forall sp L n, Zlength L = 320 -> 0 <= n <= 320 ->
  field_at Ews t_state (DOT _lens) (map (fun z => Vint (Int.repr z)) L) sp =
  data_at Ews (tarray tushort n) (map (fun z => Vint (Int.repr z)) (sublist 0 n L)) (field_address t_state (DOT _lens) sp) *
  data_at Ews (tarray tushort (320 - n)) (map (fun z => Vint (Int.repr z)) (sublist n 320 L))
    (field_address0 (tarray tushort 320) (SUB n) (field_address t_state (DOT _lens) sp)).
Proof.
  intros sp L n HL Hn. rewrite field_at_data_at. simpl nested_field_type.
  replace (map (fun z => Vint (Int.repr z)) L) with
    (map (fun z => Vint (Int.repr z)) (sublist 0 n L) ++ map (fun z => Vint (Int.repr z)) (sublist n 320 L))
    by (rewrite <- map_app, <- sublist_split, sublist_same; auto; lia).
  apply (split2_data_at_Tarray_app n 320); rewrite Zlength_map, Zlength_sublist; lia.
Qed.

Lemma cl_work_split: forall sp n, 0 <= n <= 288 ->
  field_at_ Ews t_state (DOT _work) sp =
  data_at_ Ews (tarray tushort n) (field_address t_state (DOT _work) sp) *
  data_at_ Ews (tarray tushort (288 - n)) (field_address0 (tarray tushort 288) (SUB n) (field_address t_state (DOT _work) sp)).
Proof.
  intros sp n Hn. rewrite field_at__data_at_. simpl nested_field_type. rewrite !data_at__eq.
  assert (D: default_val (tarray tushort 288) = Zrepeat Vundef n ++ Zrepeat Vundef (288 - n)).
  { change (default_val (tarray tushort 288)) with (Zrepeat Vundef 288). rewrite Zrepeat_app by lia. f_equal. lia. }
  assert (D1: default_val (tarray tushort n) = Zrepeat Vundef n) by reflexivity.
  assert (D2: default_val (tarray tushort (288 - n)) = Zrepeat Vundef (288 - n)) by reflexivity.
  rewrite D, D1, D2.
  apply (split2_data_at_Tarray_app n 288); rewrite Zlength_Zrepeat; lia.
Qed.

Definition cl_tables_rest (gsh: share) (gv: globals) : mpred :=
  data_at gsh (tarray t_code 512) (map ent lenfix_list) (gv g_lenfix) *
  data_at gsh (tarray t_code 32) (map ent distfix_list) (gv g_distfix) *
  data_at gsh (tarray tushort 19) (map (fun z => Vint (Int.repr z)) order) (gv _order).

Lemma cl_tables_rep_it: forall gsh gv,
  tables_rep gsh gv = Zlib.proof.inftrees.spec.itables gsh gv * cl_tables_rest gsh gv.
Proof. intros. unfold tables_rep, cl_tables_rest. apply pred_ext; cancel. Qed.

(* inflate_table's specification is stated in Inftrees.CS *)
Lemma cl_da_cs_us: forall sh n (v: list val) p,
  @data_at Zlib.units.Inflate.CS sh (tarray tushort n) v p = @data_at Zlib.units.Inftrees.CS sh (tarray tushort n) v p.
Proof. intros. symmetry. revert p. apply equal_f. apply (@data_at_change_composite _ _ CCE_inftrees); [apply JMeq_refl | reflexivity]. Qed.

Lemma cl_da__cs_us: forall sh n p,
  @data_at_ Zlib.units.Inflate.CS sh (tarray tushort n) p = @data_at_ Zlib.units.Inftrees.CS sh (tarray tushort n) p.
Proof. intros. symmetry. revert p. apply equal_f. apply (@data_at__change_composite _ _ CCE_inftrees). reflexivity. Qed.

Lemma cl_da_cs_uint: forall sh (v: val) p,
  @data_at Zlib.units.Inflate.CS sh tuint v p = @data_at Zlib.units.Inftrees.CS sh tuint v p.
Proof. intros. symmetry. revert p. apply equal_f. apply (@data_at_change_composite _ _ CCE_inftrees); [apply JMeq_refl | reflexivity]. Qed.

Lemma cl_da_cs_ptr: forall sh (v: val) p,
  @data_at Zlib.units.Inflate.CS sh (tptr t_code) v p = @data_at Zlib.units.Inftrees.CS sh (tptr t_code) v p.
Proof. intros. symmetry. revert p. apply equal_f. apply (@data_at_change_composite _ _ CCE_inftrees); [apply JMeq_refl | reflexivity]. Qed.

Lemma cl_da_cs_codes: forall sh (v: list (val * (val * val))) p,
  @data_at Zlib.units.Inflate.CS sh (tarray t_code 1444) v p = @data_at Zlib.units.Inftrees.CS sh (tarray t_code 1444) v p.
Proof. intros. symmetry. revert p. apply equal_f. apply (@data_at_change_composite _ _ CCE_inftrees); [apply JMeq_refl | reflexivity]. Qed.

Lemma cl_fold_next: forall sp v,
  data_at Ews (tptr t_code) v (field_address t_state (DOT _next) sp) = field_at Ews t_state (DOT _next) v sp.
Proof. intros. rewrite field_at_data_at. reflexivity. Qed.

Lemma cl_fold_lenbits: forall sp v,
  data_at Ews tuint v (field_address t_state (DOT _lenbits) sp) = field_at Ews t_state (DOT _lenbits) v sp.
Proof. intros. rewrite field_at_data_at. reflexivity. Qed.

Lemma cl_fold_codes: forall sp v, field_compatible t_state [] sp ->
  data_at Ews (tarray t_code 1444) v (offset_val 1368 sp) = field_at Ews t_state (DOT _codes) v sp.
Proof.
  intros. rewrite field_at_data_at. rewrite field_address_offset by auto with field_compatible. reflexivity.
Qed.

(* the statement cut in two: the stores and the call (cl_lens_front), the test of ret and DISTS (cl_lens_tail) *)
Definition cl_ta : statement := match cl_tables with Ssequence a _ => a | _ => Sskip end.
Definition cl_tb : statement := match cl_tables with Ssequence _ (Ssequence b _) => b | _ => Sskip end.
Definition cl_tc : statement := match cl_tables with Ssequence _ (Ssequence _ (Ssequence c _)) => c | _ => Sskip end.
Definition cl_td : statement :=
  match cl_tables with Ssequence _ (Ssequence _ (Ssequence _ (Ssequence d _))) => d | _ => Sskip end.
Definition cl_te : statement :=
  match cl_tables with Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence e _)))) => e | _ => Sskip end.

Lemma cl_tables_eq: cl_tables = Ssequence cl_ta (Ssequence cl_tb (Ssequence cl_tc (Ssequence cl_td (Ssequence cl_te cl_dists)))).
Proof. reflexivity. Qed.

Ltac cl_t_eval x :=
  let y := eval cbv beta iota zeta delta [cl_ta cl_tb cl_tc cl_td cl_te cl_body cl_tail cl_tables
    case_body inflate_LS find_switch f_inflate fn_body ls_drop] in x in exact y.
Definition cl_ta_c : statement := ltac:(cl_t_eval cl_ta).
Definition cl_tb_c : statement := ltac:(cl_t_eval cl_tb).
Definition cl_tc_c : statement := ltac:(cl_t_eval cl_tc).
Definition cl_td_c : statement := ltac:(cl_t_eval cl_td).
Definition cl_te_c : statement := ltac:(cl_t_eval cl_te).
Lemma cl_ta_eq: cl_ta = cl_ta_c. Proof. reflexivity. Qed.
Lemma cl_tb_eq: cl_tb = cl_tb_c. Proof. reflexivity. Qed.
Lemma cl_tc_eq: cl_tc = cl_tc_c. Proof. reflexivity. Qed.
Lemma cl_td_eq: cl_td = cl_td_c. Proof. reflexivity. Qed.
Lemma cl_te_eq: cl_te = cl_te_c. Proof. reflexivity. Qed.

(* the machine after the LENS table *)
Definition cl_r (m1: mst) : model.result :=
  inflate_table_model LENS (sublist 0 (i_nlen (m_s m1)) (i_lens (m_s m1))) 9 (sublist 0 ENOUGH_CODES (i_codes (m_s m1))).
Definition cl_mA (m1: mst) : mst :=
  set_m_ret (set_m_s m1 (set_i_lenbits (set_i_next (set_i_codes (cl_sT (m_s m1))
      (it_tab (sublist 0 ENOUGH_CODES (i_codes (m_s m1))) (cl_r m1))) (it_adv (cl_r m1))) (it_bits 9 (cl_r m1))))
    (it_ret (cl_r m1)).

Lemma cl_lens_m_eq2: forall m1, cl_lens_m m1 = (it_ret (cl_r m1), cl_mA m1).
Proof. intros. rewrite cl_lens_m_eq. reflexivity. Qed.

Lemma cl_lens_front_core {Espec: OracleKind} (F: frame) (m1: mst) (hv: reptype t_code) (rest: statement) (R: ret_assert)
    (L: list Z) (old: list entry) (r: model.result):
  frame_ok5 F -> mwf m1 ->
  Zlength L = i_nlen (m_s m1) -> Zlength old = ENOUGH_CODES -> old = i_codes (m_s m1) ->
  0 <= it_adv r <= ENOUGH_CODES -> 257 <= i_nlen (m_s m1) <= 286 ->
  inputs_ok LENS L 9 -> cap_ok LENS L 9 (Zlength old) -> Forall entry_ok old ->
  r = inflate_table_model LENS L 9 old /\ old = sublist 0 ENOUGH_CODES (i_codes (m_s m1)) /\
    L = sublist 0 (i_nlen (m_s m1)) (i_lens (m_s m1)) ->
  semax Delta_cases5 (loop_state_h F (set_m_ret (set_m_s m1 (set_i_lenbits (set_i_next (set_i_codes (cl_sT (m_s m1))
      (it_tab old r)) (it_adv r)) (it_bits 9 r))) (it_ret r)) hv) rest R ->
  semax Delta_cases5 (loop_state_h F m1 hv) (Ssequence cl_ta (Ssequence cl_tb (Ssequence cl_tc (Ssequence cl_td rest)))) R.
Proof.
  intros [HF Hfl] W1 ZL ZO EO RA HN IN CAP FO HIDE HR.
  pose proof (mw_s _ W1) as S1.
  rewrite cl_ta_eq, cl_tb_eq, cl_tc_eq, cl_td_eq. unfold cl_ta_c, cl_tb_c, cl_tc_c, cl_td_c.
  rewrite loop_state_h_cl. unfold loop_state_clh, cl_sep.
  abbreviate_semax.
  unfold loop_locals. freeze [0;2;3;7;9;12;14;15;16;17] FR.
  forward. forward. forward.
  assert_PROP (field_compatible t_state [] (f_sp F)) as FC.
  { entailer!. match goal with H: field_compatible t_state (DOT _codes) _ |- _ => destruct H as (A1 & A2 & A3 & A4 & A5) end.
    repeat split; auto. }
  forward. forward.
  destruct (sw_lens _ S1) as [ZL320 _].
  rewrite (cl_lens_split (f_sp F) (i_lens (m_s m1)) (i_nlen (m_s m1))) by (auto; lia).
  rewrite (cl_work_split (f_sp F) (i_nlen (m_s m1))) by lia.
  rewrite (field_at_data_at Ews t_state (DOT _next)), (field_at_data_at Ews t_state (DOT _lenbits)),
    (field_at_data_at Ews t_state (DOT _codes)).
  simpl nested_field_type.
  rewrite cl_tables_rep_it.
  rewrite <- EO. replace (sublist 0 (i_nlen (m_s m1)) (i_lens (m_s m1))) with L by apply HIDE.
  assert (EC: field_address t_state (DOT _codes) (f_sp F) = offset_val 1368 (f_sp F))
    by (rewrite field_address_offset by auto with field_compatible; reflexivity).
  rewrite EC.
  Intros.
  destruct HF as (Hshs & Hhsh & Hgsh & Htsh).
  freeze [0;1;3;5;9;11] FR2.
  rewrite (cl_da_cs_us Ews (i_nlen (m_s m1))), (cl_da__cs_us Ews (i_nlen (m_s m1))), cl_da_cs_uint, cl_da_cs_ptr,
    cl_da_cs_codes.
  change (map ent old) with (map Zlib.proof.inftrees.spec.entry_rep old).
  forward_call (1, L, 9, old, f_gv F, f_gsh F, Ews, Ews, field_address t_state (DOT _lens) (f_sp F),
    field_address t_state (DOT _work) (f_sp F), field_address t_state (DOT _next) (f_sp F),
    offset_val 1368 (f_sp F), field_address t_state (DOT _lenbits) (f_sp F)).
  { apply prop_right. rewrite ZL. rewrite !field_address_offset by auto with field_compatible. reflexivity. }
  { rewrite ZL, ZO. unfold spec.zs_rep, ENOUGH_CODES. cancel. }
  change 1 with LENS. replace (inflate_table_model LENS L 9 old) with r by exact (proj1 HIDE).
  change (map Zlib.proof.inftrees.spec.entry_rep (it_tab old r)) with (map ent (it_tab old r)).
  rewrite ZL, ZO. unfold ENOUGH_CODES. change spec.code_t with t_code.
  rewrite <- (cl_da_cs_us Ews (i_nlen (m_s m1))), <- (cl_da__cs_us Ews (i_nlen (m_s m1))), <- cl_da_cs_uint,
    <- cl_da_cs_ptr, <- cl_da_cs_codes.
  rewrite offset_offset_val. rewrite <- (cl_codes_at_off (f_sp F) (it_adv r)) by auto.
  unfold spec.zs_rep.
  thaw FR2.
  forward.
  rewrite (proj2 (proj2 HIDE)). gather_SEP 1 8.
  rewrite <- (cl_lens_split (f_sp F) (i_lens (m_s m1)) (i_nlen (m_s m1))) by (auto; lia).
  gather_SEP 2 9. rewrite <- (cl_work_split (f_sp F) (i_nlen (m_s m1))) by lia.
  rewrite cl_fold_next, cl_fold_lenbits, cl_fold_codes by auto.
  eapply semax_pre; [ | exact HR ].
  rewrite loop_state_h_cl; unfold loop_state_clh, cl_sep, loop_locals.
  thaw FR.
  assert (MR: mem_rest_cl F (set_m_ret (set_m_s m1 (set_i_lenbits (set_i_next (set_i_codes (cl_sT (m_s m1)) (it_tab old r))
              (it_adv r)) (it_bits 9 r))) (it_ret r)) = mem_rest_cl F m1) by reflexivity.
  assert (SR: cl_strm F (set_m_ret (set_m_s m1 (set_i_lenbits (set_i_next (set_i_codes (cl_sT (m_s m1)) (it_tab old r))
              (it_adv r)) (it_bits 9 r))) (it_ret r)) = cl_strm F m1) by reflexivity.
  rewrite MR, SR.
  unfold cl_sT, m_have, m_left; mnorm_goal.
  change (tref_val (f_gv F) (f_sp F) (TCodes 0)) with (codes_at (f_sp F) 0).
  rewrite (cl_codes_at_off (f_sp F) 0) by (auto; unfold ENOUGH_CODES; lia); change (1368 + 4 * 0) with 1368.
  rewrite cl_tables_rep_it.
  entailer!.
Qed.

Lemma cl_lens_front {Espec: OracleKind} (F: frame) (m1: mst) (hv: reptype t_code) (rest: statement) (R: ret_assert):
  frame_ok5 F -> mwf m1 -> m_mode m1 = CODELENS -> i_nlen (m_s m1) + i_ndist (m_s m1) <= i_have (m_s m1) ->
  semax Delta_cases5 (loop_state_h F (cl_mA m1) hv) rest R ->
  semax Delta_cases5 (loop_state_h F m1 hv) (Ssequence cl_ta (Ssequence cl_tb (Ssequence cl_tc (Ssequence cl_td rest)))) R.
Proof.
  intros HF W1 M1 X1 HR.
  destruct (cl_lens_facts m1 W1 M1 X1) as (ZL & IN & CAP & FO & ZO & EO & RA & RR & HN).
  exact (cl_lens_front_core F m1 hv rest R _ _ _ HF W1 ZL ZO EO RA HN IN CAP FO (conj eq_refl (conj eq_refl eq_refl)) HR).
Qed.

Lemma cl_lens_tail_core {Espec: OracleKind} (F: frame) (m0 mA: mst) (hv: reptype t_code) (ret: Z):
  frame_ok5 F -> -1 <= ret <= 1 -> m_ret mA = ret ->
  stepf2 (f_flush F) lenfix_list distfix_list m0 =
    (if negb (ret =? 0) then IBrk (set_bad mA M_ll_set) else cl_dists_out (f_flush F) mA) ->
  (forall (mA0: mst) (hv': reptype t_code), (ret, mA) = (0, mA0) ->
     semax Delta_cases5 (loop_state_h F mA0 hv') cl_dists
       (overridePost (fall_post5 F m0 LEN_) (switch_ret_assert (case_post2 F m0)))) ->
  semax Delta_cases5 (loop_state_h F mA hv) (Ssequence cl_te cl_dists)
    (overridePost (fall_post5 F m0 LEN_) (switch_ret_assert (case_post2 F m0))).
Proof.
  intros [HF Hfl] RR RT E0 HD. destruct HF as (Hshs & Hhsh & Hgsh & Htsh).
  rewrite cl_te_eq. unfold cl_te_c.
  rewrite loop_state_h_cl. unfold loop_state_clh, cl_sep.
  abbreviate_semax.
  destruct (Z.eq_dec ret 0) as [R0 | R0].
  2:{ (* inflate_table failed: BAD *)
    unfold loop_locals. rewrite RT.
    freeze [1;2;3;4;5;6;7;8;9;10;11;13;15;16;17] FR.
    forward_if; [ | match goal with X: Int.repr ret = Int.zero |- _ =>
                      exfalso; apply R0; apply repr_inj_signed; [rep_lia | rep_lia | exact X] end].
    unfold cl_strm, strm_rep.
    remember (f_gv F _zcalloc) as za eqn:Eza. remember (f_gv F _zcfree) as zf eqn:Ezf.
    forward. forward. forward.
    cbn [RA_break switch_ret_assert case_post2].
    Exists (set_bad mA M_ll_set).
    apply andp_right.
    { apply prop_right. rewrite E0. destruct (Z.eqb_spec ret 0); [contradiction | reflexivity]. }
    assert (MR2: mem_rest_cl F (set_bad mA M_ll_set) = mem_rest_cl F mA) by reflexivity.
    rewrite loop_state_h_def, loop_state_h_cl. unfold loop_state_clh, cl_sep, loop_locals, cl_strm, strm_rep.
    rewrite MR2. thaw FR.
    unfold set_bad, m_have, m_left. mnorm_goal. cbn [msg_val msg_ident]. rewrite <- Eza, <- Ezf.
    fold (data_at_ Tsh t_code (f_vhere F)).
    entailer!. }
  forward_if; [ exfalso; apply H; rewrite RT, R0; reflexivity | ].
  eapply semax_pre; [ | exact (HD mA hv ltac:(rewrite R0; reflexivity)) ].
  rewrite loop_state_h_cl. unfold loop_state_clh.
  apply andp_left2. unfold PROPx. simpl. intro rho. apply andp_right; [apply prop_right; auto | apply andp_left2, derives_refl].
Qed.

Lemma cl_lens_tail {Espec: OracleKind} (F: frame) (m0 m1: mst) (hv: reptype t_code):
  frame_ok5 F -> mwf m1 -> m_mode m1 = CODELENS -> i_nlen (m_s m1) + i_ndist (m_s m1) <= i_have (m_s m1) ->
  stepf2 (f_flush F) lenfix_list distfix_list m0 = cl_lens_out (f_flush F) m1 ->
  (forall (mA: mst) (hv': reptype t_code), cl_lens_m m1 = (0, mA) ->
     semax Delta_cases5 (loop_state_h F mA hv') cl_dists
       (overridePost (fall_post5 F m0 LEN_) (switch_ret_assert (case_post2 F m0)))) ->
  semax Delta_cases5 (loop_state_h F (cl_mA m1) hv) (Ssequence cl_te cl_dists)
    (overridePost (fall_post5 F m0 LEN_) (switch_ret_assert (case_post2 F m0))).
Proof.
  intros HF W1 M1 X1 E0 HD.
  destruct (cl_lens_facts m1 W1 M1 X1) as (_ & _ & _ & _ & _ & _ & _ & RR & _).
  unfold cl_lens_out in E0. rewrite cl_lens_m_eq2 in E0, HD.
  exact (cl_lens_tail_core F m0 (cl_mA m1) hv (it_ret (cl_r m1)) HF RR eq_refl E0 HD).
Qed.

Lemma cl_lens_ok : cl_lens_stmt.
Proof.
  intros Espec F m0 m1 hv HF W1 M1 L1 X1 E0 HD.
  rewrite cl_tables_eq.
  apply cl_lens_front; auto.
  apply cl_lens_tail; auto.
Qed.
