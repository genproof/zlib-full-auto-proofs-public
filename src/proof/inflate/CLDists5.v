(* case CODELENS: distcode = next; distbits = 6; inflate_table(DISTS, ...); BAD on error; mode = LEN_; Z_TREES (CLKit5.cl_dists; model cl_dists_m, cl_dists_out) *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate.CLKit5.
Require Import Zlib.proof.crc32.Spec.
Require Zlib.proof.inflate.Steps2.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* the cross-compspecs call of inflate_table: the SEP is converted by hand (cld_da_* below); Floyd's own
   change_compspecs makes forward_call hang (LLTail5.v, Body3_dict) *)
Local Ltac change_compspecs cs ::= idtac.

Lemma cld_codes_at_off: forall sp k, field_compatible t_state [] sp -> 0 <= k <= ENOUGH_CODES ->
  codes_at sp k = offset_val (1368 + 4 * k) sp.
Proof.
  intros sp k H Hk. unfold codes_at. unfold ENOUGH_CODES in Hk.
  rewrite field_address0_offset by auto with field_compatible. reflexivity.
Qed.

Lemma cld_isptr_codes_at: forall sp k, field_compatible t_state [] sp -> 0 <= k <= ENOUGH_CODES ->
  isptr (codes_at sp k).
Proof.
  intros sp k H Hk. rewrite cld_codes_at_off by auto. destruct H as [P _]. destruct sp; try contradiction. exact I.
Qed.

Definition cld_tabs (gsh: share) (gv: globals) : mpred :=
  data_at gsh (tarray t_code 512) (map ent lenfix_list) (gv g_lenfix) *
  data_at gsh (tarray t_code 32) (map ent distfix_list) (gv g_distfix) *
  data_at gsh (tarray tushort 19) (map (fun z => Vint (Int.repr z)) order) (gv _order).

Lemma cld_tables_rep: forall gsh gv, tables_rep gsh gv = Zlib.proof.inftrees.spec.itables gsh gv * cld_tabs gsh gv.
Proof. intros. unfold tables_rep, cld_tabs. apply pred_ext; cancel. Qed.

(* inflate_table's specification is stated in Inftrees.CS *)
Lemma cld_da_us: forall sh n (v: list val) p,
  @data_at Zlib.units.Inflate.CS sh (tarray tushort n) v p = @data_at Zlib.units.Inftrees.CS sh (tarray tushort n) v p.
Proof. intros. symmetry. revert p. apply equal_f. apply (@data_at_change_composite _ _ CCE_inftrees); [apply JMeq_refl | reflexivity]. Qed.

Lemma cld_da__us: forall sh n p,
  @data_at_ Zlib.units.Inflate.CS sh (tarray tushort n) p = @data_at_ Zlib.units.Inftrees.CS sh (tarray tushort n) p.
Proof. intros. symmetry. revert p. apply equal_f. apply (@data_at__change_composite _ _ CCE_inftrees). reflexivity. Qed.

Lemma cld_da_uint: forall sh (v: val) p,
  @data_at Zlib.units.Inflate.CS sh tuint v p = @data_at Zlib.units.Inftrees.CS sh tuint v p.
Proof. intros. symmetry. revert p. apply equal_f. apply (@data_at_change_composite _ _ CCE_inftrees); [apply JMeq_refl | reflexivity]. Qed.

Lemma cld_da_ptr: forall sh (v: val) p,
  @data_at Zlib.units.Inflate.CS sh (tptr t_code) v p = @data_at Zlib.units.Inftrees.CS sh (tptr t_code) v p.
Proof. intros. symmetry. revert p. apply equal_f. apply (@data_at_change_composite _ _ CCE_inftrees); [apply JMeq_refl | reflexivity]. Qed.

Lemma cld_da_codes: forall sh n (v: list (val * (val * val))) p,
  @data_at Zlib.units.Inflate.CS sh (tarray t_code n) v p = @data_at Zlib.units.Inftrees.CS sh (tarray t_code n) v p.
Proof. intros. symmetry. revert p. apply equal_f. apply (@data_at_change_composite _ _ CCE_inftrees); [apply JMeq_refl | reflexivity]. Qed.

Lemma cld_codes_split: forall sp k C, field_compatible t_state [] sp -> 0 <= k <= ENOUGH_CODES ->
  Zlength C = ENOUGH_CODES ->
  field_at Ews t_state (DOT _codes) (map ent C) sp =
  data_at Ews (tarray t_code k) (map ent (sublist 0 k C)) (field_address t_state (DOT _codes) sp) *
  data_at Ews (tarray t_code (ENOUGH_CODES - k)) (map ent (sublist k ENOUGH_CODES C)) (codes_at sp k).
Proof.
  intros sp k C FC Hk HC. unfold ENOUGH_CODES in *. rewrite field_at_data_at. simpl nested_field_type.
  replace (map ent C) with (map ent (sublist 0 k C) ++ map ent (sublist k 1444 C))
    by (rewrite <- map_app, <- sublist_split, sublist_same; auto; lia).
  rewrite (@split2_data_at_Tarray_app Zlib.units.Inflate.CS k 1444 Ews t_code (map ent (sublist 0 k C))
    (map ent (sublist k 1444 C))) by (rewrite Zlength_map, Zlength_sublist; lia).
  f_equal. f_equal. unfold codes_at.
  symmetry. exact (@field_address0_app Zlib.units.Inflate.CS t_state (DOT _codes) (SUB k) sp ltac:(discriminate)).
Qed.

Lemma cld_fa0_lens: forall sp a, field_compatible t_state [] sp -> 0 <= a <= 320 ->
  field_address0 (tarray tushort 320) (SUB a) (field_address t_state (DOT _lens) sp) =
  offset_val (2 * a) (field_address t_state (DOT _lens) sp).
Proof.
  intros sp a FC Ha.
  transitivity (field_address0 t_state [ArraySubsc a; StructField _lens] sp).
  { symmetry. exact (@field_address0_app Zlib.units.Inflate.CS t_state (DOT _lens) (SUB a) sp ltac:(discriminate)). }
  rewrite field_address0_offset by auto with field_compatible.
  rewrite field_address_offset by auto with field_compatible.
  simpl. rewrite offset_offset_val. f_equal; lia.
Qed.

Lemma cld_fa0_work: forall sp a, field_compatible t_state [] sp -> 0 <= a <= 288 ->
  field_address0 (tarray tushort 288) (SUB a) (field_address t_state (DOT _work) sp) =
  offset_val (2 * a) (field_address t_state (DOT _work) sp).
Proof.
  intros sp a FC Ha.
  transitivity (field_address0 t_state [ArraySubsc a; StructField _work] sp).
  { symmetry. exact (@field_address0_app Zlib.units.Inflate.CS t_state (DOT _work) (SUB a) sp ltac:(discriminate)). }
  rewrite field_address0_offset by auto with field_compatible.
  rewrite field_address_offset by auto with field_compatible.
  simpl. rewrite offset_offset_val. f_equal; lia.
Qed.

Lemma cld_lens_split: forall sp L a b, field_compatible t_state [] sp -> Zlength L = 320 ->
  0 <= a -> 0 <= b -> a + b <= 320 ->
  field_at Ews t_state (DOT _lens) (map (fun z => Vint (Int.repr z)) L) sp =
  data_at Ews (tarray tushort a) (map (fun z => Vint (Int.repr z)) (sublist 0 a L))
    (field_address t_state (DOT _lens) sp) *
  data_at Ews (tarray tushort b) (map (fun z => Vint (Int.repr z)) (sublist a (a + b) L))
    (offset_val (2 * a) (field_address t_state (DOT _lens) sp)) *
  data_at Ews (tarray tushort (320 - (a + b))) (map (fun z => Vint (Int.repr z)) (sublist (a + b) 320 L))
    (offset_val (2 * (a + b)) (field_address t_state (DOT _lens) sp)).
Proof.
  intros sp L a b FC HL Ha Hb Hab. rewrite field_at_data_at. simpl nested_field_type.
  rewrite (@split3_data_at_Tarray Zlib.units.Inflate.CS Ews tushort 320 a (a + b) (map (fun z => Vint (Int.repr z)) L)
    (map (fun z => Vint (Int.repr z)) L) (map (fun z => Vint (Int.repr z)) (sublist 0 a L))
    (map (fun z => Vint (Int.repr z)) (sublist a (a + b) L)) (map (fun z => Vint (Int.repr z)) (sublist (a + b) 320 L)));
    [ | hnf; simpl; auto | lia | rewrite Zlength_map; lia | rewrite sublist_same; auto; rewrite Zlength_map; lia
      | rewrite sublist_map; reflexivity | rewrite sublist_map; reflexivity | rewrite sublist_map; reflexivity].
  replace (a + b - a) with b by lia.
  rewrite !cld_fa0_lens by (auto; lia). reflexivity.
Qed.

Lemma cld_work_split: forall sp k, field_compatible t_state [] sp -> 0 <= k <= 288 ->
  field_at_ Ews t_state (DOT _work) sp =
  data_at_ Ews (tarray tushort k) (field_address t_state (DOT _work) sp) *
  data_at_ Ews (tarray tushort (288 - k)) (offset_val (2 * k) (field_address t_state (DOT _work) sp)).
Proof.
  intros sp k FC Hk. rewrite field_at__data_at_. simpl nested_field_type. rewrite !data_at__eq.
  assert (D: default_val (tarray tushort 288) = Zrepeat Vundef k ++ Zrepeat Vundef (288 - k))
    by (rewrite Zrepeat_app by lia; replace (k + (288 - k)) with 288 by lia; reflexivity).
  assert (D1: default_val (tarray tushort k) = Zrepeat Vundef k) by reflexivity.
  assert (D2: default_val (tarray tushort (288 - k)) = Zrepeat Vundef (288 - k)) by reflexivity.
  rewrite D, D1, D2.
  rewrite (split2_data_at_Tarray_app k 288) by (rewrite Zlength_Zrepeat; lia).
  rewrite cld_fa0_work by auto. reflexivity.
Qed.

(* the machine after the DISTS table *)
Definition cld_mB (mA: mst) (r: model.result) : mst :=
  let s := m_s mA in
  let old := sublist (i_next s) ENOUGH_CODES (i_codes s) in
  set_m_ret (set_m_s mA (set_i_distbits (set_i_next (set_i_codes
      (set_i_distbits (set_i_distcode s (TCodes (i_next s))) 6)
      (sublist 0 (i_next s) (i_codes s) ++ it_tab old r)) (i_next s + it_adv r)) (it_bits 6 r))) (it_ret r).

Lemma cld_m_eq: forall mA,
  cl_dists_m mA =
  (it_ret (inflate_table_model DISTS (sublist (i_nlen (m_s mA)) (i_nlen (m_s mA) + i_ndist (m_s mA)) (i_lens (m_s mA))) 6
            (sublist (i_next (m_s mA)) ENOUGH_CODES (i_codes (m_s mA)))),
   cld_mB mA (inflate_table_model DISTS (sublist (i_nlen (m_s mA)) (i_nlen (m_s mA) + i_ndist (m_s mA)) (i_lens (m_s mA))) 6
            (sublist (i_next (m_s mA)) ENOUGH_CODES (i_codes (m_s mA))))).
Proof. intros. reflexivity. Qed.

Lemma cld_adv0: forall r, it_ret r <> 0 -> it_adv r = 0.
Proof. intros [ | t | a b t] H; simpl in *; auto. lia. Qed.

(* the typecheck of forward_call's arguments needs no SEP: dropping it (to TT) avoids entailer!'s minute-long
   saturation of the call's SEP *)
Lemma cld_sep_TT: forall (Delta: tycontext) P Q (R: list mpred) (S: environ -> mpred),
  ENTAIL Delta, PROPx P (LOCALx Q (SEPx [TT])) |-- S -> ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- S.
Proof.
  intros Delta P Q R S H. eapply derives_trans; [ | exact H]. apply andp_derives; [apply derives_refl | ].
  unfold PROPx, LOCALx, SEPx. apply andp_derives; [apply derives_refl | ]. apply andp_derives; [apply derives_refl | ].
  intro rho. simpl. rewrite sepcon_emp. apply TT_right.
Qed.

Local Ltac check_typecheck ::=
  try delete_FRZR_from_SEP;
  first [goal_has_evars; idtac |
         try apply local_True_right; apply cld_sep_TT; entailer!;
         match goal with
         | |- typecheck_error (deref_byvalue ?T) => error (Function_arguments_include_a_memory_load_of_type T)
         | |- _ => idtac
         end].

(* the memory after the call, the mode field written with Y: the memory of the machine x *)
Lemma cld_mem: forall F mA r x Y,
  field_compatible t_state [] (f_sp F) ->
  Zlength (i_lens (m_s mA)) = 320 -> Zlength (i_codes (m_s mA)) = ENOUGH_CODES ->
  0 <= i_nlen (m_s mA) -> 0 <= i_ndist (m_s mA) <= 288 -> i_nlen (m_s mA) + i_ndist (m_s mA) <= 320 ->
  0 <= i_next (m_s mA) <= ENOUGH_CODES ->
  Zlength (it_tab (sublist (i_next (m_s mA)) ENOUGH_CODES (i_codes (m_s mA))) r) = ENOUGH_CODES - i_next (m_s mA) ->
  0 <= i_next (m_s mA) + it_adv r <= ENOUGH_CODES ->
  m_s x = set_i_mode (m_s (cld_mB mA r)) Y ->
  mem_rest_cl F x = mem_rest_cl F mA ->
  field_at Ews t_state (DOT _mode) (Vint (Int.repr Y)) (f_sp F) *
  field_at Ews t_state (DOT _nlen) (Vint (Int.repr (i_nlen (m_s mA)))) (f_sp F) *
  field_at Ews t_state (DOT _ndist) (Vint (Int.repr (i_ndist (m_s mA)))) (f_sp F) *
  field_at Ews t_state (DOT _have) (Vint (Int.repr (i_have (m_s mA)))) (f_sp F) *
  data_at Ews (tarray tushort (i_nlen (m_s mA)))
    (map (fun z => Vint (Int.repr z)) (sublist 0 (i_nlen (m_s mA)) (i_lens (m_s mA))))
    (field_address t_state (DOT _lens) (f_sp F)) *
  data_at Ews (tarray tushort (i_ndist (m_s mA)))
    (map (fun z => Vint (Int.repr z)) (sublist (i_nlen (m_s mA)) (i_nlen (m_s mA) + i_ndist (m_s mA)) (i_lens (m_s mA))))
    (offset_val (2 * i_nlen (m_s mA)) (field_address t_state (DOT _lens) (f_sp F))) *
  data_at Ews (tarray tushort (320 - (i_nlen (m_s mA) + i_ndist (m_s mA))))
    (map (fun z => Vint (Int.repr z)) (sublist (i_nlen (m_s mA) + i_ndist (m_s mA)) 320 (i_lens (m_s mA))))
    (offset_val (2 * (i_nlen (m_s mA) + i_ndist (m_s mA))) (field_address t_state (DOT _lens) (f_sp F))) *
  data_at Ews (tptr t_code) (offset_val (4 * it_adv r) (codes_at (f_sp F) (i_next (m_s mA))))
    (field_address t_state (DOT _next) (f_sp F)) *
  field_at Ews t_state (DOT _lencode) (tref_val (f_gv F) (f_sp F) (i_lencode (m_s mA))) (f_sp F) *
  field_at Ews t_state (DOT _distcode) (codes_at (f_sp F) (i_next (m_s mA))) (f_sp F) *
  field_at Ews t_state (DOT _lenbits) (Vint (Int.repr (i_lenbits (m_s mA)))) (f_sp F) *
  data_at Ews tuint (Vint (Int.repr (it_bits 6 r))) (field_address t_state (DOT _distbits) (f_sp F)) *
  data_at Ews (tarray t_code (i_next (m_s mA))) (map ent (sublist 0 (i_next (m_s mA)) (i_codes (m_s mA))))
    (field_address t_state (DOT _codes) (f_sp F)) *
  data_at Ews (tarray t_code (ENOUGH_CODES - i_next (m_s mA)))
    (map ent (it_tab (sublist (i_next (m_s mA)) ENOUGH_CODES (i_codes (m_s mA))) r))
    (codes_at (f_sp F) (i_next (m_s mA))) *
  data_at_ Ews (tarray tushort (i_ndist (m_s mA))) (field_address t_state (DOT _work) (f_sp F)) *
  data_at_ Ews (tarray tushort (288 - i_ndist (m_s mA)))
    (offset_val (2 * i_ndist (m_s mA)) (field_address t_state (DOT _work) (f_sp F))) *
  spec.itables (f_gsh F) (f_gv F) * cld_tabs (f_gsh F) (f_gv F) *
  mem_rest_cl F mA * cl_strm F x
  |-- mem_rep F x.
Proof.
  intros F mA r x Y FC ZL ZC H1 H2 H3 H4 ZT HA Hs HR.
  unfold mem_rep. rewrite state_rep_cl. rewrite <- HR. unfold mem_rest_cl, cl_strm.
  assert (E1: i_mode (m_s x) = Y) by (rewrite Hs; reflexivity).
  assert (E2: i_nlen (m_s x) = i_nlen (m_s mA)) by (rewrite Hs; reflexivity).
  assert (E3: i_ndist (m_s x) = i_ndist (m_s mA)) by (rewrite Hs; reflexivity).
  assert (E4: i_have (m_s x) = i_have (m_s mA)) by (rewrite Hs; reflexivity).
  assert (E5: i_lens (m_s x) = i_lens (m_s mA)) by (rewrite Hs; reflexivity).
  assert (E6: i_next (m_s x) = i_next (m_s mA) + it_adv r) by (rewrite Hs; reflexivity).
  assert (E7: i_lencode (m_s x) = i_lencode (m_s mA)) by (rewrite Hs; reflexivity).
  assert (E8: i_distcode (m_s x) = TCodes (i_next (m_s mA))) by (rewrite Hs; reflexivity).
  assert (E9: i_lenbits (m_s x) = i_lenbits (m_s mA)) by (rewrite Hs; reflexivity).
  assert (E10: i_distbits (m_s x) = it_bits 6 r) by (rewrite Hs; reflexivity).
  assert (E11: i_codes (m_s x) = sublist 0 (i_next (m_s mA)) (i_codes (m_s mA)) ++
     it_tab (sublist (i_next (m_s mA)) ENOUGH_CODES (i_codes (m_s mA))) r) by (rewrite Hs; reflexivity).
  rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9, E10, E11. clear Hs E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11.
  set (s := m_s mA) in *. set (C := i_codes s) in *. set (old := sublist (i_next s) ENOUGH_CODES C) in *.
  rewrite (cld_lens_split (f_sp F) (i_lens s) (i_nlen s) (i_ndist s)) by (auto; lia).
  rewrite (cld_work_split (f_sp F) (i_ndist s)) by (auto; lia).
  rewrite (cld_codes_split (f_sp F) (i_next s) (sublist 0 (i_next s) C ++ it_tab old r)) by
    (auto; rewrite Zlength_app, Zlength_sublist, ZT; unfold ENOUGH_CODES in *; lia).
  assert (S1: sublist 0 (i_next s) (sublist 0 (i_next s) C ++ it_tab old r) = sublist 0 (i_next s) C)
    by (unfold ENOUGH_CODES in *; list_solve).
  assert (S2: sublist (i_next s) ENOUGH_CODES (sublist 0 (i_next s) C ++ it_tab old r) = it_tab old r)
    by (unfold ENOUGH_CODES in *; list_solve).
  rewrite S1, S2.
  rewrite (field_at_data_at Ews t_state (DOT _next)), (field_at_data_at Ews t_state (DOT _distbits)).
  simpl nested_field_type.
  rewrite (cld_codes_at_off (f_sp F) (i_next s + it_adv r)) by auto.
  rewrite (cld_codes_at_off (f_sp F) (i_next s)) by auto.
  rewrite offset_offset_val. replace (1368 + 4 * i_next s + 4 * it_adv r) with (1368 + 4 * (i_next s + it_adv r)) by lia.
  rewrite cld_tables_rep. unfold tref_val. cancel.
  rewrite (cld_codes_at_off (f_sp F) (i_next s)) by auto. apply derives_refl.
Qed.

(* a pure fact of the first SEP item *)
Lemma cld_prop_hd: forall (Delta: tycontext) P Q (A: mpred) (R: list mpred) (X: Prop),
  (A |-- !! X) -> ENTAIL Delta, PROPx P (LOCALx Q (SEPx (A :: R))) |-- !! X.
Proof.
  intros Delta P Q A R X H. intro rho. unfold PROPx, LOCALx, SEPx. simpl.
  apply andp_left2. apply andp_left2. apply andp_left2.
  eapply derives_trans; [apply sepcon_derives; [exact H | apply TT_right] | ].
  rewrite prop_sepcon. apply andp_left1. apply derives_refl.
Qed.

Lemma cld_len_codes: forall sh n l p, 0 <= n ->
  data_at sh (tarray t_code n) (map ent l) p |-- !! (Zlength l = n).
Proof.
  intros sh n l p Hn. entailer!. rewrite Zlength_map in *. lia.
Qed.

(* the whole SEP after the call (as the main proof has it) gives the memory and the locals of x *)
Lemma cld_full: forall F mA r x Y hv Ld old,
  field_compatible t_state [] (f_sp F) ->
  Zlength (i_lens (m_s mA)) = 320 -> Zlength (i_codes (m_s mA)) = ENOUGH_CODES ->
  0 <= i_nlen (m_s mA) -> 0 <= i_ndist (m_s mA) <= 288 -> i_nlen (m_s mA) + i_ndist (m_s mA) <= 320 ->
  0 <= i_next (m_s mA) <= ENOUGH_CODES ->
  old = sublist (i_next (m_s mA)) ENOUGH_CODES (i_codes (m_s mA)) ->
  Ld = sublist (i_nlen (m_s mA)) (i_nlen (m_s mA) + i_ndist (m_s mA)) (i_lens (m_s mA)) ->
  Zlength (it_tab old r) = ENOUGH_CODES - i_next (m_s mA) ->
  0 <= i_next (m_s mA) + it_adv r <= ENOUGH_CODES ->
  m_s x = set_i_mode (m_s (cld_mB mA r)) Y ->
  mem_rest_cl F x = mem_rest_cl F mA ->
  data_at Ews (tarray t_code (Zlength old)) (map ent (it_tab old r)) (codes_at (f_sp F) (i_next (m_s mA))) *
  spec.itables (f_gsh F) (f_gv F) *
  data_at Ews (tarray tushort (Zlength Ld)) (map (fun x => Vint (Int.repr x)) Ld)
    (offset_val (2 * i_nlen (m_s mA)) (field_address t_state (DOT _lens) (f_sp F))) *
  data_at_ Ews (tarray tushort (Zlength Ld)) (field_address t_state (DOT _work) (f_sp F)) *
  data_at Ews (tptr t_code) (offset_val (4 * it_adv r) (codes_at (f_sp F) (i_next (m_s mA))))
    (field_address t_state (DOT _next) (f_sp F)) *
  data_at Ews tuint (Vint (Int.repr (it_bits 6 r))) (field_address t_state (DOT _distbits) (f_sp F)) *
  field_at Ews t_state (DOT _have) (Vint (Int.repr (i_have (m_s mA)))) (f_sp F) *
  field_at Ews t_state (DOT _lencode) (tref_val (f_gv F) (f_sp F) (i_lencode (m_s mA))) (f_sp F) *
  field_at Ews t_state (DOT _lenbits) (Vint (Int.repr (i_lenbits (m_s mA)))) (f_sp F) *
  mem_rest_cl F mA *
  data_at Tsh t_code hv (f_vhere F) * data_at_ Tsh t_code (f_vlast F) * data_at_ Tsh (tarray tuchar 4) (f_vhbuf F) *
  field_at Ews t_state (DOT _nlen) (Vint (Int.repr (i_nlen (m_s mA)))) (f_sp F) *
  field_at Ews t_state (DOT _ndist) (Vint (Int.repr (i_ndist (m_s mA)))) (f_sp F) *
  data_at Ews (tarray tushort (i_nlen (m_s mA)))
    (map (fun z => Vint (Int.repr z)) (sublist 0 (i_nlen (m_s mA)) (i_lens (m_s mA))))
    (field_address t_state (DOT _lens) (f_sp F)) *
  data_at Ews (tarray tushort (320 - (i_nlen (m_s mA) + i_ndist (m_s mA))))
    (map (fun z => Vint (Int.repr z)) (sublist (i_nlen (m_s mA) + i_ndist (m_s mA)) 320 (i_lens (m_s mA))))
    (offset_val (2 * (i_nlen (m_s mA) + i_ndist (m_s mA))) (field_address t_state (DOT _lens) (f_sp F))) *
  field_at Ews t_state (DOT _distcode) (codes_at (f_sp F) (i_next (m_s mA))) (f_sp F) *
  data_at Ews (tarray t_code (i_next (m_s mA))) (map ent (sublist 0 (i_next (m_s mA)) (i_codes (m_s mA))))
    (field_address t_state (DOT _codes) (f_sp F)) *
  data_at_ Ews (tarray tushort (288 - i_ndist (m_s mA)))
    (offset_val (2 * i_ndist (m_s mA)) (field_address t_state (DOT _work) (f_sp F))) *
  cld_tabs (f_gsh F) (f_gv F) *
  field_at Ews t_state (DOT _mode) (Vint (Int.repr Y)) (f_sp F) *
  cl_strm F x
  |-- mem_rep F x * locals_rep F.
Proof.
  intros F mA r x Y hv Ld old FC ZL ZC H1 H2 H3 H4 EO EL ZT HA Hs HR.
  assert (ZO: Zlength old = ENOUGH_CODES - i_next (m_s mA)) by (subst old; rewrite Zlength_sublist; lia).
  assert (ZLd: Zlength Ld = i_ndist (m_s mA)) by (subst Ld; rewrite Zlength_sublist; lia).
  rewrite ZO, ZLd. subst old Ld.
  unfold locals_rep.
  eapply derives_trans; [ | apply sepcon_derives; [apply (cld_mem F mA r x Y FC ZL ZC H1 H2 H3 H4 ZT HA Hs HR) |
    apply derives_refl]].
  rewrite <- !sepcon_assoc. cancel.
Qed.

(* loop_state of a machine that differs from m only in its istate, msg, ret and leave *)
Lemma cld_ls: forall F x m R L,
  m_inp x = m_inp m -> m_aout x = m_aout m -> m_nx x = m_nx m -> m_ow x = m_ow m -> m_have x = m_have m ->
  m_left x = m_left m -> m_hold x = m_hold m -> m_bits x = m_bits m -> m_in x = m_in m -> m_out x = m_out m ->
  m_ret x = R -> m_leave x = L ->
  loop_state F x =
  PROP (in_ok (f_ib F) (m_inp m); out_ok (f_ob F) (m_aout m))
  LOCAL (temp _strm (f_strmp F); temp _flush (zv (f_flush F)); temp _state (f_sp F);
         temp _next (in_ptr (f_ib F) (m_nx m)); temp _put (out_ptr (f_ob F) (Zlength (m_ow m)));
         temp _have (zv (m_have m)); temp _left (zv (m_left m)); temp _hold (lv (m_hold m));
         temp _bits (zv (m_bits m)); temp _in (zv (m_in m)); temp _out (zv (m_out m));
         temp _ret (zv R); temp _leave (zv L);
         lvar _here t_code (f_vhere F); lvar _last t_code (f_vlast F);
         lvar _hbuf (tarray tuchar 4) (f_vhbuf F); gvars (f_gv F))
  SEP (mem_rep F x; locals_rep F).
Proof.
  intros F x m R L E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12. unfold loop_state.
  rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9, E10, E11, E12. reflexivity.
Qed.

Lemma cld_ret_range: forall r, -1 <= it_ret r <= 1.
Proof. intros [ | t | a b t]; simpl; lia. Qed.

(* hides hypotheses from Floyd's eassumption (my_auto tried them for a minute at forward_call) *)
Inductive cld_box (P: Prop) : Prop := cld_mk : P -> cld_box P.

Lemma cl_dists_ok : cl_dists_stmt.
Proof.
  unfold cl_dists_stmt. intros Espec F m0 mA hv HF HP MW E0.
  rewrite loop_state_h_cl. unfold loop_state_clh, cl_sep.
  cl_stmt. abbreviate_semax.
  destruct HP as (SW & HM & HL & HNL & HND & HNX & HLB).
  destruct (sw_lens _ SW) as [ZL FL]. destruct (sw_codes _ SW) as [ZC FC2].
  unfold loop_locals.
  freeze [0;3;6;8;12;14;15;16;17] FR.
  assert_PROP (field_compatible t_state [] (f_sp F)) as FC.
  { entailer!. match goal with H: field_compatible t_state (DOT _nlen) _ |- _ => destruct H as (A1 & A2 & A3 & A4 & A5) end.
    repeat split; auto. }
  assert (PN: isptr (codes_at (f_sp F) (i_next (m_s mA))))
    by (apply cld_isptr_codes_at; [exact FC | unfold ENOUGH_CODES, ENOUGH_LENS in *; lia]).
  forward. forward. forward. forward. forward.
  set (nl := i_nlen (m_s mA)) in *. set (nd := i_ndist (m_s mA)) in *. set (nx := i_next (m_s mA)) in *.
  set (Ld := sublist nl (nl + nd) (i_lens (m_s mA))).
  set (old := sublist nx ENOUGH_CODES (i_codes (m_s mA))).
  set (r := inflate_table_model DISTS Ld 6 old).
  assert (Er: r = inflate_table_model DISTS Ld 6 old) by reflexivity. clearbody r.
  assert (EOld: old = sublist nx ENOUGH_CODES (i_codes (m_s mA))) by reflexivity. clearbody old.
  assert (ELd: Ld = sublist nl (nl + nd) (i_lens (m_s mA))) by reflexivity. clearbody Ld.
  pose proof (conj Er (conj EOld ELd)) as HIDE. clear Er EOld ELd.
  rewrite (cld_lens_split (f_sp F) (i_lens (m_s mA)) nl nd) by (auto; lia).
  rewrite (cld_work_split (f_sp F) nd) by (auto; lia).
  rewrite (cld_codes_split (f_sp F) nx (i_codes (m_s mA))) by (auto; unfold ENOUGH_CODES, ENOUGH_LENS in *; lia).
  rewrite (field_at_data_at Ews t_state (DOT _next)), (field_at_data_at Ews t_state (DOT _distbits)).
  simpl nested_field_type.
  rewrite cld_tables_rep.
  Intros.
  assert (ZLd: Zlength Ld = nd) by (rewrite (proj2 (proj2 HIDE)), Zlength_sublist; lia).
  assert (ZO: Zlength old = ENOUGH_CODES - nx)
    by (rewrite (proj1 (proj2 HIDE)), Zlength_sublist; unfold ENOUGH_CODES, ENOUGH_LENS in *; lia).
  assert (IOK: inputs_ok DISTS Ld 6).
  { split; [unfold DISTS; lia | split; [rewrite ZLd; unfold max_codes, DISTS; simpl; lia | split; [ | rep_lia]]].
    apply Forall_forall. intros x Hx. apply In_Znth in Hx. destruct Hx as (i & Hi & Ei). subst x.
    rewrite (proj2 (proj2 HIDE)) in Hi |- *. rewrite Zlength_sublist in Hi by lia.
    rewrite Znth_sublist by lia. unfold MAXBITS. apply HLB. lia. }
  assert (EOK: Forall entry_ok old).
  { rewrite (proj1 (proj2 HIDE)). apply Forall_sublist. exact FC2. }
  assert (COK: cap_ok DISTS Ld 6 (Zlength old)).
  { rewrite ZO. unfold cap_ok, DISTS, CODES, LENS, ENOUGH_DISTS, ENOUGH_CODES, ENOUGH_LENS in *.
    split; [intro; discriminate | split; [intro; discriminate | intro; lia]]. }
  replace (sublist nl (nl + nd) (i_lens (m_s mA))) with Ld by apply HIDE.
  replace (sublist nx ENOUGH_CODES (i_codes (m_s mA))) with old by apply HIDE.
  freeze [0;1;2;3;5;7;9;12;14] FR2.
  destruct HF as [(Hshs & Hhsh & Hgsh & Htsh) Hfl].
  rewrite <- ZLd, <- ZO.
  rewrite (cld_da_us Ews (Zlength Ld)), (cld_da__us Ews (Zlength Ld)), cld_da_uint, cld_da_ptr, cld_da_codes.
  change (map ent old) with (map spec.entry_rep old).
  assert (BOX: cld_box ((stepf2 (f_flush F) lenfix_list distfix_list m0 = cl_dists_out (f_flush F) mA) /\
    (fst (cl_dists_m mA) = 0 -> mwf3 (set_mode (snd (cl_dists_m mA)) LEN_)) /\
    (r = inflate_table_model DISTS Ld 6 old /\
     old = sublist nx ENOUGH_CODES (i_codes (m_s mA)) /\ Ld = sublist nl (nl + nd) (i_lens (m_s mA)))))
    by (constructor; auto).
  clear E0 MW HIDE.
  forward_call (DISTS, Ld, 6, old, f_gv F, f_gsh F, Ews, Ews,
    offset_val (2 * nl) (field_address t_state (DOT _lens) (f_sp F)),
    field_address t_state (DOT _work) (f_sp F), field_address t_state (DOT _next) (f_sp F),
    codes_at (f_sp F) nx, field_address t_state (DOT _distbits) (f_sp F)).
  { apply prop_right. simpl. rewrite !field_address_offset by auto with field_compatible. simpl.
    assert (PS: isptr (f_sp F)) by (destruct FC; auto).
    destruct (f_sp F) eqn:ESP; try contradiction. simpl. unfold DISTS. do 2 f_equal. f_equal.
    unfold Ptrofs.mul, ptrofs_of_int, Ptrofs.of_intu, Ptrofs.of_int.
    rewrite Int.unsigned_repr by rep_lia. rewrite !Ptrofs.unsigned_repr by rep_lia. reflexivity. }
  destruct BOX as [[E0 [MW [Er [EOld ELd]]]]].
  assert (EM: cl_dists_m mA = (it_ret r, cld_mB mA r)).
  { rewrite cld_m_eq. fold nl nd nx. rewrite <- ELd, <- EOld, <- Er. reflexivity. }
  rewrite <- Er.
  assert (BOX: cld_box ((stepf2 (f_flush F) lenfix_list distfix_list m0 = cl_dists_out (f_flush F) mA) /\
    (fst (cl_dists_m mA) = 0 -> mwf3 (set_mode (snd (cl_dists_m mA)) LEN_)) /\
    cl_dists_m mA = (it_ret r, cld_mB mA r) /\ old = sublist nx ENOUGH_CODES (i_codes (m_s mA)) /\
    Ld = sublist nl (nl + nd) (i_lens (m_s mA)))) by (constructor; auto).
  clear E0 MW Er EM EOld ELd.
  change spec.code_t with t_code. unfold spec.zs_rep.
  rewrite <- (cld_da_us Ews (Zlength Ld)), <- (cld_da__us Ews (Zlength Ld)), <- cld_da_uint, <- cld_da_ptr,
    <- cld_da_codes.
  change (map spec.entry_rep (it_tab old r)) with (map ent (it_tab old r)).
  focus_SEP 3.
  assert_PROP (Zlength (it_tab old r) = Zlength old) as ZT0
    by (apply cld_prop_hd; apply cld_len_codes; rewrite ZO; unfold ENOUGH_CODES, ENOUGH_LENS in *; lia).
  assert (ZT: Zlength (it_tab old r) = ENOUGH_CODES - nx) by lia.
  clear ZT0.
  freeze [0;1;2;3;4;5;6] FA.
  forward.
  thaw FA. thaw FR2. thaw FR.
  freeze [0;1;2;3;4;5;7;8;9;11;12;13;14;15;16;17;18;19;20;21;22] FB.
  pose proof (cld_ret_range r) as RR.
  destruct (Z.eq_dec (it_ret r) 0) as [R0 | R0].
  2:{ (* inflate_table failed: BAD *)
    forward_if; [ | match goal with X: Int.repr (it_ret r) = Int.zero |- _ =>
                      exfalso; apply R0; apply repr_inj_signed; [rep_lia | rep_lia | exact X] end].
    unfold cl_strm, strm_rep.
    remember (f_gv F _zcalloc) as za eqn:Eza. remember (f_gv F _zcfree) as zf eqn:Ezf.
    forward. forward.
    subst za zf. thaw FB.
    set (x := set_bad (cld_mB mA r) M_d_set).
    match goal with |- context [@data_at ?cs ?sh t_strm ?v ?p] =>
      change (@data_at cs sh t_strm v p) with (cl_strm F x) end.
    destruct BOX as [[E0 [MW [EM [EOld ELd]]]]].
    assert (EB: stepf2 (f_flush F) lenfix_list distfix_list m0 = IBrk x).
    { rewrite E0. unfold cl_dists_out. rewrite EM. cbv beta iota zeta.
      replace (it_ret r =? 0) with false by (symmetry; apply Z.eqb_neq; auto). reflexivity. }
    clear E0 MW EM.
    sep_apply (cld_full F mA r x 16209 hv Ld old FC ZL ZC ltac:(unfold nl in *; lia) ltac:(unfold nd in *; lia)
      ltac:(unfold nl, nd in *; lia) ltac:(unfold nx, ENOUGH_CODES, ENOUGH_LENS in *; lia) EOld ELd ZT
      ltac:(rewrite cld_adv0 by auto; unfold nx, ENOUGH_CODES, ENOUGH_LENS in *; lia) eq_refl eq_refl).
    forward.
    unfold switch_ret_assert, case_post2. cbv beta iota.
    Exists x. apply andp_right; [apply prop_right; exact EB | ].
    rewrite (cld_ls F x mA (it_ret r) (m_leave mA)) by reflexivity. entailer!. }
  (* the table is built: LEN_ *)
  forward_if; [rewrite R0 in *; contradiction | ].
  forward.
  thaw FB.
  set (x := set_mode (cld_mB mA r) LEN_).
  change (cl_strm F mA) with (cl_strm F x).
  destruct BOX as [[E0 [MW [EM [EOld ELd]]]]].
  rewrite EM in MW. cbn [fst snd] in MW. specialize (MW R0). fold x in MW.
  assert (EL: cl_dists_out (f_flush F) mA =
    if f_flush F =? Z_TREES then IBrk (set_leave x) else c_LEN_ lenfix_list distfix_list (fast lenfix_list distfix_list) x).
  { unfold cl_dists_out. rewrite EM. cbv beta iota zeta. rewrite R0. reflexivity. }
  rewrite EL in E0. clear EM EL.
  assert (Hm: m_mode x = LEN_) by reflexivity.
  assert (HA: 0 <= nx + it_adv r <= ENOUGH_CODES).
  { destruct MW as [W _]. pose proof (sw_next _ (mw_s _ W)) as SN. exact SN. }
  sep_apply (cld_full F mA r x 16199 hv Ld old FC ZL ZC ltac:(unfold nl in *; lia) ltac:(unfold nd in *; lia)
    ltac:(unfold nl, nd in *; lia) ltac:(unfold nx, ENOUGH_CODES, ENOUGH_LENS in *; lia) EOld ELd ZT
    HA eq_refl eq_refl).
  forward_if.
  - (* Z_TREES *)
    forward. forward.
    unfold switch_ret_assert, case_post2. cbv beta iota.
    Exists (set_leave x). apply andp_right; [apply prop_right; rewrite E0, H2; reflexivity | ].
    change (mem_rep F x) with (mem_rep F (set_leave x)).
    rewrite (cld_ls F (set_leave x) mA (it_ret r) 1) by reflexivity. entailer!.
  - (* LEN_ *)
    forward. unfold switch_ret_assert, case_post2. cbv beta iota. unfold fall_post5.
    Exists x. apply andp_right.
    { apply prop_right. split; [ | split; [exact Hm | split; [exact HL | exact MW]]].
      rewrite E0. replace (f_flush F =? Z_TREES) with false by (symmetry; apply Z.eqb_neq; unfold Z_TREES; lia).
      symmetry. exact (Steps2.stepf2_LEN_ (f_flush F) lenfix_list distfix_list x Hm). }
    rewrite (cld_ls F x mA (it_ret r) (m_leave mA)) by reflexivity. entailer!.
Qed.
