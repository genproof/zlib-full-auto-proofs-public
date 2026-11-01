(* inflate_fast's body from the pass lemma (FKit.iter_stmt) and the pass facts (FKit.iter_facts_stmt): the
   prologue (the locals from strm/state), the do-while loop (invariant: the machine m of the model's
   fast_loop, fuel k), the epilogue (the unused bytes back, the stores: the model's restore). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inffast.code.
Require Import Zlib.proof.inffast.F5Kit.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* the 32nd of 35 separating conjuncts to the front (on variables: a cheap proof term) *)
Lemma sepcon_32_35: forall a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35: mpred,
  a1 * a2 * a3 * a4 * a5 * a6 * a7 * a8 * a9 * a10 * a11 * a12 * a13 * a14 * a15 * a16 * a17 * a18 * a19 * a20 * a21 * a22 * a23 * a24 * a25 * a26 * a27 * a28 * a29 * a30 * a31 * a32 * a33 * a34 * a35 =
  a32 * (a1 * a2 * a3 * a4 * a5 * a6 * a7 * a8 * a9 * a10 * a11 * a12 * a13 * a14 * a15 * a16 * a17 * a18 * a19 * a20 * a21 * a22 * a23 * a24 * a25 * a26 * a27 * a28 * a29 * a30 * a31 * a33 * a34 * a35).
Proof. intros. apply pred_ext; cancel. Qed.

Lemma state_rep_codes: forall gv sp strmp headp winp s,
  state_rep gv sp strmp headp winp s =
  field_at Ews t_state (DOT _codes) (map ent (i_codes s)) sp * state_rep_nc gv sp strmp headp winp s.
Proof. intros. unfold state_rep, state_rep_nc. apply sepcon_32_35. Qed.

Lemma sepcon_mem_perm: forall c nc win head strm inr outr lf df ord it crc: mpred,
  (c * nc) * win * head * strm * inr * outr * (lf * df * ord * it) * crc =
  (c * lf * df) * win * inr * outr * (nc * head * strm * ord * it * crc).
Proof. intros. apply pred_ext; cancel. Qed.

Lemma mem_rep_fs: forall F m,
  mem_rep F m = tab_mem F (m_s m) * win_rep (f_winp F) (m_s m) * in_rep (f_ib F) * out_rep (f_ob F) (m_ow m) *
                rest_mem F m.
Proof.
  intros. unfold mem_rep, tab_mem, rest_mem, tables_rep. rewrite state_rep_codes.
  apply sepcon_mem_perm.
Qed.

Lemma sepcon_rest_perm: forall a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 hd st ord it crc: mpred,
  (a1 * a2 * a3 * a4 * a5 * a6 * a7 * a8 * a9 * a10 * a11 * a12 * a13 * a14 * a15 * a16 * a17 * a18 * a19 * a20 * a21 * a22 * a23 * a24 * a25 * a26 * a27 * a28 * a29 * a30 * a31 * a32 * a33 * a34) * hd * st * ord * it * crc =
  st * (a12 * a13 * a14 * a15 * a16 * a17 * a21 * a22 * a23 * a24) * ((a1 * a2 * a3 * a4 * a5 * a6 * a7 * a8 * a9 * a10 * a11 * a18 * a19 * a20 * a25 * a26 * a27 * a28 * a29 * a30 * a31 * a32 * a33 * a34) * hd * ord * it * crc).
Proof. intros. apply pred_ext; cancel. Qed.

(* rest_mem without strm_rep and the 10 state fields the prologue reads (and the epilogue writes) *)
Definition rest_pro (F: frame) (m: mst) : mpred :=
  let gv := f_gv F in let sp := f_sp F in let strmp := f_strmp F in let headp := f_headp F in
  let winp := f_winp F in let s := m_s m in
  (field_at Ews t_state (DOT _strm) strmp sp *
   field_at Ews t_state (DOT _mode) (zv (i_mode s)) sp *
   field_at Ews t_state (DOT _last) (zv (i_last s)) sp *
   field_at Ews t_state (DOT _wrap) (zv (i_wrap s)) sp *
   field_at Ews t_state (DOT _havedict) (zv (i_havedict s)) sp *
   field_at Ews t_state (DOT _flags) (zv (i_flags s)) sp *
   field_at Ews t_state (DOT _dmax) (zv (i_dmax s)) sp *
   field_at Ews t_state (DOT _check) (lv (i_check s)) sp *
   field_at Ews t_state (DOT _total) (lv (i_total s)) sp *
   field_at Ews t_state (DOT _head) (if i_head s then headp else nullval) sp *
   field_at Ews t_state (DOT _wbits) (zv (i_wbits s)) sp *
   field_at Ews t_state (DOT _length) (zv (i_length s)) sp *
   field_at Ews t_state (DOT _offset) (zv (i_offset s)) sp *
   field_at Ews t_state (DOT _extra) (zv (i_extra s)) sp *
   field_at Ews t_state (DOT _ncode) (zv (i_ncode s)) sp *
   field_at Ews t_state (DOT _nlen) (zv (i_nlen s)) sp *
   field_at Ews t_state (DOT _ndist) (zv (i_ndist s)) sp *
   field_at Ews t_state (DOT _have) (zv (i_have s)) sp *
   field_at Ews t_state (DOT _next) (codes_at sp (i_next s)) sp *
   field_at Ews t_state (DOT _lens) (map (fun z => Vint (Int.repr z)) (i_lens s)) sp *
   field_at_ Ews t_state (DOT _work) sp *
   field_at Ews t_state (DOT _sane) (zv (i_sane s)) sp *
   field_at Ews t_state (DOT _back) (zv (i_back s)) sp *
   field_at Ews t_state (DOT _was) (zv (i_was s)) sp) *
  head_part F m *
  data_at (f_gsh F) (tarray tushort 19) (map (fun z => Vint (Int.repr z)) order)
    (f_gv F Zlib.inflate.code._order) *
  Zlib.proof.inftrees.spec.itables (f_gsh F) (f_gv F) *
  crc_table_at (f_tsh F) (f_gv F).

(* the 10 state fields of the prologue *)
Definition state_pro (F: frame) (s: istate) : mpred :=
  field_at Ews t_state (DOT _wsize) (zv (i_wsize s)) (f_sp F) *
  field_at Ews t_state (DOT _whave) (zv (i_whave s)) (f_sp F) *
  field_at Ews t_state (DOT _wnext) (zv (i_wnext s)) (f_sp F) *
  field_at Ews t_state (DOT _window) (if i_win s then (f_winp F) else nullval) (f_sp F) *
  field_at Ews t_state (DOT _hold) (lv (i_hold s)) (f_sp F) *
  field_at Ews t_state (DOT _bits) (zv (i_bits s)) (f_sp F) *
  field_at Ews t_state (DOT _lencode) (tref_val (f_gv F) (f_sp F) (i_lencode s)) (f_sp F) *
  field_at Ews t_state (DOT _distcode) (tref_val (f_gv F) (f_sp F) (i_distcode s)) (f_sp F) *
  field_at Ews t_state (DOT _lenbits) (zv (i_lenbits s)) (f_sp F) *
  field_at Ews t_state (DOT _distbits) (zv (i_distbits s)) (f_sp F).

Definition strm_m (F: frame) (m: mst) : mpred :=
  strm_rep (f_gv F) (f_shs F) (f_strmp F)
    (in_ptr (f_ib F) (m_snx m)) (zv (Zlength (m_inp m) - m_snx m)) (m_tin m)
    (out_ptr (f_ob F) (m_sow m)) (zv (m_aout m - m_sow m)) (m_tout m)
    (msg_val (f_gv F) (m_msg m)) (f_sp F) (f_dt F) (m_adler m) (f_vres F).

Lemma rest_mem_pro: forall F m, rest_mem F m = strm_m F m * state_pro F (m_s m) * rest_pro F m.
Proof. intros. unfold rest_mem, state_rep_nc, rest_pro, state_pro, strm_m. apply sepcon_rest_perm. Qed.

Lemma win_ptr: forall winp s, win_rep winp s |-- !! is_pointer_or_null (if i_win s then winp else nullval).
Proof. intros. unfold win_rep. destruct (i_win s); entailer!. Qed.

Lemma tab_ptrs: forall F s,
  tab_mem F s |-- !! (forall t, tref_ok t -> is_pointer_or_null (tref_val (f_gv F) (f_sp F) t)).
Proof.
  intros. unfold tab_mem. entailer!. intros t T. destruct t; cbn [tref_val].
  - auto.
  - auto.
  - unfold codes_at. cbn in T. rewrite field_address0_offset.
    + destruct H as [Hp _]. destruct (f_sp F); try contradiction. simpl. auto.
    + eapply field_compatible0_cons_Tarray; [reflexivity | exact H | unfold ENOUGH_CODES in T; lia].
Qed.

#[local] Hint Resolve win_ptr tab_ptrs : saturate_local.

Lemma offset_val_field_address0_tuchar: forall n j p,
  field_compatible (tarray tuchar n) [] p -> 0 <= j <= n ->
  offset_val j p = field_address0 (tarray tuchar n) [ArraySubsc j] p.
Proof.
  intros. rewrite field_address0_offset.
  - simpl. f_equal. lia.
  - eapply field_compatible0_cons_Tarray; [reflexivity | auto | lia].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the loop: invariant (head of the body), after a continuing pass (before the test), after the loop *)

Definition K0 (m0: mst) : nat := (Z.to_nat (m_aout m0) + 1)%nat.
Definition floop (k: nat) (m: mst) : mst := fast_loop lenfix_list distfix_list k m.

Record inv_ok (F: frame) (m0 m: mst) (k: nat) : Prop := {
  iv_wf: fast_ok m; iv_mode: m_mode m = LEN; iv_have: 6 <= m_have m; iv_left: 258 <= m_left m;
  iv_bits: m_bits m <= 30; iv_in: in_ok (f_ib F) (m_inp m); iv_out: out_ok (f_ob F) (m_aout m);
  iv_loop: floop (K0 m0) m0 = floop k m; iv_fuel: m_left m + 1 <= Z.of_nat k;
  iv_bud: m_bits m - 8 * m_nx m <= m_bits m0 - 8 * m_nx m0; iv_nx: m_nx m0 <= m_nx m;
  iv_inp: m_inp m = m_inp m0; iv_aout: m_aout m = m_aout m0 }.

Record cont_ok (F: frame) (m0 m: mst) (k: nat) : Prop := {
  ct_wf: fast_ok m; ct_mode: m_mode m = LEN; ct_bits: m_bits m <= 30;
  ct_in: in_ok (f_ib F) (m_inp m); ct_out: out_ok (f_ob F) (m_aout m);
  ct_loop: floop (K0 m0) m0 =
           (if andb (m_nx m <? Zlength (m_inp m) - 5) (Zlength (m_ow m) <? m_aout m - 257)
            then floop k m else m);
  ct_fuel: m_left m + 1 <= Z.of_nat k;
  ct_bud: m_bits m - 8 * m_nx m <= m_bits m0 - 8 * m_nx m0; ct_nx: m_nx m0 <= m_nx m;
  ct_inp: m_inp m = m_inp m0; ct_aout: m_aout m = m_aout m0;
  ct_len: 6 <= Zlength (m_inp m); ct_nxle: m_nx m <= Zlength (m_inp m); ct_ow: Zlength (m_ow m) <= m_aout m;
  ct_hold: lrange (m_hold m); ct_big: 258 <= m_aout m }.

Record exit_ok (F: frame) (m0 m: mst) : Prop := {
  ex_loop: floop (K0 m0) m0 = m; ex_bits: 0 <= m_bits m <= 30;
  ex_bud: m_bits m - 8 * m_nx m <= m_bits m0 - 8 * m_nx m0;
  ex_nx: m_nx m0 <= m_nx m <= Zlength (m_inp m); ex_ow: Zlength (m_ow m) <= m_aout m;
  ex_hold: lrange (m_hold m);
  ex_in: in_ok (f_ib F) (m_inp m); ex_out: out_ok (f_ob F) (m_aout m);
  ex_inp: m_inp m = m_inp m0; ex_aout: m_aout m = m_aout m0; ex_len: 6 <= Zlength (m_inp m); ex_big: 258 <= m_aout m }.

Definition inv_a (F: frame) (m0: mst) : environ -> mpred :=
  EX m: mst, EX k: nat, PROPx [inv_ok F m0 m k] (LOCALx (fs_locals F m) (SEPx (fs_sep F m))).
Definition cont_a (F: frame) (m0: mst) : environ -> mpred :=
  EX m: mst, EX k: nat, PROPx [cont_ok F m0 m k] (LOCALx (fs_locals F m) (SEPx (fs_sep F m))).
Definition exit_a (F: frame) (m0: mst) : environ -> mpred :=
  EX m: mst, PROPx [exit_ok F m0 m] (LOCALx (fs_locals F m) (SEPx (fs_sep F m))).

(* pointer comparisons within one byte array *)
Ltac wvp_leaf := match goal with |- data_at _ (tarray tuchar _) _ _ |-- _ =>
  eapply derives_trans; [apply data_at_memory_block |];
  apply memory_block_weak_valid_pointer; [simpl sizeof; lia | simpl sizeof; lia | auto with share] end.
Ltac wvp := match goal with
  | |- _ * _ |-- _ => first [ apply sepcon_weak_valid_pointer2; wvp_leaf | apply sepcon_weak_valid_pointer1; wvp ]
  | |- _ => wvp_leaf end.
Ltac test_order_tac :=
  rewrite isptr_denote_tc_test_order by auto; unfold test_order_ptrs; rewrite sameblock_offset_val by auto;
  apply andp_right; wvp.

Lemma cmp_lt_val: forall n p i j,
  field_compatible (tarray tuchar n) [] p -> 0 <= i <= n -> 0 <= j <= n ->
  force_val (sem_cmp_pp Clt (offset_val i p) (offset_val j p)) = Vint (if i <? j then Int.one else Int.zero).
Proof.
  intros n p i j FC Hi Hj.
  destruct p; try (destruct FC; contradiction).
  destruct FC as (_ & _ & SZ & _). simpl in SZ. rewrite Z.max_r in SZ by lia.
  pose proof (Ptrofs.unsigned_range i0) as R0.
  unfold sem_cmp_pp, offset_val. simpl.
  unfold Val.cmplu_bool. simpl. destruct (eq_block b b) as [_|NE]; [|congruence]. simpl.
  unfold Ptrofs.ltu. rewrite !Ptrofs.add_unsigned.
  rewrite !(Ptrofs.unsigned_repr (Ptrofs.unsigned i0 + Ptrofs.unsigned (Ptrofs.repr _))).
  2,3: rewrite Ptrofs.unsigned_repr; unfold Ptrofs.max_unsigned; lia.
  rewrite !Ptrofs.unsigned_repr by (unfold Ptrofs.max_unsigned; lia).
  destruct (zlt (Ptrofs.unsigned i0 + i) (Ptrofs.unsigned i0 + j)), (i <? j) eqn:E; simpl; auto;
    rewrite ?Z.ltb_lt, ?Z.ltb_ge in E; lia.
Qed.

Lemma ptr_add_uint: forall p k a c, isptr p -> 0 <= a <= Int.max_unsigned -> 0 <= c <= a ->
  force_val (sem_binary_operation' Oadd (tptr tuchar) tuint (offset_val k p)
    (eval_binop Osub tuint tint (Vint (Int.repr a)) (Vint (Int.repr c)))) = offset_val (k + (a - c)) p.
Proof.
  intros. destruct p; try contradiction. unfold eval_binop, force_val2. simpl.
  f_equal. rewrite Ptrofs.add_assoc. f_equal. rewrite sub_repr. unfold Ptrofs.of_intu, Ptrofs.of_int.
  rewrite Int.unsigned_repr by rep_lia. rewrite Ptrofs.mul_commut, Ptrofs.mul_one. rewrite ptrofs_add_repr.
  reflexivity.
Qed.

Lemma ptr_sub_uint: forall p k a c, isptr p -> 0 <= a <= Int.max_unsigned -> 0 <= c <= a ->
  force_val (sem_binary_operation' Osub (tptr tuchar) tuint (offset_val k p)
    (eval_binop Osub tuint tuint (Vint (Int.repr a)) (Vint (Int.repr c)))) = offset_val (k - (a - c)) p.
Proof.
  intros. destruct p; try contradiction. unfold eval_binop, force_val2. simpl.
  f_equal. rewrite sub_repr. unfold Ptrofs.of_intu, Ptrofs.of_int.
  rewrite Int.unsigned_repr by rep_lia. rewrite Ptrofs.mul_commut, Ptrofs.mul_one.
  rewrite Ptrofs.sub_add_opp, Ptrofs.add_assoc. f_equal.
  rewrite Ptrofs.neg_repr, ptrofs_add_repr. f_equal; lia.
Qed.

Lemma mask_eq: forall b, 0 <= b <= 30 ->
  Int.sub (Int.shl (Int.repr 1) (Int.repr b)) (Int.repr 1) = Int.repr (2 ^ b - 1).
Proof.
  intros b Hb. rewrite Int.shl_mul_two_p. rewrite Int.unsigned_repr by rep_lia.
  rewrite two_p_equiv. rewrite Int.mul_commut, Int.mul_one, sub_repr. reflexivity.
Qed.

Lemma shru3: forall b, 0 <= b <= Int.max_unsigned ->
  Int.shru (Int.repr b) (Int.repr 3) = Int.repr (Z.shiftr b 3).
Proof. intros. unfold Int.shru. rewrite !Int.unsigned_repr by rep_lia. reflexivity. Qed.

Lemma ptr_sub_uint': forall p k a, isptr p -> 0 <= a <= Int.max_unsigned ->
  force_val (sem_binary_operation' Osub (tptr tuchar) tuint (offset_val k p) (Vint (Int.repr a))) =
  offset_val (k - a) p.
Proof.
  intros. destruct p; try contradiction. simpl.
  f_equal. unfold Ptrofs.of_intu, Ptrofs.of_int.
  rewrite Int.unsigned_repr by rep_lia. rewrite Ptrofs.mul_commut, Ptrofs.mul_one.
  rewrite Ptrofs.sub_add_opp, Ptrofs.add_assoc. f_equal.
  rewrite Ptrofs.neg_repr, ptrofs_add_repr. f_equal; lia.
Qed.

Lemma shl3: forall L, 0 <= L < 4 -> Int.shl (Int.repr L) (Int.repr 3) = Int.repr (L * 8).
Proof.
  intros. rewrite Int.shl_mul_two_p. rewrite Int.unsigned_repr by rep_lia.
  rewrite mul_repr. reflexivity.
Qed.

Lemma land_mask: forall h b, 0 <= h <= Int64.max_unsigned -> 0 <= b <= 30 ->
  Int64.and (Int64.repr h) (Int64.repr (2 ^ b - 1)) = Int64.repr (h mod 2 ^ b).
Proof.
  intros h b Hh Hb. unfold Int64.and. rewrite Int64.unsigned_repr by rep_lia.
  assert (0 < 2 ^ b <= 2 ^ 30) by (split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_le_mono_r; lia]).
  rewrite Int64.unsigned_repr by rep_lia.
  replace (2 ^ b - 1) with (Z.ones b) by (rewrite Z.ones_equiv; lia).
  rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma sub_pp_val: forall n p a b,
  field_compatible (tarray tuchar n) [] p -> 0 <= a <= n -> 0 <= b <= n ->
  force_val (sem_sub_pp tuchar (offset_val a p) (offset_val b p)) = Vlong (Int64.repr (a - b)).
Proof.
  intros n p a b FC Ha Hb.
  destruct p; try (destruct FC; contradiction).
  destruct FC as (_ & _ & SZ & _). simpl in SZ. rewrite Z.max_r in SZ by lia.
  pose proof (Ptrofs.unsigned_range i) as R0.
  unfold sem_sub_pp, offset_val. simpl. destruct (eq_block b0 b0) as [_|NE]; [|congruence]. simpl.
  rewrite (Ptrofs.add_commut i (Ptrofs.repr a)), (Ptrofs.add_commut i (Ptrofs.repr b)), Ptrofs.sub_shifted.
  unfold Vptrofs. destruct Archi.ptr64 eqn:A; [|discriminate]. f_equal.
  assert (D: Ptrofs.divs (Ptrofs.sub (Ptrofs.repr a) (Ptrofs.repr b)) (Ptrofs.repr 1) =
             Ptrofs.sub (Ptrofs.repr a) (Ptrofs.repr b)).
  { unfold Ptrofs.divs. change (Ptrofs.signed (Ptrofs.repr 1)) with 1. rewrite Z.quot_1_r. apply Ptrofs.repr_signed. }
  rewrite D. unfold Ptrofs.to_int64. unfold Ptrofs.sub.
  rewrite (Ptrofs.unsigned_repr a), (Ptrofs.unsigned_repr b) by (unfold Ptrofs.max_unsigned; lia).
  apply Int64.eqm_samerepr. unfold Int64.eqm. apply Zbits.eqmod_sym.
  change Int64.modulus with Ptrofs.modulus. apply Ptrofs.eqm_unsigned_repr.
Qed.

Lemma fuel_S: forall F m0 m k, inv_ok F m0 m k -> exists k', k = S k'.
Proof.
  intros F m0 m k I. destruct k as [|k']; [ | eauto].
  exfalso. pose proof (iv_fuel _ _ _ _ I). pose proof (iv_left _ _ _ _ I). simpl in *. lia.
Qed.

(* the facts after a pass *)
Lemma pass_cont: forall F m0 m k m', iter_facts_stmt -> inv_ok F m0 m (S k) ->
  fast_iter lenfix_list distfix_list m = (true, m') -> cont_ok F m0 m' k.
Proof.
  intros F m0 m k m' IFC I E.
  destruct I as [W MD HV LF B IN OU LP FU BU NX INP AO].
  pose proof (mw_nx _ (fast_ok_mwf _ W)) as NXR. pose proof (Zlength_nonneg (m_ow m)) as OWN.
  destruct (IFC m true m' W MD HV LF B E)
    as (I1 & A1 & (N1 & N2) & (B1 & B2) & BB & HL & (O1 & O2) & G).
  destruct (G eq_refl) as (W' & MD' & OW).
  assert (L: floop (K0 m0) m0 =
    (if andb (m_nx m' <? Zlength (m_inp m') - 5) (Zlength (m_ow m') <? m_aout m' - 257)
     then floop k m' else m')).
  { rewrite LP. unfold floop. cbn [fast_loop]. rewrite E. reflexivity. }
  rewrite Nat2Z.inj_succ in FU.
  constructor; [ | | | | | exact L | .. ].
  all: unfold m_left, m_have in *; rewrite ?I1, ?A1; try assumption; try lia.
Qed.

Lemma pass_exit: forall F m0 m k m', iter_facts_stmt -> inv_ok F m0 m (S k) ->
  fast_iter lenfix_list distfix_list m = (false, m') -> exit_ok F m0 m'.
Proof.
  intros F m0 m k m' IFC I E.
  destruct I as [W MD HV LF B IN OU LP FU BU NX INP AO].
  pose proof (mw_nx _ (fast_ok_mwf _ W)) as NXR. pose proof (Zlength_nonneg (m_ow m)) as OWN.
  destruct (IFC m false m' W MD HV LF B E)
    as (I1 & A1 & (N1 & N2) & (B1 & B2) & BB & HL & (O1 & O2) & G).
  assert (L: floop (K0 m0) m0 = m').
  { rewrite LP. unfold floop. cbn [fast_loop]. rewrite E. reflexivity. }
  constructor; [ exact L | .. ].
  all: unfold m_left, m_have in *; rewrite ?I1, ?A1; try assumption; try lia.
Qed.

Lemma body_ok {Espec: OracleKind} (IT: iter_stmt) (IFC: iter_facts_stmt) (F: frame) (m0: mst):
  writable_share (f_shs F) -> readable_share (f_gsh F) ->
  semax Delta_fast (inv_a F m0) s_iter (loop1_ret_assert (cont_a F m0) (normal_ret_assert (exit_a F m0))).
Proof.
  intros SH SG. unfold inv_a.
  apply extract_exists_pre; intro m. apply extract_exists_pre; intro k.
  apply semax_extract_PROP; intro I.
  destruct (fuel_S _ _ _ _ I) as [k' ->].
  pose proof I as I'. destruct I' as [W MD HV LF B IN OU LP FU BU NX INP AO].
  eapply semax_post; [ | | | | apply (IT Espec F m W MD HV LF B IN OU SH SG) ].
  - (* normal: a pass that goes on *)
    unfold fpost, cont_a, fs_state, loop1_ret_assert, normal_ret_assert. cbn [RA_normal app].
    Intros m'. Exists m' k'.
    pose proof (pass_cont F m0 m k' m' IFC I H) as C.
    apply andp_left2. unfold PROPx.
    apply andp_right; [apply prop_right; simpl; auto | apply andp_left2; apply derives_refl].
  - (* break *)
    unfold fpost, exit_a, fs_state, loop1_ret_assert, normal_ret_assert. cbn [RA_break RA_normal app].
    Intros m'. Exists m'.
    pose proof (pass_exit F m0 m k' m' IFC I H) as C.
    apply andp_left2. unfold PROPx.
    apply andp_right; [apply prop_right; simpl; auto | apply andp_left2; apply derives_refl].
  - unfold fpost. cbn [RA_continue]. apply andp_left2. apply FF_left.
  - intros vl. unfold fpost. cbn [RA_return]. apply andp_left2. apply FF_left.
Qed.

Lemma typed_true_if: forall b: bool, typed_true tint (Vint (if b then Int.one else Int.zero)) -> b = true.
Proof. intros [|] H; auto. inversion H. Qed.
Lemma typed_false_if: forall b: bool, typed_false tint (Vint (if b then Int.one else Int.zero)) -> b = false.
Proof. intros [|] H; auto. inversion H. Qed.

Lemma incr_ok {Espec: OracleKind} (F: frame) (m0: mst):
  semax Delta_fast (cont_a F m0) s_incr (loop2_ret_assert (inv_a F m0) (normal_ret_assert (exit_a F m0))).
Proof.
  unfold cont_a.
  apply extract_exists_pre; intro m. apply extract_exists_pre; intro k.
  apply semax_extract_PROP; intro C.
  pose proof C as C'. destruct C' as [W MD B IN OU LP FU BU NX INP AO LEN NXL OW HL BIG].
  pose proof (mw_nx _ (fast_ok_mwf _ W)) as NXR. pose proof (Zlength_nonneg (m_ow m)) as OWN.
  stmt_simpl. unfold fs_locals, fs_sep.
  destruct (f_ib F) as [ | ish ip ilo inn ic] eqn:EIB.
  { exfalso. cbn [in_ok] in IN. rewrite IN, Zlength_nil in LEN. lia. }
  destruct (f_ob F) as [osh op olo onn oc] eqn:EOB.
  destruct IN as (Hish & Hip & Hilo & Hinn & Hic & Himax & Hisub & Hibytes).
  destruct OU as (Hosh & Hop & Holo & Haout & Hlo & Hoc & Homax).
  cbn [in_ptr out_ptr in_rep out_rep].
  abbreviate_semax.
  assert_PROP (field_compatible (tarray tuchar inn) [] ip /\ field_compatible (tarray tuchar onn) [] op) as FC by entailer!.
  destruct FC as [FCi FCo].
  set (c := andb (m_nx m <? Zlength (m_inp m) - 5) (Zlength (m_ow m) <? m_aout m - 257)).
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _t'1 (Vint (if c then Int.one else Int.zero)) :: Q) (SEPx R))) end.
  { test_order_tac. }
  { (* in < last *)
    pose proof (cmp_lt_val inn ip (ilo + m_nx m) (ilo + (Zlength (m_inp m) - 5)) FCi ltac:(lia) ltac:(lia)) as E.
    unfold force_val in E. rewrite E in H. apply typed_true_if in H.
    forward.
    { entailer!. test_order_tac. }
    pose proof (cmp_lt_val onn op (olo + Zlength (m_ow m)) (olo + (m_aout m - 257)) FCo ltac:(lia) ltac:(lia)) as E2.
    assert (EV: force_val (sem_cast tint tbool (eval_binop Olt (tptr tuchar) (tptr tuchar)
                  (offset_val (olo + Zlength (m_ow m)) op) (offset_val (olo + (m_aout m - 257)) op))) =
                Vint (if c then Int.one else Int.zero)).
    { unfold eval_binop, force_val2, sem_binary_operation'. simpl sem_cmp. rewrite E2. subst c.
      replace (m_nx m <? Zlength (m_inp m) - 5) with true by (symmetry; apply Z.ltb_lt; apply Z.ltb_lt in H; lia).
      replace (olo + Zlength (m_ow m) <? olo + (m_aout m - 257)) with (Zlength (m_ow m) <? m_aout m - 257)
        by (destruct (Zlength (m_ow m) <? m_aout m - 257) eqn:Q; symmetry;
            [apply Z.ltb_lt in Q; apply Z.ltb_lt | apply Z.ltb_ge in Q; apply Z.ltb_ge]; lia).
      simpl andb. destruct (Zlength (m_ow m) <? m_aout m - 257); reflexivity. }
    rewrite EV. entailer!. }
  { (* not in < last *)
    pose proof (cmp_lt_val inn ip (ilo + m_nx m) (ilo + (Zlength (m_inp m) - 5)) FCi ltac:(lia) ltac:(lia)) as E.
    unfold force_val in E. rewrite E in H. apply typed_false_if in H.
    forward.
    assert (EV: c = false).
    { subst c. replace (m_nx m <? Zlength (m_inp m) - 5) with false; [reflexivity |].
      symmetry. apply Z.ltb_ge. apply Z.ltb_ge in H. lia. }
    rewrite EV. entailer!. }
  forward_if.
  - (* go on *)
    assert (CT: c = true) by (destruct c; [reflexivity | contradiction]).
    assert (I: inv_ok F m0 m k).
    { pose proof CT as CT'. subst c. apply andb_prop in CT'. destruct CT' as [C1 C2].
      apply Z.ltb_lt in C1. apply Z.ltb_lt in C2.
      constructor; auto; unfold m_have, m_left in *; try lia.
      - rewrite EIB. split; [exact Hish|]. repeat split; auto.
      - rewrite EOB. split; [exact Hosh|]. repeat split; auto.
      - rewrite LP. replace (andb _ _) with true by (symmetry; apply andb_true_intro; split; apply Z.ltb_lt; lia).
        reflexivity. }
    forward. unfold inv_a. Exists m k. unfold fs_locals, fs_sep. rewrite EIB, EOB. cbn [in_ptr out_ptr in_rep out_rep].
    entailer!.
  - (* leave the loop *)
    assert (CF: c = false) by (destruct c; [inversion H | reflexivity]).
    assert (X: exit_ok F m0 m).
    { constructor; auto; try lia.
      - rewrite LP. fold c. rewrite CF. reflexivity.
      - pose proof (mw_bits _ (fast_ok_mwf _ W)). lia.
      - rewrite EIB. split; [exact Hish|]. repeat split; auto.
      - rewrite EOB. split; [exact Hosh|]. repeat split; auto. }
    forward. unfold exit_a. Exists m. unfold fs_locals, fs_sep. rewrite EIB, EOB. cbn [in_ptr out_ptr in_rep out_rep].
    entailer!.
Qed.

Lemma s_loop_eq: s_loop = Sloop s_iter s_incr.
Proof. reflexivity. Qed.

Lemma loop_ok {Espec: OracleKind} (IT: iter_stmt) (IFC: iter_facts_stmt) (F: frame) (m0: mst):
  writable_share (f_shs F) -> readable_share (f_gsh F) ->
  semax Delta_fast (inv_a F m0) s_loop (normal_ret_assert (exit_a F m0)).
Proof.
  intros SH SG. rewrite s_loop_eq.
  apply semax_loop with (Q' := cont_a F m0).
  - apply body_ok; auto.
  - apply incr_ok.
Qed.

Lemma epi_ok {Espec: OracleKind} (F: frame) (m0: mst):
  m_bits m0 < 8 -> 0 <= m_nx m0 -> writable_share (f_shs F) ->
  Zlength (m_inp m0) <= Int.max_signed -> m_aout m0 <= Int.max_signed ->
  semax Delta_fast (exit_a F m0) s_epi
    (frame_ret_assert (function_body_ret_assert tvoid
       (PROP () RETURN () SEP (mem_rep F (fast lenfix_list distfix_list m0)))) (stackframe_of f_inflate_fast)).
Proof.
  intros B0 N0 SHS INR AOR.
  unfold exit_a. Intros m'.
  match goal with H: exit_ok _ _ _ |- _ => rename H into X end.
  pose proof X as X'.
  destruct X' as [LPf B' BU' NX' OW' HL' IN2 OU2 INP' AO' LEN' BIG'].
  assert (FM: fast lenfix_list distfix_list m0 =
    let len := Z.shiftr (m_bits m') 3 in
    let m2 := set_m_nx m' (m_nx m' - len) in
    let bits := m_bits m2 - len * 8 in
    restore (set_m_bits (set_m_hold m2 (m_hold m2 mod 2 ^ bits)) bits)).
  { unfold fast. fold (floop (Z.to_nat (m_aout m0) + 1) m0). change (Z.to_nat (m_aout m0) + 1)%nat with (K0 m0).
    rewrite LPf. reflexivity. }
  clear X LPf.
  assert (INR': Zlength (m_inp m') <= Int.max_signed) by (rewrite INP'; exact INR).
  assert (AOR': m_aout m' <= Int.max_signed) by (rewrite AO'; exact AOR).
  stmt_simpl.
  unfold fs_locals, fs_sep. rewrite rest_mem_pro. unfold strm_m, strm_rep, state_pro.
  destruct (f_ib F) as [ | ish ip ilo inn ic] eqn:EIB.
  { exfalso. cbn [in_ok] in IN2. rewrite IN2, Zlength_nil in LEN'. lia. }
  destruct (f_ob F) as [osh op olo onn oc] eqn:EOB.
  destruct IN2 as (Hish & Hip & Hilo & Hinn & Hic & Himax & Hisub & Hibytes).
  destruct OU2 as (Hosh & Hop & Holo & Haout & Hlo & Hoc & Homax).
  cbn [in_ptr out_ptr in_rep out_rep].
  abbreviate_semax.
  Intros.
  remember (f_gv F inflate.code._zcalloc) as zca eqn:EZA. remember (f_gv F inflate.code._zcfree) as zcf eqn:EZF.
  assert_PROP (field_compatible (tarray tuchar inn) [] ip /\ field_compatible (tarray tuchar onn) [] op) as FC by entailer!.
  destruct FC as [FCi FCo].
  forward.
  rewrite shru3 by rep_lia.
  set (L := Z.shiftr (m_bits m') 3).
  assert (HL: L = m_bits m' / 8) by (subst L; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (HL2: 0 <= L <= m_nx m' - m_nx m0).
  { rewrite HL. split; [apply Z.div_pos; lia |].
    assert (m_bits m' / 8 < m_nx m' - m_nx m0 + 1) by (apply Z.div_lt_upper_bound; lia). lia. }
  assert (HL3: L < 4) by (rewrite HL; apply Z.div_lt_upper_bound; lia).
  forward.
  rewrite ptr_sub_uint' by (auto; rep_lia).
  forward.
  rewrite shl3, sub_repr by lia.
  set (B2 := m_bits m' - L * 8).
  assert (HB2m: B2 = m_bits m' mod 8) by (unfold B2; rewrite HL, Z.mod_eq by lia; lia).
  assert (HB2: 0 <= B2 < 8) by (rewrite HB2m; apply Z.mod_pos_bound; lia).
  forward.
  { entailer!. change (Int.unsigned Int.iwordsize) with 32. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    pose proof (Z.mod_pos_bound (m_bits m') 8 ltac:(lia)) as MB. rewrite Z.mod_eq in MB by lia. lia. }
  assert (P2: 1 <= 2 ^ B2 <= 128).
  { pose proof (Z.pow_pos_nonneg 2 B2 ltac:(lia) ltac:(lia)). split; [lia |].
    change 128 with (2^7). apply Z.pow_le_mono_r; lia. }
  rewrite mask_eq by lia. rewrite Int.unsigned_repr by rep_lia. rewrite land_mask by (auto; lia).
  forward. forward.
  set (NX2 := m_nx m' - L).
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _t'45 (Vlong (Int64.repr (Zlength (m_inp m') - NX2))) :: Q) (SEPx R))) end.
  { test_order_tac. }
  { forward.
    { entailer!. erewrite (sub_pp_val _ ip) by (eauto; lia).
      apply andp_right; apply prop_right.
      - rewrite Int64.signed_repr by rep_lia. rep_lia.
      - rewrite sameblock_offset_val by auto. exact I. }
    entailer!. erewrite (sub_pp_val _ ip) by (eauto; lia). simpl. f_equal.
    change (Int.signed (Int.repr 5)) with 5. rewrite add64_repr. f_equal. unfold NX2. lia. }
  { forward.
    { entailer!. erewrite (sub_pp_val _ ip) by (eauto; lia).
      apply andp_right; apply prop_right.
      - rewrite Int64.signed_repr by rep_lia. rep_lia.
      - rewrite sameblock_offset_val by auto. exact I. }
    entailer!. erewrite (sub_pp_val _ ip) by (eauto; lia). simpl. f_equal.
    change (Int.signed (Int.repr 5)) with 5. rewrite sub64_repr. f_equal. unfold NX2. lia. }
  forward.
  pose proof (Zlength_nonneg (m_ow m')) as OWN.
  set (OW2 := Zlength (m_ow m')).
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _t'46 (Vlong (Int64.repr (m_aout m' - OW2))) :: Q) (SEPx R))) end.
  { entailer!. test_order_tac. }
  { forward.
    { entailer!. erewrite (sub_pp_val _ op) by (eauto; lia).
      apply andp_right; apply prop_right.
      - rewrite Int64.signed_repr by rep_lia. rep_lia.
      - rewrite sameblock_offset_val by auto. exact I. }
    entailer!. erewrite (sub_pp_val _ op) by (eauto; lia). simpl. f_equal.
    change (Int.signed (Int.repr 257)) with 257. rewrite add64_repr. f_equal. lia. }
  { forward.
    { entailer!. erewrite (sub_pp_val _ op) by (eauto; lia).
      apply andp_right; apply prop_right.
      - rewrite Int64.signed_repr by rep_lia. rep_lia.
      - rewrite sameblock_offset_val by auto. exact I. }
    entailer!. erewrite (sub_pp_val _ op) by (eauto; lia). simpl. f_equal.
    change (Int.signed (Int.repr 257)) with 257. rewrite sub64_repr. f_equal. lia. }
  forward. forward. forward. forward.
  rewrite FM. cbv zeta. rewrite mem_rep_fs, rest_mem_pro. unfold strm_m, strm_rep, state_pro.
  rewrite EIB, EOB. unfold restore, upd_s.
  cbn [m_s m_h m_inp m_aout m_nx m_ow m_hold m_bits m_tin m_tout m_snx m_sow m_msg m_adler set_m_s set_m_nx
       set_m_bits set_m_hold set_m_snx set_m_sow in_ptr out_ptr in_rep out_rep i_wsize i_whave i_wnext i_win
       i_hold i_bits i_lencode i_distcode i_lenbits i_distbits set_i_bits set_i_hold].
  match goal with |- context [rest_pro F (set_m_s ?x ?y)] =>
    replace (rest_pro F (set_m_s x y)) with (rest_pro F m') by reflexivity end.
  match goal with |- context [tab_mem F (set_i_bits ?x ?y)] =>
    replace (tab_mem F (set_i_bits x y)) with (tab_mem F (m_s m')) by reflexivity end.
  match goal with |- context [win_rep ?w (set_i_bits ?x ?y)] =>
    replace (win_rep w (set_i_bits x y)) with (win_rep w (m_s m')) by reflexivity end.
  unfold NX2, OW2 in *. rewrite !Int64.Z_mod_modulus_eq, !Z.mod_small by rep_lia.
  replace (ilo + m_nx m' - Z.shiftr (m_bits m') 3) with (ilo + (m_nx m' - Z.shiftr (m_bits m') 3)) by lia.
  cancel.
Qed.

Lemma fast_main (IT: iter_stmt) (IFC: iter_facts_stmt):
  semax_body Vprog_fast Gprog_fast f_inflate_fast inflate_fast_spec3.
Proof.
  start_function.
  assert (DS: tycontext_sub Delta_fast Delta).
  { unfold tycontext_sub. split.
    { intro id. replace (temp_types Delta) with (temp_types Delta_fast) by reflexivity.
      destruct (Maps.PTree.get id (temp_types Delta_fast)); auto. }
    split. { intro id. replace (var_types Delta) with (var_types Delta_fast) by reflexivity. reflexivity. }
    split. { reflexivity. }
    split. { intro id. replace (glob_types Delta) with (glob_types Delta_fast) by reflexivity.
             destruct (Maps.PTree.get id (glob_types Delta_fast)); simpl; auto. }
    split. { intro id. unfold Delta_fast. simpl. auto. }
    { intro id. replace (annotations Delta) with (annotations Delta_fast) by reflexivity.
      destruct (Maps.PTree.get id (annotations Delta_fast)) as [a|]; simpl; auto. destruct a; auto. } }
  rename H into W, H0 into MD, H1 into SNX, H2 into SOW, H3 into HH, H4 into HB, H5 into HV, H6 into LF,
    H7 into B8, H8 into OUTEQ, H9 into IN, H10 into OU, SH into SHS, SH0 into SHG.
  rewrite mem_rep_fs, rest_mem_pro.
  unfold strm_m, strm_rep, state_pro.
  pose proof (mw_nx _ (fast_ok_mwf _ W)) as NXR. pose proof (Zlength_nonneg (m_ow m)) as OWN.
  pose proof (mw_s _ (fast_ok_mwf _ W)) as SW.
  pose proof IN as IN'. pose proof OU as OU'.
  destruct (f_ib F) as [ | ish ip ilo inn ic] eqn:EIB.
  { exfalso. cbn [in_ok] in IN. unfold m_have in HV. rewrite IN, Zlength_nil in HV. lia. }
  destruct (f_ob F) as [osh op olo onn oc] eqn:EOB.
  destruct IN as (Hish & Hip & Hilo & Hinn & Hic & Himax & Hisub & Hibytes).
  destruct OU as (Hosh & Hop & Holo & Haout & Hlo & Hoc & Homax).
  cbn [in_ptr out_ptr].
  Intros.
  remember (f_gv F inflate.code._zcalloc) as zca eqn:EZA. remember (f_gv F inflate.code._zcfree) as zcf eqn:EZF.
  assert_PROP (isptr (f_sp F)) as SPP by entailer!.
  assert_PROP (is_pointer_or_null (if i_win (m_s m) then f_winp F else nullval)) by entailer!.
  assert_PROP (forall t, tref_ok t -> is_pointer_or_null (tref_val (f_gv F) (f_sp F) t)) as TP by entailer!.
  pose proof (TP _ (sw_lencode _ SW)) as TPL. pose proof (TP _ (sw_distcode _ SW)) as TPD.
  forward. forward. forward. forward. forward. forward. forward. forward.
  forward. forward. forward. forward. forward. forward. forward. forward.
  forward. forward. forward.
  forward.
  { entailer!. pose proof (sw_lenbits _ SW). rewrite Int.unsigned_repr by rep_lia.
    change (Int.unsigned Int.iwordsize) with 32. lia. }
  forward.
  forward.
  { entailer!. pose proof (sw_distbits _ SW). rewrite Int.unsigned_repr by rep_lia.
    change (Int.unsigned Int.iwordsize) with 32. lia. }
  unfold MORE_COMMANDS, abbreviate.
  pose proof (mw_inp _ (fast_ok_mwf _ W)) as INPR. pose proof (mw_aout _ (fast_ok_mwf _ W)) as AOR.
  unfold m_have, m_left in HV, LF.
  rewrite (ptr_add_uint ip (ilo + m_snx m) (Zlength (m_inp m) - m_snx m) 5) by (auto; rep_lia).
  rewrite (ptr_sub_uint op (olo + m_sow m) (m_out m) (m_aout m - m_sow m)) by (auto; rep_lia).
  rewrite (ptr_add_uint op (olo + m_sow m) (m_aout m - m_sow m) 257) by (auto; rep_lia).
  assert (I0: inv_ok F m m (K0 m)).
  { constructor; auto; unfold m_have, m_left; try lia.
    - rewrite EIB. exact IN'.
    - rewrite EOB. exact OU'.
    - unfold K0. rewrite Nat2Z.inj_add, Z2Nat.id by lia. simpl. lia. }
  eapply semax_seq'.
  { eapply semax_pre; [ | apply (semax_Delta_subsumption _ _ _ _ _ DS (loop_ok IT IFC F m SHS SHG)) ].
    unfold inv_a. Exists m (K0 m). unfold fs_locals, fs_sep. rewrite rest_mem_pro.
    unfold strm_m, strm_rep, state_pro. rewrite EIB, EOB. cbn [in_ptr out_ptr in_rep out_rep].
    rewrite <- EZA, <- EZF.
    entailer!.
    pose proof (sw_lenbits _ SW). pose proof (sw_distbits _ SW).
    rewrite !mask_eq by lia.
    split; [f_equal; lia |]. split; [f_equal; lia |]. split; [f_equal; lia |]. auto. }
  unfold POSTCONDITION, abbreviate.
  eapply semax_Delta_subsumption; [exact DS |].
  apply epi_ok; [exact B8 | apply NXR | exact SHS | apply INPR | apply AOR].
Qed.
