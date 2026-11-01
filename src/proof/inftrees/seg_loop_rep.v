(* Part sl_rep of the main loop of inflate_table (seg_loop_defs.v). *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inftrees.
Require Import Zlib.inftrees.code.
Require Import Zlib.proof.inftrees.seg_loop_defs.

#[local] Existing Instance Inftrees.CS.

Lemma sl_rep_shl1 k : 0 <= k < 32 -> Int.shl (Int.repr 1) (Int.repr k) = Int.repr (2 ^ k).
Proof.
intros. unfold Int.shl. rewrite !Int.unsigned_repr by rep_lia.
rewrite Z.shiftl_1_l. reflexivity.
Qed.

Lemma sl_rep_znth_bound (l: list Z) lo hi i : lo <= 0 <= hi -> Forall (fun x => lo <= x <= hi) l ->
  lo <= Znth i l <= hi.
Proof.
intros B F. destruct (zlt i 0); [rewrite Znth_outofbounds by lia; unfold default, Inhabitant_Z; lia | ].
destruct (zle (Zlength l) i); [rewrite Znth_outofbounds by lia; unfold default, Inhabitant_Z; lia | ].
eapply Forall_forall in F; [exact F | apply Znth_In; lia].
Qed.

Lemma sl_rep_entry_ok type sy bits : 0 <= sy <= 65535 -> 0 <= bits <= 255 ->
  entry_ok (sym_entry type sy bits).
Proof.
intros S B. unfold sym_entry, entry_ok.
destruct (sy + 1 <? match_of type); [cbn; lia | ].
destruct (match_of type <=? sy); [ | cbn; lia].
cbn [e_op e_bits e_val].
assert (Forall (fun x => 0 <= x <= 255) (extra_of type)).
{ unfold extra_of; repeat destruct (_ =? _); repeat constructor; lia. }
assert (Forall (fun x => 0 <= x <= 65535) (base_of type)).
{ unfold base_of; repeat destruct (_ =? _); repeat constructor; lia. }
split; [apply sl_rep_znth_bound; auto; lia | split; [lia | apply sl_rep_znth_bound; auto; lia]].
Qed.

Lemma sl_rep_split sh n k (v: list (reptype code_t)) p : 0 <= k <= n -> Zlength v = n ->
  field_compatible (tarray code_t n) [] p ->
  data_at sh (tarray code_t n) v p =
  (data_at sh (tarray code_t k) (sublist 0 k v) p *
   data_at sh (tarray code_t (n - k)) (sublist k n v) (offset_val (4 * k) p))%logic.
Proof.
intros K L FC.
rewrite (split2_data_at_Tarray sh code_t n k v v (sublist 0 k v) (sublist k n v)) by list_solve.
rewrite (field_address0_offset (tarray code_t n)) by auto with field_compatible.
reflexivity.
Qed.

Lemma sl_rep_ze8 x : 0 <= x < 256 -> Int.zero_ext 8 (Int.repr x) = Int.repr x.
Proof. intros. apply zero_ext_inrange. rewrite Int.unsigned_repr by rep_lia. simpl. lia. Qed.

Lemma sl_rep_ze16 x : 0 <= x < 65536 -> Int.zero_ext 16 (Int.repr x) = Int.repr x.
Proof. intros. apply zero_ext_inrange. rewrite Int.unsigned_repr by rep_lia. simpl. lia. Qed.

Lemma sl_rep_idx hf d k : 0 <= hf <= Int.max_unsigned -> 0 <= d < 32 -> 0 <= k ->
  Z.shiftr hf d + k <= Int.max_unsigned ->
  Int.unsigned (Int.add (Int.shru (Int.repr hf) (Int.repr d)) (Int.repr k)) = Z.shiftr hf d + k.
Proof.
intros. unfold Int.shru. rewrite !Int.unsigned_repr by rep_lia.
assert (0 <= Z.shiftr hf d) by (apply Z.shiftr_nonneg; lia).
rewrite add_repr. apply Int.unsigned_repr. lia.
Qed.

Lemma sl_rep_join sh n k i (t: list entry) e p :
  field_compatible (tarray code_t n) [] p -> Zlength t = n -> 0 <= k -> 0 <= i -> k + i < n ->
  (data_at sh (tarray code_t k) (sublist 0 k (map entry_rep t)) p *
   data_at sh (tarray code_t (n - k)) (upd_Znth i (sublist k n (map entry_rep t)) (entry_rep e))
     (offset_val (4 * k) p))%logic
  |-- data_at sh (tarray code_t n) (map entry_rep (upd_Znth (k + i) t e)) p.
Proof.
intros FC L K I N.
rewrite (sl_rep_split sh n k (map entry_rep (upd_Znth (k + i) t e)) p) by (auto; list_solve).
apply derives_refl'. f_equal; f_equal; list_solve.
Qed.

Lemma sl_rep_ok : loop_facts -> sl_rep_stmt.
Proof.
intros LF Espec X s WF.
destruct LF as (SSO & ROO & RKO & _).
destruct X as [type lens req old gv shg shl sh pl pw ptab pt pb vh vc vo].
unfold it_wf in WF; cbn [c_type c_lens c_req c_old c_gv c_shg c_shl c_sh c_pl c_pw c_ptab c_pt c_pb c_here c_count c_offs] in WF.
destruct WF as (SHg & SHl & SH & IN & OLD & CAP).
unfold SL_here, SL_rep, sl_t1, here_, sl_props, sl_locs, sl_K, sl_sep, params_locs, count_at, work_sorted,
  sl_here_e, base_v, extra_v, it_mx, it_root;
cbn [c_type c_lens c_req c_old c_gv c_shg c_shl c_sh c_pl c_pw c_ptab c_pt c_pb c_here c_count c_offs].
unfold Delta_it. simplify_func_tycontext.
unfold sl_rep.
abbreviate_semax.
Intros.
assert (AO: acc_ok type lens req (Zlength old)) by (unfold acc_ok; auto).
destruct (RKO _ _ _ _ _ _ AO H2) as (IT & SK).
destruct IT as (IS & IL & ID & IC & IH & IN0 & INU & IU & IU2 & ILO & ICN & ICF & IC1 & ITL).
forward.
{ entailer!. change (Int.unsigned Int.iwordsize) with 32. lia. }
rewrite Int.sub_signed, !Int.signed_repr, sl_rep_shl1 by rep_lia.
forward.
{ entailer!. change (Int.unsigned Int.iwordsize) with 32. lia. }
rewrite sl_rep_shl1 by rep_lia.
forward.
set (e := sym_entry type (Znth (s_sym s) (sorted_syms lens)) (s_len s - s_drop s)).
set (I := 2 ^ (s_len s - s_drop s)).
set (nn := 2 ^ (s_curr s - (s_len s - s_drop s))).
set (b := s_next s + Z.shiftr (s_huff s) (s_drop s)).
set (FIN := rep_fill (s_tab s) b I (Z.to_nat nn) e).
assert (FI: 2 ^ s_curr s = nn * I).
{ unfold nn, I. rewrite <- Z.pow_add_r by lia. f_equal. lia. }
assert (I1: 1 <= I) by (unfold I; pose proof (Z.pow_pos_nonneg 2 (s_len s - s_drop s)); lia).
assert (N1: 1 <= nn) by (unfold nn; pose proof (Z.pow_pos_nonneg 2 (s_curr s - (s_len s - s_drop s))); lia).
match goal with |- semax _ (PROPx _ (LOCALx (?Lmin :: _ :: ?Q) (SEPx (?R0 :: ?R1 :: ?R2 :: ?R3 :: ?R4 :: ?R5 :: _ :: ?R)))) _ _ =>
forward_loop (EX m: Z, EX t: list entry,
  PROPx [1 <= m <= nn; Zlength t = Zlength old; rep_fill t b I (Z.to_nat m) e = FIN]
  (LOCALx (Lmin :: temp _fill (Vint (Int.repr (m * I))) :: Q)
  (SEPx (R0 :: R1 :: R2 :: R3 :: R4 :: R5 :: data_at sh (tarray code_t (Zlength old)) (map entry_rep t) pt :: R))))%assert
 continue: (EX m: Z, EX t: list entry,
  PROPx [0 <= m < nn; Zlength t = Zlength old; rep_fill t b I (Z.to_nat m) e = FIN]
  (LOCALx (Lmin :: temp _fill (Vint (Int.repr (m * I))) :: Q)
  (SEPx (R0 :: R1 :: R2 :: R3 :: R4 :: R5 :: data_at sh (tarray code_t (Zlength old)) (map entry_rep t) pt :: R))))%assert
 break: (PROPx []
  (LOCALx (Lmin :: Q)
  (SEPx (R0 :: R1 :: R2 :: R3 :: R4 :: R5 :: data_at sh (tarray code_t (Zlength old)) (map entry_rep FIN) pt :: R))))
end.
- rewrite FI. Exists nn (s_tab s). entailer!.
- Intros m t.
  forward.
  rewrite sub_repr. replace (m * I - I) with ((m - 1) * I) by ring.
  assert (HH: 0 <= Z.shiftr (s_huff s) (s_drop s) < I).
  { rewrite Z.shiftr_div_pow2 by lia. rewrite Z.shiftl_1_l in IH. split; [apply Z.div_pos; lia | ].
    apply Z.div_lt_upper_bound; [lia | ]. unfold I.
    replace (2 ^ s_drop s * 2 ^ (s_len s - s_drop s)) with (2 ^ s_len s). lia.
    rewrite <- Z.pow_add_r by lia. f_equal; lia. }
  assert (F15: nn * I <= 32768) by (rewrite <- FI; change 32768 with (2^15); apply Z.pow_le_mono_r; lia).
  rewrite Z.shiftl_1_l in INU.
  assert (EOK: entry_ok e).
  { destruct IN as (TY & NC & LR & RQ). destruct (SSO lens LR) as (SL & SF).
    assert (SY: 0 <= Znth (s_sym s) (sorted_syms lens) < Zlength lens).
    { eapply Forall_forall in SF; [apply SF | apply Znth_In; lia]. }
    assert (MC: max_codes type <= 288) by (unfold max_codes; repeat (destruct (_ =? _)); lia).
    apply sl_rep_entry_ok; lia. }
  set (h := Z.shiftr (s_huff s) (s_drop s)) in *.
  assert_PROP (field_compatible (tarray code_t (Zlength old)) [] pt) as FC by entailer!.
  rewrite (sl_rep_split sh (Zlength old) (s_next s)) by (try list_solve; lia).
  Intros.
  destruct EOK as (EO & EB & EV).
  change (entry_rep e) with (Vint (Int.repr (e_op e)), (Vint (Int.repr (e_bits e)), Vint (Int.repr (e_val e)))).
  assert (IDX: Int.unsigned (Int.add (Int.shru (Int.repr (s_huff s)) (Int.repr (s_drop s)))
                                     (Int.repr ((m - 1) * I))) = h + (m - 1) * I).
  { rewrite Z.shiftl_1_l in IH. apply sl_rep_idx; try lia.
    - assert (2 ^ s_len s <= 2 ^ 15) by (apply Z.pow_le_mono_r; lia). rep_lia.
    - apply Z.mul_nonneg_nonneg; lia.
    - fold h. assert ((m - 1) * I <= (nn - 1) * I) by (apply Z.mul_le_mono_nonneg_r; lia). rep_lia. }
  assert (IB: 0 <= h + (m - 1) * I < 2 ^ s_curr s).
  { assert ((m - 1) * I <= (nn - 1) * I) by (apply Z.mul_le_mono_nonneg_r; lia).
    assert (0 <= (m - 1) * I) by (apply Z.mul_nonneg_nonneg; lia). lia. }
  forward.
  { entailer!. rep_lia. }
  forward.
  { entailer!. change (Int.unsigned Int.iwordsize) with 32. lia. }
  rewrite IDX.
  forward.
  { entailer!. rep_lia. }
  forward.
  { entailer!. change (Int.unsigned Int.iwordsize) with 32. lia. }
  rewrite IDX.
  forward.
  { entailer!. rep_lia. }
  forward.
  { entailer!. change (Int.unsigned Int.iwordsize) with 32. lia. }
  rewrite IDX.
  set (L := sublist (s_next s) (Zlength old) (map entry_rep t)).
  assert (LL: Zlength L = Zlength old - s_next s) by (unfold L; list_solve).
  assert (II: 0 <= h + (m-1)*I < Zlength L) by lia.
  rewrite !upd_Znth_same by (rewrite ?Zlength_upd_Znth; exact II).
  rewrite !upd_Znth_twice by (rewrite ?Zlength_upd_Znth; exact II).
  cbn [fst snd].
  rewrite sl_rep_ze8, sl_rep_ze8, sl_rep_ze16 by lia.
  change (Vint (Int.repr (e_op e)), (Vint (Int.repr (e_bits e)), Vint (Int.repr (e_val e)))) with (entry_rep e).
  unfold L. sep_apply (sl_rep_join sh (Zlength old) (s_next s) (h + (m - 1) * I) t e pt FC H4); try lia.
  Exists (m - 1) (upd_Znth (s_next s + (h + (m - 1) * I)) t e).
  entailer!.
  split; [rewrite Zlength_upd_Znth; exact H4 | ].
  rewrite <- H5. replace (Z.to_nat m) with (S (Z.to_nat (m - 1))) by lia.
  cbn [rep_fill].
  replace (b + Z.of_nat (Z.to_nat (m - 1)) * I) with (s_next s + (h + (m - 1) * I))
    by (rewrite Z2Nat.id by lia; unfold b; ring).
  reflexivity.
- Intros m t. forward_if.
  + forward.
    assert (M0: m <> 0) by (intro; subst m; apply H6; reflexivity).
    Exists m t. entailer!.
  + forward.
    destruct (sl_R _) as [rn rb rc rr]; cbv iota beta; simpl_ret_assert.
    assert (F15: nn * I <= 32768) by (rewrite <- FI; change 32768 with (2^15); apply Z.pow_le_mono_r; lia).
    assert (0 <= m * I <= nn * I) by nia.
    apply repr_inj_unsigned in H6; [ | rep_lia | rep_lia].
    assert (M0: m = 0) by nia.
    subst m. simpl in H5. subst t. entailer!.
- unfold POSTCONDITION, abbreviate. simpl_ret_assert.
  destruct (sl_R _) as [rn rb rc rr]; cbv iota beta; cbn [RA_normal].
  assert (FE: rep_fill (s_tab s) (s_next s + Z.shiftr (s_huff s) (s_drop s)) (Z.shiftl 1 (s_len s - s_drop s))
     (Z.to_nat (Z.shiftl 1 (s_curr s) / Z.shiftl 1 (s_len s - s_drop s))) e = FIN).
  { rewrite !Z.shiftl_1_l. fold I. rewrite FI, Z.div_mul by lia. reflexivity. }
  fold e. rewrite FE.
  entailer!.
  rewrite !Z.shiftl_1_l in *. auto.
Qed.
