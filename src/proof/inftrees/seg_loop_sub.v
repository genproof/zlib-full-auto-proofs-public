(* Part sl_sub of the main loop of inflate_table (seg_loop_defs.v). *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inftrees.
Require Import Zlib.inftrees.code.
Require Import Zlib.proof.inftrees.seg_loop_defs.

#[local] Existing Instance Inftrees.CS.
#[local] Arguments counts : simpl never.

(* The values of a new sub-table (model.v step). *)
Definition sl_d' (X: itctx) (s: state) : Z := st_drop' (it_root X) s.
Definition sl_c' (X: itctx) (s: state) : Z :=
  sub_bits (st_len' (c_lens X) s) (sl_d' X s) (it_mx X) (st_cnt' s).
Definition sl_u' (X: itctx) (s: state) : Z := s_used s + Z.shiftl 1 (sl_c' X s).
Definition sl_n' (X: itctx) (s: state) : Z := s_next s + Z.shiftl 1 (s_curr s).
Definition sl_l' (X: itctx) (s: state) : Z := Z.land (st_huff' s) (Z.shiftl 1 (it_root X) - 1).

Definition sl_cond (X: itctx) (s: state) : bool :=
  ((it_root X <? st_len' (c_lens X) s) && negb (sl_l' X s =? s_low s))%bool.

Lemma sl_sub_step_nosub (X: itctx) s :
  ~ (st_c s = 0 /\ s_len s = it_mx X) -> sl_cond X s = false ->
  step (c_type X) (c_lens X) (sorted_syms (c_lens X)) (it_root X) (it_mx X) s =
  Continue (mkSt (st_huff' s) (s_sym s + 1) (st_len' (c_lens X) s) (s_curr s) (s_drop s) (s_low s)
                 (s_used s) (s_next s) (st_cnt' s) (sl_t1 X s)).
Proof.
intros NB C.
unfold sl_cond, sl_l', st_len', st_huff', st_cnt', st_c, sl_t1, sl_here_e in *.
unfold step; cbv zeta.
destruct ((Znth (s_len s) (s_cnt s) - 1 =? 0) && (s_len s =? it_mx X))%bool eqn:E.
{ exfalso; apply NB; apply andb_prop in E; destruct E; split; lia. }
rewrite C. reflexivity.
Qed.

Lemma sl_sub_step_sub (X: itctx) s :
  ~ (st_c s = 0 /\ s_len s = it_mx X) -> sl_cond X s = true ->
  step (c_type X) (c_lens X) (sorted_syms (c_lens X)) (it_root X) (it_mx X) s =
  if over (c_type X) (sl_u' X s) then
    Full (mkSt (st_huff' s) (s_sym s + 1) (st_len' (c_lens X) s) (sl_c' X s) (sl_d' X s) (s_low s)
               (sl_u' X s) (sl_n' X s) (st_cnt' s) (sl_t1 X s))
  else
    Continue (mkSt (st_huff' s) (s_sym s + 1) (st_len' (c_lens X) s) (sl_c' X s) (sl_d' X s) (sl_l' X s)
               (sl_u' X s) (sl_n' X s) (st_cnt' s)
               (upd_Znth (sl_l' X s) (sl_t1 X s) (mkE (sl_c' X s) (it_root X) (sl_n' X s)))).
Proof.
intros NB C.
unfold sl_cond, sl_u', sl_c', sl_d', sl_n', sl_l', st_drop', st_len', st_huff', st_cnt', st_c, sl_t1, sl_here_e in *.
unfold step; cbv zeta.
destruct ((Znth (s_len s) (s_cnt s) - 1 =? 0) && (s_len s =? it_mx X))%bool eqn:E.
{ exfalso; apply NB; apply andb_prop in E; destruct E; split; lia. }
rewrite C. reflexivity.
Qed.

Lemma sl_sub_bincr_nonneg k huff incr : 0 <= incr -> 0 <= bincr_loop k huff incr.
Proof.
revert incr. induction k; intros incr H; simpl; [lia | ].
destruct (Z.land huff incr =? 0); [lia | ]. apply IHk. apply Z.shiftr_nonneg. lia.
Qed.

Lemma sl_sub_huff_nonneg s : 0 <= s_huff s -> 1 <= s_len s -> 0 <= st_huff' s.
Proof.
intros H L. unfold st_huff', next_huff.
assert (0 <= bincr_loop 16 (s_huff s) (Z.shiftl 1 (s_len s - 1))).
{ apply sl_sub_bincr_nonneg. rewrite Z.shiftl_1_l. apply Z.pow_nonneg. lia. }
destruct (_ =? 0) eqn:E; [lia | ].
apply Z.eqb_neq in E.
assert (0 <= Z.land (s_huff s) (bincr_loop 16 (s_huff s) (Z.shiftl 1 (s_len s - 1)) - 1))
  by (apply Z.land_nonneg; lia).
lia.
Qed.

Lemma sl_sub_land_mod a r : 0 <= r -> Z.land a (Z.shiftl 1 r - 1) = a mod 2 ^ r.
Proof.
intros. rewrite Z.shiftl_1_l. replace (2 ^ r - 1) with (Z.ones r) by (rewrite Z.ones_equiv; lia).
apply Z.land_ones; lia.
Qed.

Lemma sl_sub_addp p n m : isptr p -> 0 <= m <= Int.max_unsigned ->
  force_val (sem_binary_operation' Oadd (tptr (Tstruct ___gp_code noattr)) tuint
     (offset_val (4 * n) p) (Vint (Int.repr m))) = offset_val (4 * (n + m)) p.
Proof.
intros. destruct p; try contradiction. simpl. unfold sem_add_ptr_int. simpl.
f_equal. rewrite Ptrofs.add_assoc. f_equal. unfold Ptrofs.of_intu, Ptrofs.of_int.
rewrite (Int.unsigned_repr m) by lia. rewrite ptrofs_mul_repr, ptrofs_add_repr. f_equal. lia.
Qed.

Lemma sl_sub_zs (l: list Z) i : 0 <= i < Zlength l -> Znth i (zs_rep l) = Vint (Int.repr (Znth i l)).
Proof. intros. unfold zs_rep. rewrite Znth_map by lia. reflexivity. Qed.

Lemma sl_sub_cnt_ok s : Zlength (s_cnt s) = 16 -> Forall (fun c => 0 <= c <= 288) (s_cnt s) ->
  1 <= Znth (s_len s) (s_cnt s) -> 0 <= s_len s < 16 ->
  Zlength (st_cnt' s) = 16 /\ Forall (fun c => 0 <= c <= 288) (st_cnt' s).
Proof.
intros Z F C L. unfold st_cnt', st_c. split.
- rewrite Zlength_upd_Znth; auto.
- apply Forall_upd_Znth; auto.
  rewrite Forall_Znth in F. specialize (F (s_len s) ltac:(lia)). cbv beta in F. lia.
Qed.

(* One round of the sub-table size loop. *)
Lemma sl_sub_loop_step k curr drop mx left cnt :
  curr + drop < mx -> 0 < left - Znth (curr + drop) cnt ->
  sub_loop (S k) curr drop mx left cnt = sub_loop k (curr + 1) drop mx (2 * (left - Znth (curr + drop) cnt)) cnt.
Proof.
intros A B. cbn [sub_loop]. rewrite (proj2 (Z.ltb_lt _ _) A).
rewrite (proj2 (Z.leb_gt _ _) B). reflexivity.
Qed.

Lemma sl_sub_loop_exit k curr drop mx left cnt :
  mx <= curr + drop -> sub_loop (S k) curr drop mx left cnt = curr.
Proof. intros A. cbn [sub_loop]. rewrite (proj2 (Z.ltb_ge _ _) A). reflexivity. Qed.

Lemma sl_sub_loop_brk k curr drop mx left cnt :
  curr + drop < mx -> left - Znth (curr + drop) cnt <= 0 -> sub_loop (S k) curr drop mx left cnt = curr.
Proof.
intros A B. cbn [sub_loop]. rewrite (proj2 (Z.ltb_lt _ _) A).
rewrite (proj2 (Z.leb_le _ _) B). reflexivity.
Qed.

Lemma sl_sub_loop_ge k curr drop mx left cnt : curr <= sub_loop k curr drop mx left cnt.
Proof.
revert curr left. induction k; intros curr left; cbn [sub_loop]; [lia | ].
destruct (curr + drop <? mx); [ | lia].
destruct (left - Znth (curr + drop) cnt <=? 0); [lia | ].
specialize (IHk (curr + 1) (2 * (left - Znth (curr + drop) cnt))). lia.
Qed.

(* return 1: the model's result is REnough of the table after the replicate loop. *)
Lemma sl_sub_model (X: itctx) s k :
  acc_ok (c_type X) (c_lens X) (c_req X) (Zlength (c_old X)) ->
  reach (c_type X) (c_lens X) (c_req X) (c_old X) k s ->
  reach_final_stmt ->
  ~ (st_c s = 0 /\ s_len s = it_mx X) -> sl_cond X s = true -> over (c_type X) (sl_u' X s) = true ->
  it_model X = REnough (sl_t1 X s).
Proof.
intros AO R RF NB C O.
pose proof (sl_sub_step_sub X s NB C) as ST. rewrite O in ST.
pose proof (RF _ _ _ _ _ _ AO R _ ST I) as RN.
destruct AO as (_ & _ & MX & (lft & LF & T) & OV).
unfold it_model, inflate_table_model.
replace (maxlen (c_lens X) =? 0) with false by lia.
rewrite LF, T. unfold it_root, it_mx in *. rewrite OV, RN. reflexivity.
Qed.

(* The root table fits in the table (LENS / DISTS). *)
Lemma sl_sub_root_cap type lens req cap :
  type <> CODES -> 0 <= type <= 2 -> cap_ok type lens req cap -> over type (Z.shiftl 1 (root_of req lens)) = false ->
  Z.shiftl 1 (root_of req lens) <= cap.
Proof.
intros NC T (_ & CL & CD) O. unfold over, CODES, LENS, DISTS, ENOUGH_LENS, ENOUGH_DISTS in *.
assert (type = 1 \/ type = 2) as [-> | ->] by lia; cbn in O.
- rewrite ?orb_false_r in O. apply Z.ltb_ge in O. specialize (CL eq_refl). lia.
- rewrite ?orb_false_r in O. apply Z.ltb_ge in O. specialize (CD eq_refl). lia.
Qed.

Lemma sl_sub_ltb a b : bool2val (zlt a b) = Vint (Int.repr (Z.b2z (a <? b))).
Proof.
destruct (zlt a b) as [Hl|Hl].
- rewrite (proj2 (Z.ltb_lt _ _) Hl). reflexivity.
- rewrite (proj2 (Z.ltb_ge a b) ltac:(lia)). reflexivity.
Qed.

Lemma sl_sub_ze8 x : 0 <= x < 256 -> Int.zero_ext 8 (Int.repr x) = Int.repr x.
Proof. intros. apply zero_ext_inrange. rewrite Int.unsigned_repr by rep_lia. simpl. lia. Qed.

Lemma sl_sub_ze16 x : 0 <= x < 65536 -> Int.zero_ext 16 (Int.repr x) = Int.repr x.
Proof. intros. apply zero_ext_inrange. rewrite Int.unsigned_repr by rep_lia. simpl. lia. Qed.

(* (ushort)(next - *table) *)
Lemma sl_sub_subpp p n : isptr p -> 0 <= n <= 32768 ->
  force_val (sem_cast_i2i I16 Unsigned (force_val (sem_cast_l2i I16 Unsigned
    (force_val (sem_sub_pp (Tstruct ___gp_code noattr) (offset_val (4 * n) p) p))))) = Vint (Int.repr n).
Proof.
intros P N. destruct p; try contradiction. unfold sem_sub_pp. simpl. rewrite if_true by auto. simpl.
rewrite Ptrofs.sub_add_l, Ptrofs.sub_idem, Ptrofs.add_zero_l.
unfold Ptrofs.divs. rewrite !Ptrofs.signed_repr by rep_lia.
replace (Z.quot (4 * n) 4) with n by (rewrite Z.mul_comm, Z.quot_mul; lia).
rewrite Ptrofs.unsigned_repr by rep_lia. rewrite Int64.Z_mod_modulus_eq, Z.mod_small by rep_lia.
rewrite !sl_sub_ze16 by lia. reflexivity.
Qed.

Lemma sl_sub_rep_fill_len (t: list entry) b i n e : Zlength (rep_fill t b i n e) = Zlength t.
Proof.
revert t. induction n; intros t; simpl; [reflexivity | ].
rewrite IHn. apply Zlength_upd_Znth.
Qed.

Lemma sl_sub_R (X: itctx) : sl_R X =
  {| RA_normal := (EX s: state, A_loop X s)%argsassert; RA_break := (EX s: state, A_brk X s)%argsassert;
     RA_continue := (EX s: state, A_loop X s)%argsassert; RA_return := RA_return (POST_it X) |}.
Proof. unfold sl_R, loop1_ret_assert, overridePost. destruct (POST_it X); reflexivity. Qed.

#[local] Arguments sub_loop : simpl never.
#[local] Arguments sl_c' : simpl never.
#[local] Arguments sl_t1 : simpl never.

Lemma sl_sub_ok : loop_facts -> sl_sub_stmt.
Proof.
intros LF Espec X s WF.
destruct LF as (SSO & ROO & RKO & RRO & RSO & RBO & RSTO & RFO).
pose proof WF as WF'. unfold it_wf in WF'.
destruct WF' as (SHg & SHl & SH & IN & OLD & CAP).
unfold SL_cnt, sl_props, sl_locs, sl_K, sl_sep, params_locs.
rewrite sl_sub_R. unfold overridePost. cbv iota.
unfold Delta_it. simplify_func_tycontext.
unfold sl_sub.
abbreviate_semax.
Intros.
assert (AO: acc_ok (c_type X) (c_lens X) (c_req X) (Zlength (c_old X))) by (unfold acc_ok; auto).
destruct (RKO _ _ _ _ _ _ AO H3) as (IT & SK).
destruct (ROO _ _ _ _ AO) as (RT1 & RT2 & RT3).
fold (it_root X) (it_mx X) in RT1, RT2, RT3.
destruct IT as (IS & IL & ID & IC & IH & INX & INU & IUC & IU32 & ILO & ZC & FC & C1 & ZT).
assert (LR: 1 <= st_len' (c_lens X) s <= 15).
{ unfold st_len'. destruct (st_c s =? 0) eqn:C0; [|lia].
  apply Z.eqb_eq in C0.
  assert (s_len s <> it_mx X) by (intro; apply H; auto).
  pose proof (RRO _ _ _ _ _ _ AO H3 C0 H4).
  destruct IN as (_ & _ & FL & _).
  destruct (SSO _ FL) as (_ & FW).
  rewrite Forall_Znth in FW; specialize (FW (s_sym s + 1) ltac:(lia)); lia. }
assert (HN: 0 <= st_huff' s) by (apply sl_sub_huff_nonneg; lia).
assert (P2R: 2 <= 2 ^ it_root X <= 2 ^ 15).
{ split; [apply (Z.pow_le_mono_r 2 1) | apply Z.pow_le_mono_r]; lia. }
assert (LL: 0 <= sl_l' X s < 2 ^ it_root X).
{ unfold sl_l'. rewrite sl_sub_land_mod by lia. apply Z.mod_pos_bound. lia. }
assert (MK: Z.shiftl 1 (it_root X) - 1 = 2 ^ it_root X - 1) by (rewrite Z.shiftl_1_l; reflexivity).
match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
  forward_if (PROPx P (LOCALx (temp _t'8 (Vint (Int.repr (Z.b2z (sl_cond X s)))) :: Q) (SEPx R)))
end.
{ forward. entailer!.
  unfold sl_cond. rewrite (proj2 (Z.ltb_lt _ _) H4). cbn [andb]. fold (sl_l' X s).
  destruct (Z.eq_dec (sl_l' X s) (s_low s)) as [E|E].
  - rewrite E, Z.eqb_refl, Int.eq_true. reflexivity.
  - rewrite (proj2 (Z.eqb_neq _ _) E), Int.eq_false. reflexivity.
    intro E'. apply (f_equal Int.unsigned) in E'. rewrite !Int.unsigned_repr in E' by rep_lia. contradiction. }
{ forward. entailer!.
  unfold sl_cond. rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity. }
forward_if.
2: {
  forward.
  pose proof (sl_sub_step_nosub X s H H4) as ST.
  match type of ST with _ = Continue ?t => set (s1 := t) in ST end.
  assert (R': reach (c_type X) (c_lens X) (c_req X) (c_old X) (Z.to_nat (s_sym s1)) s1).
  { replace (Z.to_nat (s_sym s1)) with (S (Z.to_nat (s_sym s))) by (simpl; lia). eapply RSTO; eauto. }
  Exists s1. unfold A_loop, it_sep, count_at, here_, params_locs. subst s1.
  cbn [s_huff s_sym s_len s_curr s_drop s_low s_used s_next s_cnt s_tab] in *.
  entailer!. }
assert (C2: it_root X < st_len' (c_lens X) s /\ sl_l' X s <> s_low s).
{ unfold sl_cond in H4. apply andb_prop in H4. destruct H4 as [A B].
  apply Z.ltb_lt in A. apply negb_true_iff, Z.eqb_neq in B. auto. }
destruct C2 as [C2 C3].
destruct (RSO _ _ _ _ _ _ AO H3 H C2 C3) as (NC & DL & SB).
change (sl_d' X s <= st_len' (c_lens X) s) in DL.
change (sl_c' X s <= 15) in SB.
assert (DR: 1 <= sl_d' X s).
{ unfold sl_d', st_drop'. destruct (s_drop s =? 0) eqn:E; [lia|]. apply Z.eqb_neq in E. lia. }
match goal with |- semax _ (PROPx ?P (LOCALx (?a :: ?b :: ?c :: ?d :: ?e :: ?f :: _ :: ?Q) (SEPx ?R))) _ _ =>
  forward_if (PROPx P (LOCALx (a :: b :: c :: d :: e :: f :: temp _drop (Vint (Int.repr (sl_d' X s))) :: Q) (SEPx R)))
end.
{ forward. entailer!. unfold sl_d', st_drop'. rewrite H5. reflexivity. }
{ forward. entailer!. unfold sl_d', st_drop'. rewrite (proj2 (Z.eqb_neq _ _) H5). reflexivity. }
forward.
assert_PROP (isptr (c_pt X)) as PT by entailer!.
rewrite sl_sub_addp by (auto; rewrite Z.shiftl_1_l;
  assert (2 ^ s_curr s <= 2 ^ 15) by (apply Z.pow_le_mono_r; lia); rep_lia).
fold (sl_n' X s).
forward.
rewrite sub_repr.
set (c0 := st_len' (c_lens X) s - sl_d' X s).
assert (C0R: 0 <= c0 <= 14) by (unfold c0; lia).
assert (E0: sl_c' X s = sub_loop (Z.to_nat (16 - 0)) (c0 + 0) (sl_d' X s) (it_mx X) (2 ^ c0) (st_cnt' s))
  by (rewrite Z.add_0_r; unfold sl_c', sub_bits; rewrite Z.shiftl_1_l; reflexivity).
assert (C0E: c0 = st_len' (c_lens X) s - sl_d' X s) by reflexivity.
clearbody c0.
forward.
{ entailer!. change (Int.unsigned Int.iwordsize) with 32. lia. }
assert (SHc0: Int.shl (Int.repr 1) (Int.repr c0) = Int.repr (2 ^ c0)).
{ unfold Int.shl. rewrite !Int.unsigned_repr by rep_lia. rewrite Z.shiftl_1_l. reflexivity. }
rewrite SHc0.
destruct (sl_sub_cnt_ok s ZC FC C1 ltac:(lia)) as (ZC' & FC').
assert (MX15: it_mx X <= 15) by lia.
unfold count_at.
match goal with |- semax _ (PROPx ?P (LOCALx (_ :: _ :: ?Q) (SEPx ?R))) _ _ =>
forward_loop (EX j: Z, EX lf: Z,
  PROPx [0 <= j; c0 + j <= 15; 1 <= lf <= 2 ^ (c0 + j);
         sl_c' X s = sub_loop (Z.to_nat (16 - j)) (c0 + j) (sl_d' X s) (it_mx X) lf (st_cnt' s)]
  (LOCALx (temp _left (Vint (Int.repr lf)) :: temp _curr (Vint (Int.repr (c0 + j))) :: Q) (SEPx R)))
break: (PROPx [] (LOCALx (temp _curr (Vint (Int.repr (sl_c' X s))) :: Q) (SEPx R)))
end.
{ assert (P0: 1 <= 2 ^ c0 <= 2 ^ (c0 + 0)) by (rewrite Z.add_0_r; split; [apply (Z.pow_le_mono_r 2 0); lia | lia]).
  Exists 0 (2 ^ c0). entailer!. }
{ Intros j lf.
  assert (FU: Z.to_nat (16 - j) = S (Z.to_nat (16 - (j + 1)))) by lia.
  rewrite FU in H8.
  forward_if.
  2: { forward. entailer!. rewrite H8, sl_sub_loop_exit by lia. reflexivity. }
  assert (CI: 0 <= c0 + j + sl_d' X s < 16) by lia.
  assert (CB: 0 <= Znth (c0 + j + sl_d' X s) (st_cnt' s) <= 288).
  { rewrite Forall_Znth in FC'. apply FC'. lia. }
  assert (LF2: 2 ^ (c0 + j) <= 2 ^ 15) by (apply Z.pow_le_mono_r; lia).
  forward.
  { rewrite sl_sub_zs by lia. go_lower. apply prop_right. simpl. rewrite Int.unsigned_repr by rep_lia. lia. }
  rewrite sl_sub_zs by lia.
  forward.
  rewrite sub_repr.
  set (cn := Znth (c0 + j + sl_d' X s) (st_cnt' s)) in *.
  clear SSO ROO RKO RRO RSO RBO RSTO RFO H3 AO IS IH ID IC INX INU IUC ILO ZC FC C1 ZT SK RT1 RT3 E0.
  forward_if.
  { forward. entailer!. rewrite H8, sl_sub_loop_brk by (unfold cn in *; lia). reflexivity. }
  { forward. forward.
    assert (SH1: Int.shl (Int.repr (lf - cn)) (Int.repr 1) = Int.repr (2 * (lf - cn))).
    { unfold Int.shl. rewrite !Int.unsigned_repr by rep_lia. rewrite Z.shiftl_mul_pow2 by lia. f_equal. lia. }
    rewrite SH1, add_repr.
    assert (P1: 1 <= 2 * (lf - cn) <= 2 ^ (c0 + (j + 1))).
    { replace (c0 + (j + 1)) with (Z.succ (c0 + j)) by lia. rewrite Z.pow_succ_r by lia. lia. }
    assert (P2: sl_c' X s = sub_loop (Z.to_nat (16 - (j + 1))) (c0 + (j + 1)) (sl_d' X s) (it_mx X)
                                     (2 * (lf - cn)) (st_cnt' s)).
    { rewrite H8, sl_sub_loop_step by (unfold cn in *; lia). f_equal; lia. }
    Exists (j + 1) (2 * (lf - cn)).
    replace (c0 + j + 1) with (c0 + (j + 1)) by lia.
    entailer!. } }
assert (CL: 0 <= sl_c' X s) by (rewrite E0; pose proof (sl_sub_loop_ge (Z.to_nat (16 - 0)) (c0 + 0) (sl_d' X s) (it_mx X) (2 ^ c0) (st_cnt' s)); lia).
assert (P2C: 1 <= 2 ^ sl_c' X s <= 32768) by (split; [apply (Z.pow_le_mono_r 2 0) | apply (Z.pow_le_mono_r 2 _ 15)]; lia).
assert (U0: 0 <= s_used s) by (rewrite Z.shiftl_1_l in INU; pose proof (Z.pow_nonneg 2 (s_curr s)); lia).
forward.
{ go_lower. apply prop_right. simpl. rewrite Int.unsigned_repr by rep_lia. change (Int.unsigned Int.iwordsize) with 32. lia. }
assert (SHc: Int.shl (Int.repr 1) (Int.repr (sl_c' X s)) = Int.repr (Z.shiftl 1 (sl_c' X s))).
{ unfold Int.shl. rewrite !Int.unsigned_repr by rep_lia. reflexivity. }
rewrite SHc, add_repr. fold (sl_u' X s).
assert (UR: 0 <= sl_u' X s <= 65536) by (unfold sl_u'; rewrite Z.shiftl_1_l; lia).
assert (TY: c_type X = 1 \/ c_type X = 2) by (destruct IN as (T & _); unfold CODES in NC; lia).
assert (MF: over (c_type X) (sl_u' X s) = true -> it_model X = REnough (sl_t1 X s))
  by (intro; eapply sl_sub_model; eauto).
assert (RC: over (c_type X) (sl_u' X s) = false ->
  reach (c_type X) (c_lens X) (c_req X) (c_old X) (Z.to_nat (s_sym s + 1))
    (mkSt (st_huff' s) (s_sym s + 1) (st_len' (c_lens X) s) (sl_c' X s) (sl_d' X s) (sl_l' X s)
          (sl_u' X s) (sl_n' X s) (st_cnt' s)
          (upd_Znth (sl_l' X s) (sl_t1 X s) (mkE (sl_c' X s) (it_root X) (sl_n' X s))))).
{ intro O. pose proof (sl_sub_step_sub X s H H4) as ST. rewrite O in ST.
  replace (Z.to_nat (s_sym s + 1)) with (S (Z.to_nat (s_sym s))) by lia. eapply RSTO; eauto. }
assert (LC: sl_l' X s < Zlength (c_old X)).
{ pose proof (sl_sub_root_cap _ _ _ _ NC (proj1 IN) CAP H2). rewrite Z.shiftl_1_l in H5. unfold it_root in LL. lia. }
assert (NR: 0 <= sl_n' X s <= 32768) by (unfold sl_n'; rewrite Z.shiftl_1_l in *; pose proof (Z.pow_nonneg 2 (s_curr s)); lia).
assert (RT0: 1 <= it_root X) by lia.
clear SSO ROO RKO RRO RSO RBO RSTO RFO H3 AO IS IH ID IC INX INU IUC ILO ZC FC C1 SK RT1 RT3 E0 C0E SHc0 SHc
  CAP OLD IN C2 C3 DL DR LR HN MK FC' ZC' c0 C0R IL.
match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
  forward_if (PROPx P (LOCALx (temp _t'6 (Vint (Int.repr (Z.b2z ((c_type X =? 1) && (852 <? sl_u' X s))%bool))) :: Q) (SEPx R)))
end.
{ forward. entailer!. replace (c_type X =? 1) with true by lia. rewrite sl_sub_ltb. reflexivity. }
{ forward. entailer!. replace (c_type X =? 1) with false by lia. reflexivity. }
match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
  forward_if (PROPx P (LOCALx (temp _t'7 (Vint (Int.repr (Z.b2z (over (c_type X) (sl_u' X s))))) :: Q) (SEPx R)))
end.
{ forward. entailer!. unfold over, LENS, DISTS, ENOUGH_LENS, ENOUGH_DISTS. rewrite H3. reflexivity. }
{ forward_if.
  { forward. forward. entailer!. unfold over, LENS, DISTS, ENOUGH_LENS, ENOUGH_DISTS.
    rewrite H3, H5. cbn [Z.eqb Pos.eqb andb orb]. rewrite sl_sub_ltb. reflexivity. }
  { forward. entailer!. unfold over, LENS, DISTS, ENOUGH_LENS, ENOUGH_DISTS.
    rewrite H3. replace (c_type X =? 2) with false by lia. reflexivity. } }
forward_if.
{ apply (semax_post (POST_it X)).
  1-3: unfold POST_it; simpl RA_normal; simpl RA_break; simpl RA_continue; intros; go_lowerx; normalize.
  1: intros; apply andp_left2; unfold POSTCONDITION, abbreviate; simpl RA_return; apply derives_refl.
  unfold POST_it. forward.
  rewrite (MF H3). cbn [it_ret it_tab it_adv it_bits]. rewrite Z.mul_0_r, isptr_offset_val_zero by auto.
  unfold here_, work_sorted. entailer!. }
forward. forward. rewrite ?and_repr. fold (sl_l' X s). forward. forward. forward. forward. forward. forward.
{ entailer!. apply prop_right. destruct (c_pt X); try contradiction. simpl. unfold sameblock, is_true.
  destruct (peq b b); [reflexivity | congruence]. }
rewrite sl_sub_subpp by auto.
set (L := map entry_rep (sl_t1 X s)).
assert (LH: 0 <= sl_l' X s < Zlength L)
  by (subst L; rewrite Zlength_map; unfold sl_t1; rewrite sl_sub_rep_fill_len; lia).
assert (LD: L = map entry_rep (sl_t1 X s)) by reflexivity.
clearbody L.
rewrite !upd_Znth_same by (rewrite ?Zlength_upd_Znth; exact LH).
rewrite !upd_Znth_twice by (rewrite ?Zlength_upd_Znth; exact LH).
cbn [fst snd].
rewrite !sl_sub_ze8 by lia.
change (Vint (Int.repr (sl_c' X s)), (Vint (Int.repr (it_root X)), Vint (Int.repr (sl_n' X s))))
  with (entry_rep (mkE (sl_c' X s) (it_root X) (sl_n' X s))).
rewrite LD, upd_Znth_map.
specialize (RC H3).
Exists (mkSt (st_huff' s) (s_sym s + 1) (st_len' (c_lens X) s) (sl_c' X s) (sl_d' X s) (sl_l' X s)
          (sl_u' X s) (sl_n' X s) (st_cnt' s)
          (upd_Znth (sl_l' X s) (sl_t1 X s) (mkE (sl_c' X s) (it_root X) (sl_n' X s)))).
unfold A_loop, it_sep, count_at, here_, params_locs.
cbn [s_huff s_sym s_len s_curr s_drop s_low s_used s_next s_cnt s_tab] in *.
entailer!.
Qed.
