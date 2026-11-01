(* inflate_fast (BodyF5.v): the length branch (F5Kit s_lenbr, model flen). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inffast.code.
Require Import Zlib.proof.inffast.F5Kit.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* ---------------------------------------------------------------------------------------------- *)
(* the pieces of s_lenbr                                                                          *)

(* len = here->val *)
Definition s_lbA := at_path (p_lenbr ++ [0]%nat) fbody.
(* op &= 15 *)
Definition s_lbB := at_path (p_lenbr ++ [1;0]%nat) fbody.
(* if (op) { extra length bits } *)
Definition s_lbC := at_path (p_lenbr ++ [1;1;0]%nat) fbody.
(* if (bits < 15) { two bytes } *)
Definition s_lbD := at_path (p_lenbr ++ [1;1;1;0]%nat) fbody.
(* if (op & 16) { distance } else { invalid distance code } *)
Definition s_lbif := at_path (p_lenbr ++ [1;1;1;1;1;1]%nat) fbody.
Definition s_lbthen := at_path (p_lenbr ++ [1;1;1;1;1;1;0]%nat) fbody.
Definition s_lbelse := at_path (p_lenbr ++ [1;1;1;1;1;1;1]%nat) fbody.
(* the distance's extra bits: dist = here->val; op &= 15; pulls; dist += ...; hold >>= op; bits -= op *)
Definition s_lbT1 := at_path (p_lenbr ++ [1;1;1;1;1;1;0;0]%nat) fbody.
Definition s_lbT2 := at_path (p_lenbr ++ [1;1;1;1;1;1;0;1;0]%nat) fbody.
Definition s_lbT3 := at_path (p_lenbr ++ [1;1;1;1;1;1;0;1;1;0]%nat) fbody.
Definition s_lbT4 := at_path (p_lenbr ++ [1;1;1;1;1;1;0;1;1;1;0]%nat) fbody.
Definition s_lbT5 := at_path (p_lenbr ++ [1;1;1;1;1;1;0;1;1;1;1;0]%nat) fbody.
Definition s_lbT6 := at_path (p_lenbr ++ [1;1;1;1;1;1;0;1;1;1;1;1;0]%nat) fbody.

Lemma lb_split: s_lenbr =
  Ssequence s_lbA (Ssequence s_lbB (Ssequence s_lbC (Ssequence s_lbD (Ssequence s_dhere (Ssequence s_dloop s_lbif))))).
Proof. reflexivity. Qed.

Lemma lb_if_split: s_lbif = Sifthenelse (Ebinop Oand (Etempvar _op tuint) (Econst_int (Int.repr 16) tint) tuint)
  s_lbthen s_lbelse.
Proof. reflexivity. Qed.

Lemma lb_then_split: s_lbthen =
  Ssequence s_lbT1 (Ssequence s_lbT2 (Ssequence s_lbT3 (Ssequence s_lbT4 (Ssequence s_lbT5 (Ssequence s_lbT6 s_copy))))).
Proof. reflexivity. Qed.

Ltac lb_simpl :=
  match goal with |- semax _ _ ?c _ =>
    let c' := eval cbv beta iota delta [
      s_lbA s_lbB s_lbC s_lbD s_lbif s_lbthen s_lbelse s_lbT1 s_lbT2 s_lbT3 s_lbT4 s_lbT5 s_lbT6
      p_lenbr app at_path child fbody f_inflate_fast fn_body] in c in
    change c with c'
  end.

(* ---------------------------------------------------------------------------------------------- *)
(* the model                                                                                       *)

(* the rest of flen after the length's extra bits and the refill *)
Definition lb_tail (s: istate) (L: Z) (r: entry * mst) : bool * mst :=
  let '(here, m) := r in
  if negb (Z.land (e_op here) 16 =? 0) then
    let '(dist, m) := distx here m in fcopy s L dist m
  else (false, set_bad m F_d_code).

Lemma lb_flen_eq: forall s e m L m1, lenx e m = (L, m1) ->
  flen s e m = lb_tail s L (dwalk s (refill2 m1)).
Proof. intros s e m L m1 E. unfold flen. rewrite E. reflexivity. Qed.

Ltac lb_splits := repeat match goal with |- _ /\ _ => split end.

Lemma lb_u32: forall x, 0 <= x <= Int.max_unsigned -> u32 x = x.
Proof. intros x H. unfold u32. apply Z.mod_small. rep_lia. Qed.

Lemma lb_land15: forall op, 16 <= op <= 21 -> Z.land op 15 = op - 16.
Proof.
  intros op H.
  assert (op = 16 \/ op = 17 \/ op = 18 \/ op = 19 \/ op = 20 \/ op = 21) by lia.
  repeat (destruct H0 as [H0|H0]; [subst op; reflexivity|]); subst op; reflexivity.
Qed.

Lemma lb_shiftr_range: forall x n, 0 <= x <= Int64.max_unsigned -> 0 <= n -> 0 <= Z.shiftr x n <= Int64.max_unsigned.
Proof.
  intros x n H Hn. rewrite Z.shiftr_div_pow2 by lia. split.
  - apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia].
  - apply Z.le_trans with x; [ | lia]. apply Z.div_le_upper_bound; [apply Z.pow_pos_nonneg; lia |].
    assert (1 <= 2 ^ n) by (apply Z.pow_le_mono_r with (a := 2) in Hn; [ simpl in Hn; lia | lia]). nia.
Qed.

Lemma lb_mwf_dropbits: forall m n, mwf m -> 0 <= n <= m_bits m -> mwf (dropbits n m).
Proof.
  intros m n W Hn. destruct W. constructor; simpl; auto.
  - apply lb_shiftr_range; auto. lia.
  - unfold u32. rewrite Z.mod_small by lia. lia.
Qed.

Lemma lb_mwf_pull: forall m, mwf m -> m_have m <> 0 -> m_bits m <= 31 -> mwf (pull m).
Proof.
  intros m W Hh Hb. pose proof (mw_hold _ W) as WH. pose proof (mw_nx _ W) as WNX.
  destruct W. constructor; simpl; auto.
  - unfold m_have in Hh. lia.
  - unfold lrange, u64. pose proof (Z.mod_pos_bound (m_hold m + Znth (m_nx m) (m_inp m) * 2 ^ m_bits m) (2^64)). rep_lia.
  - unfold u32. rewrite Z.mod_small by lia. lia.
Qed.

Lemma lb_fast_pull: forall m, fast_ok m -> m_have m <> 0 -> m_bits m <= 31 ->
  fast_ok (fpull m) /\ m_bits (fpull m) = m_bits m + 8 /\ m_have (fpull m) = m_have m - 1 /\
  m_s (fpull m) = m_s m /\ m_inp (fpull m) = m_inp m /\ m_aout (fpull m) = m_aout m /\ m_ow (fpull m) = m_ow m.
Proof.
  intros m [W T] Hh Hb.
  pose proof (mw_bits _ W) as HB.
  split; [split; [apply lb_mwf_pull; auto | exact T]|].
  split; [unfold fpull, pull; cbn [m_bits set_m_bits]; apply lb_u32; rep_lia|].
  split; [unfold m_have, fpull, pull; cbn; lia|].
  repeat split; reflexivity.
Qed.

Lemma lb_fast_drop: forall m n, fast_ok m -> 0 <= n <= m_bits m ->
  let m' := set_m_bits (set_m_hold m (Z.shiftr (m_hold m) n)) (u32 (m_bits m - n)) in
  fast_ok m' /\ m_bits m' = m_bits m - n /\ m_have m' = m_have m /\
  m_s m' = m_s m /\ m_inp m' = m_inp m /\ m_aout m' = m_aout m /\ m_ow m' = m_ow m.
Proof.
  intros m n [W T] Hn. pose proof (mw_bits _ W) as HB. cbv zeta.
  split; [split; [apply (lb_mwf_dropbits m n W Hn) | exact T]|].
  split; [cbn [m_bits set_m_bits]; apply lb_u32; rep_lia|].
  repeat split; reflexivity.
Qed.

Lemma lb_lenx_facts: forall m e L m1,
  fast_ok m -> 16 <= e_op e <= 21 -> 3 <= e_val e <= 258 -> len_ok e ->
  33 <= 8 * m_have m + m_bits m -> m_bits m <= 30 -> lenx e m = (L, m1) ->
  3 <= L <= 258 /\ fast_ok m1 /\ m_s m1 = m_s m /\ m_inp m1 = m_inp m /\ m_aout m1 = m_aout m /\
  m_ow m1 = m_ow m /\ 0 <= m_bits m1 <= 30 /\ 28 <= 8 * m_have m1 + m_bits m1.
Proof.
  intros m e L m1 FW OP EV LO BUD B30 E.
  pose proof (fast_ok_mwf _ FW) as W.
  pose proof (mw_bits _ W) as HB. pose proof (mwf_have _ W) as HV.
  unfold lenx in E. rewrite (lb_land15 _ OP) in E.
  destruct (e_op e - 16 =? 0) eqn:E0; cbn [negb] in E.
  - inversion E; subst. apply Z.eqb_eq in E0. lb_splits; auto; lia.
  - apply Z.eqb_neq in E0. unfold len_ok in LO. specialize (LO OP).
    assert (P: 0 < 2 ^ (e_op e - 16)) by (apply Z.pow_pos_nonneg; lia).
    assert (P5: 2 ^ (e_op e - 16) <= 32) by (change 32 with (2 ^ 5); apply Z.pow_le_mono_r; lia).
    destruct (Z.ltb_spec (m_bits m) (e_op e - 16)) as [EB|EB].
    + replace (if m_bits m <? e_op e - 16 then fpull m else m) with (fpull m) in E
        by (rewrite (proj2 (Z.ltb_lt _ _) EB); reflexivity).
      destruct (lb_fast_pull m FW ltac:(lia) ltac:(lia)) as (FWp & Bp & Hp & Sp & Ip & Ap & Op).
      set (mp := fpull m) in *.
      destruct (lb_fast_drop mp (e_op e - 16) FWp ltac:(lia)) as (FW1 & B1 & H1 & S1 & I1 & A1 & O1).
      apply pair_equal_spec in E as [EL EM]. rewrite <- EL, <- EM.
      pose proof (Z.mod_pos_bound (m_hold mp) (2 ^ (e_op e - 16)) P).
      split; [rewrite lb_u32 by rep_lia; lia|].
      split; [exact FW1|]. rewrite S1, I1, A1, O1, Sp, Ip, Ap, Op, B1, H1, Hp, Bp. lb_splits; auto; lia.
    + replace (if m_bits m <? e_op e - 16 then fpull m else m) with m in E
        by (rewrite (proj2 (Z.ltb_ge _ _) EB); reflexivity).
      destruct (lb_fast_drop m (e_op e - 16) FW ltac:(lia)) as (FW1 & B1 & H1 & S1 & I1 & A1 & O1).
      apply pair_equal_spec in E as [EL EM]. rewrite <- EL, <- EM.
      pose proof (Z.mod_pos_bound (m_hold m) (2 ^ (e_op e - 16)) P).
      split; [rewrite lb_u32 by rep_lia; lia|].
      split; [exact FW1|]. rewrite S1, I1, A1, O1, B1, H1. lb_splits; auto; lia.
Qed.

Lemma lb_refill_facts: forall m1,
  fast_ok m1 -> 0 <= m_bits m1 <= 30 -> 28 <= 8 * m_have m1 + m_bits m1 ->
  fast_ok (refill2 m1) /\ m_s (refill2 m1) = m_s m1 /\ m_inp (refill2 m1) = m_inp m1 /\
  m_aout (refill2 m1) = m_aout m1 /\ m_ow (refill2 m1) = m_ow m1 /\ 15 <= m_bits (refill2 m1) <= 30 /\
  8 * m_have (refill2 m1) + m_bits (refill2 m1) = 8 * m_have m1 + m_bits m1.
Proof.
  intros m1 FW B BUD. pose proof (mwf_have _ (fast_ok_mwf _ FW)) as HV.
  unfold refill2. destruct (Z.ltb_spec (m_bits m1) 15) as [EB|EB].
  - destruct (lb_fast_pull m1 FW ltac:(lia) ltac:(lia)) as (FWp & Bp & Hp & Sp & Ip & Ap & Op).
    destruct (lb_fast_pull (fpull m1) FWp ltac:(lia) ltac:(lia)) as (FWq & Bq & Hq & Sq & Iq & Aq & Oq).
    rewrite Sq, Iq, Aq, Oq, Bq, Hq, Sp, Ip, Ap, Op, Bp, Hp. lb_splits; auto; lia.
  - lb_splits; auto; lia.
Qed.

Lemma lb_mwf_hb: forall m h b, mwf m -> lrange h -> 0 <= b <= 39 -> mwf (set_m_bits (set_m_hold m h) b).
Proof. intros m h b W Hh Hb. destruct W. constructor; simpl; auto. Qed.

Lemma lb_dwalk_facts: forall m2 e3 m3,
  dwalk_facts_stmt -> fast_ok m2 -> m_mode m2 = LEN -> 15 <= m_bits m2 <= 30 -> dwalk (m_s m2) m2 = (e3, m3) ->
  entry_ok e3 /\ final_ok DISTS e3 /\ fast_ok m3 /\ m_s m3 = m_s m2 /\ m_inp m3 = m_inp m2 /\
  m_aout m3 = m_aout m2 /\ m_ow m3 = m_ow m2 /\ 0 <= m_bits m3 <= 30 /\
  8 * m_have m2 + m_bits m2 - 15 <= 8 * m_have m3 + m_bits m3.
Proof.
  intros m2 e3 m3 DWF FW MD B E.
  pose proof (DWF m2 FW MD ltac:(lia)) as D. rewrite E in D.
  destruct D as (EO & FO & _ & B3 & EM).
  pose proof (fast_ok_mwf _ FW) as W. pose proof (mw_hold _ W) as HH.
  set (b3 := m_bits m3) in *. clearbody b3. subst m3. cbn [m_bits set_m_bits set_m_hold].
  assert (HR: lrange (Z.shiftr (m_hold m2) (m_bits m2 - b3))).
  { pose proof (lb_shiftr_range (m_hold m2) (m_bits m2 - b3) HH ltac:(lia)). exact H. }
  lb_splits; auto.
  - split; [apply lb_mwf_hb; auto; lia | exact (proj2 FW)].
  - lia.
  - lia.
  - unfold m_have; cbn. lia.
Qed.

(* distx's pulls *)
Definition lb_dq (opx: Z) (m: mst) : mst :=
  if m_bits m <? opx then (let m := fpull m in if m_bits m <? opx then fpull m else m) else m.

Lemma lb_distx_eq: forall here m,
  distx here m =
  (u32 (e_val here + m_hold (lb_dq (Z.land (e_op here) 15) m) mod 2 ^ Z.land (e_op here) 15),
   set_m_bits (set_m_hold (lb_dq (Z.land (e_op here) 15) m)
                 (Z.shiftr (m_hold (lb_dq (Z.land (e_op here) 15) m)) (Z.land (e_op here) 15)))
     (u32 (m_bits (lb_dq (Z.land (e_op here) 15) m) - Z.land (e_op here) 15))).
Proof. reflexivity. Qed.

Lemma lb_dq_facts: forall m opx, fast_ok m -> 0 <= opx <= 13 -> 13 <= 8 * m_have m + m_bits m -> m_bits m <= 30 ->
  fast_ok (lb_dq opx m) /\ opx <= m_bits (lb_dq opx m) <= 38 /\
  8 * m_have (lb_dq opx m) + m_bits (lb_dq opx m) = 8 * m_have m + m_bits m /\
  m_s (lb_dq opx m) = m_s m /\ m_inp (lb_dq opx m) = m_inp m /\ m_aout (lb_dq opx m) = m_aout m /\
  m_ow (lb_dq opx m) = m_ow m.
Proof.
  intros m opx FW Ho BUD B. pose proof (mwf_have _ (fast_ok_mwf _ FW)) as HV.
  pose proof (mw_bits _ (fast_ok_mwf _ FW)) as HB.
  unfold lb_dq. destruct (Z.ltb_spec (m_bits m) opx) as [EB|EB].
  - destruct (lb_fast_pull m FW ltac:(lia) ltac:(lia)) as (FWp & Bp & Hp & Sp & Ip & Ap & Op).
    cbv zeta. destruct (Z.ltb_spec (m_bits (fpull m)) opx) as [EB2|EB2].
    + destruct (lb_fast_pull (fpull m) FWp ltac:(lia) ltac:(lia)) as (FWq & Bq & Hq & Sq & Iq & Aq & Oq).
      rewrite Sq, Iq, Aq, Oq, Bq, Hq, Sp, Ip, Ap, Op, Bp, Hp. lb_splits; auto; lia.
    + rewrite Sp, Ip, Ap, Op, Bp, Hp. lb_splits; auto; lia.
  - lb_splits; auto; lia.
Qed.

Lemma lb_land15d: forall op, 16 <= op <= 29 -> Z.land op 15 = op - 16.
Proof.
  intros op H.
  assert (op = 16 \/ op = 17 \/ op = 18 \/ op = 19 \/ op = 20 \/ op = 21 \/ op = 22 \/ op = 23 \/
          op = 24 \/ op = 25 \/ op = 26 \/ op = 27 \/ op = 28 \/ op = 29) by lia.
  repeat (destruct H0 as [H0|H0]; [subst op; reflexivity|]); subst op; reflexivity.
Qed.

Lemma lb_dist_final: forall e, final_ok DISTS e -> Z.land (e_op e) 16 <> 0 ->
  16 <= e_op e <= 29 /\ 1 <= e_val e <= 32768.
Proof.
  intros e H A. unfold final_ok in H. cbn in H. destruct H as [H | [_ H]]; [exact H|].
  exfalso. apply A. change 16 with (Z.land 48 16). rewrite Z.land_assoc, H. reflexivity.
Qed.

Lemma lb_distx_facts: forall m3 e3 D m4,
  fast_ok m3 -> final_ok DISTS e3 -> Z.land (e_op e3) 16 <> 0 ->
  13 <= 8 * m_have m3 + m_bits m3 -> m_bits m3 <= 30 -> distx e3 m3 = (D, m4) ->
  1 <= D <= 65536 /\ fast_ok m4 /\ m_s m4 = m_s m3 /\ m_inp m4 = m_inp m3 /\ m_aout m4 = m_aout m3 /\
  m_ow m4 = m_ow m3.
Proof.
  intros m3 e3 D m4 FW FO A16 BUD B E.
  destruct (lb_dist_final e3 FO A16) as [OP EV].
  rewrite lb_distx_eq in E. rewrite (lb_land15d _ OP) in E.
  destruct (lb_dq_facts m3 (e_op e3 - 16) FW ltac:(lia) BUD B) as (FWq & Bq & Hq & Sq & Iq & Aq & Oq).
  set (mq := lb_dq (e_op e3 - 16) m3) in *.
  apply pair_equal_spec in E as [ED EM]. rewrite <- ED, <- EM.
  destruct (lb_fast_drop mq (e_op e3 - 16) FWq ltac:(lia)) as (FW1 & B1 & H1 & S1 & I1 & A1 & O1).
  assert (P: 0 < 2 ^ (e_op e3 - 16)) by (apply Z.pow_pos_nonneg; lia).
  assert (P13: 2 ^ (e_op e3 - 16) <= 8192) by (change 8192 with (2 ^ 13); apply Z.pow_le_mono_r; lia).
  pose proof (Z.mod_pos_bound (m_hold mq) (2 ^ (e_op e3 - 16)) P).
  split; [rewrite lb_u32 by rep_lia; lia|].
  split; [exact FW1|]. rewrite S1, I1, A1, O1, Sq, Iq, Aq, Oq. lb_splits; auto.
Qed.

Lemma lb_and_eq: forall op c, 0 <= op <= 255 -> 0 <= c <= 255 ->
  Int.eq (Int.repr (Z.land op c)) Int.zero = (Z.land op c =? 0).
Proof.
  intros op c Ho Hc.
  assert (0 <= Z.land op c <= 255).
  { split; [apply Z.land_nonneg; lia|].
    destruct (Z.eq_dec (Z.land op c) 0) as [Z0|Z0]; [lia|].
    assert (0 < Z.land op c) by (pose proof (proj2 (Z.land_nonneg op c) ltac:(lia)); lia).
    assert (Z.land op c < 2 ^ 8); [|lia].
    apply Z.log2_lt_pow2; [lia|].
    pose proof (Z.log2_land op c ltac:(lia) ltac:(lia)).
    pose proof (Z.log2_le_mono op 255 ltac:(lia)). change (Z.log2 255) with 7 in *. lia. }
  unfold Int.eq. rewrite Int.unsigned_repr by rep_lia. change (Int.unsigned Int.zero) with 0.
  destruct (zeq (Z.land op c) 0); destruct (Z.land op c =? 0) eqn:E; auto;
    [apply Z.eqb_neq in E | apply Z.eqb_eq in E]; lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* a byte pulled from the input                                                                    *)

Lemma lb_in_byte: forall sh p lo n c inp j,
  in_ok (InBuf sh p lo n c) inp -> 0 <= j < Zlength inp ->
  @Znth val Vundef (lo + j) c = Vint (Int.repr (Znth j inp)).
Proof.
  intros sh p lo n c inp j H Hj. unfold in_ok in H. destruct H as (_&_&Hlo&Hn&Hc&_&Hsub&_).
  rewrite <- Znth_byte_vals by lia. rewrite <- Hsub. rewrite Znth_sublist by lia. f_equal. lia.
Qed.

Lemma lb_hold_add_eq: forall h b bt, 0 <= b -> 0 <= bt < 64 ->
  Int64.repr (u64 (h + b * 2 ^ bt)) = Int64.add (Int64.repr h) (Int64.shl (Int64.repr b) (Int64.repr bt)).
Proof.
  intros h b bt Hb Hbt. unfold u64.
  rewrite Int64.shl_mul_two_p. rewrite (Int64.unsigned_repr bt) by rep_lia.
  rewrite two_p_equiv. unfold Int64.mul.
  assert (P: 0 <= 2 ^ bt <= Int64.max_unsigned).
  { split. apply Z.pow_nonneg; lia.
    assert (2 ^ bt <= 2 ^ 63) by (apply Z.pow_le_mono_r; lia). rep_lia. }
  rewrite (Int64.unsigned_repr (2 ^ bt)) by exact P.
  rewrite Int64.add_unsigned.
  apply Int64.eqm_samerepr.
  apply Int64.eqm_trans with (h + b * 2 ^ bt)%Z.
  - change (2 ^ 64) with Int64.modulus. apply Int64.eqm_sym. apply Zbits.eqmod_mod. reflexivity.
  - apply Int64.eqm_add.
    + apply Int64.eqm_unsigned_repr.
    + apply Int64.eqm_trans with (Int64.unsigned (Int64.repr b) * 2 ^ bt)%Z.
      * apply Int64.eqm_mult. apply Int64.eqm_unsigned_repr. apply Int64.eqm_refl.
      * apply Int64.eqm_unsigned_repr.
Qed.

Lemma lb_bytes_ok_Znth: forall l j, bytes_ok l -> 0 <= j < Zlength l -> 0 <= Znth j l <= 255.
Proof.
  intros l j H Hj. unfold bytes_ok in H. rewrite Forall_forall in H. apply H. apply Znth_In. auto.
Qed.

Lemma lb_ptr_inc: forall k p, isptr p ->
  force_val (sem_binary_operation' Oadd (tptr tuchar) tint (offset_val k p) (Vint (Int.repr 1))) =
  offset_val (k + 1) p.
Proof.
  intros k p P. destruct p; try contradiction. simpl. f_equal.
  rewrite Ptrofs.add_assoc. f_equal. unfold Ptrofs.of_ints. rewrite Int.signed_repr by rep_lia.
  rewrite ptrofs_mul_repr, ptrofs_add_repr. reflexivity.
Qed.

Lemma lb_fpull_nx: forall m, m_nx (fpull m) = m_nx m + 1. Proof. reflexivity. Qed.
Lemma lb_fpull_s: forall m, m_s (fpull m) = m_s m. Proof. reflexivity. Qed.
Lemma lb_fpull_inp: forall m, m_inp (fpull m) = m_inp m. Proof. reflexivity. Qed.
Lemma lb_fpull_ow: forall m, m_ow (fpull m) = m_ow m. Proof. reflexivity. Qed.
Lemma lb_fpull_aout: forall m, m_aout (fpull m) = m_aout m. Proof. reflexivity. Qed.
Lemma lb_fs_sep_pull: forall F m, fs_sep F (fpull m) = fs_sep F m. Proof. reflexivity. Qed.

Lemma lb_pull_hold: forall m inp, m_inp m = inp -> lrange (m_hold m) -> 0 <= Znth (m_nx m) inp <= 255 ->
  0 <= m_bits m < 64 ->
  Int64.add (Int64.repr (m_hold m))
    (Int64.shl (Int64.repr (Int.unsigned (Int.repr (Znth (m_nx m) inp))))
       (Int64.repr (Int.unsigned (Int.repr (m_bits m))))) = Int64.repr (m_hold (fpull m)).
Proof.
  intros m inp E Hh Hb Hbt. subst inp.
  rewrite !Int.unsigned_repr by rep_lia. rewrite <- lb_hold_add_eq by lia. reflexivity.
Qed.

Lemma lb_pull_bits: forall m, 0 <= m_bits m <= 31 -> m_bits (fpull m) = m_bits m + 8.
Proof. intros m H. unfold fpull, pull. cbn [m_bits set_m_bits]. apply lb_u32. rep_lia. Qed.

(* lenx's pull *)
Definition lb_lq (opx: Z) (m: mst) : mst := if m_bits m <? opx then fpull m else m.

Lemma lb_lenx_eq: forall here m,
  lenx here m =
  if negb (Z.land (e_op here) 15 =? 0) then
    (u32 (e_val here + m_hold (lb_lq (Z.land (e_op here) 15) m) mod 2 ^ Z.land (e_op here) 15),
     set_m_bits (set_m_hold (lb_lq (Z.land (e_op here) 15) m)
                   (Z.shiftr (m_hold (lb_lq (Z.land (e_op here) 15) m)) (Z.land (e_op here) 15)))
       (u32 (m_bits (lb_lq (Z.land (e_op here) 15) m) - Z.land (e_op here) 15)))
  else (e_val here, m).
Proof. reflexivity. Qed.

Lemma lb_hold_hb: forall m h b, m_hold (set_m_bits (set_m_hold m h) b) = h. Proof. reflexivity. Qed.
Lemma lb_bits_hb: forall m h b, m_bits (set_m_bits (set_m_hold m h) b) = b. Proof. reflexivity. Qed.
Lemma lb_nx_hb: forall m h b, m_nx (set_m_bits (set_m_hold m h) b) = m_nx m. Proof. reflexivity. Qed.
Lemma lb_s_hb: forall m h b, m_s (set_m_bits (set_m_hold m h) b) = m_s m. Proof. reflexivity. Qed.
Lemma lb_inp_hb: forall m h b, m_inp (set_m_bits (set_m_hold m h) b) = m_inp m. Proof. reflexivity. Qed.
Lemma lb_ow_hb: forall m h b, m_ow (set_m_bits (set_m_hold m h) b) = m_ow m. Proof. reflexivity. Qed.
Lemma lb_aout_hb: forall m h b, m_aout (set_m_bits (set_m_hold m h) b) = m_aout m. Proof. reflexivity. Qed.
Lemma lb_fs_sep_hb: forall F m h b, fs_sep F (set_m_bits (set_m_hold m h) b) = fs_sep F m. Proof. reflexivity. Qed.

Ltac lb_tcu := intro; unfold local, lift1, liftx, lift; simpl; apply prop_right;
  rewrite Int.unsigned_repr by rep_lia; rep_lia.

Lemma lb_tab_isptr: forall F s t, tref_ok t -> tab_mem F s |-- !! isptr (tref_val (f_gv F) (f_sp F) t).
Proof.
  intros F s t T. unfold tab_mem. entailer!. destruct t; cbn [tref_val].
  - auto.
  - auto.
  - unfold codes_at. cbn in T. rewrite field_address0_offset.
    + destruct H as [Hp _]. destruct (f_sp F); try contradiction. simpl. auto.
    + eapply field_compatible0_cons_Tarray; [reflexivity | exact H | unfold ENOUGH_CODES in T; lia].
Qed.

Lemma lb_lq_facts: forall m opx, fast_ok m -> 0 <= opx <= 5 -> 33 <= 8 * m_have m + m_bits m -> m_bits m <= 30 ->
  fast_ok (lb_lq opx m) /\ opx <= m_bits (lb_lq opx m) <= 30 /\
  8 * m_have (lb_lq opx m) + m_bits (lb_lq opx m) = 8 * m_have m + m_bits m /\
  m_s (lb_lq opx m) = m_s m /\ m_inp (lb_lq opx m) = m_inp m /\ m_aout (lb_lq opx m) = m_aout m /\
  m_ow (lb_lq opx m) = m_ow m.
Proof.
  intros m opx FW Ho BUD B. pose proof (mwf_have _ (fast_ok_mwf _ FW)) as HV.
  pose proof (mw_bits _ (fast_ok_mwf _ FW)) as HB.
  unfold lb_lq. destruct (Z.ltb_spec (m_bits m) opx) as [EB|EB].
  - destruct (lb_fast_pull m FW ltac:(lia) ltac:(lia)) as (FWp & Bp & Hp & Sp & Ip & Ap & Op).
    rewrite Sp, Ip, Ap, Op, Bp, Hp. lb_splits; auto; lia.
  - lb_splits; auto; lia.
Qed.

Lemma lb_len_add: forall v h op, lrange h -> 0 <= op <= 15 ->
  Int.add (Int.repr v) (Int.and (Int.repr (Int64.unsigned (Int64.repr h)))
    (Int.sub (Int.shl (Int.repr 1) (Int.repr op)) (Int.repr 1))) = Int.repr (v + h mod 2 ^ op).
Proof.
  intros v h op Hh Ho. unfold lrange in Hh.
  assert (P: 0 < 2 ^ op) by (apply Z.pow_pos_nonneg; lia).
  assert (P15: 2 ^ op <= 2 ^ 15) by (apply Z.pow_le_mono_r; lia).
  rewrite Int64.unsigned_repr by rep_lia.
  rewrite Int.shl_mul_two_p, (Int.unsigned_repr op) by rep_lia.
  rewrite two_p_equiv, Int.mul_commut, Int.mul_one, sub_repr.
  unfold Int.and. rewrite (Int.unsigned_repr (2 ^ op - 1)) by rep_lia.
  replace (2 ^ op - 1) with (Z.ones op) by (rewrite Z.ones_equiv; lia).
  rewrite Z.land_ones by lia. rewrite Int.unsigned_repr_eq.
  rewrite (Znumtheory.Zmod_div_mod (2 ^ op) Int.modulus h).
  - rewrite add_repr. reflexivity.
  - lia.
  - reflexivity.
  - exists (2 ^ (32 - op)). change Int.modulus with (2 ^ 32). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

Lemma lb_shru: forall h n, lrange h -> 0 <= n <= 255 ->
  Int64.shru (Int64.repr h) (Int64.repr (Int.unsigned (Int.repr n))) = Int64.repr (Z.shiftr h n).
Proof.
  intros h n Hh Hn. unfold lrange in Hh. rewrite Int.unsigned_repr by rep_lia.
  unfold Int64.shru. rewrite !Int64.unsigned_repr by rep_lia. reflexivity.
Qed.

(* rest_mem with strm_rep and state->mode apart *)
Definition lb_rest_nm (F: frame) (m: mst) : mpred :=
  let gv := f_gv F in let sp := f_sp F in let s := m_s m in
  (field_at Ews t_state (DOT _strm) (f_strmp F) sp *
   field_at Ews t_state (DOT _last) (zv (i_last s)) sp *
   field_at Ews t_state (DOT _wrap) (zv (i_wrap s)) sp *
   field_at Ews t_state (DOT _havedict) (zv (i_havedict s)) sp *
   field_at Ews t_state (DOT _flags) (zv (i_flags s)) sp *
   field_at Ews t_state (DOT _dmax) (zv (i_dmax s)) sp *
   field_at Ews t_state (DOT _check) (lv (i_check s)) sp *
   field_at Ews t_state (DOT _total) (lv (i_total s)) sp *
   field_at Ews t_state (DOT _head) (if i_head s then f_headp F else nullval) sp *
   field_at Ews t_state (DOT _wbits) (zv (i_wbits s)) sp *
   field_at Ews t_state (DOT _wsize) (zv (i_wsize s)) sp *
   field_at Ews t_state (DOT _whave) (zv (i_whave s)) sp *
   field_at Ews t_state (DOT _wnext) (zv (i_wnext s)) sp *
   field_at Ews t_state (DOT _window) (if i_win s then f_winp F else nullval) sp *
   field_at Ews t_state (DOT _hold) (lv (i_hold s)) sp *
   field_at Ews t_state (DOT _bits) (zv (i_bits s)) sp *
   field_at Ews t_state (DOT _length) (zv (i_length s)) sp *
   field_at Ews t_state (DOT _offset) (zv (i_offset s)) sp *
   field_at Ews t_state (DOT _extra) (zv (i_extra s)) sp *
   field_at Ews t_state (DOT _lencode) (tref_val gv sp (i_lencode s)) sp *
   field_at Ews t_state (DOT _distcode) (tref_val gv sp (i_distcode s)) sp *
   field_at Ews t_state (DOT _lenbits) (zv (i_lenbits s)) sp *
   field_at Ews t_state (DOT _distbits) (zv (i_distbits s)) sp *
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
  Zlib.proof.crc32.Spec.crc_table_at (f_tsh F) (f_gv F).

Lemma lb_rest_perm: forall a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 hd st ord it crc: mpred,
  (a1 * a2 * a3 * a4 * a5 * a6 * a7 * a8 * a9 * a10 * a11 * a12 * a13 * a14 * a15 * a16 * a17 * a18 * a19 * a20 * a21 * a22 * a23 * a24 * a25 * a26 * a27 * a28 * a29 * a30 * a31 * a32 * a33 * a34) * hd * st * ord * it * crc = st * a2 * ((a1 * a3 * a4 * a5 * a6 * a7 * a8 * a9 * a10 * a11 * a12 * a13 * a14 * a15 * a16 * a17 * a18 * a19 * a20 * a21 * a22 * a23 * a24 * a25 * a26 * a27 * a28 * a29 * a30 * a31 * a32 * a33 * a34) * hd * ord * it * crc).
Proof. intros. apply pred_ext; cancel. Qed.

Lemma lb_rest_split: forall F m, rest_mem F m =
  strm_rep (f_gv F) (f_shs F) (f_strmp F)
    (in_ptr (f_ib F) (m_snx m)) (zv (Zlength (m_inp m) - m_snx m)) (m_tin m)
    (out_ptr (f_ob F) (m_sow m)) (zv (m_aout m - m_sow m)) (m_tout m)
    (msg_val (f_gv F) (m_msg m)) (f_sp F) (f_dt F) (m_adler m) (f_vres F) *
  field_at Ews t_state (DOT _mode) (zv (i_mode (m_s m))) (f_sp F) * lb_rest_nm F m.
Proof. intros. unfold rest_mem, state_rep_nc, lb_rest_nm. apply lb_rest_perm. Qed.

Lemma lb_rest_bad: forall F m e, lb_rest_nm F (set_bad m e) = lb_rest_nm F m. Proof. reflexivity. Qed.
Lemma lb_locals_bad: forall F m e, fs_locals F (set_bad m e) = fs_locals F m. Proof. reflexivity. Qed.
Lemma lb_tab_bad: forall F m e, tab_mem F (m_s (set_bad m e)) = tab_mem F (m_s m). Proof. reflexivity. Qed.
Lemma lb_win_bad: forall F m e, win_rep (f_winp F) (m_s (set_bad m e)) = win_rep (f_winp F) (m_s m). Proof. reflexivity. Qed.
Lemma lb_ow_bad: forall m e, m_ow (set_bad m e) = m_ow m. Proof. reflexivity. Qed.
Lemma lb_rest_mem_bad: forall F m e, rest_mem F (set_bad m e) =
  strm_rep (f_gv F) (f_shs F) (f_strmp F)
    (in_ptr (f_ib F) (m_snx m)) (zv (Zlength (m_inp m) - m_snx m)) (m_tin m)
    (out_ptr (f_ob F) (m_sow m)) (zv (m_aout m - m_sow m)) (m_tout m)
    (f_gv F (msg_ident e)) (f_sp F) (f_dt F) (m_adler m) (f_vres F) *
  field_at Ews t_state (DOT _mode) (zv BAD) (f_sp F) * lb_rest_nm F m.
Proof. intros. rewrite lb_rest_split. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the C pieces                                                                                    *)

(* len = here->val; op &= 15; if (op) { ... } *)
Lemma lb_lenx_ok {Espec: OracleKind} (TF: tab_focus_stmt) (F: frame) (m: mst) (j: Z) (e: entry) (L: Z) (m1: mst)
    (X: statement) (R: ret_assert):
  fast_ok m -> 0 <= j < tab_size (i_lencode (m_s m)) ->
  tab_entry lenfix_list distfix_list (m_s m) (i_lencode (m_s m)) j = e ->
  entry_ok e -> 16 <= e_op e <= 21 -> 3 <= e_val e <= 258 -> len_ok e ->
  33 <= 8 * m_have m + m_bits m -> m_bits m <= 30 -> in_ok (f_ib F) (m_inp m) -> readable_share (f_gsh F) ->
  lenx e m = (L, m1) ->
  semax Delta_fast (fs_state F m1 [] [temp _len (zv L)]) X R ->
  semax Delta_fast (fs_state F m [] [temp _here (entry_ptr F (i_lencode (m_s m)) j); temp _op (zv (e_op e))])
    (Ssequence s_lbA (Ssequence s_lbB (Ssequence s_lbC X))) R.
Proof.
  intros FW J TE EO OP EV LO BUD B30 INOK SHG ELX HX. destruct R as [Rn Rb Rc Rr].
  lb_simpl. unfold fs_state, fs_locals, fs_sep; cbn [app]. abbreviate_semax.
  pose proof (fast_ok_mwf _ FW) as W. pose proof (mwf_have _ W) as HV. pose proof (mw_hold _ W) as HH.
  pose proof (mw_bits _ W) as HB.
  set (s := m_s m) in *. set (t := i_lencode s) in *.
  assert (T: tref_ok t) by apply (sw_lencode _ (mw_s _ W)).
  assert (Hc: Zlength (i_codes s) = ENOUGH_CODES) by apply (proj1 (sw_codes _ (mw_s _ W))).
  sep_apply (TF F s t j T Hc J). Intros.
  unfold ent. rewrite TE.
  destruct EO as (Eo & Eb & Ev).
  assert (RS: readable_share (tab_sh F t)) by (clearbody t; destruct t; simpl; auto with share).
  forward. { lb_tcu. }
  forward.
  sep_apply (modus_ponens_wand (data_at (tab_sh F t) t_code (Vint (Int.repr (e_op e)), (Vint (Int.repr (e_bits e)), Vint (Int.repr (e_val e)))) (entry_ptr F t j)) (tab_mem F s)).
  forward.
  rewrite and_repr, (lb_land15 _ OP).
  rewrite lb_lenx_eq, (lb_land15 _ OP) in ELX.
  forward_if (fs_state F m1 [] [temp _len (zv L)]).
  - (* extra bits *)
    assert (O0: e_op e - 16 <> 0) by (intro Z0; apply H; rewrite Z0; reflexivity).
    rewrite (proj2 (Z.eqb_neq _ _) O0) in ELX. cbn [negb] in ELX.
    apply pair_equal_spec in ELX as [EL EM].
    set (opx := e_op e - 16) in *.
    assert (Hopx: 1 <= opx <= 5) by lia.
    destruct (lb_lq_facts m opx FW ltac:(lia) BUD B30) as (FWq & Bq & BUDq & Sq & Iq & Aq & Oq).
    forward_if (fs_state F (lb_lq opx m) [] [temp _here (entry_ptr F t j); temp _op (zv opx); temp _len (zv (e_val e))]).
    + (* one byte *)
      assert (H1: 1 <= m_have m) by lia.
      pose proof (mw_nx _ W) as NX.
      pose proof INOK as INOK'.
      destruct (f_ib F) as [|ish ip ilo inb ic] eqn:IB.
      { exfalso. unfold in_ok in INOK. unfold m_have in H1. rewrite INOK, Zlength_nil in H1. lia. }
      destruct INOK' as (Hsh & Hip & Hlo & Hn & Hic & Hmax & Hsub & Hbytes).
      cbn [in_ptr in_rep].
      assert_PROP (field_compatible (tarray tuchar inb) [] ip) by entailer!.
      forward. forward.
      rewrite lb_ptr_inc by auto.
      assert (Hj: 0 <= m_nx m < Zlength (m_inp m)) by (unfold m_have in H1; lia).
      pose proof (lb_in_byte _ _ _ _ _ _ _ INOK Hj) as HBYTE.
      pose proof (lb_bytes_ok_Znth _ _ Hbytes Hj) as HBR.
      rewrite (offset_val_field_address_tuchar inb (ilo + m_nx m) ip) by (auto; lia).
      forward.
      { rewrite HBYTE. entailer!. try (rewrite Int.unsigned_repr by rep_lia); rep_lia. }
      rewrite HBYTE.
      forward.
      { entailer!. change (Int.unsigned Int64.iwordsize') with 64. lia. }
      forward.
      rewrite (lb_pull_hold m (m_inp m)) by (auto; lia).
      rewrite add_repr, <- (lb_pull_bits m) by lia.
      replace (ilo + m_nx m + 1) with (ilo + m_nx (fpull m)) by (rewrite lb_fpull_nx; lia).
      replace (lb_lq opx m) with (fpull m) by (unfold lb_lq; rewrite (proj2 (Z.ltb_lt _ _)) by lia; reflexivity).
      unfold fs_state, fs_locals. rewrite !lb_fs_sep_pull. unfold fs_sep. cbn [app].
      rewrite IB. cbn [in_ptr in_rep]. rewrite !lb_fpull_s, !lb_fpull_inp, !lb_fpull_ow, !lb_fpull_aout.
      entailer!. apply derives_refl.
    + (* enough bits *)
      forward.
      replace (lb_lq opx m) with m by (unfold lb_lq; rewrite (proj2 (Z.ltb_ge _ _)) by lia; reflexivity).
      unfold fs_state, fs_locals, fs_sep; cbn [app]. entailer!. apply derives_refl.
    + unfold fs_state, fs_locals, fs_sep; cbn [app].
      pose proof (mw_hold _ (fast_ok_mwf _ FWq)) as HHq.
      forward.
      { entailer!. change (Int.unsigned Int.iwordsize) with 32. lia. }
      rewrite lb_len_add by (auto; lia).
      forward.
      { entailer!. change (Int.unsigned Int64.iwordsize') with 64. lia. }
      rewrite lb_shru by (auto; lia).
      forward.
      rewrite sub_repr.
      rewrite <- EL, <- EM.
      assert (P: 0 < 2 ^ opx) by (apply Z.pow_pos_nonneg; lia).
      assert (P5: 2 ^ opx <= 32) by (change 32 with (2 ^ 5); apply Z.pow_le_mono_r; lia).
      pose proof (Z.mod_pos_bound (m_hold (lb_lq opx m)) (2 ^ opx) P).
      unfold len_ok in LO. specialize (LO OP). fold opx in LO.
      rewrite (lb_u32 (e_val e + _)) by rep_lia.
      unfold fs_state, fs_locals. rewrite lb_fs_sep_hb. unfold fs_sep. cbn [app].
      rewrite lb_hold_hb, lb_bits_hb, lb_nx_hb, lb_s_hb, lb_inp_hb, lb_ow_hb, lb_aout_hb.
      rewrite lb_u32 by rep_lia.
      entailer!.
  - (* none *)
    assert (O0: e_op e - 16 = 0) by (apply repr_inj_unsigned; [rep_lia | rep_lia | exact H]).
    rewrite (proj2 (Z.eqb_eq _ _) O0) in ELX. cbn [negb] in ELX.
    apply pair_equal_spec in ELX as [EL EM]. subst L m1.
    forward.
    unfold fs_state, fs_locals, fs_sep; cbn [app]. entailer!. apply derives_refl.
  - exact HX.
Qed.

(* if (bits < 15) { two bytes } *)
Lemma lb_refill_ok {Espec: OracleKind} (F: frame) (m1: mst) (L: Z) (X: statement) (R: ret_assert):
  fast_ok m1 -> 0 <= m_bits m1 <= 30 -> 28 <= 8 * m_have m1 + m_bits m1 -> in_ok (f_ib F) (m_inp m1) ->
  semax Delta_fast (fs_state F (refill2 m1) [] [temp _len (zv L)]) X R ->
  semax Delta_fast (fs_state F m1 [] [temp _len (zv L)]) (Ssequence s_lbD X) R.
Proof.
  intros FW B BUD INOK HX. destruct R as [Rn Rb Rc Rr].
  lb_simpl. unfold fs_state, fs_locals, fs_sep; cbn [app]. abbreviate_semax.
  pose proof (fast_ok_mwf _ FW) as W. pose proof (mwf_have _ W) as HV. pose proof (mw_hold _ W) as HH.
  forward_if (fs_state F (refill2 m1) [] [temp _len (zv L)]).
  - assert (H2: 2 <= m_have m1) by lia.
    replace (refill2 m1) with (fpull (fpull m1))
      by (unfold refill2; rewrite (proj2 (Z.ltb_lt _ _)) by lia; reflexivity).
    pose proof (mw_nx _ W) as NX.
    pose proof INOK as INOK'.
    destruct (f_ib F) as [|ish ip ilo inb ic] eqn:IB.
    { exfalso. unfold in_ok in INOK. unfold m_have in H2. rewrite INOK, Zlength_nil in H2. lia. }
    destruct INOK' as (Hsh & Hip & Hlo & Hn & Hc & Hmax & Hsub & Hbytes).
    cbn [in_ptr in_rep].
    assert_PROP (field_compatible (tarray tuchar inb) [] ip) by entailer!.
    forward. forward.
    rewrite lb_ptr_inc by auto.
    assert (Hj: 0 <= m_nx m1 < Zlength (m_inp m1)) by (unfold m_have in H2; lia).
    pose proof (lb_in_byte _ _ _ _ _ _ _ INOK Hj) as HBYTE.
    pose proof (lb_bytes_ok_Znth _ _ Hbytes Hj) as HBR.
    rewrite (offset_val_field_address_tuchar inb (ilo + m_nx m1) ip) by (auto; lia).
    forward.
    { entailer!. rewrite HBYTE. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    rewrite HBYTE.
    forward.
    { entailer!. change (Int.unsigned Int64.iwordsize') with 64. lia. }
    forward.
    rewrite (lb_pull_hold m1 (m_inp m1)) by (auto; lia).
    rewrite add_repr, <- (lb_pull_bits m1) by lia.
    replace (ilo + m_nx m1 + 1) with (ilo + m_nx (fpull m1)) by (rewrite lb_fpull_nx; lia).
    (* the second byte *)
    destruct (lb_fast_pull m1 FW ltac:(lia) ltac:(lia)) as (FWp & Bp & Hp & _).
    pose proof (mw_hold _ (fast_ok_mwf _ FWp)) as HHp.
    assert (Hj2: 0 <= m_nx (fpull m1) < Zlength (m_inp m1)) by (rewrite lb_fpull_nx; unfold m_have in H2; lia).
    pose proof (lb_in_byte _ _ _ _ _ _ _ INOK Hj2) as HBYTE2.
    pose proof (lb_bytes_ok_Znth _ _ Hbytes Hj2) as HBR2.
    forward. forward.
    rewrite lb_ptr_inc by auto.
    rewrite (offset_val_field_address_tuchar inb (ilo + m_nx (fpull m1)) ip) by (auto; lia).
    forward.
    { rewrite HBYTE2. entailer!. rewrite lb_fpull_nx in HBR2. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    rewrite HBYTE2.
    forward.
    { rewrite Bp. entailer!. change (Int.unsigned Int64.iwordsize') with 64. lia. }
    forward.
    rewrite (lb_pull_hold (fpull m1) (m_inp m1)) by (auto; lia).
    rewrite add_repr, <- (lb_pull_bits (fpull m1)) by lia.
    replace (ilo + m_nx (fpull m1) + 1) with (ilo + m_nx (fpull (fpull m1))) by (rewrite lb_fpull_nx; lia).
    replace (refill2 m1) with (fpull (fpull m1))
      by (unfold refill2; rewrite (proj2 (Z.ltb_lt _ _)) by lia; reflexivity).
    unfold fs_state, fs_locals. rewrite !lb_fs_sep_pull. unfold fs_sep. cbn [app].
    rewrite IB. cbn [in_ptr in_rep]. rewrite !lb_fpull_s, !lb_fpull_inp, !lb_fpull_ow, !lb_fpull_aout.
    entailer!.
  - forward.
    replace (refill2 m1) with m1 by (unfold refill2; rewrite (proj2 (Z.ltb_ge _ _)) by lia; reflexivity).
    unfold fs_state, fs_locals, fs_sep; cbn [app]. entailer!.
  - exact HX.
Qed.

(* dist = here->val; op &= 15; pulls; dist += ...; hold >>= op; bits -= op *)
Lemma lb_distx_ok {Espec: OracleKind} (TF: tab_focus_stmt) (F: frame) (m3: mst) (j: Z) (e3: entry) (L D: Z)
    (m4: mst) (X: statement) (R: ret_assert):
  fast_ok m3 -> 0 <= j < tab_size (i_distcode (m_s m3)) ->
  tab_entry lenfix_list distfix_list (m_s m3) (i_distcode (m_s m3)) j = e3 ->
  entry_ok e3 -> final_ok DISTS e3 -> Z.land (e_op e3) 16 <> 0 ->
  13 <= 8 * m_have m3 + m_bits m3 -> m_bits m3 <= 30 -> in_ok (f_ib F) (m_inp m3) -> readable_share (f_gsh F) ->
  distx e3 m3 = (D, m4) ->
  semax Delta_fast (fs_state F m4 [] [temp _len (zv L); temp _dist (zv D)]) X R ->
  semax Delta_fast
    (fs_state F m3 [] [temp _here (entry_ptr F (i_distcode (m_s m3)) j); temp _op (zv (e_op e3)); temp _len (zv L)])
    (Ssequence s_lbT1 (Ssequence s_lbT2 (Ssequence s_lbT3 (Ssequence s_lbT4 (Ssequence s_lbT5 (Ssequence s_lbT6 X)))))) R.
Proof.
  intros FW J TE EO FO A16 BUD B30 INOK SHG EDX HX. destruct R as [Rn Rb Rc Rr].
  lb_simpl. unfold fs_state, fs_locals, fs_sep; cbn [app]. abbreviate_semax.
  pose proof (fast_ok_mwf _ FW) as W. pose proof (mwf_have _ W) as HV. pose proof (mw_hold _ W) as HH.
  pose proof (mw_bits _ W) as HB.
  destruct (lb_dist_final e3 FO A16) as [OP EV].
  set (s := m_s m3) in *. set (t := i_distcode s) in *.
  assert (T: tref_ok t) by apply (sw_distcode _ (mw_s _ W)).
  assert (Hc: Zlength (i_codes s) = ENOUGH_CODES) by apply (proj1 (sw_codes _ (mw_s _ W))).
  sep_apply (TF F s t j T Hc J). Intros.
  unfold ent. rewrite TE.
  destruct EO as (Eo & Eb & Ev).
  assert (RS: readable_share (tab_sh F t)) by (clearbody t; destruct t; simpl; auto with share).
  forward. { lb_tcu. }
  forward.
  sep_apply (modus_ponens_wand (data_at (tab_sh F t) t_code (Vint (Int.repr (e_op e3)), (Vint (Int.repr (e_bits e3)), Vint (Int.repr (e_val e3)))) (entry_ptr F t j)) (tab_mem F s)).
  forward.
  rewrite and_repr, (lb_land15d _ OP).
  rewrite lb_distx_eq, (lb_land15d _ OP) in EDX.
  apply pair_equal_spec in EDX as [ED EM].
  set (opx := e_op e3 - 16) in *.
  assert (Hopx: 0 <= opx <= 13) by lia.
  destruct (lb_dq_facts m3 opx FW Hopx BUD B30) as (FWq & Bq & BUDq & Sq & Iq & Aq & Oq).
  forward_if (fs_state F (lb_dq opx m3) []
    [temp _here (entry_ptr F t j); temp _op (zv opx); temp _dist (zv (e_val e3)); temp _len (zv L)]).
  - (* one or two bytes *)
    assert (H1: 1 <= m_have m3) by lia.
    pose proof (mw_nx _ W) as NX.
    pose proof INOK as INOK'.
    destruct (f_ib F) as [|ish ip ilo inb ic] eqn:IB.
    { exfalso. unfold in_ok in INOK. unfold m_have in H1. rewrite INOK, Zlength_nil in H1. lia. }
    destruct INOK' as (Hsh & Hip & Hlo & Hn & Hic & Hmax & Hsub & Hbytes).
    cbn [in_ptr in_rep].
    assert_PROP (field_compatible (tarray tuchar inb) [] ip) by entailer!.
    forward. forward.
    rewrite lb_ptr_inc by auto.
    assert (Hj: 0 <= m_nx m3 < Zlength (m_inp m3)) by (unfold m_have in H1; lia).
    pose proof (lb_in_byte _ _ _ _ _ _ _ INOK Hj) as HBYTE.
    pose proof (lb_bytes_ok_Znth _ _ Hbytes Hj) as HBR.
    rewrite (offset_val_field_address_tuchar inb (ilo + m_nx m3) ip) by (auto; lia).
    forward.
    { rewrite HBYTE. entailer!. try (rewrite Int.unsigned_repr by rep_lia); rep_lia. }
    rewrite HBYTE.
    forward.
    { entailer!. change (Int.unsigned Int64.iwordsize') with 64. lia. }
    forward.
    rewrite (lb_pull_hold m3 (m_inp m3)) by (auto; lia).
    rewrite add_repr, <- (lb_pull_bits m3) by lia.
    replace (ilo + m_nx m3 + 1) with (ilo + m_nx (fpull m3)) by (rewrite lb_fpull_nx; lia).
    destruct (lb_fast_pull m3 FW ltac:(lia) ltac:(lia)) as (FWp & Bp & Hp & _).
    pose proof (mw_hold _ (fast_ok_mwf _ FWp)) as HHp.
    forward_if.
    + (* the second byte *)
      assert (HC2: m_bits (fpull m3) < opx) by (rewrite Bp; rewrite lb_u32, Int.unsigned_repr in H2 by rep_lia; lia).
      clear H2.
      assert (Hj2: 0 <= m_nx (fpull m3) < Zlength (m_inp m3)).
      { rewrite lb_fpull_nx. unfold m_have in *. lia. }
      pose proof (lb_in_byte _ _ _ _ _ _ _ INOK Hj2) as HBYTE2.
      pose proof (lb_bytes_ok_Znth _ _ Hbytes Hj2) as HBR2.
      forward. forward.
      rewrite lb_ptr_inc by auto.
      rewrite (offset_val_field_address_tuchar inb (ilo + m_nx (fpull m3)) ip) by (auto; lia).
      forward.
      { rewrite HBYTE2. entailer!. rewrite lb_fpull_nx in HBR2. try (rewrite Int.unsigned_repr by rep_lia); rep_lia. }
      rewrite HBYTE2.
      forward.
      { rewrite Bp. entailer!. change (Int.unsigned Int64.iwordsize') with 64. lia. }
      forward.
      rewrite (lb_pull_hold (fpull m3) (m_inp m3)) by (auto; lia).
      rewrite add_repr, <- (lb_pull_bits (fpull m3)) by lia.
      replace (ilo + m_nx (fpull m3) + 1) with (ilo + m_nx (fpull (fpull m3))) by (rewrite lb_fpull_nx; lia).
      replace (lb_dq opx m3) with (fpull (fpull m3))
        by (unfold lb_dq; rewrite (proj2 (Z.ltb_lt _ _) H); cbv zeta; rewrite (proj2 (Z.ltb_lt _ _) HC2); reflexivity).
      unfold fs_state, fs_locals. rewrite !lb_fs_sep_pull. unfold fs_sep. cbn [app].
      rewrite IB. cbn [in_ptr in_rep]. rewrite !lb_fpull_s, !lb_fpull_inp, !lb_fpull_ow, !lb_fpull_aout.
      entailer!. apply derives_refl.
    + assert (HC2: opx <= m_bits (fpull m3)) by (rewrite Bp; rewrite lb_u32, Int.unsigned_repr in H2 by rep_lia; lia).
      clear H2.
      forward.
      replace (lb_dq opx m3) with (fpull m3)
        by (unfold lb_dq; rewrite (proj2 (Z.ltb_lt _ _) H); cbv zeta; rewrite (proj2 (Z.ltb_ge _ _) HC2); reflexivity).
      unfold fs_state, fs_locals. rewrite !lb_fs_sep_pull. unfold fs_sep. cbn [app].
      rewrite IB. cbn [in_ptr in_rep]. rewrite !lb_fpull_s, !lb_fpull_inp, !lb_fpull_ow, !lb_fpull_aout.
      entailer!. apply derives_refl.
  - (* enough bits *)
    forward.
    replace (lb_dq opx m3) with m3 by (unfold lb_dq; rewrite (proj2 (Z.ltb_ge _ _)) by lia; reflexivity).
    unfold fs_state, fs_locals, fs_sep; cbn [app]. entailer!. apply derives_refl.
  - unfold fs_state, fs_locals, fs_sep; cbn [app].
    pose proof (mw_hold _ (fast_ok_mwf _ FWq)) as HHq.
    forward.
    { entailer!. change (Int.unsigned Int.iwordsize) with 32. lia. }
    rewrite lb_len_add by (auto; lia).
    forward.
    { entailer!. change (Int.unsigned Int64.iwordsize') with 64. lia. }
    rewrite lb_shru by (auto; lia).
    forward.
    rewrite sub_repr.
    subst D m4.
    assert (P: 0 < 2 ^ opx) by (apply Z.pow_pos_nonneg; lia).
    assert (P13: 2 ^ opx <= 8192) by (change 8192 with (2 ^ 13); apply Z.pow_le_mono_r; lia).
    pose proof (Z.mod_pos_bound (m_hold (lb_dq opx m3)) (2 ^ opx) P).
    eapply semax_pre; [| exact HX].
    unfold fs_state, fs_locals. rewrite lb_fs_sep_hb. unfold fs_sep. cbn [app].
    rewrite (lb_u32 (e_val e3 + _)) by rep_lia.
    rewrite lb_hold_hb, lb_bits_hb, lb_nx_hb, lb_s_hb, lb_inp_hb, lb_ow_hb, lb_aout_hb.
    rewrite lb_u32 by rep_lia.
    rewrite Sq, Iq, Aq, Oq.
    entailer!.
Qed.

(* strm->msg = "invalid distance code"; state->mode = BAD; break; *)
Lemma lb_bad_ok {Espec: OracleKind} (F: frame) (m3: mst) (j: Z) (e3: entry) (L: Z):
  fast_ok m3 -> writable_share (f_shs F) ->
  semax Delta_fast
    (fs_state F m3 [] [temp _here (entry_ptr F (i_distcode (m_s m3)) j); temp _op (zv (e_op e3)); temp _len (zv L)])
    s_lbelse (fpost F (false, set_bad m3 F_d_code)).
Proof.
  intros FW SHS.
  lb_simpl. unfold fs_state, fs_locals, fs_sep; cbn [app]. rewrite lb_rest_split. unfold strm_rep.
  abbreviate_semax.
  remember (f_gv F inflate.code._zcalloc) as zca eqn:EZA. remember (f_gv F inflate.code._zcfree) as zcf eqn:EZF.
  Intros.
  forward.
  forward.
  forward.
  unfold fpost. cbn [RA_break]. Exists (set_bad m3 F_d_code).
  unfold fs_state. rewrite lb_locals_bad. unfold fs_locals, fs_sep. cbn [app].
  rewrite lb_tab_bad, lb_win_bad, lb_ow_bad, lb_rest_mem_bad. unfold strm_rep.
  rewrite <- EZA, <- EZF. cbn [msg_ident].
  entailer!.
Qed.

(* if (op & 16) { ... } else { ... } *)
Lemma lb_if_ok {Espec: OracleKind} (TF: tab_focus_stmt) (CP: copy_stmt) (F: frame) (m3: mst) (j: Z) (e3: entry) (L: Z):
  fast_ok m3 -> m_mode m3 = LEN -> 0 <= j < tab_size (i_distcode (m_s m3)) ->
  tab_entry lenfix_list distfix_list (m_s m3) (i_distcode (m_s m3)) j = e3 ->
  entry_ok e3 -> final_ok DISTS e3 -> 3 <= L <= 258 ->
  13 <= 8 * m_have m3 + m_bits m3 -> m_bits m3 <= 30 -> 258 <= m_left m3 ->
  in_ok (f_ib F) (m_inp m3) -> out_ok (f_ob F) (m_aout m3) ->
  writable_share (f_shs F) -> readable_share (f_gsh F) ->
  semax Delta_fast
    (fs_state F m3 [] [temp _here (entry_ptr F (i_distcode (m_s m3)) j); temp _op (zv (e_op e3)); temp _len (zv L)])
    s_lbif (fpost F (lb_tail (m_s m3) L (e3, m3))).
Proof.
  intros FW MD J3 TE3 EO FO HL BUD B30 LEFT INOK OUTOK SHS SHG.
  rewrite lb_if_split. unfold fs_state, fs_locals, fs_sep; cbn [app].
  pose proof EO as (Eo & Eb & Ev).
  forward_if.
  - (* a distance code *)
    assert (A16: Z.land (e_op e3) 16 <> 0). { intro Z0. apply H. rewrite and_repr, Z0. reflexivity. }
    clear H.
    destruct (distx e3 m3) as [D m4] eqn:EDX.
    destruct (lb_distx_facts m3 e3 D m4 FW FO A16 BUD B30 EDX) as (HD & FW4 & S4 & I4 & A4 & O4).
    unfold POSTCONDITION, abbreviate. unfold lb_tail.
    destruct (Z.land (e_op e3) 16 =? 0) eqn:E; [apply Z.eqb_eq in E; contradiction|]. cbn [negb].
    rewrite EDX.
    rewrite lb_then_split.
    apply (lb_distx_ok TF F m3 j e3 L D m4); auto.
    rewrite <- S4.
    apply (CP Espec F m4 L D); auto.
    + unfold m_mode. rewrite S4. exact MD.
    + unfold m_left in LEFT. rewrite O4, A4. lia.
    + rewrite A4. exact OUTOK.
  - (* invalid *)
    assert (A16: Z.land (e_op e3) 16 = 0).
    { rewrite and_repr in H. apply Z.eqb_eq. rewrite <- lb_and_eq by lia. rewrite H. reflexivity. }
    clear H.
    unfold POSTCONDITION, abbreviate. unfold lb_tail. rewrite A16. cbn [Z.eqb negb].
    apply (lb_bad_ok F m3 j e3 L); auto.
Qed.

Lemma f5_lenbr_ok : tab_focus_stmt -> dwalk_facts_stmt -> walk_dist_stmt -> copy_stmt -> lenbr_stmt.
Proof.
  intros TF DWF WD CP Espec F m j e FW MD J TE EO OP EV LO BUD B30 LEFT INOK OUTOK SHS SHG.
  rewrite lb_split.
  destruct (lenx e m) as [L m1] eqn:ELX.
  destruct (lb_lenx_facts m e L m1 FW OP EV LO BUD B30 ELX)
    as (HL & FW1 & S1 & I1 & A1 & O1 & B1 & BUD1).
  rewrite (lb_flen_eq _ _ _ _ _ ELX).
  apply (lb_lenx_ok TF F m j e L m1); auto.
  destruct (lb_refill_facts m1 FW1 B1 BUD1) as (FW2 & S2 & I2 & A2 & O2 & B2 & BUD2).
  apply lb_refill_ok; [auto|auto|auto|rewrite I1; auto|].
  set (m2 := refill2 m1) in *.
  assert (MD2: m_mode m2 = LEN) by (unfold m_mode; rewrite S2, S1; exact MD).
  apply seq_assoc. eapply semax_seq'.
  { apply (WD Espec F m2 L FW2 MD2); auto; lia. }
  apply extract_exists_pre; intro j3.
  rewrite S2, S1.
  destruct (dwalk (m_s m) m2) as [e3 m3] eqn:EDW.
  rewrite <- S1, <- S2 in EDW.
  destruct (lb_dwalk_facts m2 e3 m3 DWF FW2 MD2 B2 EDW) as (EO3 & FO3 & FW3 & S3 & I3 & A3 & O3 & B3 & BUD3).
  cbn [fst snd].
  unfold fs_state at 1. apply semax_extract_PROP; intro J3. apply semax_extract_PROP; intro TE3.
  assert (SM: m_s m3 = m_s m) by congruence. rewrite <- SM in J3, TE3 |- *.
  apply (lb_if_ok TF CP F m3 j3 e3 L); auto.
  - unfold m_mode; rewrite S3; exact MD2.
  - lia.
  - lia.
  - unfold m_left in *. rewrite O3, A3, O2, A2, O1, A1. exact LEFT.
  - rewrite I3, I2, I1. exact INOK.
  - rewrite A3, A2, A1. exact OUTOK.
Qed.
