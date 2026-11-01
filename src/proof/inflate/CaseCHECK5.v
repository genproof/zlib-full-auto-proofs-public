(* inflate(), case CHECK (index 26) in Delta_cases5: if (wrap) { NEEDBITS(32); out -= left; strm->total_out +=
   out; state->total += out; if ((wrap & 4) && out) strm->adler = state->check = UPDATE_CHECK(check, put - out,
   out); out = left; if ((wrap & 4) && (flags ? hold : ZSWAP32(hold)) != check) { strm->msg = "incorrect data
   check"; mode = BAD; break; } INITBITS(); } state->mode = LENGTH; falls into LENGTH.  Kit: CKKit5.v. *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate.CaseHyps5.
Require Import Zlib.proof.inflate.MwfLemmas.
Require Import Zlib.proof.inflate.Steps2.
Require Import Zlib.proof.inflate.NeedKit5.
Require Import Zlib.proof.inflate.NeedBits3_5.
Require Import Zlib.proof.inflate.CKKit5.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Require Import Zlib.proof.crc32.Combine.

(* ---------------------------------------------------------------------------------------------- *)
(* the model of CHECK cut into the steps of the C code                                            *)

(* strm->total_out += out; state->total += out *)
Definition ck_tot (m: mst) (o: Z) : mst :=
  upd_s (set_m_tout m (u64 (m_tout m + o))) (fun s => set_i_total s (u64 (i_total s + o))).

(* if ((state->wrap & 4) && out) strm->adler = state->check = UPDATE_CHECK(state->check, put - out, out) *)
Definition ck_newcheck (m: mst) (o: Z) : Z :=
  update_check (i_flags (m_s m)) (i_check (m_s m)) (sublist (Zlength (m_ow m) - o) (Zlength (m_ow m)) (m_ow m)).
Definition ck_cond (m: mst) (o: Z) : bool := negb (Z.land (i_wrap (m_s m)) 4 =? 0) && negb (o =? 0).
Definition ck_upd (m: mst) (o: Z) : mst :=
  if ck_cond m o then set_m_adler (upd_s m (fun s => set_i_check s (ck_newcheck m o))) (ck_newcheck m o) else m.

(* the check comparison *)
Definition ck_bad (m: mst) : bool :=
  negb (Z.land (i_wrap (m_s m)) 4 =? 0) &&
  negb ((if i_flags (m_s m) =? 0 then swap32 (m_hold m) else m_hold m) =? i_check (m_s m)).

Lemma ck_upd_leave: forall m o, m_leave (ck_upd m o) = m_leave m.
Proof. intros. unfold ck_upd. destruct (ck_cond m o); reflexivity. Qed.

Lemma ck_upd_left: forall m o, m_left (ck_upd m o) = m_left m.
Proof. intros. unfold ck_upd. destruct (ck_cond m o); reflexivity. Qed.

Lemma c_CHECK_eq': forall m,
  i_wrap (m_s m) <> 0 -> m_leave (needbits 32 m) = 0 ->
  c_CHECK m =
  (let m1 := needbits 32 m in
   let o := u32 (m_out m1 - m_left m1) in
   let mc := set_m_out (ck_upd (ck_tot m1 o) o) (m_left (ck_upd (ck_tot m1 o) o)) in
   if ck_bad mc then IBrk (set_bad mc M_dcheck) else c_LENGTH (set_mode (initbits mc) LENGTH)).
Proof.
  intros m W L. unfold c_CHECK. rewrite (proj2 (Z.eqb_neq _ _) W). cbn [negb]. rewrite L.
  cbv zeta. change (0 =? 1) with false. cbv iota. clear L. generalize (needbits 32 m). intro m1.
  unfold ck_bad, ck_upd, ck_cond, ck_newcheck, ck_tot. reflexivity.
Qed.

Lemma c_CHECK_eq: forall m,
  i_wrap (m_s m) <> 0 -> m_leave (needbits 32 m) = 0 ->
  c_CHECK m =
  (let m1 := needbits 32 m in
   let o := u32 (m_out m1 - m_left m1) in
   let mc := set_m_out (ck_upd (ck_tot m1 o) o) (m_left m1) in
   if ck_bad mc then IBrk (set_bad mc M_dcheck) else c_LENGTH (set_mode (initbits mc) LENGTH)).
Proof.
  intros m W L. rewrite (c_CHECK_eq' m W L). cbv zeta. clear L. generalize (needbits 32 m). intro m1.
  rewrite ck_upd_left. reflexivity.
Qed.

Lemma c_CHECK_eq0: forall m, i_wrap (m_s m) = 0 -> c_CHECK m = c_LENGTH (set_mode m LENGTH).
Proof. intros m W. unfold c_CHECK. rewrite W. reflexivity. Qed.



(* ---------------------------------------------------------------------------------------------- *)
(* mwf of the steps                                                                               *)

Lemma ck_lrange_u64: forall x, lrange (u64 x).
Proof. intros x. unfold lrange, u64. pose proof (Z.mod_pos_bound x (2 ^ 64)). rep_lia. Qed.

Lemma ck_mwf_tot: forall m o, mwf m -> mwf (ck_tot m o).
Proof.
  intros m o W. destruct W as [MD S H]; constructor; auto; cbn [ck_tot upd_s set_m_s set_m_tout m_s m_h m_inp m_aout
    m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave m_adler m_tin m_tout m_snx m_sow m_mode] in *; auto.
  - destruct MD; constructor; auto.
  - destruct S; constructor; auto. apply ck_lrange_u64.
  - apply ck_lrange_u64.
Qed.

Lemma ck_newcheck_range: forall m o, mwf m -> lrange (ck_newcheck m o).
Proof.
  intros m o W.
  assert (IB: is_bytes (sublist (Zlength (m_ow m) - o) (Zlength (m_ow m)) (m_ow m))).
  { unfold is_bytes. apply Forall_sublist. apply (mw_ow _ W). }
  unfold ck_newcheck, update_check, lrange. destruct (i_flags (m_s m) =? 0).
  - pose proof (adler32_z_val_range (i_check (m_s m)) _ IB). rep_lia.
  - pose proof (ref_crc32_range (i_check (m_s m)) _ IB). unfold is32 in H. rep_lia.
Qed.

Lemma ck_mwf_upd: forall m o, mwf m -> mwf (ck_upd m o).
Proof.
  intros m o W. unfold ck_upd. destruct (ck_cond m o); [ | exact W].
  pose proof (ck_newcheck_range m o W) as R.
  destruct W as [MD S H]; constructor; auto; cbn [upd_s set_m_s set_m_adler m_s m_h m_inp m_aout
    m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave m_adler m_tin m_tout m_snx m_sow m_mode] in *; auto.
  - destruct MD; constructor; auto.
  - destruct S; constructor; auto.
Qed.

Lemma ck_mwf_out_late: forall m x, mwf m -> urange x ->
  (m_mode m = LENGTH \/ m_mode m = DONE \/ m_mode m = BAD) -> mwf (set_m_out m x).
Proof. intros m x W H M. destruct W; constructor; auto. Qed.

Lemma ck_swf3_plain: forall s, i_mode s = LENGTH -> swf3 s.
Proof.
  intros s E. constructor; rewrite E; intros; unfold decode_mode, HEAD, LENGTH, LEN_, LEN, LENEXT, DIST, DISTEXT,
    MATCH, LIT in *; lia.
Qed.

Lemma ck_mode_fin: forall m, mwf m -> m_mode m = CHECK -> mwf3 (set_mode m LENGTH).
Proof.
  intros m W M. split.
  - apply mwf_set_mode_plain; [exact W | unfold HEAD, LENGTH, SYNC; lia | unfold LENLENS, LENGTH; lia
      | unfold CODELENS, LENGTH; lia | unfold decode_mode, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT, LENGTH; lia
      | right; left; reflexivity].
  - apply ck_swf3_plain. reflexivity.
Qed.

Lemma ck_mwf3_fin: forall m1 o, mwf m1 ->
  mwf3 (set_mode (initbits (set_m_out (ck_upd (ck_tot m1 o) o) (m_left m1))) LENGTH).
Proof.
  intros m1 o W.
  pose proof (mwf_left _ W) as HL.
  assert (W2: mwf (ck_upd (ck_tot m1 o) o)) by (apply ck_mwf_upd, ck_mwf_tot, W).
  change (set_mode (initbits (set_m_out (ck_upd (ck_tot m1 o) o) (m_left m1))) LENGTH)
    with (set_m_out (set_mode (initbits (ck_upd (ck_tot m1 o) o)) LENGTH) (m_left m1)).
  split.
  - apply ck_mwf_out_late; [ | unfold urange; rep_lia | left; reflexivity].
    apply mwf_set_mode_plain; [apply mwf_initbits, W2 | unfold HEAD, LENGTH, SYNC; lia | unfold LENLENS, LENGTH; lia
      | unfold CODELENS, LENGTH; lia | unfold decode_mode, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT, LENGTH; lia
      | right; left; reflexivity].
  - apply ck_swf3_plain. reflexivity.
Qed.


(* ---------------------------------------------------------------------------------------------- *)
(* the statements after NEEDBITS(32)                                                              *)

Definition ck_tail : statement :=
  match case_body 26 with Ssequence (Ssequence _ (Sifthenelse _ (Ssequence _ t) _)) _ => t | _ => Sskip end.

Lemma ck_upd_out: forall m1 o L,
  set_m_out (ck_upd (ck_tot (set_m_out m1 o) o) o) L = set_m_out (ck_upd (ck_tot m1 o) o) L.
Proof.
  intros. unfold ck_upd.
  change (ck_cond (ck_tot (set_m_out m1 o) o) o) with (ck_cond (ck_tot m1 o) o).
  destruct (ck_cond (ck_tot m1 o) o); reflexivity.
Qed.

Lemma mem_rep_k_tout: forall F m x, mem_rep_k F (set_m_tout m x) = mem_rep_k F m.
Proof. reflexivity. Qed.
Lemma mem_rep_k_tot: forall F m o, mem_rep_k F (ck_tot m o) = mem_rep_k F m.
Proof. reflexivity. Qed.
Lemma mem_rep_k_out: forall F m x, mem_rep_k F (set_m_out m x) = mem_rep_k F m.
Proof. reflexivity. Qed.
Lemma mem_rep_k_upd: forall F m o, mem_rep_k F (ck_upd m o) = mem_rep_k F m.
Proof. intros. unfold ck_upd. destruct (ck_cond m o); reflexivity. Qed.

Lemma mem_rep_k_chk: forall F m c,
  mem_rep_k F (set_m_adler (upd_s m (fun s => set_i_check s c)) c) = mem_rep_k F m.
Proof. reflexivity. Qed.

Lemma ck_add_u64: forall a b, Int64.add (Int64.repr a) (Int64.repr b) = Int64.repr (u64 (a + b)).
Proof.
  intros. unfold Int64.add. apply Int64.eqm_samerepr. unfold u64.
  change (2 ^ 64) with Int64.modulus.
  apply Int64.eqm_trans with (a + b).
  - apply Int64.eqm_add; apply Int64.eqm_sym; apply Int64.eqm_unsigned_repr.
  - unfold Int64.eqm. apply Zbits.eqmod_mod. apply Int64.modulus_pos.
Qed.


Definition ck_rest3 : statement :=
  match ck_tail with Ssequence _ (Ssequence _ (Ssequence _ r)) => r | _ => Sskip end.
Definition ck_upd_stmt : statement := match ck_rest3 with Ssequence u _ => u | _ => Sskip end.
Definition ck_rest4 : statement := match ck_rest3 with Ssequence _ r => r | _ => Sskip end.

Lemma ck_tail_eq: exists s1 s2 s3, ck_tail = Ssequence s1 (Ssequence s2 (Ssequence s3 (Ssequence ck_upd_stmt ck_rest4))).
Proof. do 3 eexists. reflexivity. Qed.

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

Lemma ck_upd_ok {Espec: OracleKind} (F: frame) (mt: mst) (o: Z):
  frame_ok F -> lrange (i_check (m_s mt)) -> 0 <= i_wrap (m_s mt) <= 15 -> srange (i_flags (m_s mt)) ->
  m_out mt = o -> o = Zlength (m_ow mt) -> bytes_ok (m_ow mt) -> 0 <= o <= Int.max_signed ->
  Zlength (m_ow mt) <= m_aout mt ->
  semax Delta_cases5 (loop_state F mt) ck_upd_stmt (normal_ret_assert (loop_state F (ck_upd mt o))).
Proof.
  intros FOK RC RW RF EO HO BO Ho0 HOW. pose proof FOK as (HWS & HWH & HRG & HRT).
  cbv beta iota zeta delta [ck_upd_stmt ck_rest3 ck_tail case_body inflate_LS find_switch f_inflate fn_body ls_drop].
  unfold ck_upd. destruct (ck_cond mt o) eqn:Ec.
  2: { rewrite !loop_state_ksplit. unfold loop_state_k. rewrite EO.
       abbreviate_semax.
       forward.
       forward_if (temp _t'90 (Vint Int.zero)).
       - forward. entailer!.
         unfold ck_cond in Ec. rewrite (ck_flagbit _ _ H1) in Ec. cbn [negb andb] in Ec.
         apply negb_false_iff, Z.eqb_eq in Ec. rewrite Ec. reflexivity.
       - forward. entailer!.
       - forward_if.
         + exfalso. apply H1. reflexivity.
         + forward. entailer!. }
  unfold ck_cond in Ec. apply andb_prop in Ec. destruct Ec as [Ec1 Ec2].
  apply negb_true_iff, Z.eqb_neq in Ec1. apply negb_true_iff, Z.eqb_neq in Ec2.
  set (c := ck_newcheck mt o).
  destruct F as [gv shs strmp sp headp winp hsh xb nb cb ib ob gsh tsh dt vres vhere vlast vhbuf flush].
  destruct ob as [osh op olo on oc].
  cbn [f_ob] in *.
  rewrite !loop_state_ksplit. unfold loop_state_k. rewrite EO.
  abbreviate_semax.
  forward.
  forward_if (temp _t'90 (Vint Int.one)).
  { forward. entailer!. rewrite ck_tbool by rep_lia. rewrite (proj2 (Z.eqb_neq _ _) Ec2). reflexivity. }
  { exfalso. apply Ec1. apply Z.eqb_eq. apply (ck_flagbit0 _ _ H1); rep_lia. }
  forward_if; [ | exfalso; exact (Int.one_not_zero H1)].
  frame_simpl.
  destruct H0 as (Hosh & Hop & Holo & Haout & Hlo & Hoc & Hon).
  forward.
  assert (Hc: c = update_check (i_flags (m_s mt)) (i_check (m_s mt)) (m_ow mt)).
  { unfold c, ck_newcheck. rewrite <- HO. rewrite Z.sub_diag, HO, sublist_same by reflexivity. reflexivity. }
  forward_if (temp _t'86 (Vlong (Int64.repr c))).
  { (* crc32 *)
    forward.
    forward_call (i_check (m_s mt), offset_val olo op, o, false, osh, op, olo, on,
                  sublist 0 olo oc ++ byte_vals (m_ow mt) ++ sublist (olo + Zlength (m_ow mt)) on oc,
                  m_ow mt, false, Ews, gv, tsh).
    { apply prop_right. destruct op; try contradiction. simpl. unfold sem_sub_pi. simpl.
      rewrite Ptrofs.mul_commut, Ptrofs.mul_one. unfold Ptrofs.of_intu, Ptrofs.of_int.
      rewrite Int.unsigned_repr by rep_lia.
      rewrite <- HO. rewrite <- ptrofs_add_repr, <- Ptrofs.add_assoc.
      rewrite Ptrofs.sub_add_opp, Ptrofs.add_assoc, Ptrofs.add_neg_zero, Ptrofs.add_zero. reflexivity. }
    { rewrite <- ck_da_cs_crc. cancel. }
    { split; [ | apply cbuf_valid_pos; lia]. unfold cbuf_ok. split; [reflexivity | ]. split; [auto | ].
      split; [lia | ]. split; [lia | ]. split; [lia | ]. split; [exact BO | ].
      rewrite HO. unfold bytes_rep, byte_vals. autorewrite with sublist. list_solve. }
    forward.
    rewrite Hc. unfold update_check. rewrite (proj2 (Z.eqb_neq _ _) H0'). rewrite <- ck_da_cs_crc.
    entailer!. }
  { (* adler32 *)
    forward.
    forward_call (i_check (m_s mt), offset_val olo op, o, false, osh, op, olo, on,
                  sublist 0 olo oc ++ byte_vals (m_ow mt) ++ sublist (olo + Zlength (m_ow mt)) on oc,
                  m_ow mt, false, Ews).
    { apply prop_right. destruct op; try contradiction. simpl. unfold sem_sub_pi. simpl.
      rewrite Ptrofs.mul_commut, Ptrofs.mul_one. unfold Ptrofs.of_intu, Ptrofs.of_int.
      rewrite Int.unsigned_repr by rep_lia.
      rewrite <- HO. rewrite <- ptrofs_add_repr, <- Ptrofs.add_assoc.
      rewrite Ptrofs.sub_add_opp, Ptrofs.add_assoc, Ptrofs.add_neg_zero, Ptrofs.add_zero. reflexivity. }
    { rewrite <- ck_da_cs_adler. cancel. }
    { split; [ | apply cbuf_valid_pos; lia]. unfold cbuf_ok. split; [reflexivity | ]. split; [auto | ].
      split; [lia | ]. split; [lia | ]. split; [lia | ]. split; [exact BO | ].
      rewrite HO. unfold bytes_rep, byte_vals. autorewrite with sublist. list_solve. }
    forward.
    assert (F0: i_flags (m_s mt) = 0) by (apply ck_int_zero; [unfold srange in RF; rep_lia | assumption]).
    rewrite Hc. unfold update_check. rewrite F0, Z.eqb_refl. rewrite <- ck_da_cs_adler.
    entailer!. }
  forward. forward.
  unfold strm_k, strm_rep.
  remember (gv _zcalloc) as zca eqn:Hzca. remember (gv _zcfree) as zcf eqn:Hzcf.
  forward.
  rewrite mem_rep_k_chk. unfold strm_k, strm_rep. frame_simpl_goal. rewrite <- Hzca, <- Hzcf. mnorm_goal.
  change (m_have (set_m_adler (upd_s mt (fun s : istate => set_i_check s c)) c)) with (m_have mt).
  change (m_left (set_m_adler (upd_s mt (fun s : istate => set_i_check s c)) c)) with (m_left mt).
  clearbody c. entailer!.
  unfold out_ok. split; [exact Hosh | ]. split; [exact Hop | ]. repeat split; auto; lia.
Qed.


Definition ck_cmp_stmt : statement := match ck_rest4 with Ssequence _ (Ssequence c _) => c | _ => Sskip end.
Definition ck_init_stmt : statement := match ck_rest4 with Ssequence _ (Ssequence _ c) => c | _ => Sskip end.

Lemma ck_rest4_eq: exists s1, ck_rest4 = Ssequence s1 (Ssequence ck_cmp_stmt ck_init_stmt).
Proof. eexists. reflexivity. Qed.


(* ZSWAP32(hold) as the code computes it on an unsigned long *)
Lemma ck_swap_eval: forall q, lrange q ->
  Int64.add
    (Int64.add
       (Int64.add (Int64.and (Int64.shru (Int64.repr q) (Int64.repr 24)) (Int64.repr 255))
          (Int64.and (Int64.shru (Int64.repr q) (Int64.repr 8)) (Int64.repr 65280)))
       (Int64.shl (Int64.repr (Z.land q 65280)) (Int64.repr 8)))
    (Int64.shl (Int64.repr (Z.land q 255)) (Int64.repr 24)) = Int64.repr (swap32 q).
Proof.
  intros q R. unfold lrange in R.
  assert (P1: Int64.and (Int64.shru (Int64.repr q) (Int64.repr 24)) (Int64.repr 255) =
              Int64.repr (Z.shiftr q 24 mod 256)).
  { unfold Int64.and, Int64.shru. rewrite (Int64.unsigned_repr q) by rep_lia.
    change (Int64.unsigned (Int64.repr 24)) with 24. change (Int64.unsigned (Int64.repr 255)) with 255.
    pose proof (Zshiftr_range q 24 R ltac:(lia)). rewrite Int64.unsigned_repr by rep_lia.
    change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. }
  assert (P2: Int64.and (Int64.shru (Int64.repr q) (Int64.repr 8)) (Int64.repr 65280) =
              Int64.repr (Z.land (Z.shiftr q 8) 65280)).
  { unfold Int64.and, Int64.shru. rewrite (Int64.unsigned_repr q) by rep_lia.
    change (Int64.unsigned (Int64.repr 8)) with 8. change (Int64.unsigned (Int64.repr 65280)) with 65280.
    pose proof (Zshiftr_range q 8 R ltac:(lia)). rewrite Int64.unsigned_repr by rep_lia. reflexivity. }
  assert (P3: Int64.shl (Int64.repr (Z.land q 65280)) (Int64.repr 8) = Int64.repr (Z.shiftl (Z.land q 65280) 8)).
  { unfold Int64.shl. pose proof (ck_land_range q 65280 ltac:(lia)).
    rewrite Int64.unsigned_repr by rep_lia. reflexivity. }
  assert (P4: Int64.shl (Int64.repr (Z.land q 255)) (Int64.repr 24) = Int64.repr (Z.shiftl (q mod 256) 24)).
  { unfold Int64.shl. pose proof (ck_land_range q 255 ltac:(lia)).
    rewrite Int64.unsigned_repr by rep_lia. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. }
  rewrite P1, P2, P3, P4, !add64_repr. reflexivity.
Qed.


Lemma ck_swap_range: forall q, lrange q -> lrange (swap32 q).
Proof.
  intros q R. unfold lrange in *. unfold swap32.
  pose proof (Z.mod_pos_bound (Z.shiftr q 24) 256 ltac:(lia)) as A.
  pose proof (ck_land_range (Z.shiftr q 8) 65280 ltac:(lia)) as B.
  pose proof (ck_land_range q 65280 ltac:(lia)) as C.
  pose proof (Z.mod_pos_bound q 256 ltac:(lia)) as D.
  rewrite !Z.shiftl_mul_pow2 by lia. rep_lia.
Qed.

Lemma ck_cmp_val: forall x y, lrange x -> lrange y ->
  bool2val (Int64.cmpu Cne (Int64.repr x) (Int64.repr y)) = Vint (Int.repr (if negb (x =? y) then 1 else 0)).
Proof.
  intros x y Rx Ry. unfold Int64.cmpu. destruct (Z.eqb_spec x y).
  - subst. rewrite Int64.eq_true. reflexivity.
  - rewrite Int64.eq_false; [reflexivity | ]. intro E. apply (f_equal Int64.unsigned) in E.
    unfold lrange in *. rewrite !Int64.unsigned_repr in E by rep_lia. contradiction.
Qed.

Lemma ck_cmp_ok {Espec: OracleKind} (F: frame) (mc m: mst) (R: ret_assert):
  frame_ok F -> lrange (m_hold mc) -> lrange (i_check (m_s mc)) -> 0 <= i_wrap (m_s mc) <= 15 ->
  srange (i_flags (m_s mc)) ->
  RA_break R = RA_normal (case_post2 F m) ->
  (ck_bad mc = true -> stepf2 (f_flush F) lenfix_list distfix_list m = IBrk (set_bad mc M_dcheck)) ->
  semax Delta_cases5 (loop_state F mc) ck_cmp_stmt (overridePost (!! (ck_bad mc = false) && loop_state F mc) R).
Proof.
  intros FOK RH RC RW RF HR HB. pose proof FOK as (HWS & HWH & HRG & HRT).
  cbv beta iota zeta delta [ck_cmp_stmt ck_rest4 ck_rest3 ck_tail case_body inflate_LS find_switch f_inflate fn_body ls_drop].
  rewrite loop_state_ksplit. unfold loop_state_k.
  abbreviate_semax.
  forward.
  forward_if (temp _t'91 (Vint (Int.repr (if ck_bad mc then 1 else 0)))).
  { forward.
    forward_if (temp _t'92 (Vlong (Int64.repr (if i_flags (m_s mc) =? 0 then swap32 (m_hold mc) else m_hold mc)))).
    { forward. entailer!.
      destruct (Z.eqb_spec (i_flags (m_s mc)) 0) as [E | E]; [ | reflexivity].
      exfalso. match goal with H: Int.repr (i_flags (m_s mc)) <> Int.zero |- _ => apply H; rewrite E; reflexivity end. }
    { forward. entailer!.
      assert (F0: i_flags (m_s mc) = 0) by (apply ck_int_zero; [unfold srange in RF; rep_lia | assumption]).
      rewrite F0, Z.eqb_refl, ck_swap_eval by exact RH. reflexivity. }
    forward. forward.
    destruct R as [Rn Rb Rc Rr]. cbn [RA_normal].
    entailer!.
    assert (RX: lrange (if i_flags (m_s mc) =? 0 then swap32 (m_hold mc) else m_hold mc))
      by (destruct (i_flags (m_s mc) =? 0); [apply ck_swap_range | ]; exact RH).
    rewrite (ck_cmp_val _ _ RX RC). unfold ck_bad. rewrite (ck_flagbit _ _ H1). reflexivity. }
  { forward.
    destruct R as [Rn Rb Rc Rr]. cbn [RA_normal].
    entailer!.
    unfold ck_bad. rewrite (ck_flagbit0 _ _ H1) by rep_lia. reflexivity. }
  forward_if.
  { assert (Eb: ck_bad mc = true) by (destruct (ck_bad mc); [reflexivity | exfalso; apply H1; reflexivity]).
    unfold abbreviate in POSTCONDITION, MORE_COMMANDS. subst POSTCONDITION MORE_COMMANDS.
    match goal with |- semax _ _ _ ?P =>
      assert (HR2: RA_break P = RA_normal (case_post2 F m)) by (destruct R; exact HR);
      eapply semax_pre; [ | apply (bad_okk_dcheck F HWS mc m P HR2 (HB Eb))] end.
    rewrite loop_state_ksplit. unfold loop_state_k. entailer!. }
  { assert (Eb: ck_bad mc = false) by (destruct (ck_bad mc); [exfalso; exact (Int.one_not_zero H1) | reflexivity]).
    forward.
    destruct R as [Rn Rb Rc Rr]. cbn [RA_normal].
    entailer!. }
Qed.

Lemma ck_tail_ok {Espec: OracleKind} (F: frame) (m m1: mst) (R: ret_assert):
  frame_ok F -> mwf m1 -> m_out m1 = m_aout m1 ->
  RA_break R = RA_normal (case_post2 F m) ->
  (let o := Zlength (m_ow m1) in let mc := set_m_out (ck_upd (ck_tot m1 o) o) (m_left m1) in
   (ck_bad mc = true -> stepf2 (f_flush F) lenfix_list distfix_list m = IBrk (set_bad mc M_dcheck)) /\
   (ck_bad mc = false -> loop_state F (initbits mc) |-- RA_normal R)) ->
  semax Delta_cases5 (loop_state F m1) ck_tail R.
Proof.
  intros FOK W OE HR HBN. cbv zeta in HBN. destruct HBN as [HB HN].
  pose proof FOK as (HWS & HWH & HRG & HRT).
  set (o := Zlength (m_ow m1)) in *.
  assert (Ho: m_out m1 - m_left m1 = o) by (unfold m_left, o; lia).
  pose proof (mwf_left _ W) as HLEFT. pose proof (mw_ow _ W) as WOW. pose proof (mw_aout _ W) as WAOUT.
  assert (Ho0: 0 <= o <= Int.max_signed) by (unfold o; pose proof (Zlength_nonneg (m_ow m1)); lia).
  assert (Hod: o = Zlength (m_ow m1)) by reflexivity. clearbody o.
  cbv beta iota zeta delta [ck_tail case_body inflate_LS find_switch f_inflate fn_body ls_drop].
  (* out = out - left *)
  apply semax_seq' with (P' := loop_state F (set_m_out m1 o)).
  { unfold loop_state. abbreviate_semax. forward. rewrite sub_repr, Ho. clear Ho Hod. entailer!.
    apply derives_refl. }
  set (mA := set_m_out m1 o).
  assert (HmA: mA = set_m_out m1 o) by reflexivity. clearbody mA.
  assert (EoA: m_out mA = o) by (rewrite HmA; reflexivity).
  (* strm->total_out += out *)
  apply semax_seq' with (P' := loop_state F (set_m_tout mA (u64 (m_tout mA + o)))).
  { rewrite !loop_state_ksplit. unfold loop_state_k, strm_k, strm_rep.
    rewrite mem_rep_k_tout.
    abbreviate_semax.
    remember (f_gv F _zcalloc) as zca eqn:Hzca. remember (f_gv F _zcfree) as zcf eqn:Hzcf.
    forward. forward. clear Ho Hod.
    replace (Int.unsigned (Int.repr (m_out mA))) with o by (rewrite EoA, Int.unsigned_repr by rep_lia; reflexivity).
    rewrite ck_add_u64.
    mnorm_goal.
    entailer!. }
  (* state->total += out *)
  apply semax_seq' with (P' := loop_state F (ck_tot mA o)).
  { clear Ho Hod. rewrite !loop_state_ksplit. unfold loop_state_k, strm_k. rewrite mem_rep_k_tot, mem_rep_k_tout.
    unfold ck_tot. mnorm_goal. rewrite EoA.
    abbreviate_semax.
    forward. forward.
    rewrite Int.unsigned_repr by rep_lia. rewrite ck_add_u64.
    entailer!. }
  subst mA.
  pose proof (ck_mwf_tot m1 o W) as Wt.
  pose proof (ck_mwf_upd _ o Wt) as Wu.
  (* the UPDATE_CHECK block *)
  apply semax_seq' with (P' := loop_state F (ck_upd (ck_tot (set_m_out m1 o) o) o)).
  { apply ck_upd_ok; auto.
    - exact (sw_check _ (mw_s _ Wt)).
    - exact (sw_wrap_range _ (mw_s _ Wt)).
    - exact (sw_flags _ (mw_s _ Wt)).
    - exact (proj2 WOW).
    - exact (proj1 WOW). }
  (* out = left *)
  apply semax_seq' with (P' := loop_state F (set_m_out (ck_upd (ck_tot m1 o) o) (m_left m1))).
  { rewrite <- (ck_upd_out m1 o (m_left m1)).
    unfold loop_state. abbreviate_semax. forward. clear Ho Hod.
    entailer!.
    - rewrite ck_upd_left. reflexivity.
    - apply derives_refl. }
  set (mc := set_m_out (ck_upd (ck_tot m1 o) o) (m_left m1)) in *.
  apply semax_seq with (Q := !! (ck_bad mc = false) && loop_state F mc).
  { apply (ck_cmp_ok F mc m R); auto.
    - exact (mw_hold _ Wu).
    - exact (sw_check _ (mw_s _ Wu)).
    - exact (sw_wrap_range _ (mw_s _ Wu)).
    - exact (sw_flags _ (mw_s _ Wu)). }
  apply semax_extract_prop. intros Eb.
  eapply ConseqFacts.semax_post''; [ | apply semax_initbits_k].
  eapply derives_trans; [apply andp_left2, derives_refl | exact (HN Eb)].
Qed.

Lemma ck_o_eq: forall m1, mwf m1 -> m_out m1 = m_aout m1 -> u32 (m_out m1 - m_left m1) = Zlength (m_ow m1).
Proof.
  intros m1 W OE. unfold u32, m_left. rewrite OE.
  pose proof (mw_ow _ W) as A. pose proof (mw_aout _ W) as B. pose proof (Zlength_nonneg (m_ow m1)).
  rewrite Z.mod_small; rep_lia.
Qed.

Lemma case_CHECK5 {Espec: OracleKind} (F: frame) : frame_ok5 F -> case_ok5 F LENGTH 27 -> case_ok5 F CHECK 26.
Proof.
  intros [FOK FL] HY m HM HL [W W3].
  pose proof FOK as (HWS & HWH & HRG & HRT).
  pose proof (sw_wrap_range _ (mw_s _ W)) as RW.
  apply (case_fallthrough5 F m LENGTH 26); [lia | exact HY | ].
  case_body_stmt.
  apply semax_seq with (Q := EX m': mst,
    !! (stepf2 (f_flush F) lenfix_list distfix_list m = c_LENGTH (set_mode m' LENGTH) /\ m_leave m' = 0 /\
        mwf3 (set_mode m' LENGTH)) && loop_state F m').
  2: { apply extract_exists_pre. intro m'. apply semax_extract_prop. intros (E1 & L1 & W1).
       eapply ConseqFacts.semax_post''; [ | apply semax_store_mode5].
       unfold fall_post5. Exists (set_mode m' LENGTH).
       apply andp_right; [ | apply andp_left2; apply derives_refl].
       apply prop_right. split.
       { rewrite E1. symmetry. exact (stepf2_LENGTH (f_flush F) lenfix_list distfix_list (set_mode m' LENGTH) eq_refl). }
       split; [reflexivity | ]. split; [exact L1 | exact W1]. }
  assert (E0: i_wrap (m_s m) = 0 -> stepf2 (f_flush F) lenfix_list distfix_list m = c_LENGTH (set_mode m LENGTH)).
  { intro Z0. rewrite (stepf2_CHECK _ _ _ _ HM). apply c_CHECK_eq0. exact Z0. }
  assert (EL: i_wrap (m_s m) <> 0 -> m_leave (needbits 32 m) = 1 ->
              stepf2 (f_flush F) lenfix_list distfix_list m = IBrk (needbits 32 m)).
  { intros Z0 E. rewrite (stepf2_CHECK _ _ _ _ HM). unfold c_CHECK. rewrite (proj2 (Z.eqb_neq _ _) Z0).
    cbv zeta. rewrite E. reflexivity. }
  assert (EC: i_wrap (m_s m) <> 0 -> m_leave (needbits 32 m) = 0 ->
     let m1 := needbits 32 m in let o := Zlength (m_ow m1) in
     let mc := set_m_out (ck_upd (ck_tot m1 o) o) (m_left m1) in
     stepf2 (f_flush F) lenfix_list distfix_list m =
       if ck_bad mc then IBrk (set_bad mc M_dcheck) else c_LENGTH (set_mode (initbits mc) LENGTH)).
  { intros Z0 L0. rewrite (stepf2_CHECK _ _ _ _ HM). rewrite (c_CHECK_eq m Z0 L0). cbv zeta.
    rewrite ck_o_eq; [reflexivity | apply mwf_needbits; [exact W | lia] | ].
    destruct (ck_needbits_f_keep 4 32 m) as (_ & _ & _ & A4 & _ & _ & A7 & _).
    unfold needbits. rewrite A4, A7. apply mwf_out_eq; [exact W | | | ]; rewrite HM; unfold CHECK, LENGTH, DONE, BAD; lia. }
  rewrite loop_state_ksplit. unfold loop_state_k.
  abbreviate_semax.
  forward.
  forward_if.
  - (* wrap *)
    assert (Z0: i_wrap (m_s m) <> 0) by (intro Z1; rewrite Z1 in *; contradiction).
    eapply semax_pre; [ | eapply (semax_needbits_seq5 F m m 32)].
    { rewrite loop_state_ksplit. unfold loop_state_k. entailer!. }
    { apply semax_needbits_CHECK5; auto; lia. }
    { exact W. }
    { lia. }
    { reflexivity. }
    { exact (EL Z0). }
    apply semax_extract_prop. intros HL0.
    pose proof (EC Z0 HL0) as E. cbv zeta in E. clear EL EC E0.
    pose proof (mwf_needbits 32 m W ltac:(lia)) as W1.
    assert (OE1: m_out (needbits 32 m) = m_aout (needbits 32 m)).
    { destruct (ck_needbits_f_keep 4 32 m) as (_ & _ & _ & A4 & _ & _ & A7 & _).
      unfold needbits. rewrite A4, A7. apply mwf_out_eq; [exact W | | | ]; rewrite HM; unfold CHECK, LENGTH, DONE, BAD; lia. }
    set (m1 := needbits 32 m) in *. clearbody m1.
    apply (ck_tail_ok F m m1); auto.
    split.
    + intro Eb. rewrite E, Eb. reflexivity.
    + intro Eb. unfold abbreviate in POSTCONDITION. subst POSTCONDITION. cbn [RA_normal overridePost].
      Exists (initbits (set_m_out (ck_upd (ck_tot m1 (Zlength (m_ow m1))) (Zlength (m_ow m1))) (m_left m1))).
      apply andp_right; [apply prop_right | apply derives_refl].
      split; [rewrite E, Eb; reflexivity | ].
      split; [unfold initbits; cbn [m_leave set_m_out set_m_bits set_m_hold]; rewrite ck_upd_leave; exact HL0 | ].
      apply ck_mwf3_fin. exact W1.
  - (* no wrap *)
    assert (Z0: i_wrap (m_s m) = 0) by (apply ck_int_zero; [rep_lia | assumption]).
    forward.
    Exists m. rewrite loop_state_ksplit. unfold loop_state_k.
    entailer!.
    pose proof (ck_mode_fin m W HM) as WM. pose proof (E0 Z0) as E0'.
    exact WM.
Qed.
