(* inflate_fast (BodyF5.v): the two table walks of the C code (F5Kit s_lhere/s_lloop, s_dhere/s_dloop). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inffast.code.
Require Import Zlib.proof.inffast.F5Kit.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* ---------------------------------------------------------------------------------------------- *)
(* the walk as the C code does it: one entry per pass                                              *)

Definition f5k_hb (m: mst) (h b: Z) : mst := set_m_bits (set_m_hold m h) b.

(* hold >>= here->bits; bits -= here->bits *)
Definition f5k_drop (e: entry) (mk: mst) : mst :=
  set_m_bits (set_m_hold mk (Z.shiftr (m_hold mk) (e_bits e))) (u32 (m_bits mk - e_bits e)).

(* what a pass at entry j of t with the machine mk needs, k passes of the model left *)
Fixpoint f5k_wok (lf: Z -> bool) (t: tref) (s: istate) (k: nat) (j: Z) (mk: mst) : Prop :=
  let e := tab_entry lenfix_list distfix_list s t j in
  m_s mk = s /\ 0 <= j < tab_size t /\ entry_ok e /\ e_bits e <= m_bits mk <= 30 /\ lrange (m_hold mk) /\
  (lf (e_op e) = true ->
    1 <= e_op e <= 15 /\
    match k with
    | O => False
    | S k' => f5k_wok lf t s k' (e_val e + m_hold (f5k_drop e mk) mod 2 ^ e_op e) (f5k_drop e mk)
    end).

Lemma f5k_fwalk_stop: forall lf t k e mk,
  (k = O \/ lf (e_op e) = false) ->
  fwalk_f lenfix_list distfix_list k lf t e mk = (e, f5k_drop e mk).
Proof.
  intros lf t k e mk [H|H].
  - subst k. reflexivity.
  - destruct k; simpl; [reflexivity|]. rewrite H. reflexivity.
Qed.

Lemma f5k_fwalk_link: forall lf t k e mk,
  lf (e_op e) = true ->
  fwalk_f lenfix_list distfix_list (S k) lf t e mk =
  fwalk_f lenfix_list distfix_list k lf t
    (tab_entry lenfix_list distfix_list (m_s mk) t (e_val e + m_hold (f5k_drop e mk) mod 2 ^ e_op e))
    (f5k_drop e mk).
Proof. intros. simpl. rewrite H. reflexivity. Qed.

Lemma f5k_drop_hb: forall e m h b,
  f5k_drop e (f5k_hb m h b) = f5k_hb m (Z.shiftr h (e_bits e)) (u32 (b - e_bits e)).
Proof. intros. reflexivity. Qed.

(* the kinds' link tests *)
Lemma f5k_link_sub: forall op, Z.land op 240 = 0 -> Z.land op 16 = 0 /\ Z.land op 64 = 0.
Proof.
  intros op H. split.
  - change 16 with (Z.land 240 16). rewrite Z.land_assoc, H. reflexivity.
  - change 64 with (Z.land 240 64). rewrite Z.land_assoc, H. reflexivity.
Qed.

Lemma f5k_len_link_true: forall op, islink LENS op = true -> len_link op = true.
Proof.
  intros op H. unfold islink in H. cbn in H. apply andb_prop in H as [H1 H2].
  apply Z.eqb_eq in H2. destruct (f5k_link_sub op H2) as [A B].
  unfold len_link. rewrite A, B. destruct (op =? 0); reflexivity || discriminate.
Qed.

Lemma f5k_dist_link_true: forall op, islink DISTS op = true -> dist_link op = true.
Proof.
  intros op H. unfold islink in H. cbn in H.
  apply Z.eqb_eq in H. destruct (f5k_link_sub op H) as [A B].
  unfold dist_link. rewrite A, B. reflexivity.
Qed.

Lemma f5k_len_final: forall e, final_ok LENS e -> len_link (e_op e) = false.
Proof.
  intros e H. unfold final_ok in H. cbn in H. unfold len_link.
  destruct H as [[H _] | [[H _] | [H | [H _]]]].
  - rewrite H. reflexivity.
  - assert (E: e_op e = 16 \/ e_op e = 17 \/ e_op e = 18 \/ e_op e = 19 \/ e_op e = 20 \/ e_op e = 21) by lia.
    destruct E as [E|[E|[E|[E|[E|E]]]]]; rewrite E; reflexivity.
  - rewrite H. reflexivity.
  - destruct (Z.land (e_op e) 64 =? 0) eqn:E; [apply Z.eqb_eq in E; contradiction|].
    rewrite !orb_true_r. reflexivity.
Qed.

Lemma f5k_dist_final: forall e, final_ok DISTS e -> dist_link (e_op e) = false.
Proof.
  intros e H. unfold final_ok in H. cbn in H. unfold dist_link.
  destruct H as [[H _] | [H _]].
  - assert (E: exists k, 0 <= k <= 13 /\ e_op e = 16 + k) by (exists (e_op e - 16); lia).
    destruct E as (k & K & E). rewrite E.
    assert (Z.land (16 + k) 16 = 16).
    { assert (k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/
              k = 10 \/ k = 11 \/ k = 12 \/ k = 13) by lia.
      repeat (destruct H0 as [H0|H0]; [subst k; reflexivity|]); subst k; reflexivity. }
    rewrite H0. reflexivity.
  - destruct (Z.land (e_op e) 64 =? 0) eqn:E; [apply Z.eqb_eq in E; contradiction|].
    rewrite orb_true_r. reflexivity.
Qed.

Lemma f5k_lrange_shiftr: forall h n, lrange h -> 0 <= n -> lrange (Z.shiftr h n).
Proof.
  intros h n [H0 H1] Hn. rewrite Z.shiftr_div_pow2 by lia. split.
  - apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia].
  - assert (0 < 2 ^ n) by (apply Z.pow_pos_nonneg; lia).
    pose proof (Z.div_le_upper_bound h (2 ^ n) h H). nia.
Qed.

Lemma f5k_wok_unfold: forall lf t s k j mk,
  f5k_wok lf t s k j mk <->
  (let e := tab_entry lenfix_list distfix_list s t j in
   m_s mk = s /\ 0 <= j < tab_size t /\ entry_ok e /\ e_bits e <= m_bits mk <= 30 /\ lrange (m_hold mk) /\
   (lf (e_op e) = true ->
     1 <= e_op e <= 15 /\
     match k with
     | O => False
     | S k' => f5k_wok lf t s k' (e_val e + m_hold (f5k_drop e mk) mod 2 ^ e_op e) (f5k_drop e mk)
     end)).
Proof. intros. destruct k; reflexivity. Qed.

(* the start of a walk on a valid table *)
Lemma f5k_wok_start: forall kind lf s t rb sz m,
  tvalid_b kind lenfix_list distfix_list s t rb sz -> sz <= tab_size t ->
  (forall op, islink kind op = true -> lf op = true) ->
  (forall e, final_ok kind e -> lf (e_op e) = false) ->
  m_s m = s -> 15 <= m_bits m <= 30 -> lrange (m_hold m) ->
  f5k_wok lf t s 2 (m_hold m mod 2 ^ rb) m.
Proof.
  intros kind lf s t rb sz m [R S T] Hsz HL HF Hs Hb Hh.
  assert (Hi: 0 <= m_hold m mod 2 ^ rb < 2 ^ rb) by (apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia).
  destruct (T _ Hi) as [Eok Rt]. cbv zeta in Rt.
  set (e := tab_entry lenfix_list distfix_list s t (m_hold m mod 2 ^ rb)) in *.
  apply f5k_wok_unfold. cbv zeta. fold e.
  destruct (islink kind (e_op e)) eqn:IL.
  - destruct Rt as (R1 & R2 & R3 & R4).
    split; [auto|]. split; [lia|]. split; [auto|]. split; [lia|]. split; [auto|].
    intros _. split; [lia|].
    set (m1 := f5k_drop e m).
    assert (Hj: 0 <= m_hold m1 mod 2 ^ e_op e < 2 ^ e_op e) by (apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia).
    destruct (R4 _ Hj) as (S1 & S2 & S3 & S4 & S5). cbv zeta in S1, S2, S3, S4, S5.
    set (e2 := tab_entry lenfix_list distfix_list s t (e_val e + m_hold m1 mod 2 ^ e_op e)) in *.
    assert (B1: m_bits m1 = m_bits m - rb).
    { unfold m1, f5k_drop. simpl. rewrite R1. unfold u32. apply Z.mod_small. lia. }
    apply f5k_wok_unfold. cbv zeta. fold e2.
    split; [unfold m1; simpl; auto|]. split; [lia|]. split; [auto|]. split; [lia|]. split.
    { unfold m1, f5k_drop; simpl. apply f5k_lrange_shiftr; auto. destruct Eok as (_ & ? & _); lia. }
    intros L. rewrite (HF _ S5) in L. discriminate.
  - destruct Rt as [R1 R2].
    split; [auto|]. split; [lia|]. split; [auto|]. split; [lia|]. split; [auto|].
    intros L. rewrite (HF _ R2) in L. discriminate.
Qed.

Lemma f5k_wok_len: forall m,
  fast_ok m -> m_mode m = LEN -> 15 <= m_bits m <= 30 ->
  f5k_wok len_link (i_lencode (m_s m)) (m_s m) 2 (m_hold m mod 2 ^ i_lenbits (m_s m)) m.
Proof.
  intros m [W (sz & Hsz & TV & _)] Hmd Hb.
  eapply f5k_wok_start; eauto using f5k_len_link_true, f5k_len_final.
  apply (mw_hold _ W).
Qed.

Lemma f5k_wok_dist: forall m,
  fast_ok m -> m_mode m = LEN -> 15 <= m_bits m <= 30 ->
  f5k_wok dist_link (i_distcode (m_s m)) (m_s m) 2 (m_hold m mod 2 ^ i_distbits (m_s m)) m.
Proof.
  intros m [W _] Hmd Hb.
  destruct (md_tables _ (mw_md _ W)) as [_ (sz & Hsz & TV)].
  { unfold decode_mode. right; left. exact Hmd. }
  eapply f5k_wok_start; eauto using f5k_dist_link_true, f5k_dist_final.
  apply (mw_hold _ W).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the C side                                                                                      *)

Lemma f5k_hold_hb: forall m h b, m_hold (f5k_hb m h b) = h.
Proof. reflexivity. Qed.
Lemma f5k_ms_hb: forall m h b, m_s (f5k_hb m h b) = m_s m.
Proof. reflexivity. Qed.

Lemma f5k_fs_sep_hb: forall F m h b, fs_sep F (f5k_hb m h b) = fs_sep F m.
Proof. reflexivity. Qed.

Lemma f5k_tab_isptr: forall F s t, tref_ok t -> tab_mem F s |-- !! isptr (tref_val (f_gv F) (f_sp F) t).
Proof.
  intros F s t T. unfold tab_mem. entailer!. destruct t; cbn [tref_val].
  - auto.
  - auto.
  - unfold codes_at. cbn in T. rewrite field_address0_offset.
    + destruct H as [Hp _]. destruct (f_sp F); try contradiction. simpl. auto.
    + eapply field_compatible0_cons_Tarray; [reflexivity | exact H | unfold ENOUGH_CODES in T; lia].
Qed.

Lemma f5k_add_long: forall p j, isptr p ->
  force_val (sem_add_ptr_long t_code p (Vlong (Int64.repr j))) = offset_val (4 * j) p.
Proof.
  intros p j P. destruct p; try contradiction. simpl.
  unfold sem_add_ptr_long. simpl. f_equal. f_equal.
  unfold Ptrofs.of_int64. rewrite ptrofs_mul_repr. apply Ptrofs.eqm_samerepr.
  apply Ptrofs.eqm_mult; [apply Ptrofs.eqm_refl|]. apply Ptrofs.eqm_sym. unfold Ptrofs.eqm.
  apply Int64.eqm_unsigned_repr.
Qed.

Lemma f5k_land_mask: forall h b, 0 <= h <= Int64.max_unsigned -> 0 <= b <= 30 ->
  Int64.and (Int64.repr h) (Int64.repr (2 ^ b - 1)) = Int64.repr (h mod 2 ^ b).
Proof.
  intros h b Hh Hb. unfold Int64.and. rewrite Int64.unsigned_repr by rep_lia.
  assert (0 < 2 ^ b <= 2 ^ 30) by (split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_le_mono_r; lia]).
  rewrite Int64.unsigned_repr by rep_lia.
  replace (2 ^ b - 1) with (Z.ones b) by (rewrite Z.ones_equiv; lia).
  rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma f5k_here0: forall p h rb, isptr p -> lrange h -> 0 <= rb <= 15 ->
  force_val (sem_binary_operation' Oadd (tptr t_code) tulong p
    (eval_binop Oand tulong tuint (Vlong (Int64.repr h)) (Vint (Int.repr (2 ^ rb - 1))))) =
  offset_val (4 * (h mod 2 ^ rb)) p.
Proof.
  intros p h rb P Hh Hrb.
  assert (0 < 2 ^ rb <= 2 ^ 15) by (split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_le_mono_r; lia]).
  unfold eval_binop, force_val2. simpl.
  rewrite Int.unsigned_repr by rep_lia.
  rewrite f5k_land_mask by (unfold lrange in Hh; lia).
  apply f5k_add_long; auto.
Qed.

Lemma f5k_shru: forall h n, lrange h -> 0 <= n <= 255 ->
  Int64.shru (Int64.repr h) (Int64.repr (Int.unsigned (Int.repr n))) = Int64.repr (Z.shiftr h n).
Proof.
  intros h n Hh Hn. unfold lrange in Hh. rewrite Int.unsigned_repr by rep_lia.
  unfold Int64.shru. rewrite !Int64.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma f5k_u32: forall x, 0 <= x <= Int.max_unsigned -> u32 x = x.
Proof. intros x H. unfold u32. apply Z.mod_small. rep_lia. Qed.

Definition f5k_vb (x: bool) : val := Vint (if x then Int.one else Int.zero).

Lemma f5k_and_eq: forall op c, 0 <= op <= 255 -> 0 <= c <= 255 ->
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

Lemma f5k_here1: forall p v h op, isptr p -> 0 <= v <= 65535 -> lrange h -> 1 <= op <= 15 ->
  force_val (sem_binary_operation' Oadd (tptr t_code) tulong
    (eval_binop Oadd (tptr t_code) tushort p (Vint (Int.repr v)))
    (eval_binop Oand tulong tuint (Vlong (Int64.repr h))
       (eval_binop Osub tuint tint (eval_binop Oshl tuint tuint (Vint (Int.repr 1)) (Vint (Int.repr op)))
          (Vint (Int.repr 1))))) =
  offset_val (4 * (v + h mod 2 ^ op)) p.
Proof.
  intros p v h op P Hv Hh Ho.
  assert (0 < 2 ^ op <= 2 ^ 15) by (split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_le_mono_r; lia]).
  assert (0 <= h mod 2 ^ op < 2 ^ op) by (apply Z.mod_pos_bound; lia).
  destruct p; try contradiction.
  unfold eval_binop, force_val2. simpl.
  rewrite Int.shl_mul_two_p, Int.unsigned_repr by rep_lia. rewrite two_p_equiv.
  rewrite Int.mul_commut, Int.mul_one, sub_repr.
  rewrite Int.unsigned_repr by rep_lia.
  rewrite f5k_land_mask by (unfold lrange in Hh; lia).
  unfold Ptrofs.of_int64, Ptrofs.of_ints.
  rewrite Int64.unsigned_repr by rep_lia. rewrite Int.signed_repr by rep_lia.
  rewrite !ptrofs_mul_repr, Ptrofs.add_assoc, ptrofs_add_repr.
  f_equal. f_equal. f_equal. lia.
Qed.

Ltac f5k_tcu := intro; unfold local, lift1, liftx, lift; simpl; apply prop_right;
  rewrite Int.unsigned_repr by rep_lia; rep_lia.

Lemma f5k_walk_len (TF: tab_focus_stmt): walk_len_stmt.
Proof.
  intros Espec F m FO Hmd Hb Hg.
  stmt_simpl. unfold fs_state, fs_locals, fs_sep; cbn [app]. abbreviate_semax.
  assert (W := fast_ok_mwf _ FO).
  set (s := m_s m) in *. set (t := i_lencode s) in *.
  assert (T: tref_ok t) by apply (sw_lencode _ (mw_s _ W)).
  assert (Hc: Zlength (i_codes s) = ENOUGH_CODES) by apply (proj1 (sw_codes _ (mw_s _ W))).
  assert (RB: 0 <= i_lenbits s <= 15) by apply (sw_lenbits _ (mw_s _ W)).
  assert (Hh: lrange (m_hold m)) by apply (mw_hold _ W).
  assert_PROP (isptr (tref_val (f_gv F) (f_sp F) t)) as P by (sep_apply (f5k_tab_isptr F s t T); entailer!).
  forward.
  rewrite f5k_here0 by auto.
  forward_loop (EX k: nat, EX j: Z, EX h: Z, EX b: Z,
     fs_state F (f5k_hb m h b)
       [f5k_wok len_link t s k j (f5k_hb m h b);
        fwalk_f lenfix_list distfix_list k len_link t (tab_entry lenfix_list distfix_list s t j) (f5k_hb m h b) =
        lwalk s m]
       [temp _here (entry_ptr F t j)])
    break: (EX j: Z,
       fs_state F (snd (lwalk (m_s m) m))
         [0 <= j < tab_size (i_lencode (m_s m));
          tab_entry lenfix_list distfix_list (m_s m) (i_lencode (m_s m)) j = fst (lwalk (m_s m) m)]
         [temp _here (entry_ptr F (i_lencode (m_s m)) j); temp _op (zv (e_op (fst (lwalk (m_s m) m))))]).
  - Exists 2%nat (m_hold m mod 2 ^ i_lenbits s) (m_hold m) (m_bits m).
    unfold fs_state, fs_locals. rewrite f5k_fs_sep_hb. unfold fs_sep.
    cbn [f5k_hb set_m_bits set_m_hold m_s m_hold m_bits m_nx m_inp m_ow m_aout app].
    assert (E0: f5k_hb m (m_hold m) (m_bits m) = m) by (destruct m; reflexivity).
    rewrite E0.
    pose proof (f5k_wok_len m FO Hmd Hb) as WK.
    entailer!. apply derives_refl.
  - Intros k j h b.
    unfold fs_state, fs_locals. rewrite f5k_fs_sep_hb. unfold fs_sep.
    cbn [f5k_hb set_m_bits set_m_hold m_s m_hold m_bits m_nx m_inp m_ow m_aout app].
    change (m_s m) with s. change (i_lencode s) with t.
    Intros. rename H into WK, H0 into EW.
    apply f5k_wok_unfold in WK. cbv zeta in WK. destruct WK as (Ws & Wj & We & Wb & Wh & Wl).
    sep_apply (TF F s t j T Hc Wj). Intros.
    unfold ent.
    set (e := tab_entry lenfix_list distfix_list s t j) in *.
    destruct We as (Eo & Eb & Ev).
    cbn [f5k_hb set_m_bits set_m_hold m_hold m_bits] in Wb, Wh.
    assert (RS: readable_share (tab_sh F t)) by (clearbody t; destruct t; simpl; auto with share).
    forward. { f5k_tcu. }
    forward. abbreviate_semax.
    forward. { entailer!. change (Int.unsigned Int64.iwordsize') with 64. lia. }
    rewrite f5k_shru by (auto; lia).
    forward.
    forward. { f5k_tcu. }
    forward.
    rewrite sub_repr.
    forward_if (temp _t'4 (f5k_vb ((e_op e =? 0) || negb (Z.land (e_op e) 16 =? 0)))).
    { forward. entailer!. rewrite H. reflexivity. }
    { forward. entailer!. unfold f5k_vb. rewrite f5k_and_eq by lia.
      apply Z.eqb_neq in H. rewrite H. simpl. destruct (Z.land (e_op e) 16 =? 0); reflexivity. }
    forward_if (temp _t'5 (f5k_vb (negb (len_link (e_op e))))).
    { forward. entailer!.
      destruct (orb (e_op e =? 0) (negb (Z.land (e_op e) 16 =? 0))) eqn:EB; [|contradiction].
      unfold f5k_vb, len_link. rewrite EB. reflexivity. }
    { forward. entailer!.
      destruct (orb (e_op e =? 0) (negb (Z.land (e_op e) 16 =? 0))) eqn:EB; [discriminate|].
      unfold f5k_vb, len_link. rewrite EB. rewrite f5k_and_eq by lia. simpl.
      destruct (Z.land (e_op e) 64 =? 0); reflexivity. }
    forward_if.
    { (* not a link: break *)
      forward.
      assert (LL: len_link (e_op e) = false) by (destruct (len_link (e_op e)); [contradiction|reflexivity]).
      change (m_s m) with s. change (i_lencode s) with t.
      rewrite <- EW. rewrite f5k_fwalk_stop by auto. cbn [fst snd].
      Exists j. unfold fs_state, fs_locals. rewrite f5k_drop_hb, f5k_fs_sep_hb. unfold fs_sep.
      cbn [f5k_hb set_m_bits set_m_hold m_s m_hold m_bits m_nx m_inp m_ow m_aout app].
      rewrite f5k_u32 by rep_lia.
      sep_apply (modus_ponens_wand (data_at (tab_sh F t) t_code (Vint (Int.repr (e_op e)), (Vint (Int.repr (e_bits e)), Vint (Int.repr (e_val e)))) (entry_ptr F t j)) (tab_mem F s)).
      entailer!. }
    (* a link: the second level *)
    assert (LL: len_link (e_op e) = true) by (destruct (len_link (e_op e)); [reflexivity|discriminate]).
    destruct (Wl LL) as [Ho Wk]. destruct k as [|k']; [contradiction|].
    forward. { f5k_tcu. }
    forward.
    { entailer!. change (Int.unsigned Int.iwordsize) with 32. lia. }
    assert (Wh1: lrange (Z.shiftr h (e_bits e))) by (apply f5k_lrange_shiftr; auto; lia).
    rewrite f5k_here1 by (auto; lia).
    rewrite f5k_fwalk_link in EW by exact LL.
    rewrite f5k_drop_hb, f5k_hold_hb, f5k_ms_hb, f5k_u32 in EW by rep_lia.
    rewrite f5k_drop_hb, f5k_hold_hb, f5k_u32 in Wk by rep_lia.
    Exists k' (e_val e + Z.shiftr h (e_bits e) mod 2 ^ e_op e) (Z.shiftr h (e_bits e)) (b - e_bits e).
    unfold fs_state, fs_locals. rewrite f5k_fs_sep_hb. unfold fs_sep.
    cbn [f5k_hb set_m_bits set_m_hold m_s m_hold m_bits m_nx m_inp m_ow m_aout app].
    sep_apply (modus_ponens_wand (data_at (tab_sh F t) t_code (Vint (Int.repr (e_op e)), (Vint (Int.repr (e_bits e)), Vint (Int.repr (e_val e)))) (entry_ptr F t j)) (tab_mem F s)).
    entailer!.
  - Intros j0. Exists j0. unfold fs_state, fs_locals, fs_sep; cbn [app]. entailer!. apply derives_refl.
Qed.

Lemma f5k_walk_dist (TF: tab_focus_stmt): walk_dist_stmt.
Proof.
  intros Espec F m L FO Hmd Hb Hg.
  stmt_simpl. unfold fs_state, fs_locals, fs_sep; cbn [app]. abbreviate_semax.
  assert (W := fast_ok_mwf _ FO).
  set (s := m_s m) in *. set (t := i_distcode s) in *.
  assert (T: tref_ok t) by apply (sw_distcode _ (mw_s _ W)).
  assert (Hc: Zlength (i_codes s) = ENOUGH_CODES) by apply (proj1 (sw_codes _ (mw_s _ W))).
  assert (RB: 0 <= i_distbits s <= 15) by apply (sw_distbits _ (mw_s _ W)).
  assert (Hh: lrange (m_hold m)) by apply (mw_hold _ W).
  assert_PROP (isptr (tref_val (f_gv F) (f_sp F) t)) as P by (sep_apply (f5k_tab_isptr F s t T); entailer!).
  forward.
  rewrite f5k_here0 by auto.
  forward_loop (EX k: nat, EX j: Z, EX h: Z, EX b: Z,
     fs_state F (f5k_hb m h b)
       [f5k_wok dist_link t s k j (f5k_hb m h b);
        fwalk_f lenfix_list distfix_list k dist_link t (tab_entry lenfix_list distfix_list s t j) (f5k_hb m h b) =
        dwalk s m]
       [temp _here (entry_ptr F t j); temp _len (zv L)])
    break: (EX j: Z,
       fs_state F (snd (dwalk (m_s m) m))
         [0 <= j < tab_size (i_distcode (m_s m));
          tab_entry lenfix_list distfix_list (m_s m) (i_distcode (m_s m)) j = fst (dwalk (m_s m) m)]
         [temp _here (entry_ptr F (i_distcode (m_s m)) j); temp _op (zv (e_op (fst (dwalk (m_s m) m))));
          temp _len (zv L)]).
  - Exists 2%nat (m_hold m mod 2 ^ i_distbits s) (m_hold m) (m_bits m).
    unfold fs_state, fs_locals. rewrite f5k_fs_sep_hb. unfold fs_sep.
    cbn [f5k_hb set_m_bits set_m_hold m_s m_hold m_bits m_nx m_inp m_ow m_aout app].
    assert (E0: f5k_hb m (m_hold m) (m_bits m) = m) by (destruct m; reflexivity).
    rewrite E0.
    pose proof (f5k_wok_dist m FO Hmd Hb) as WK.
    entailer!. apply derives_refl.
  - Intros k j h b.
    unfold fs_state, fs_locals. rewrite f5k_fs_sep_hb. unfold fs_sep.
    cbn [f5k_hb set_m_bits set_m_hold m_s m_hold m_bits m_nx m_inp m_ow m_aout app].
    change (m_s m) with s. change (i_distcode s) with t.
    Intros. rename H into WK, H0 into EW.
    apply f5k_wok_unfold in WK. cbv zeta in WK. destruct WK as (Ws & Wj & We & Wb & Wh & Wl).
    sep_apply (TF F s t j T Hc Wj). Intros.
    unfold ent.
    set (e := tab_entry lenfix_list distfix_list s t j) in *.
    destruct We as (Eo & Eb & Ev).
    cbn [f5k_hb set_m_bits set_m_hold m_hold m_bits] in Wb, Wh.
    assert (RS: readable_share (tab_sh F t)) by (clearbody t; destruct t; simpl; auto with share).
    forward. { f5k_tcu. }
    forward. abbreviate_semax.
    forward. { entailer!. change (Int.unsigned Int64.iwordsize') with 64. lia. }
    rewrite f5k_shru by (auto; lia).
    forward.
    forward. { f5k_tcu. }
    forward.
    rewrite sub_repr.
    forward_if (temp _t'10 (f5k_vb (negb (dist_link (e_op e))))).
    { forward. entailer!.
      rewrite and_repr in H.
      assert (A16: (Z.land (e_op e) 16 =? 0) = false) by (rewrite <- f5k_and_eq by lia; apply Int.eq_false; auto).
      unfold f5k_vb, dist_link. rewrite A16. simpl. reflexivity. }
    { forward. entailer!.
      rewrite and_repr in H.
      assert (A16: (Z.land (e_op e) 16 =? 0) = true) by (rewrite <- f5k_and_eq by lia; rewrite H; reflexivity).
      unfold f5k_vb, dist_link. rewrite A16. rewrite f5k_and_eq by lia. simpl.
      destruct (Z.land (e_op e) 64 =? 0); reflexivity. }
    forward_if.
    { (* not a link: break *)
      forward.
      assert (LL: dist_link (e_op e) = false) by (destruct (dist_link (e_op e)); [contradiction|reflexivity]).
      change (m_s m) with s. change (i_distcode s) with t.
      rewrite <- EW. rewrite f5k_fwalk_stop by auto. cbn [fst snd].
      Exists j. unfold fs_state, fs_locals. rewrite f5k_drop_hb, f5k_fs_sep_hb. unfold fs_sep.
      cbn [f5k_hb set_m_bits set_m_hold m_s m_hold m_bits m_nx m_inp m_ow m_aout app].
      rewrite f5k_u32 by rep_lia.
      sep_apply (modus_ponens_wand (data_at (tab_sh F t) t_code (Vint (Int.repr (e_op e)), (Vint (Int.repr (e_bits e)), Vint (Int.repr (e_val e)))) (entry_ptr F t j)) (tab_mem F s)).
      entailer!. }
    (* a link: the second level *)
    assert (LL: dist_link (e_op e) = true) by (destruct (dist_link (e_op e)); [reflexivity|discriminate]).
    destruct (Wl LL) as [Ho Wk]. destruct k as [|k']; [contradiction|].
    forward. { f5k_tcu. }
    forward.
    { entailer!. change (Int.unsigned Int.iwordsize) with 32. lia. }
    assert (Wh1: lrange (Z.shiftr h (e_bits e))) by (apply f5k_lrange_shiftr; auto; lia).
    rewrite f5k_here1 by (auto; lia).
    rewrite f5k_fwalk_link in EW by exact LL.
    rewrite f5k_drop_hb, f5k_hold_hb, f5k_ms_hb, f5k_u32 in EW by rep_lia.
    rewrite f5k_drop_hb, f5k_hold_hb, f5k_u32 in Wk by rep_lia.
    Exists k' (e_val e + Z.shiftr h (e_bits e) mod 2 ^ e_op e) (Z.shiftr h (e_bits e)) (b - e_bits e).
    unfold fs_state, fs_locals. rewrite f5k_fs_sep_hb. unfold fs_sep.
    cbn [f5k_hb set_m_bits set_m_hold m_s m_hold m_bits m_nx m_inp m_ow m_aout app].
    sep_apply (modus_ponens_wand (data_at (tab_sh F t) t_code (Vint (Int.repr (e_op e)), (Vint (Int.repr (e_bits e)), Vint (Int.repr (e_val e)))) (entry_ptr F t j)) (tab_mem F s)).
    entailer!.
  - Intros j0. Exists j0. unfold fs_state, fs_locals, fs_sep; cbn [app]. entailer!. apply derives_refl.
Qed.

Lemma f5_walks : tab_focus_stmt -> lwalk_facts_stmt -> dwalk_facts_stmt -> walk_len_stmt /\ walk_dist_stmt.
Proof.
  intros TF _ _. split; [exact (f5k_walk_len TF) | exact (f5k_walk_dist TF)].
Qed.
