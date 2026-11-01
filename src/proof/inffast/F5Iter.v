(* inflate_fast (BodyF5.v): one pass of the loop (F5Kit s_iter, model fast_iter = refill2, lwalk, fdisp). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inffast.code.
Require Import Zlib.proof.inffast.F5Kit.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* ---------------------------------------------------------------------------------------------- *)
(* the pieces of s_iter                                                                           *)

(* if (bits < 15) { two bytes } *)
Definition p_refill : list nat := [1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0;0;0]%nat.
Definition s_refill := at_path p_refill fbody.
(* if (op == 0) literal else if (op & 16) length else if (op & 32) end-of-block else error *)
Definition p_chain : list nat := [1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0;0;1;1;1]%nat.
Definition s_chain := at_path p_chain fbody.

Lemma s_iter_eq: s_iter = Ssequence s_refill (Ssequence s_lhere (Ssequence s_lloop s_chain)).
Proof. reflexivity. Qed.

Ltac fi_simpl :=
  match goal with |- semax _ _ ?c _ =>
    let c' := eval cbv beta iota delta [s_refill s_chain s_lenbr p_refill p_chain p_lenbr
      at_path child fbody f_inflate_fast fn_body] in c in
    change c with c'
  end.

Lemma fi_lenbr_eq: s_lenbr = at_path [0]%nat (at_path [1]%nat s_chain).
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* pure facts                                                                                      *)

Lemma fi_in_byte: forall sh p lo n c inp j,
  in_ok (InBuf sh p lo n c) inp -> 0 <= j < Zlength inp ->
  @Znth val Vundef (lo + j) c = Vint (Int.repr (Znth j inp)).
Proof.
  intros sh p lo n c inp j H Hj. unfold in_ok in H. destruct H as (_&_&Hlo&Hn&Hc&_&Hsub&_).
  rewrite <- Znth_byte_vals by lia. rewrite <- Hsub. rewrite Znth_sublist by lia. f_equal. lia.
Qed.

Lemma fi_hold_add: forall h b bt, 0 <= b -> 0 <= bt < 64 ->
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

Lemma fi_bytes_Znth: forall l j, bytes_ok l -> 0 <= j < Zlength l -> 0 <= Znth j l <= 255.
Proof.
  intros l j H Hj. unfold bytes_ok in H. rewrite Forall_forall in H. apply H. apply Znth_In. auto.
Qed.

Lemma fi_inc: forall p k, isptr p ->
  force_val (sem_binary_operation' Oadd (tptr tuchar) tint (offset_val k p) (Vint (Int.repr 1))) =
  offset_val (k + 1) p.
Proof.
  intros p k P. destruct p; try contradiction. simpl. f_equal.
  rewrite Ptrofs.add_assoc. f_equal. change (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_ints (Int.repr 1))) with (Ptrofs.repr 1).
  rewrite ptrofs_add_repr. reflexivity.
Qed.

Lemma fi_mwf_hb: forall m h b, mwf m -> lrange h -> 0 <= b <= 39 -> mwf (set_m_bits (set_m_hold m h) b).
Proof. intros m h b W H B. destruct W; constructor; cbn; auto. Qed.

Lemma fi_fast_ok_hb: forall m h b, fast_ok m -> lrange h -> 0 <= b <= 39 ->
  fast_ok (set_m_bits (set_m_hold m h) b).
Proof. intros m h b [W T] H B. split; [apply fi_mwf_hb; auto | exact T]. Qed.

Lemma fi_mwf_pull: forall m, mwf m -> m_nx m < Zlength (m_inp m) -> m_bits m <= 31 -> mwf (fpull m).
Proof.
  intros m W N B. pose proof (mw_bits _ W). pose proof (mw_nx _ W).
  destruct W; constructor; cbn; auto; try lia.
  - unfold lrange, u64. pose proof (Z.mod_pos_bound (m_hold m + Znth (m_nx m) (m_inp m) * 2 ^ m_bits m) (2 ^ 64)).
    rep_lia.
  - unfold u32. rewrite Z.mod_small by lia. lia.
Qed.

Lemma fi_fast_ok_pull: forall m, fast_ok m -> m_nx m < Zlength (m_inp m) -> m_bits m <= 31 -> fast_ok (fpull m).
Proof. intros m [W T] N B. split; [apply fi_mwf_pull; auto | exact T]. Qed.

Lemma fi_lrange_shiftr: forall h k, lrange h -> 0 <= k -> lrange (Z.shiftr h k).
Proof.
  intros h k [H0 H1] K. split.
  - apply Z.shiftr_nonneg. lia.
  - rewrite Z.shiftr_div_pow2 by lia.
    assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
    pose proof (Z.div_le_upper_bound h (2 ^ k) h ltac:(lia) ltac:(nia)). lia.
Qed.

(* the refill *)
Record refill_facts (m m2: mst) : Prop := {
  rf_ok: fast_ok m2; rf_s: m_s m2 = m_s m; rf_inp: m_inp m2 = m_inp m; rf_aout: m_aout m2 = m_aout m;
  rf_ow: m_ow m2 = m_ow m; rf_bits: 15 <= m_bits m2 <= 30;
  rf_bud: 8 * m_have m2 + m_bits m2 = 8 * m_have m + m_bits m }.

Lemma fi_pull_bits: forall m, 0 <= m_bits m <= 31 -> m_bits (fpull m) = m_bits m + 8.
Proof. intros. cbn. unfold u32. apply Z.mod_small. lia. Qed.

Lemma fi_refill_facts: forall m, fast_ok m -> 2 <= m_have m -> m_bits m <= 30 -> refill_facts m (refill2 m).
Proof.
  intros m FW HV B. pose proof (mw_bits _ (fast_ok_mwf _ FW)). unfold refill2, m_have in *.
  destruct (m_bits m <? 15) eqn:E.
  - apply Z.ltb_lt in E.
    assert (B1: m_bits (fpull m) = m_bits m + 8) by (apply fi_pull_bits; lia).
    assert (B2: m_bits (fpull (fpull m)) = m_bits m + 16) by (rewrite fi_pull_bits; lia).
    assert (FW1: fast_ok (fpull m)) by (apply fi_fast_ok_pull; auto; lia).
    constructor; auto.
    + apply fi_fast_ok_pull; auto; [cbn; lia | rewrite B1; lia].
    + rewrite B2. lia.
    + rewrite B2. cbn. unfold m_have. lia.
  - apply Z.ltb_ge in E. constructor; auto.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the statements                                                                                  *)

Lemma fi_refill {Espec: OracleKind}: forall F m,
  fast_ok m -> 2 <= m_have m -> m_bits m <= 30 -> in_ok (f_ib F) (m_inp m) ->
  semax Delta_fast (fs_state F m [] []) s_refill (normal_ret_assert (fs_state F (refill2 m) [] [])).
Proof.
  intros F m FW HV B INOK.
  fi_simpl. unfold fs_state, fs_locals, fs_sep; cbn [app]. abbreviate_semax.
  pose proof (fast_ok_mwf _ FW) as W.
  pose proof (mw_bits _ W). pose proof (mw_nx _ W). pose proof (mw_hold _ W). pose proof (mw_inp _ W).
  forward_if (PROPx [] (LOCALx (fs_locals F (refill2 m)) (SEPx (fs_sep F (refill2 m))))).
  - destruct (f_ib F) as [ | ish ip ilo inb ic] eqn:IB; cbn [in_ptr in_rep].
    { exfalso. unfold in_ok in INOK. unfold m_have in HV. rewrite INOK, Zlength_nil in HV. lia. }
    pose proof INOK as INOK'. destruct INOK' as (Hish & Hip & Hilo & Hinb & Hic & Hinbm & Hsub & Hbytes).
    assert_PROP (field_compatible (tarray tuchar inb) [] ip) by entailer!.
    assert (Hj0: 0 <= m_nx m < Zlength (m_inp m)) by (unfold m_have in HV; lia).
    assert (Hj1: 0 <= m_nx m + 1 < Zlength (m_inp m)) by (unfold m_have in HV; lia).
    pose proof (fi_in_byte _ _ _ _ _ _ _ INOK Hj0) as BY0.
    pose proof (fi_in_byte _ _ _ _ _ _ _ INOK Hj1) as BY1.
    pose proof (fi_bytes_Znth _ _ Hbytes Hj0) as R0.
    pose proof (fi_bytes_Znth _ _ Hbytes Hj1) as R1.
    forward. forward.
    rewrite fi_inc by auto.
    rewrite (offset_val_field_address_tuchar inb (ilo + m_nx m) ip) by (auto; lia).
    forward.
    { rewrite BY0. entailer!. rep_lia. }
    rewrite BY0.
    forward.
    { entailer!. change (Int.unsigned Int64.iwordsize') with 64. lia. }
    forward.
    forward. forward.
    rewrite fi_inc by auto.
    rewrite (offset_val_field_address_tuchar inb (ilo + m_nx m + 1) ip) by (auto; lia).
    forward.
    { replace (ilo + m_nx m + 1) with (ilo + (m_nx m + 1)) by lia. rewrite BY1. entailer!. rep_lia. }
    replace (ilo + m_nx m + 1) with (ilo + (m_nx m + 1)) by lia. rewrite BY1.
    forward.
    { entailer!. change (Int.unsigned Int64.iwordsize') with 64. lia. }
    forward.
    unfold refill2. rewrite (proj2 (Z.ltb_lt _ _)) by lia.
    assert (E: fpull (fpull m) = set_m_bits (set_m_hold (set_m_nx m (m_nx m + 2))
                 (u64 (u64 (m_hold m + Znth (m_nx m) (m_inp m) * 2 ^ m_bits m) +
                       Znth (m_nx m + 1) (m_inp m) * 2 ^ (m_bits m + 8)))) (m_bits m + 16)).
    { unfold fpull, pull. cbn. unfold u32. rewrite !Z.mod_small by lia.
      replace (m_nx m + 1 + 1) with (m_nx m + 2) by lia. replace (m_bits m + 8 + 8) with (m_bits m + 16) by lia.
      destruct m; reflexivity. }
    rewrite E. unfold fs_locals, fs_sep. cbn [m_s m_nx m_hold m_bits m_inp m_ow m_aout set_m_bits set_m_hold set_m_nx].
    rewrite IB. cbn [in_ptr in_rep].
    rewrite !Int.unsigned_repr by rep_lia. rewrite !add_repr. rewrite Int.unsigned_repr by rep_lia.
    rewrite <- fi_hold_add by lia. rewrite <- fi_hold_add by lia.
    entailer!.
    + split; [f_equal; lia | do 2 f_equal; lia].
    + apply derives_refl.
  - forward. unfold refill2. rewrite (proj2 (Z.ltb_ge _ _)) by lia. unfold fs_locals, fs_sep. entailer!.
Qed.

Ltac fi_tcu := intro; unfold local, lift1, liftx, lift; simpl; apply prop_right;
  rewrite Int.unsigned_repr by rep_lia; rep_lia.

Lemma fi_zext8: forall v, 0 <= v <= Int.max_unsigned -> Int.zero_ext 8 (Int.repr v) = Int.repr (v mod 256).
Proof.
  intros v Hv. rewrite <- (Int.repr_unsigned (Int.zero_ext 8 (Int.repr v))).
  rewrite Int.zero_ext_mod by (cbn; lia). rewrite Int.unsigned_repr by lia. reflexivity.
Qed.

Lemma fi_land_range: forall op c, 0 <= op <= 255 -> 0 <= c <= 255 -> 0 <= Z.land op c <= 255.
Proof.
  intros op c Ho Hc.
  split; [apply Z.land_nonneg; lia|].
  destruct (Z.eq_dec (Z.land op c) 0) as [Z0|Z0]; [lia|].
  assert (0 < Z.land op c) by (pose proof (proj2 (Z.land_nonneg op c) ltac:(lia)); lia).
  assert (Z.land op c < 2 ^ 8); [|lia].
  apply Z.log2_lt_pow2; [lia|].
  pose proof (Z.log2_land op c ltac:(lia) ltac:(lia)).
  pose proof (Z.log2_le_mono op 255 ltac:(lia)). change (Z.log2 255) with 7 in *. lia.
Qed.

Lemma fi_and_zero: forall op c, 0 <= op <= 255 -> 0 <= c <= 255 ->
  Int.and (Int.repr op) (Int.repr c) = Int.zero -> Z.land op c = 0.
Proof.
  intros op c Ho Hc H. pose proof (fi_land_range op c Ho Hc).
  unfold Int.and in H. rewrite !Int.unsigned_repr in H by rep_lia.
  apply (f_equal Int.unsigned) in H. rewrite Int.unsigned_repr in H by rep_lia. exact H.
Qed.

(* rest_mem without state->mode and strm_rep (the stores of the break branches) *)
Definition rest_ms (F: frame) (m: mst) : mpred :=
  let s := m_s m in let sp := f_sp F in
  field_at Ews t_state (DOT _strm) (f_strmp F) sp *
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
  field_at Ews t_state (DOT _lencode) (tref_val (f_gv F) sp (i_lencode s)) sp *
  field_at Ews t_state (DOT _distcode) (tref_val (f_gv F) sp (i_distcode s)) sp *
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
  field_at Ews t_state (DOT _was) (zv (i_was s)) sp *
  head_part F m *
  data_at (f_gsh F) (tarray tushort 19) (map (fun z => Vint (Int.repr z)) order)
    (f_gv F Zlib.inflate.code._order) *
  Zlib.proof.inftrees.spec.itables (f_gsh F) (f_gv F) *
  Zlib.proof.crc32.Spec.crc_table_at (f_tsh F) (f_gv F).

Definition strm_m (F: frame) (m: mst) : mpred :=
  strm_rep (f_gv F) (f_shs F) (f_strmp F)
    (in_ptr (f_ib F) (m_snx m)) (zv (Zlength (m_inp m) - m_snx m)) (m_tin m)
    (out_ptr (f_ob F) (m_sow m)) (zv (m_aout m - m_sow m)) (m_tout m)
    (msg_val (f_gv F) (m_msg m)) (f_sp F) (f_dt F) (m_adler m) (f_vres F).

Lemma rest_mem_ms: forall F m,
  rest_mem F m = field_at Ews t_state (DOT _mode) (zv (i_mode (m_s m))) (f_sp F) * strm_m F m * rest_ms F m.
Proof. intros. unfold rest_mem, state_rep_nc, rest_ms, strm_m. apply pred_ext; cancel. Qed.

Lemma rest_ms_mode: forall F m v, rest_ms F (set_mode m v) = rest_ms F m.
Proof. reflexivity. Qed.

Lemma rest_ms_msg: forall F m v, rest_ms F (set_m_msg m v) = rest_ms F m.
Proof. reflexivity. Qed.

Lemma fi_chain {Espec: OracleKind}: tab_focus_stmt -> lenbr_stmt -> forall F m j e,
  fast_ok m -> m_mode m = LEN -> entry_ok e -> final_ok LENS e -> len_ok e -> len_link (e_op e) = false ->
  33 <= 8 * m_have m + m_bits m -> m_bits m <= 30 -> 258 <= m_left m ->
  in_ok (f_ib F) (m_inp m) -> out_ok (f_ob F) (m_aout m) ->
  writable_share (f_shs F) -> readable_share (f_gsh F) ->
  semax Delta_fast
    (fs_state F m [0 <= j < tab_size (i_lencode (m_s m));
                   tab_entry lenfix_list distfix_list (m_s m) (i_lencode (m_s m)) j = e]
       [temp _here (entry_ptr F (i_lencode (m_s m)) j); temp _op (zv (e_op e))])
    s_chain (fpost F (fdisp (m_s m) e m)).
Proof.
  intros TF LB F m j e FW MD EO FO LO LL BUD B30 LF INOK OUTOK SHS SHG.
  fi_simpl. unfold fs_state, fs_locals, fs_sep; cbn [app]. abbreviate_semax.
  Intros. rename H into J. rename H0 into TE.
  pose proof (fast_ok_mwf _ FW) as W.
  pose proof EO as (Eo & Eb & Ev).
  forward_if.
  - (* literal *)
    unfold fdisp. rewrite (proj2 (Z.eqb_eq _ _) H).
    set (s := m_s m) in *. set (t := i_lencode s) in *.
    assert (T: tref_ok t) by apply (sw_lencode _ (mw_s _ W)).
    assert (Hc: Zlength (i_codes s) = ENOUGH_CODES) by apply (proj1 (sw_codes _ (mw_s _ W))).
    destruct (f_ob F) as [osh op olo on oc] eqn:OB. cbn [out_ptr out_rep].
    pose proof OUTOK as (Hosh & Hop & Holo & Haout & Hlo & Hoc & Homax).
    assert_PROP (field_compatible (tarray tuchar on) [] op) by entailer!.
    forward. forward.
    rewrite fi_inc by auto.
    sep_apply (TF F s t j T Hc J). Intros.
    rewrite TE. unfold ent.
    assert (RS: readable_share (tab_sh F t)) by (clearbody t; destruct t; simpl; auto with share).
    forward. { fi_tcu. }
    assert (OW: Zlength (m_ow m) + 258 <= m_aout m) by (unfold m_left in LF; lia).
    pose proof (Zlength_nonneg (m_ow m)).
    rewrite (offset_val_field_address_tuchar on (olo + Zlength (m_ow m)) op) by (auto; lia).
    forward.
    pose proof (Z.mod_pos_bound (e_val e) 256 ltac:(lia)).
    rewrite fi_zext8 by rep_lia. rewrite fi_zext8 by rep_lia. rewrite Zmod_mod.
    subst on. rewrite out_rep_snoc by lia.
    cbn [RA_normal fpost]. Exists (set_m_ow m (m_ow m ++ [e_val e mod 256])).
    unfold fs_state, fs_locals, fs_sep.
    change (rest_mem F (set_m_ow m (m_ow m ++ [e_val e mod 256]))) with (rest_mem F m).
    cbn [app m_s m_ow m_nx m_inp m_aout m_hold m_bits set_m_ow].
    rewrite OB. cbn [out_ptr]. rewrite Zlength_app, Zlength_cons, Zlength_nil.
    sep_apply (modus_ponens_wand (data_at (tab_sh F t) t_code (Vint (Int.repr (e_op e)), (Vint (Int.repr (e_bits e)), Vint (Int.repr (e_val e)))) (entry_ptr F t j)) (tab_mem F s)).
    entailer!.
    + f_equal. lia.
    + apply derives_refl.
  - forward_if.
    + (* length *)
      rewrite !Int.unsigned_repr in H0' by rep_lia. change (Int.unsigned (Int.repr 16)) with 16 in H0'.
      assert (OPR: 16 <= e_op e <= 21 /\ 3 <= e_val e <= 258).
      { unfold final_ok in FO. cbn in FO. destruct FO as [[F1 F2] | [F1 | [F1 | [F1 F2]]]].
        - lia.
        - exact F1.
        - exfalso. rewrite F1 in H0'. apply H0'. reflexivity.
        - exfalso. apply H0'. change 16 with (Z.land 48 16). rewrite Z.land_assoc, F2. reflexivity. }
      unfold MORE_COMMANDS, POSTCONDITION, abbreviate.
      unfold fdisp. rewrite (proj2 (Z.eqb_neq _ _) H), (proj2 (Z.eqb_neq _ _) H0'). cbn [negb].
      match goal with |- semax _ _ ?c _ => change c with s_lenbr end.
      eapply semax_pre; [ | apply (LB Espec F m j e); auto; try lia].
      unfold fs_state, fs_locals, fs_sep. cbn [app]. apply andp_left2. apply derives_refl.
    + forward_if.
      * (* end-of-block *)
        apply fi_and_zero in H0; [ | lia | lia].
        rewrite !Int.unsigned_repr in H1' by rep_lia. change (Int.unsigned (Int.repr 32)) with 32 in H1'.
        unfold POSTCONDITION, abbreviate. unfold fdisp.
        rewrite (proj2 (Z.eqb_neq _ _) H), H0, (proj2 (Z.eqb_neq _ _) H1'). cbn [negb Z.eqb].
        rewrite rest_mem_ms. Intros.
        forward.
        forward.
        cbn [RA_break fpost]. Exists (set_mode m Zlib.proof.inflate.Model.TYPE).
        unfold fs_state, fs_locals, fs_sep. rewrite rest_mem_ms, rest_ms_mode.
        change (strm_m F (set_mode m Zlib.proof.inflate.Model.TYPE)) with (strm_m F m).
        change (tab_mem F (m_s (set_mode m Zlib.proof.inflate.Model.TYPE))) with (tab_mem F (m_s m)).
        change (win_rep (f_winp F) (m_s (set_mode m Zlib.proof.inflate.Model.TYPE))) with (win_rep (f_winp F) (m_s m)).
        unfold win_val. cbn [app m_nx m_inp m_ow m_aout m_hold m_bits set_mode upd_s set_m_s m_s i_wsize i_whave i_wnext i_win i_lencode i_distcode i_lenbits i_distbits i_mode set_i_mode].
        unfold Zlib.proof.inflate.Model.TYPE.
        entailer!.
      * (* invalid *)
        apply fi_and_zero in H0; [ | lia | lia].
        apply fi_and_zero in H1; [ | lia | lia].
        unfold POSTCONDITION, abbreviate. unfold fdisp.
        rewrite (proj2 (Z.eqb_neq _ _) H), H0, H1. cbn [negb Z.eqb].
        rewrite rest_mem_ms. Intros.
        unfold strm_m, strm_rep.
        remember (f_gv F inflate.code._zcalloc) as zca eqn:EZA.
        remember (f_gv F inflate.code._zcfree) as zcf eqn:EZF.
        forward.
        forward.
        forward.
        cbn [RA_break fpost]. Exists (set_bad m F_ll_code).
        unfold fs_state, fs_locals, fs_sep. rewrite rest_mem_ms.
        change (rest_ms F (set_bad m F_ll_code)) with (rest_ms F m).
        change (tab_mem F (m_s (set_bad m F_ll_code))) with (tab_mem F (m_s m)).
        change (win_rep (f_winp F) (m_s (set_bad m F_ll_code))) with (win_rep (f_winp F) (m_s m)).
        unfold strm_m, strm_rep. rewrite <- EZA, <- EZF.
        unfold win_val. cbn [app m_nx m_inp m_ow m_aout m_hold m_bits set_bad set_mode upd_s set_m_s set_m_msg m_s
          m_snx m_sow m_tin m_tout m_adler m_msg msg_val msg_ident
          i_wsize i_whave i_wnext i_win i_lencode i_distcode i_lenbits i_distbits i_mode set_i_mode].
        unfold Zlib.proof.inflate.Model.BAD.
        entailer!.
Qed.

Lemma f5_iter_ok : tab_focus_stmt -> lwalk_facts_stmt -> walk_len_stmt -> lenbr_stmt -> iter_stmt.
Proof.
  intros TF LWF WL LB Espec F m FW MD HV LF B30 INOK OUTOK SHS SHG.
  rewrite fast_iter_eq, s_iter_eq.
  pose proof (fi_refill_facts m FW ltac:(lia) B30) as RF.
  eapply semax_seq'. { apply fi_refill; auto; lia. }
  destruct RF as [FW2 S2 I2 A2 O2 B2 U2].
  set (m2 := refill2 m) in *. clearbody m2.
  rewrite <- S2.
  apply seq_assoc.
  eapply semax_seq'. { apply WL; auto. unfold m_mode in *; rewrite S2; auto. }
  pose proof (LWF m2 FW2 ltac:(unfold m_mode in *; rewrite S2; auto) ltac:(lia)) as LF2.
  destruct (lwalk (m_s m2) m2) as [e m1] eqn:LW. cbn [fst snd].
  destruct LF2 as (EO & FO & LO & LL & BB & E1).
  Intros j.
  assert (M1: m_s m1 = m_s m2 /\ m_inp m1 = m_inp m2 /\ m_aout m1 = m_aout m2 /\ m_ow m1 = m_ow m2 /\
              m_nx m1 = m_nx m2) by (rewrite E1; repeat split).
  destruct M1 as (S1 & I1 & A1 & O1 & N1).
  assert (W2 := fast_ok_mwf _ FW2).
  assert (FW1: fast_ok m1).
  { rewrite E1. apply fi_fast_ok_hb; auto; [ | lia].
    apply fi_lrange_shiftr; [apply (mw_hold _ W2) | lia]. }
  rewrite <- S1.
  apply fi_chain; auto.
  - unfold m_mode in *. rewrite S1, S2. auto.
  - pose proof (mw_bits _ (fast_ok_mwf _ FW)). unfold m_have in *. rewrite I1, N1. lia.
  - lia.
  - unfold m_left in *. rewrite A1, O1, A2, O2. lia.
  - rewrite I1, I2. auto.
  - rewrite A1, A2. auto.
Qed.
