(* inflate_fast (BodyF5.v): the match copy, window or direct (F5Kit s_copy, model fcopy). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inffast.code.
Require Import Zlib.proof.inffast.F5Kit.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* ---------------------------------------------------------------------------------------------- *)
(* the model: the window part of fcopy, its cases, and what it gives the tail                     *)

(* fcopy's (ow, sr, len) before the tail, the window case (op = dist - out > 0) *)
Definition wsplit (s: istate) (len dist: Z) (ow0: list Z) : list Z * src * Z :=
  let op := dist - Zlength ow0 in
  let w := i_wdata s in
  let wsz := i_wsize s in let wnx := i_wnext s in
  if wnx =? 0 then
    if op <? len then
      let '(ow, _) := copy_bytes w (SWin (wsz - op)) op ow0 in
      (ow, SOut (Zlength ow - dist), len - op)
    else (ow0, SWin (wsz - op), len)
  else if wnx <? op then
    let op2 := op - wnx in
    if op2 <? len then
      let '(ow, _) := copy_bytes w (SWin (wsz + wnx - op)) op2 ow0 in
      let len := len - op2 in
      if wnx <? len then
        let '(ow, _) := copy_bytes w (SWin 0) wnx ow in
        (ow, SOut (Zlength ow - dist), len - wnx)
      else (ow, SWin 0, len)
    else (ow0, SWin (wsz + wnx - op), len)
  else
    if op <? len then
      let '(ow, _) := copy_bytes w (SWin (wnx - op)) op ow0 in
      (ow, SOut (Zlength ow - dist), len - op)
    else (ow0, SWin (wnx - op), len).

Lemma fcopy_eq: forall s L D m,
  fcopy s L D m =
  (if Zlength (m_ow m) <? D then
     if andb (i_whave s <? D - Zlength (m_ow m)) (negb (i_sane s =? 0)) then (false, set_bad m F_far) else
     let '(ow, sr, len) := wsplit s L D (m_ow m) in
     let '(ow, _) := copy_bytes (i_wdata s) sr len ow in (true, set_m_ow m ow)
   else
     let '(ow, _) := copy_bytes (i_wdata s) (SOut (Zlength (m_ow m) - D)) L (m_ow m) in
     (true, set_m_ow m ow)).
Proof. intros. reflexivity. Qed.

Lemma fcopy_win: forall m L D ow1 sr L',
  Zlength (m_ow m) < D -> D - Zlength (m_ow m) <= i_whave (m_s m) ->
  wsplit (m_s m) L D (m_ow m) = (ow1, sr, L') ->
  fcopy (m_s m) L D m = (true, set_m_ow (set_m_ow m ow1) (fst (copy_bytes (i_wdata (m_s m)) sr L' ow1))).
Proof.
  intros m L D ow1 sr L' H1 H2 H3. rewrite fcopy_eq.
  replace (Zlength (m_ow m) <? D) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (i_whave (m_s m) <? D - Zlength (m_ow m)) with false by (symmetry; apply Z.ltb_ge; lia).
  simpl andb. cbv iota. rewrite H3. destruct (copy_bytes _ _ _ _); reflexivity.
Qed.

Lemma fcopy_direct: forall m L D,
  D <= Zlength (m_ow m) ->
  fcopy (m_s m) L D m =
  (true, set_m_ow m (fst (copy_bytes (i_wdata (m_s m)) (SOut (Zlength (m_ow m) - D)) L (m_ow m)))).
Proof.
  intros m L D H1. rewrite fcopy_eq.
  replace (Zlength (m_ow m) <? D) with false by (symmetry; apply Z.ltb_ge; lia).
  destruct (copy_bytes _ _ _ _); reflexivity.
Qed.

Lemma fcopy_far: forall m L D,
  Zlength (m_ow m) < D -> i_whave (m_s m) < D - Zlength (m_ow m) -> i_sane (m_s m) = 1 ->
  fcopy (m_s m) L D m = (false, set_bad m F_far).
Proof.
  intros m L D H1 H2 H3. rewrite fcopy_eq.
  replace (Zlength (m_ow m) <? D) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (i_whave (m_s m) <? D - Zlength (m_ow m)) with true by (symmetry; apply Z.ltb_lt; lia).
  rewrite H3. reflexivity.
Qed.

Lemma c_copy_f_len: forall n w sr ow, Zlength (fst (copy_f n w sr ow)) = Zlength ow + Z.of_nat n.
Proof.
  induction n; intros; simpl; [lia | ].
  destruct sr; rewrite IHn, Zlength_app, Zlength_cons, Zlength_nil; lia.
Qed.

Lemma c_copy_bytes_len: forall w sr c ow, 0 <= c -> Zlength (fst (copy_bytes w sr c ow)) = Zlength ow + c.
Proof. intros. unfold copy_bytes. rewrite c_copy_f_len. lia. Qed.

Lemma c_copy_f_bytes: forall n w sr ow, bytes_ok w -> bytes_ok ow ->
  (forall i, sr = SWin i -> 0 <= i /\ i + Z.of_nat n <= Zlength w) ->
  (forall i, sr = SOut i -> 0 <= i < Zlength ow) ->
  bytes_ok (fst (copy_f n w sr ow)).
Proof.
  induction n; intros w sr ow BW BO HW HO; simpl; [exact BO | ].
  destruct sr as [i | i].
  - destruct (HW i eq_refl) as [A B].
    apply IHn; auto.
    + unfold bytes_ok. apply Forall_app. split; [exact BO | ]. constructor; [ | constructor].
      apply (proj1 (Forall_Znth _ _) BW); lia.
    + intros j E. inversion E; subst. lia.
    + intros j E. discriminate.
  - destruct (HO i eq_refl) as [A B].
    apply IHn; auto.
    + unfold bytes_ok. apply Forall_app. split; [exact BO | ]. constructor; [ | constructor].
      apply (proj1 (Forall_Znth _ _) BO); lia.
    + intros j E. discriminate.
    + intros j E. inversion E; subst. rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed.

Lemma c_copy_win_bytes: forall w i n ow, bytes_ok w -> bytes_ok ow -> 0 <= i -> 0 <= n -> i + n <= Zlength w ->
  bytes_ok (fst (copy_bytes w (SWin i) n ow)).
Proof.
  intros. unfold copy_bytes. apply c_copy_f_bytes; auto.
  - intros j E; inversion E; subst. rewrite Z2Nat.id by lia. lia.
  - intros j E; discriminate.
Qed.

Lemma fast_ok_ow: forall m o, fast_ok m -> Zlength (m_ow m) <= Zlength o <= m_aout m -> bytes_ok o ->
  fast_ok (set_m_ow m o).
Proof.
  intros m o [W T] A B. split; [ | exact T].
  destruct W. constructor; cbn [set_m_ow m_s m_h m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret
    m_leave m_adler m_msg m_tin m_tout m_snx m_sow m_mode] in *; auto; try lia.
  split; [lia | exact B].
Qed.

Ltac fin_ws := unfold set_m_ow; cbn [src_ok m_s m_ow];
  match goal with H: i_win _ = true |- _ => rewrite ?H end; repeat split; try reflexivity; lia.

(* what the window part gives the tail *)
Lemma wsplit_ok: forall m L D ow1 sr L',
  fast_ok m -> 3 <= L <= 258 -> Zlength (m_ow m) < D -> D - Zlength (m_ow m) <= i_whave (m_s m) ->
  Zlength (m_ow m) + 258 <= m_aout m ->
  wsplit (m_s m) L D (m_ow m) = (ow1, sr, L') ->
  fast_ok (set_m_ow m ow1) /\ 0 <= L' <= 258 /\ src_ok (set_m_ow m ow1) sr L' /\
  Zlength (m_ow m) <= Zlength ow1 /\ Zlength ow1 + L' = Zlength (m_ow m) + L.
Proof.
  intros m L D ow1 sr L' FOK HL HD1 HD2 HA WS.
  pose proof FOK as [W _].
  pose proof (mw_s _ W) as SW. pose proof (mw_ow _ W) as [OWA OWB].
  pose proof (sw_wdata _ SW) as [WL WB]. pose proof (sw_wnext _ SW) as [WN1 WN2].
  pose proof (sw_whave _ SW) as WHV. pose proof (sw_wvalid _ SW) as WV. pose proof (sw_wsize _ SW) as WSZ.
  assert (WIN: i_win (m_s m) = true) by (destruct WSZ as [E | [E _]]; [lia | exact E]).
  pose proof (Zlength_nonneg (m_ow m)) as OWN.
  unfold wsplit in WS.
  set (op := D - Zlength (m_ow m)) in *.
  set (w := i_wdata (m_s m)) in *.
  assert (FO: forall o, Zlength (m_ow m) <= Zlength o <= m_aout m -> bytes_ok o ->
    fast_ok (set_m_ow m o)) by (intros; apply fast_ok_ow; auto).
  destruct (Z.eqb_spec (i_wnext (m_s m)) 0) as [W0 | W0].
  - (* wnext = 0: the window is full *)
    assert (WF: i_whave (m_s m) = i_wsize (m_s m))
      by (destruct (Z_lt_le_dec (i_whave (m_s m)) (i_wsize (m_s m))) as [Q|Q]; [specialize (WV Q) |]; lia).
    destruct (Z.ltb_spec op L) as [OL | OL].
    + destruct (copy_bytes w (SWin (i_wsize (m_s m) - op)) op (m_ow m)) as [o1 s1] eqn:C.
      inversion WS; subst ow1 sr L'; clear WS.
      assert (LN: Zlength o1 = Zlength (m_ow m) + op)
        by (change o1 with (fst (o1, s1)); rewrite <- C; apply c_copy_bytes_len; lia).
      assert (BO: bytes_ok o1)
        by (change o1 with (fst (o1, s1)); rewrite <- C; apply c_copy_win_bytes; auto; lia).
      split; [apply FO; auto; lia | ]. unfold op in *; fin_ws.
    + inversion WS; subst ow1 sr L'; clear WS.
      split; [apply FO; auto; lia | ]. unfold op in *; fin_ws.
  - destruct (Z.ltb_spec (i_wnext (m_s m)) op) as [WO | WO].
    + (* wrap around: the window is full *)
      assert (WF: i_whave (m_s m) = i_wsize (m_s m))
        by (destruct (Z_lt_le_dec (i_whave (m_s m)) (i_wsize (m_s m))) as [Q|Q]; [specialize (WV Q) |]; lia).
      destruct (Z.ltb_spec (op - i_wnext (m_s m)) L) as [OL | OL].
      * destruct (copy_bytes w (SWin (i_wsize (m_s m) + i_wnext (m_s m) - op)) (op - i_wnext (m_s m)) (m_ow m))
          as [o1 s1] eqn:C.
        assert (LN: Zlength o1 = Zlength (m_ow m) + (op - i_wnext (m_s m)))
          by (change o1 with (fst (o1, s1)); rewrite <- C; apply c_copy_bytes_len; lia).
        assert (BO: bytes_ok o1)
          by (change o1 with (fst (o1, s1)); rewrite <- C; apply c_copy_win_bytes; auto; lia).
        destruct (Z.ltb_spec (i_wnext (m_s m)) (L - (op - i_wnext (m_s m)))) as [OL2 | OL2].
        -- destruct (copy_bytes w (SWin 0) (i_wnext (m_s m)) o1) as [o2 s2] eqn:C2.
           inversion WS; subst ow1 sr L'; clear WS.
           assert (LN2: Zlength o2 = Zlength o1 + i_wnext (m_s m))
             by (change o2 with (fst (o2, s2)); rewrite <- C2; apply c_copy_bytes_len; lia).
           assert (BO2: bytes_ok o2)
             by (change o2 with (fst (o2, s2)); rewrite <- C2; apply c_copy_win_bytes; auto; lia).
           split; [apply FO; auto; lia | ]. unfold op in *; fin_ws.
        -- inversion WS; subst ow1 sr L'; clear WS.
           split; [apply FO; auto; lia | ]. unfold op in *; fin_ws.
      * inversion WS; subst ow1 sr L'; clear WS.
        split; [apply FO; auto; lia | ]. unfold op in *; fin_ws.
    + (* contiguous *)
      assert (WH: i_wnext (m_s m) <= i_whave (m_s m))
        by (destruct (Z_lt_le_dec (i_whave (m_s m)) (i_wsize (m_s m))) as [Q|Q]; [specialize (WV Q) |]; lia).
      destruct (Z.ltb_spec op L) as [OL | OL].
      * destruct (copy_bytes w (SWin (i_wnext (m_s m) - op)) op (m_ow m)) as [o1 s1] eqn:C.
        inversion WS; subst ow1 sr L'; clear WS.
        assert (LN: Zlength o1 = Zlength (m_ow m) + op)
          by (change o1 with (fst (o1, s1)); rewrite <- C; apply c_copy_bytes_len; lia).
        assert (BO: bytes_ok o1)
          by (change o1 with (fst (o1, s1)); rewrite <- C; apply c_copy_win_bytes; auto; lia).
        split; [apply FO; auto; lia | ]. unfold op in *; fin_ws.
      * inversion WS; subst ow1 sr L'; clear WS.
        split; [apply FO; auto; lia | ]. unfold op in *; fin_ws.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* pointers into the output                                                                       *)

Lemma out_ptr_isptr: forall ob aout k, out_ok ob aout -> isptr (out_ptr ob k).
Proof. intros [sh p lo n c] aout k (_ & P & _). destruct p; try contradiction. exact I. Qed.

Lemma out_ptr_sameblock: forall ob aout a b, out_ok ob aout -> is_true (sameblock (out_ptr ob a) (out_ptr ob b)).
Proof.
  intros [sh p lo n c] aout a b (_ & P & _). destruct p; try contradiction.
  unfold out_ptr, offset_val, sameblock. destruct (peq b0 b0); [reflexivity | congruence].
Qed.

Lemma out_sub_val: forall ob aout a b, out_ok ob aout -> 0 <= a <= aout -> 0 <= b <= aout ->
  force_val (sem_cast tlong tuint (eval_binop Osub (tptr tuchar) (tptr tuchar) (out_ptr ob a) (out_ptr ob b))) =
  Vint (Int.repr (a - b)).
Proof.
  intros [sh p lo n c] aout a b (_ & P & LO & A0 & LN & _ & MX) Ha Hb. destruct p; try contradiction.
  unfold out_ptr, offset_val, eval_binop. simpl.
  unfold sem_sub_pp. simpl. destruct (eq_block b0 b0) as [_|NE]; [|congruence]. simpl.
  rewrite (Ptrofs.add_commut i (Ptrofs.repr (lo + a))), (Ptrofs.add_commut i (Ptrofs.repr (lo + b))),
    Ptrofs.sub_shifted.
  assert (Dv: Ptrofs.divs (Ptrofs.sub (Ptrofs.repr (lo + a)) (Ptrofs.repr (lo + b))) (Ptrofs.repr 1) =
             Ptrofs.sub (Ptrofs.repr (lo + a)) (Ptrofs.repr (lo + b))).
  { unfold Ptrofs.divs. change (Ptrofs.signed (Ptrofs.repr 1)) with 1. rewrite Z.quot_1_r. apply Ptrofs.repr_signed. }
  rewrite Dv. unfold Ptrofs.sub.
  rewrite (Ptrofs.unsigned_repr (lo + a)), (Ptrofs.unsigned_repr (lo + b)) by (unfold Ptrofs.max_unsigned in *; lia).
  replace (lo + a - (lo + b)) with (a - b) by lia.
  unfold Vptrofs. destruct Archi.ptr64 eqn:AR; [|discriminate]. simpl.
  f_equal. unfold Int64.loword.
  rewrite Ptrofs.unsigned_repr_eq, Int64.Z_mod_modulus_eq. change Int64.modulus with Ptrofs.modulus.
  rewrite Z.mod_mod by (compute; congruence). apply Int.eqm_samerepr. unfold Int.eqm. apply Zbits.eqmod_sym.
  eapply Zbits.eqmod_divides; [apply Zbits.eqmod_mod; compute; reflexivity | ]. exists (2^32). reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the memory of the break: state->sane, state->mode and strm apart from rest_mem                 *)

Definition strm_x (F: frame) (m: mst) : mpred :=
  strm_rep (f_gv F) (f_shs F) (f_strmp F)
    (in_ptr (f_ib F) (m_snx m)) (zv (Zlength (m_inp m) - m_snx m)) (m_tin m)
    (out_ptr (f_ob F) (m_sow m)) (zv (m_aout m - m_sow m)) (m_tout m)
    (msg_val (f_gv F) (m_msg m)) (f_sp F) (f_dt F) (m_adler m) (f_vres F).

Definition rest_x (F: frame) (m: mst) : mpred :=
  let gv := f_gv F in let sp := f_sp F in let s := m_s m in
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
  field_at Ews t_state (DOT _back) (zv (i_back s)) sp *
  field_at Ews t_state (DOT _was) (zv (i_was s)) sp *
  head_part F m *
  data_at (f_gsh F) (tarray tushort 19) (map (fun z => Vint (Int.repr z)) order)
    (f_gv F Zlib.inflate.code._order) *
  Zlib.proof.inftrees.spec.itables (f_gsh F) (f_gv F) *
  crc_table_at (f_tsh F) (f_gv F).

(* the sane and mode fields and strm to the front (on variables: a cheap proof term) *)
Lemma sepcon_rest_split: forall a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 hd st ord it crc: mpred,
  (a1 * a2 * a3 * a4 * a5 * a6 * a7 * a8 * a9 * a10 * a11 * a12 * a13 * a14 * a15 * a16 * a17 * a18 * a19 * a20 * a21 * a22 * a23 * a24 * a25 * a26 * a27 * a28 * a29 * a30 * a31 * a32 * a33 * a34) * hd * st * ord * it * crc =
  a32 * a2 * st * (a1 * a3 * a4 * a5 * a6 * a7 * a8 * a9 * a10 * a11 * a12 * a13 * a14 * a15 * a16 * a17 * a18 * a19 * a20 * a21 * a22 * a23 * a24 * a25 * a26 * a27 * a28 * a29 * a30 * a31 * a33 * a34 * hd * ord * it * crc).
Proof. intros. apply pred_ext; cancel. Qed.

Lemma rest_mem_split: forall F m,
  rest_mem F m =
  field_at Ews t_state (DOT _sane) (zv (i_sane (m_s m))) (f_sp F) *
  field_at Ews t_state (DOT _mode) (zv (i_mode (m_s m))) (f_sp F) *
  strm_x F m * rest_x F m.
Proof. intros. unfold rest_mem, state_rep_nc, rest_x, strm_x. apply sepcon_rest_split. Qed.

Lemma rest_x_bad: forall F m e, rest_x F (set_bad m e) = rest_x F m.
Proof. intros. reflexivity. Qed.

Lemma bad_s: forall m e, m_s (set_bad m e) = set_i_mode (m_s m) BAD.
Proof. reflexivity. Qed.
Lemma tab_mem_mode: forall F s v, tab_mem F (set_i_mode s v) = tab_mem F s.
Proof. reflexivity. Qed.
Lemma win_rep_mode: forall w s v, win_rep w (set_i_mode s v) = win_rep w s.
Proof. reflexivity. Qed.
Lemma win_val_mode: forall F s v, win_val F (set_i_mode s v) = win_val F s.
Proof. reflexivity. Qed.

Lemma eval_sub_uint: forall a c,
  eval_binop Osub tuint tuint (Vint (Int.repr a)) (Vint (Int.repr c)) = Vint (Int.repr (a - c)).
Proof. intros. unfold eval_binop. simpl. rewrite sub_repr. reflexivity. Qed.

Lemma eval_add_uint: forall a c,
  eval_binop Oadd tuint tuint (Vint (Int.repr a)) (Vint (Int.repr c)) = Vint (Int.repr (a + c)).
Proof. intros. unfold eval_binop. simpl. rewrite add_repr. reflexivity. Qed.

Lemma ptr_add_u: forall p x, isptr p -> 0 <= x <= Int.max_unsigned ->
  force_val (sem_binary_operation' Oadd (tptr tuchar) tuint p (Vint (Int.repr x))) = offset_val x p.
Proof.
  intros. destruct p; try contradiction. simpl.
  f_equal. unfold Ptrofs.of_intu, Ptrofs.of_int.
  rewrite Int.unsigned_repr by rep_lia. rewrite Ptrofs.mul_commut, Ptrofs.mul_one. reflexivity.
Qed.

Lemma out_ptr_sub_u: forall ob aout k a, out_ok ob aout -> 0 <= a <= Int.max_unsigned ->
  force_val (sem_binary_operation' Osub (tptr tuchar) tuint (out_ptr ob k) (Vint (Int.repr a))) =
  out_ptr ob (k - a).
Proof.
  intros [sh p lo n c] aout k a (_ & P & _) A. destruct p; try contradiction. simpl.
  f_equal. unfold Ptrofs.of_intu, Ptrofs.of_int.
  rewrite Int.unsigned_repr by rep_lia. rewrite Ptrofs.mul_commut, Ptrofs.mul_one.
  rewrite Ptrofs.sub_add_opp, Ptrofs.add_assoc. f_equal.
  rewrite Ptrofs.neg_repr, ptrofs_add_repr. f_equal; lia.
Qed.

Lemma set_m_ow_id: forall m, set_m_ow m (m_ow m) = m.
Proof. intros []. reflexivity. Qed.

(* the cases of wsplit, along the C code *)

Lemma ws_0_lt: forall s L D ow op, op = D - Zlength ow -> i_wnext s = 0 -> op < L ->
  wsplit s L D ow =
  (fst (copy_bytes (i_wdata s) (SWin (i_wsize s - op)) op ow), SOut (Zlength (fst (copy_bytes (i_wdata s) (SWin (i_wsize s - op)) op ow)) - D), L - op).
Proof.
  intros s L D ow op Eop A B. unfold wsplit. subst op. rewrite A. cbn [Z.eqb].
  rewrite (proj2 (Z.ltb_lt _ _) B). destruct (copy_bytes _ _ _ _); reflexivity.
Qed.

Lemma ws_0_ge: forall s L D ow op, op = D - Zlength ow -> i_wnext s = 0 -> L <= op -> wsplit s L D ow = (ow, SWin (i_wsize s - op), L).
Proof.
  intros s L D ow op Eop A B. unfold wsplit. subst op. rewrite A. cbn [Z.eqb].
  rewrite (proj2 (Z.ltb_ge _ _) B). reflexivity.
Qed.

Lemma ws_wrap_lt_lt: forall s L D ow op, op = D - Zlength ow -> i_wnext s <> 0 -> i_wnext s < op -> op - i_wnext s < L -> i_wnext s < L - (op - i_wnext s) ->
  wsplit s L D ow =
  (fst (copy_bytes (i_wdata s) (SWin 0) (i_wnext s) (fst (copy_bytes (i_wdata s) (SWin (i_wsize s + i_wnext s - op)) (op - i_wnext s) ow))),
   SOut (Zlength (fst (copy_bytes (i_wdata s) (SWin 0) (i_wnext s) (fst (copy_bytes (i_wdata s) (SWin (i_wsize s + i_wnext s - op)) (op - i_wnext s) ow)))) - D),
   L - (op - i_wnext s) - i_wnext s).
Proof.
  intros s L D ow op Eop A B C E. unfold wsplit. subst op.
  rewrite (proj2 (Z.eqb_neq _ _) A), (proj2 (Z.ltb_lt _ _) B), (proj2 (Z.ltb_lt _ _) C).
  destruct (copy_bytes (i_wdata s) (SWin (i_wsize s + i_wnext s - (D - Zlength ow))) (D - Zlength ow - i_wnext s) ow) as [o1 s1]; cbn [fst].
  rewrite (proj2 (Z.ltb_lt _ _) E). destruct (copy_bytes _ _ _ o1); reflexivity.
Qed.

Lemma ws_wrap_lt_ge: forall s L D ow op, op = D - Zlength ow -> i_wnext s <> 0 -> i_wnext s < op -> op - i_wnext s < L -> L - (op - i_wnext s) <= i_wnext s ->
  wsplit s L D ow = (fst (copy_bytes (i_wdata s) (SWin (i_wsize s + i_wnext s - op)) (op - i_wnext s) ow), SWin 0, L - (op - i_wnext s)).
Proof.
  intros s L D ow op Eop A B C E. unfold wsplit. subst op.
  rewrite (proj2 (Z.eqb_neq _ _) A), (proj2 (Z.ltb_lt _ _) B), (proj2 (Z.ltb_lt _ _) C).
  destruct (copy_bytes (i_wdata s) (SWin (i_wsize s + i_wnext s - (D - Zlength ow))) (D - Zlength ow - i_wnext s) ow) as [o1 s1]; cbn [fst].
  rewrite (proj2 (Z.ltb_ge _ _) E). reflexivity.
Qed.

Lemma ws_wrap_ge: forall s L D ow op, op = D - Zlength ow -> i_wnext s <> 0 -> i_wnext s < op -> L <= op - i_wnext s ->
  wsplit s L D ow = (ow, SWin (i_wsize s + i_wnext s - op), L).
Proof.
  intros s L D ow op Eop A B C. unfold wsplit. subst op.
  rewrite (proj2 (Z.eqb_neq _ _) A), (proj2 (Z.ltb_lt _ _) B), (proj2 (Z.ltb_ge _ _) C). reflexivity.
Qed.

Lemma ws_in_lt: forall s L D ow op, op = D - Zlength ow -> i_wnext s <> 0 -> op <= i_wnext s -> op < L ->
  wsplit s L D ow =
  (fst (copy_bytes (i_wdata s) (SWin (i_wnext s - op)) op ow), SOut (Zlength (fst (copy_bytes (i_wdata s) (SWin (i_wnext s - op)) op ow)) - D), L - op).
Proof.
  intros s L D ow op Eop A B C. unfold wsplit. subst op.
  rewrite (proj2 (Z.eqb_neq _ _) A), (proj2 (Z.ltb_ge _ _) B), (proj2 (Z.ltb_lt _ _) C).
  destruct (copy_bytes _ _ _ _); reflexivity.
Qed.

Lemma ws_in_ge: forall s L D ow op, op = D - Zlength ow -> i_wnext s <> 0 -> op <= i_wnext s -> L <= op ->
  wsplit s L D ow = (ow, SWin (i_wnext s - op), L).
Proof.
  intros s L D ow op Eop A B C. unfold wsplit. subst op.
  rewrite (proj2 (Z.eqb_neq _ _) A), (proj2 (Z.ltb_ge _ _) B), (proj2 (Z.ltb_ge _ _) C). reflexivity.
Qed.


Lemma m_ow_ow: forall m o, m_ow (set_m_ow m o) = o. Proof. reflexivity. Qed.
Lemma m_s_ow: forall m o, m_s (set_m_ow m o) = m_s m. Proof. reflexivity. Qed.
Lemma m_nx_ow: forall m o, m_nx (set_m_ow m o) = m_nx m. Proof. reflexivity. Qed.
Lemma m_inp_ow: forall m o, m_inp (set_m_ow m o) = m_inp m. Proof. reflexivity. Qed.
Lemma m_aout_ow: forall m o, m_aout (set_m_ow m o) = m_aout m. Proof. reflexivity. Qed.
Lemma m_hold_ow: forall m o, m_hold (set_m_ow m o) = m_hold m. Proof. reflexivity. Qed.
Lemma m_bits_ow: forall m o, m_bits (set_m_ow m o) = m_bits m. Proof. reflexivity. Qed.
Lemma rest_mem_ow: forall F m o, rest_mem F (set_m_ow m o) = rest_mem F m. Proof. reflexivity. Qed.
Lemma set_m_ow_ow: forall m a b, set_m_ow (set_m_ow m a) b = set_m_ow m b. Proof. reflexivity. Qed.
Ltac ow_norm := rewrite ?set_m_ow_ow, ?m_ow_ow, ?m_s_ow, ?m_nx_ow, ?m_inp_ow, ?m_aout_ow, ?m_hold_ow, ?m_bits_ow,
  ?rest_mem_ow.

Lemma f5_copy_ok : wloop_stmt s_wloop1 -> wloop_stmt s_wloop2 -> wloop_stmt s_wloop3 -> wloop_stmt s_wloop4 ->
  tail_stmt -> direct_stmt -> copy_stmt.
Proof.
  intros WL1 WL2 WL3 WL4 TL DR. intros Espec F m L D FOK MD HL HD HOW OOK SHS.
  stmt_simpl. unfold fs_state, fs_locals, fs_sep; cbn [app]. abbreviate_semax.
  pose proof (Zlength_nonneg (m_ow m)) as OWN.
  pose proof (mw_ow _ (fast_ok_mwf _ FOK)) as [OWA OWB].
  pose proof (out_ptr_isptr _ _ (Zlength (m_ow m)) OOK) as PO.
  pose proof (out_ptr_isptr _ _ 0 OOK) as PB.
  forward.
  { entailer!. apply prop_right. eapply out_ptr_sameblock; eauto. }
  rewrite (out_sub_val _ (m_aout m)) by (auto; lia). rewrite Z.sub_0_r.
  pose proof (mw_aout _ (fast_ok_mwf _ FOK)) as AOR.
  pose proof (mw_s _ (fast_ok_mwf _ FOK)) as SW.
  pose proof (sw_whave _ SW) as WHV. pose proof (sw_wnext _ SW) as [WN1 WN2]. pose proof (sw_sane _ SW) as SANE.
  assert (WSZ: i_wsize (m_s m) <= 2 ^ 23).
  { destruct (sw_wsize _ SW) as [E | [_ E]]; [lia | rewrite E; apply Z.pow_le_mono_r; [lia | apply (sw_wbits _ SW)]]. }
  forward_if.
  2: { (* direct from the output *)
    assert (DH: D <= Zlength (m_ow m)) by (try rewrite Int.unsigned_repr in H by rep_lia; lia).
    eapply semax_post; [ | | | | eapply semax_pre; [ | apply (DR Espec F m L D FOK ltac:(lia) ltac:(lia) ltac:(lia) OOK)] ].
    - unfold POSTCONDITION, abbreviate, fpost, normal_ret_assert. cbn [RA_normal].
      rewrite fcopy_direct by exact DH.
      apply andp_left2. Exists (set_m_ow m (fst (copy_bytes (i_wdata (m_s m)) (SOut (Zlength (m_ow m) - D)) L (m_ow m)))).
      unfold fs_state, PROPx. apply andp_right; [apply prop_right; simpl; auto | apply andp_left2; apply derives_refl].
    - unfold normal_ret_assert. cbn [RA_break]. apply andp_left2, FF_left.
    - unfold normal_ret_assert. cbn [RA_continue]. apply andp_left2, FF_left.
    - intros vl. unfold normal_ret_assert. cbn [RA_return]. apply andp_left2, FF_left.
    - unfold fs_state, fs_locals, fs_sep; cbn [app]. entailer!. }
  try rewrite Int.unsigned_repr in H by rep_lia.
  forward. rewrite sub_repr.
  set (OP := D - Zlength (m_ow m)).
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx ((OP <= i_whave (m_s m)) :: P) (LOCALx Q (SEPx R))) end.
  { (* too far back: break *)
    try rewrite !Int.unsigned_repr in H0 by (unfold OP; rep_lia).
    rewrite rest_mem_split. unfold strm_x, strm_rep. Intros.
    remember (f_gv F inflate.code._zcalloc) as zca eqn:EZA. remember (f_gv F inflate.code._zcfree) as zcf eqn:EZF.
    forward.
    forward_if.
    2: { exfalso. rewrite SANE in H1. inversion H1. }
    forward. forward. forward.
    unfold fpost; cbn [RA_break].
    rewrite (fcopy_far m L D) by (auto; fold OP; lia).
    Exists (set_bad m F_far). unfold fs_state, fs_locals, fs_sep; cbn [app].
    rewrite rest_mem_split, rest_x_bad. unfold strm_x, strm_rep.
    rewrite bad_s, tab_mem_mode, win_rep_mode, win_val_mode.
    cbn [set_bad set_mode upd_s set_m_s set_m_msg m_ow m_nx m_hold m_bits m_inp m_aout m_s m_msg m_snx m_sow
         m_tin m_tout m_adler i_mode i_sane i_wsize i_whave i_wnext i_lencode i_distcode i_lenbits i_distbits
         set_i_mode msg_val msg_ident].
    rewrite <- EZA, <- EZF. unfold BAD.
    entailer!. }
  { forward. try rewrite !Int.unsigned_repr in H0 by (unfold OP; rep_lia).
    unfold fpost; simpl RA_normal. entailer!. }
  Intros.
  assert (WIN: i_win (m_s m) = true)
    by (destruct (sw_wsize _ SW) as [E | [E _]]; [unfold OP in *; lia | exact E]).
  assert (WV: win_val F (m_s m) = f_winp F) by (unfold win_val; rewrite WIN; reflexivity).
  assert_PROP (isptr (f_winp F)) as PW by (unfold win_rep; rewrite WIN; entailer!).
  rewrite WV.
  forward.
  remember (f_winp F) as wp eqn:EWP.
  forward_if (EX ow1: list Z, EX sr: src, EX L': Z,
    fs_state F (set_m_ow m ow1) [wsplit (m_s m) L D (m_ow m) = (ow1, sr, L')]
      [temp _len (zv L'); temp _from (src_ptr F sr); temp _dist (zv D)]).
  { forward.
    subst wp. rewrite eval_sub_uint, ptr_add_u by (auto; unfold OP in *; rep_lia).
    assert (WF: i_whave (m_s m) = i_wsize (m_s m)).
    { destruct (Z_lt_le_dec (i_whave (m_s m)) (i_wsize (m_s m))) as [Q|Q];
        [pose proof (sw_wvalid _ SW Q); unfold OP in *; lia | lia]. }
    forward_if.
    + (* op < len: op bytes from the end of the window, the rest from the output *)
      forward. rewrite sub_repr.
      eapply semax_seq'.
      { eapply semax_pre; [ | apply (WL1 Espec F m (i_wsize (m_s m) - OP) OP (L - OP) D FOK);
          auto; unfold OP in *; lia ].
        unfold fs_state, fs_locals, fs_sep; cbn [app]. rewrite WV. entailer!. }
      set (ow1 := fst (copy_bytes (i_wdata (m_s m)) (SWin (i_wsize (m_s m) - OP)) OP (m_ow m))).
      unfold fs_state, fs_locals, fs_sep; cbn [app]. ow_norm.
      unfold MORE_COMMANDS, abbreviate.
      remember (f_ob F) as ob eqn:EOB.
      forward.
      { subst ob. entailer!. all: eapply out_ptr_isptr; eauto. }
      subst ob. rewrite (out_ptr_sub_u _ (m_aout m)) by (auto; rep_lia).
      unfold fpost; cbn [RA_normal].
      Exists ow1 (SOut (Zlength ow1 - D)) (L - OP).
      unfold fs_state, fs_locals, fs_sep; cbn [app src_ptr]. ow_norm. rewrite WV.
      rewrite (ws_0_lt (m_s m) L D (m_ow m) OP eq_refl) by (unfold OP in *; lia).
      entailer!.
    + forward.
      unfold fpost; cbn [RA_normal].
      Exists (m_ow m) (SWin (i_wsize (m_s m) - OP)) L.
      unfold fs_state, fs_locals, fs_sep; cbn [app src_ptr]. rewrite set_m_ow_id, WV.
      rewrite (ws_0_ge (m_s m) L D (m_ow m) OP eq_refl) by (unfold OP in *; lia).
      entailer!. }
  { (* wnext <> 0 *)
    assert (W0: i_wnext (m_s m) <> 0).
    { intro E. rewrite E in H1. apply H1. reflexivity. }
    forward_if.
    + (* wnext < op: wrap around the window, which is full *)
      assert (WF: i_whave (m_s m) = i_wsize (m_s m)).
      { destruct (Z_lt_le_dec (i_whave (m_s m)) (i_wsize (m_s m))) as [Q|Q];
          [pose proof (sw_wvalid _ SW Q); unfold OP in *; lia | lia]. }
      forward.
      subst wp. rewrite eval_add_uint, eval_sub_uint, ptr_add_u by (auto; unfold OP in *; rep_lia).
      forward. rewrite sub_repr.
      forward_if.
      * (* some from the end of the window *)
        forward. rewrite sub_repr.
        eapply semax_seq'.
        { eapply semax_pre; [ | apply (WL2 Espec F m (i_wsize (m_s m) + i_wnext (m_s m) - OP) (OP - i_wnext (m_s m))
              (L - (OP - i_wnext (m_s m))) D FOK); auto; unfold OP in *; lia ].
          unfold fs_state, fs_locals, fs_sep; cbn [app]. rewrite WV. entailer!. }
        set (ow1 := fst (copy_bytes (i_wdata (m_s m)) (SWin (i_wsize (m_s m) + i_wnext (m_s m) - OP))
                     (OP - i_wnext (m_s m)) (m_ow m))).
        assert (LN1: Zlength ow1 = Zlength (m_ow m) + (OP - i_wnext (m_s m)))
          by (apply c_copy_bytes_len; unfold OP in *; lia).
        assert (FO1: fast_ok (set_m_ow m ow1)).
        { pose proof (sw_wdata _ SW) as [WL WB]. apply fast_ok_ow; auto; [unfold OP in *; lia | ].
          apply c_copy_win_bytes; auto; unfold OP in *; lia. }
        unfold fs_state, fs_locals, fs_sep; cbn [app]. ow_norm.
        unfold MORE_COMMANDS, abbreviate. rewrite WV.
        forward.
        forward_if.
        -- (* and some from the start of the window *)
           forward. forward. rewrite sub_repr.
           eapply semax_seq'.
           { eapply semax_pre; [ | apply (WL3 Espec F (set_m_ow m ow1) 0 (i_wnext (m_s m))
                 (L - (OP - i_wnext (m_s m)) - i_wnext (m_s m)) D FO1);
                 ow_norm; auto; unfold OP in *; lia ].
             unfold fs_state, fs_locals, fs_sep; cbn [app]. ow_norm. rewrite WV, isptr_offset_val_zero by auto.
             entailer!. }
           set (ow2 := fst (copy_bytes (i_wdata (m_s (set_m_ow m ow1))) (SWin 0) (i_wnext (m_s m))
                         (m_ow (set_m_ow m ow1)))).
           unfold fs_state, fs_locals, fs_sep; cbn [app]. ow_norm.
           unfold MORE_COMMANDS, abbreviate.
           remember (f_ob F) as ob eqn:EOB.
           forward.
           { subst ob. entailer!. all: eapply out_ptr_isptr; eauto. }
           subst ob. rewrite (out_ptr_sub_u _ (m_aout m)) by (auto; rep_lia).
           unfold fpost; cbn [RA_normal].
           Exists ow2 (SOut (Zlength ow2 - D)) (L - (OP - i_wnext (m_s m)) - i_wnext (m_s m)).
           unfold fs_state, fs_locals, fs_sep; cbn [app src_ptr]. ow_norm. rewrite WV.
           rewrite (ws_wrap_lt_lt (m_s m) L D (m_ow m) OP eq_refl) by (unfold OP in *; lia).
           entailer!.
        -- forward.
           unfold fpost; cbn [RA_normal].
           Exists ow1 (SWin 0) (L - (OP - i_wnext (m_s m))).
           unfold fs_state, fs_locals, fs_sep; cbn [app src_ptr]. ow_norm. rewrite WV, isptr_offset_val_zero by auto.
           rewrite (ws_wrap_lt_ge (m_s m) L D (m_ow m) OP eq_refl) by (unfold OP in *; lia).
           entailer!.
      * forward.
        unfold fpost; cbn [RA_normal].
        Exists (m_ow m) (SWin (i_wsize (m_s m) + i_wnext (m_s m) - OP)) L.
        unfold fs_state, fs_locals, fs_sep; cbn [app src_ptr]. rewrite set_m_ow_id, WV.
        rewrite (ws_wrap_ge (m_s m) L D (m_ow m) OP eq_refl) by (unfold OP in *; lia).
        entailer!.
    + (* op <= wnext: contiguous in the window *)
      assert (WH: i_wnext (m_s m) <= i_whave (m_s m)).
      { destruct (Z_lt_le_dec (i_whave (m_s m)) (i_wsize (m_s m))) as [Q|Q];
          [pose proof (sw_wvalid _ SW Q); lia | specialize (WN2 ltac:(unfold OP in *; lia)); lia]. }
      forward.
      subst wp. rewrite eval_sub_uint, ptr_add_u by (auto; unfold OP in *; rep_lia).
      forward_if.
      * forward. rewrite sub_repr.
        eapply semax_seq'.
        { eapply semax_pre; [ | apply (WL4 Espec F m (i_wnext (m_s m) - OP) OP (L - OP) D FOK);
            auto; unfold OP in *; lia ].
          unfold fs_state, fs_locals, fs_sep; cbn [app]. rewrite WV. entailer!. }
        set (ow1 := fst (copy_bytes (i_wdata (m_s m)) (SWin (i_wnext (m_s m) - OP)) OP (m_ow m))).
        unfold fs_state, fs_locals, fs_sep; cbn [app]. ow_norm.
        unfold MORE_COMMANDS, abbreviate.
        remember (f_ob F) as ob eqn:EOB.
        forward.
        { subst ob. entailer!. all: eapply out_ptr_isptr; eauto. }
        subst ob. rewrite (out_ptr_sub_u _ (m_aout m)) by (auto; rep_lia).
        unfold fpost; cbn [RA_normal].
        Exists ow1 (SOut (Zlength ow1 - D)) (L - OP).
        unfold fs_state, fs_locals, fs_sep; cbn [app src_ptr]. ow_norm. rewrite WV.
        rewrite (ws_in_lt (m_s m) L D (m_ow m) OP eq_refl) by (unfold OP in *; lia).
        entailer!.
      * forward.
        unfold fpost; cbn [RA_normal].
        Exists (m_ow m) (SWin (i_wnext (m_s m) - OP)) L.
        unfold fs_state, fs_locals, fs_sep; cbn [app src_ptr]. rewrite set_m_ow_id, WV.
        rewrite (ws_in_ge (m_s m) L D (m_ow m) OP eq_refl) by (unfold OP in *; lia).
        entailer!. }
  (* the tail: the rest from sr *)
  subst wp. Intros ow1 sr L'.
  unfold fs_state. apply semax_extract_PROP; intro WS.
  destruct (wsplit_ok m L D ow1 sr L' FOK HL H ltac:(unfold OP in *; lia) HOW WS) as (FO1 & HL' & SO & LE1 & LE2).
  eapply semax_post; [ | | | | eapply semax_pre;
    [ | apply (TL Espec F (set_m_ow m ow1) sr L' D FO1 HL' SO); ow_norm; [lia | auto] ] ].
  - unfold normal_ret_assert, fpost; cbn [RA_normal].
    rewrite (fcopy_win m L D ow1 sr L') by (auto; unfold OP in *; lia).
    apply andp_left2.
    Exists (set_m_ow (set_m_ow m ow1) (fst (copy_bytes (i_wdata (m_s (set_m_ow m ow1))) sr L' (m_ow (set_m_ow m ow1))))).
    unfold fs_state, PROPx. apply andp_right; [apply prop_right; split; [reflexivity | exact I] | ].
    apply andp_left2; apply derives_refl.
  - unfold normal_ret_assert. cbn [RA_break]. apply andp_left2, FF_left.
  - unfold normal_ret_assert. cbn [RA_continue]. apply andp_left2, FF_left.
  - intros vl. unfold normal_ret_assert. cbn [RA_return]. apply andp_left2, FF_left.
  - unfold fs_state. apply andp_left2, derives_refl.
Qed.
