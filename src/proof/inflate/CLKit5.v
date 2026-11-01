(* The case CODELENS (18) of inflate()'s switch (Cases5_CL.v), cut into parts:
   - the Clight cut into its statements (cl_while: the while loop; cl_lookup / cl_small / cl_rep / cl_fill: the
     pieces of one pass; cl_tail: after the loop; cl_tables / cl_dists: the two inflate_table calls);
   - the model (Model.v codelens_iter, c_CODELENS) cut the same way (cl_small_m, cl_rep_m, cl_lens_m, cl_dists_m,
     cl_dists_out) with the equations that glue it back;
   - the state with the local `here` holding a value (loop_state_h) and with the temporaries len / copy
     (loop_state_hc), and their field split (loop_state_clh: the twelve fields the case touches, the z_stream
     and the static tables apart; the rest of the memory one opaque SEP item, as TLKit5.v);
   - the statements of the parts (cl_*_stmt), proved in CL<Part>5.v. *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Export Zlib.proof.inflate.CaseHyps5.
Require Export Zlib.proof.inflate.Model2.
Require Export Zlib.proof.inflate.NeedBits.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* ---------------------------------------------------------------------------------------------- *)
(* the Clight                                                                                     *)

Definition cl_body : statement := case_body 18.
Definition cl_while : statement := match cl_body with Ssequence w _ => w | _ => Sskip end.
Definition cl_tail : statement := match cl_body with Ssequence _ t => t | _ => Sskip end.
Definition cl_loopbody : statement := match cl_while with Sloop b _ => b | _ => Sskip end.
(* while (state->have < state->nlen + state->ndist) *)
Definition cl_cond : statement := match cl_loopbody with Ssequence c _ => c | _ => Sskip end.
Definition cl_iter : statement := match cl_loopbody with Ssequence _ i => i | _ => Sskip end.
(* for (;;) { here = state->lencode[BITS(state->lenbits)]; if (here.bits <= bits) break; PULLBYTE(); } *)
Definition cl_lookup : statement := match cl_iter with Ssequence l _ => l | _ => Sskip end.
Definition cl_branch : statement :=
  match cl_iter with Ssequence _ (Ssequence _ (Ssequence _ b)) => b | _ => Sskip end.
(* here.val < 16: DROPBITS(here.bits); state->lens[state->have++] = here.val; *)
Definition cl_small : statement := match cl_branch with Sifthenelse _ s _ => s | _ => Sskip end.
Definition cl_big : statement := match cl_branch with Sifthenelse _ _ b => b | _ => Sskip end.
(* the repeat codes 16 / 17 / 18: NEEDBITS(here.bits + 2/3/7), DROPBITS(here.bits), (16: have == 0 -> BAD),
   len, copy, DROPBITS(2/3/7) *)
Definition cl_rep : statement := match cl_big with Ssequence r _ => r | _ => Sskip end.
(* if (state->have + copy > state->nlen + state->ndist) { BAD } while (copy--) state->lens[state->have++] = len; *)
Definition cl_fill : statement := match cl_big with Ssequence _ f => f | _ => Sskip end.
(* after the loop: if (leave) break; if (mode == BAD) break; if (lens[256] == 0) { BAD } cl_tables *)
Definition cl_tables : statement :=
  match cl_tail with Ssequence _ (Ssequence _ (Ssequence _ t)) => t | _ => Sskip end.
(* next = codes; lencode = next; lenbits = 9; ret = inflate_table(LENS, ...); if (ret) { BAD } cl_dists *)
Definition cl_dists : statement :=
  match cl_tables with Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ d)))) => d
                     | _ => Sskip end.

Ltac cl_stmt := cbv beta iota zeta delta [cl_body cl_while cl_tail cl_loopbody cl_cond cl_iter cl_lookup cl_branch
  cl_small cl_big cl_rep cl_fill cl_tables cl_dists case_body inflate_LS find_switch f_inflate fn_body ls_drop].

Lemma cl_body_eq: cl_body = Ssequence cl_while cl_tail.
Proof. reflexivity. Qed.

Lemma cl_while_eq: cl_while = Sloop (Ssequence cl_cond cl_iter) Sskip.
Proof. reflexivity. Qed.

Lemma cl_iter_eq: cl_iter =
  Ssequence cl_lookup
    (Ssequence (Sifthenelse (Etempvar _leave tint) Sbreak Sskip)
      (Ssequence (Sset _t'290 (Efield (Evar _here (Tstruct ___gp_code noattr)) _val tushort))
        (Sifthenelse (Ebinop Olt (Etempvar _t'290 tushort) (Econst_int (Int.repr 16) tint) tint)
          cl_small cl_big))).
Proof. reflexivity. Qed.

Lemma cl_big_eq: cl_big = Ssequence cl_rep cl_fill.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the model                                                                                      *)

(* here.val < 16 *)
Definition cl_small_m (here: entry) (m: mst) : mst :=
  let m := dropbits (e_bits here) m in
  upd_s m (fun s => set_i_have (set_i_lens s (upd_Znth (i_have s) (i_lens s) (e_val here))) (i_have s + 1)).

(* here.val >= 16: (machine, len, copy, ok) *)
Definition cl_rep_m (here: entry) (m: mst) : mst * Z * Z * bool :=
      if e_val here =? 16 then
        let m := needbits (e_bits here + 2) m in
        if m_leave m =? 1 then (m, 0, 0, false) else
        let m := dropbits (e_bits here) m in
        if i_have (m_s m) =? 0 then (set_bad m M_repeat, 0, 0, true) else
        let len := Znth (i_have (m_s m) - 1) (i_lens (m_s m)) in
        let copy := 3 + bitsn m 2 in
        (dropbits 2 m, len, copy, true)
      else if e_val here =? 17 then
        let m := needbits (e_bits here + 3) m in
        if m_leave m =? 1 then (m, 0, 0, false) else
        let m := dropbits (e_bits here) m in
        let copy := 3 + bitsn m 3 in
        (dropbits 3 m, 0, copy, true)
      else
        let m := needbits (e_bits here + 7) m in
        if m_leave m =? 1 then (m, 0, 0, false) else
        let m := dropbits (e_bits here) m in
        let copy := 11 + bitsn m 7 in
        (dropbits 7 m, 0, copy, true).

Lemma codelens_iter_eq: forall fx dx m,
  codelens_iter fx dx m =
  let '(here, m1, ok) := lookup1 fx dx (i_lencode (m_s m)) (i_lenbits (m_s m)) m in
  if negb ok then CLleave m1 else
  if e_val here <? 16 then CLnext (cl_small_m here m1) else
  let '(m2, len, copy, ok2) := cl_rep_m here m1 in
  if negb ok2 then CLleave m2 else
  if m_mode m2 =? BAD then CLbad m2 else
  if i_nlen (m_s m2) + i_ndist (m_s m2) <? i_have (m_s m2) + copy then CLbad (set_bad m2 M_repeat) else
  CLnext (upd_s m2 (lens_fill (Z.to_nat copy) len)).
Proof.
  intros. unfold codelens_iter.
  destruct (lookup1 fx dx (i_lencode (m_s m)) (i_lenbits (m_s m)) m) as [[here m1] ok]. reflexivity.
Qed.

(* the LENS table: (ret, machine after it) *)
Definition cl_lens_m (m1: mst) : Z * mst :=
  let s := set_i_lenbits (set_i_lencode (set_i_next (m_s m1) 0) (TCodes 0)) 9 in
  let '(r, codes, nxt, lb) := call_table LENS 0 (i_nlen s) 9 s in
  (r, set_m_ret (set_m_s m1 (set_i_lenbits (set_i_next (set_i_codes s codes) nxt) lb)) r).

(* the DISTS table: (ret, machine after it) *)
Definition cl_dists_m (m: mst) : Z * mst :=
  let s := set_i_distbits (set_i_distcode (m_s m) (TCodes (i_next (m_s m)))) 6 in
  let '(r, codes, nxt, db) := call_table DISTS (i_nlen s) (i_ndist s) 6 s in
  (r, set_m_ret (set_m_s m (set_i_distbits (set_i_next (set_i_codes s codes) nxt) db)) r).

(* the rest of the step from the DISTS table on *)
Definition cl_dists_out (fl: Z) (m: mst) : iout :=
  let '(r, m) := cl_dists_m m in
  if negb (r =? 0) then IBrk (set_bad m M_d_set) else
  let m := set_mode m LEN_ in
  if fl =? Z_TREES then IBrk (set_leave m) else
  c_LEN_ lenfix_list distfix_list (fast lenfix_list distfix_list) m.

(* the rest of the step from the LENS table on *)
Definition cl_lens_out (fl: Z) (m1: mst) : iout :=
  let '(r, mA) := cl_lens_m m1 in
  if negb (r =? 0) then IBrk (set_bad mA M_ll_set) else cl_dists_out fl mA.

Lemma c_CODELENS_eq: forall fl m,
  c_CODELENS fl lenfix_list distfix_list (fast lenfix_list distfix_list) m =
  match codelens_loop lenfix_list distfix_list 320 m with
  | CLleave m1 => IBrk m1
  | CLbad m1 => IBrk m1
  | CLnext m1 =>
      if Znth 256 (i_lens (m_s m1)) =? 0 then IBrk (set_bad m1 M_eob) else cl_lens_out fl m1
  end.
Proof.
  intros. unfold c_CODELENS.
  destruct (codelens_loop lenfix_list distfix_list 320 m) as [m1 | m1 | m1]; [ | exact eq_refl | exact eq_refl].
  destruct (Znth 256 (i_lens (m_s m1)) =? 0); [exact eq_refl | ].
  unfold cl_lens_out, cl_lens_m. cbv zeta.
  destruct (call_table LENS 0 _ 9 _) as [[[r c] n] b].
  destruct (negb (r =? 0)); [exact eq_refl | ].
  unfold cl_dists_out, cl_dists_m. cbv zeta.
  destruct (call_table DISTS _ _ 6 _) as [[[r2 c2] n2] d2]. exact eq_refl.
Qed.

(* the while loop's exits *)
Definition cl_exit (m m1: mst) : Prop :=
  (codelens_loop lenfix_list distfix_list 320 m = CLnext m1 /\ mwf m1 /\ m_mode m1 = CODELENS /\ m_leave m1 = 0 /\
     i_nlen (m_s m1) + i_ndist (m_s m1) <= i_have (m_s m1)) \/
  (codelens_loop lenfix_list distfix_list 320 m = CLleave m1 /\ m_leave m1 = 1) \/
  (codelens_loop lenfix_list distfix_list 320 m = CLbad m1 /\ m_leave m1 = 0 /\ m_mode m1 = BAD).

(* what the DISTS part needs of the machine after the LENS table *)
Definition cl_dists_pre (mA: mst) : Prop :=
  swf (m_s mA) /\ m_mode mA = CODELENS /\ m_leave mA = 0 /\
  257 <= i_nlen (m_s mA) <= 286 /\ 1 <= i_ndist (m_s mA) <= 30 /\ 0 <= i_next (m_s mA) <= ENOUGH_LENS /\
  (forall k, i_nlen (m_s mA) <= k < i_nlen (m_s mA) + i_ndist (m_s mA) -> 0 <= Znth k (i_lens (m_s mA)) <= 15).

(* ---------------------------------------------------------------------------------------------- *)
(* the states                                                                                     *)

(* the loop state with the local `here` holding hv *)
Definition loop_state_h (F: frame) (m: mst) (hv: reptype t_code) : environ -> mpred :=
  PROPx [in_ok (f_ib F) (m_inp m); out_ok (f_ob F) (m_aout m)]
  (LOCALx (loop_locals F m)
  (SEPx [mem_rep F m; data_at Tsh t_code hv (f_vhere F); data_at_ Tsh t_code (f_vlast F);
         data_at_ Tsh (tarray tuchar 4) (f_vhbuf F)])).

(* and the temporaries len and copy *)
Definition loop_state_hc (F: frame) (m: mst) (hv: reptype t_code) (len copy: Z) : environ -> mpred :=
  PROPx [in_ok (f_ib F) (m_inp m); out_ok (f_ob F) (m_aout m)]
  (LOCALx (temp _len (zv len) :: temp _copy (zv copy) :: loop_locals F m)
  (SEPx [mem_rep F m; data_at Tsh t_code hv (f_vhere F); data_at_ Tsh t_code (f_vlast F);
         data_at_ Tsh (tarray tuchar 4) (f_vhbuf F)])).

Lemma loop_state_h_def: forall F m, loop_state F m = loop_state_h F m (default_val t_code).
Proof.
  intros. unfold loop_state, loop_state_h, locals_rep. f_equal. f_equal.
  unfold SEPx. extensionality rho. simpl. rewrite !sepcon_emp.
  unfold data_at_, field_at_. rewrite !sepcon_assoc. reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the field split: mode, nlen, ndist, have, lens, next, lencode, distcode, lenbits, distbits, codes, work *)

Definition state_rest_cl (gv: globals) (sp strmp headp winp: val) (s: istate) : mpred :=
  field_at Ews t_state (DOT _strm) strmp sp *
  field_at Ews t_state (DOT _last) (zv (i_last s)) sp *
  field_at Ews t_state (DOT _wrap) (zv (i_wrap s)) sp *
  field_at Ews t_state (DOT _havedict) (zv (i_havedict s)) sp *
  field_at Ews t_state (DOT _flags) (zv (i_flags s)) sp *
  field_at Ews t_state (DOT _dmax) (zv (i_dmax s)) sp *
  field_at Ews t_state (DOT _check) (lv (i_check s)) sp *
  field_at Ews t_state (DOT _total) (lv (i_total s)) sp *
  field_at Ews t_state (DOT _head) (if i_head s then headp else nullval) sp *
  field_at Ews t_state (DOT _wbits) (zv (i_wbits s)) sp *
  field_at Ews t_state (DOT _wsize) (zv (i_wsize s)) sp *
  field_at Ews t_state (DOT _whave) (zv (i_whave s)) sp *
  field_at Ews t_state (DOT _wnext) (zv (i_wnext s)) sp *
  field_at Ews t_state (DOT _window) (if i_win s then winp else nullval) sp *
  field_at Ews t_state (DOT _hold) (lv (i_hold s)) sp *
  field_at Ews t_state (DOT _bits) (zv (i_bits s)) sp *
  field_at Ews t_state (DOT _length) (zv (i_length s)) sp *
  field_at Ews t_state (DOT _offset) (zv (i_offset s)) sp *
  field_at Ews t_state (DOT _extra) (zv (i_extra s)) sp *
  field_at Ews t_state (DOT _ncode) (zv (i_ncode s)) sp *
  field_at Ews t_state (DOT _sane) (zv (i_sane s)) sp *
  field_at Ews t_state (DOT _back) (zv (i_back s)) sp *
  field_at Ews t_state (DOT _was) (zv (i_was s)) sp.

Lemma sepcon_cl_35: forall a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35: mpred,
  a1 * a2 * a3 * a4 * a5 * a6 * a7 * a8 * a9 * a10 * a11 * a12 * a13 * a14 * a15 * a16 * a17 * a18 * a19 * a20 * a21 * a22 * a23 * a24 * a25 * a26 * a27 * a28 * a29 * a30 * a31 * a32 * a33 * a34 * a35 =
  a2 * a26 * a27 * a28 * a30 * a29 * a21 * a22 * a23 * a24 * a32 * a31 *
  (a1 * a3 * a4 * a5 * a6 * a7 * a8 * a9 * a10 * a11 * a12 * a13 * a14 * a15 * a16 * a17 * a18 * a19 * a20 * a25 * a33 * a34 * a35).
Proof. intros. apply pred_ext; cancel. Qed.

Lemma state_rep_cl: forall gv sp strmp headp winp s,
  state_rep gv sp strmp headp winp s =
  field_at Ews t_state (DOT _mode) (zv (i_mode s)) sp *
  field_at Ews t_state (DOT _nlen) (zv (i_nlen s)) sp *
  field_at Ews t_state (DOT _ndist) (zv (i_ndist s)) sp *
  field_at Ews t_state (DOT _have) (zv (i_have s)) sp *
  field_at Ews t_state (DOT _lens) (map (fun z => Vint (Int.repr z)) (i_lens s)) sp *
  field_at Ews t_state (DOT _next) (codes_at sp (i_next s)) sp *
  field_at Ews t_state (DOT _lencode) (tref_val gv sp (i_lencode s)) sp *
  field_at Ews t_state (DOT _distcode) (tref_val gv sp (i_distcode s)) sp *
  field_at Ews t_state (DOT _lenbits) (zv (i_lenbits s)) sp *
  field_at Ews t_state (DOT _distbits) (zv (i_distbits s)) sp *
  field_at Ews t_state (DOT _codes) (map ent (i_codes s)) sp *
  field_at_ Ews t_state (DOT _work) sp *
  state_rest_cl gv sp strmp headp winp s.
Proof. intros. unfold state_rep, state_rest_cl. apply sepcon_cl_35. Qed.

(* the memory but those twelve fields, the z_stream and the static tables *)
Definition mem_rest_cl (F: frame) (m: mst) : mpred :=
  state_rest_cl (f_gv F) (f_sp F) (f_strmp F) (f_headp F) (f_winp F) (m_s m) *
  win_rep (f_winp F) (m_s m) *
  head_part F m *
  in_rep (f_ib F) *
  out_rep (f_ob F) (m_ow m) *
  crc_table_at (f_tsh F) (f_gv F).

Definition cl_strm (F: frame) (m: mst) : mpred :=
  strm_rep (f_gv F) (f_shs F) (f_strmp F)
    (in_ptr (f_ib F) (m_snx m)) (zv (Zlength (m_inp m) - m_snx m)) (m_tin m)
    (out_ptr (f_ob F) (m_sow m)) (zv (m_aout m - m_sow m)) (m_tout m)
    (msg_val (f_gv F) (m_msg m)) (f_sp F) (f_dt F) (m_adler m) (f_vres F).

Definition cl_sep (F: frame) (m: mst) (hv: reptype t_code) : list mpred :=
  let s := m_s m in let sp := f_sp F in
  [field_at Ews t_state (DOT _mode) (zv (i_mode s)) sp;
   field_at Ews t_state (DOT _nlen) (zv (i_nlen s)) sp;
   field_at Ews t_state (DOT _ndist) (zv (i_ndist s)) sp;
   field_at Ews t_state (DOT _have) (zv (i_have s)) sp;
   field_at Ews t_state (DOT _lens) (map (fun z => Vint (Int.repr z)) (i_lens s)) sp;
   field_at Ews t_state (DOT _next) (codes_at sp (i_next s)) sp;
   field_at Ews t_state (DOT _lencode) (tref_val (f_gv F) sp (i_lencode s)) sp;
   field_at Ews t_state (DOT _distcode) (tref_val (f_gv F) sp (i_distcode s)) sp;
   field_at Ews t_state (DOT _lenbits) (zv (i_lenbits s)) sp;
   field_at Ews t_state (DOT _distbits) (zv (i_distbits s)) sp;
   field_at Ews t_state (DOT _codes) (map ent (i_codes s)) sp;
   field_at_ Ews t_state (DOT _work) sp;
   cl_strm F m;
   tables_rep (f_gsh F) (f_gv F);
   mem_rest_cl F m;
   data_at Tsh t_code hv (f_vhere F);
   data_at_ Tsh t_code (f_vlast F);
   data_at_ Tsh (tarray tuchar 4) (f_vhbuf F)].

Definition loop_state_clh (F: frame) (m: mst) (hv: reptype t_code) : environ -> mpred :=
  PROPx [in_ok (f_ib F) (m_inp m); out_ok (f_ob F) (m_aout m)]
  (LOCALx (loop_locals F m) (SEPx (cl_sep F m hv))).

Definition loop_state_clhc (F: frame) (m: mst) (hv: reptype t_code) (len copy: Z) : environ -> mpred :=
  PROPx [in_ok (f_ib F) (m_inp m); out_ok (f_ob F) (m_aout m)]
  (LOCALx (temp _len (zv len) :: temp _copy (zv copy) :: loop_locals F m) (SEPx (cl_sep F m hv))).

Lemma cl_sep_eq: forall F m hv,
  SEPx (A := environ) [mem_rep F m; data_at Tsh t_code hv (f_vhere F); data_at_ Tsh t_code (f_vlast F);
        data_at_ Tsh (tarray tuchar 4) (f_vhbuf F)] = SEPx (cl_sep F m hv).
Proof.
  intros. unfold cl_sep, cl_strm, mem_rep, mem_rest_cl. rewrite state_rep_cl.
  unfold SEPx. extensionality rho. simpl. apply pred_ext; cancel.
Qed.

Lemma loop_state_h_cl: forall F m hv, loop_state_h F m hv = loop_state_clh F m hv.
Proof. intros. unfold loop_state_h, loop_state_clh. rewrite cl_sep_eq. reflexivity. Qed.

Lemma loop_state_hc_cl: forall F m hv len copy, loop_state_hc F m hv len copy = loop_state_clhc F m hv len copy.
Proof. intros. unfold loop_state_hc, loop_state_clhc. rewrite cl_sep_eq. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* small helpers (TLKit5.v's, renamed)                                                            *)

Lemma cl_semax_dowhile0 {Espec: OracleKind} (Delta: tycontext) (P Q: environ -> mpred) (c rest: statement)
    (R: ret_assert):
  semax Delta P c (normal_ret_assert Q) -> semax Delta Q rest R ->
  semax Delta P (Ssequence (Sloop c Sbreak) rest) R.
Proof.
  intros H1 H2. apply semax_seq with Q; [ | exact H2].
  apply semax_loop with (Q' := Q).
  - destruct R. eapply semax_post; [ | | | | exact H1]; intros; simpl_ret_assert;
      first [apply andp_left2, derives_refl | apply andp_left2, FF_left].
  - eapply semax_pre; [ | apply semax_break]. destruct R. simpl_ret_assert. apply andp_left2, derives_refl.
Qed.

Lemma cl_int_and_ones: forall b k, 0 <= b -> 0 <= k <= 32 ->
  Int.and (Int.repr b) (Int.repr (2 ^ k - 1)) = Int.repr (b mod 2 ^ k).
Proof.
  intros b k Hb Hk. unfold Int.and.
  rewrite (Int.unsigned_repr_eq b).
  rewrite (Int.unsigned_repr (2 ^ k - 1)).
  - f_equal. replace (2 ^ k - 1) with (Z.ones k) by (rewrite Z.ones_equiv; lia). rewrite Z.land_ones by lia.
    change Int.modulus with (2 ^ 32). symmetry. apply Znumtheory.Zmod_div_mod.
    + apply Z.pow_pos_nonneg; lia.
    + lia.
    + exists (2 ^ (32 - k)). rewrite <- Z.pow_add_r by lia. f_equal. lia.
  - split; [ | change Int.max_unsigned with (2 ^ 32 - 1)].
    + assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia). lia.
    + assert (2 ^ k <= 2 ^ 32) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

Lemma cl_long_shru_eq: forall h n, 0 <= h <= Int64.max_unsigned -> 0 <= n < 64 ->
  Int64.shru (Int64.repr h) (Int64.repr n) = Int64.repr (Z.shiftr h n).
Proof.
  intros h n Hh Hn. unfold Int64.shru.
  rewrite (Int64.unsigned_repr h) by lia. rewrite (Int64.unsigned_repr n) by rep_lia. reflexivity.
Qed.

Lemma cl_u32_repr: forall x, Int.repr (u32 x) = Int.repr x.
Proof.
  intros. unfold u32. apply Int.eqm_samerepr. unfold Int.eqm. apply Zbits.eqmod_sym, Zbits.eqmod_mod.
  reflexivity.
Qed.

(* BITS(k)'s mask (1U << k) - 1 *)
Ltac cl_mask_simpl :=
  repeat match goal with |- context [Int.sub (Int.shl (Int.repr 1) (Int.repr ?k)) (Int.repr 1)] =>
    change (Int.sub (Int.shl (Int.repr 1) (Int.repr k)) (Int.repr 1)) with (Int.repr (2 ^ k - 1)) end.

(* ---------------------------------------------------------------------------------------------- *)
(* the statements of the parts                                                                    *)

(* the table lookup loop (CLLookup5.v) *)
Definition cl_lookup_stmt : Prop :=
  forall {Espec: OracleKind} (F: frame) (m: mst) (hv: reptype t_code),
  frame_ok5 F -> mwf m -> m_mode m = CODELENS -> m_leave m = 0 ->
  semax Delta_cases5 (loop_state_h F m hv) cl_lookup
    (normal_ret_assert (EX here: entry, EX m1: mst, EX ok: bool,
       !! (lookup1 lenfix_list distfix_list (i_lencode (m_s m)) (i_lenbits (m_s m)) m = (here, m1, ok)) &&
       loop_state_h F m1 (ent here))).

(* a code length 0..15 (CLSmall5.v) *)
Definition cl_small_stmt : Prop :=
  forall {Espec: OracleKind} (F: frame) (m: mst) (here: entry),
  frame_ok5 F -> mwf m -> m_mode m = CODELENS -> m_leave m = 0 -> entry_ok here ->
  e_bits here <= m_bits m -> e_val here < 16 ->
  i_have (m_s m) < i_nlen (m_s m) + i_ndist (m_s m) ->
  semax Delta_cases5 (loop_state_h F m (ent here)) cl_small
    (normal_ret_assert (loop_state_h F (cl_small_m here m) (ent here))).

(* a repeat code 16, 17 or 18 (any value >= 16: 18's branch is the C else): CLRep5.v *)
Definition cl_rep_stmt : Prop :=
  forall {Espec: OracleKind} (F: frame) (m: mst) (here: entry),
  frame_ok5 F -> mwf m -> m_mode m = CODELENS -> m_leave m = 0 -> entry_ok here ->
  e_bits here <= m_bits m -> e_bits here <= 15 -> 16 <= e_val here ->
  i_have (m_s m) < i_nlen (m_s m) + i_ndist (m_s m) ->
  semax Delta_cases5 (loop_state_h F m (ent here)) cl_rep
    {| RA_normal := EX m2: mst, EX len: Z, EX copy: Z,
         !! (cl_rep_m here m = (m2, len, copy, true) /\ m_mode m2 = CODELENS /\ m_leave m2 = 0) &&
         loop_state_hc F m2 (ent here) len copy;
       RA_break := EX m2: mst,
         !! ((cl_rep_m here m = (m2, 0, 0, false) /\ m_leave m2 = 1) \/
             (cl_rep_m here m = (m2, 0, 0, true) /\ m_mode m2 = BAD /\ m_leave m2 = 0)) &&
         loop_state_h F m2 (ent here);
       RA_continue := FF;
       RA_return := fun _ _ => FF |}.

(* the range check and the copy loop (CLFill5.v) *)
Definition cl_fill_stmt : Prop :=
  forall {Espec: OracleKind} (F: frame) (m: mst) (here: entry) (len copy: Z),
  frame_ok5 F -> mwf m -> m_mode m = CODELENS -> m_leave m = 0 ->
  0 <= len <= 65535 -> 1 <= copy <= 138 -> i_have (m_s m) <= i_nlen (m_s m) + i_ndist (m_s m) ->
  semax Delta_cases5 (loop_state_hc F m (ent here) len copy) cl_fill
    {| RA_normal := !! (i_have (m_s m) + copy <= i_nlen (m_s m) + i_ndist (m_s m)) &&
         loop_state_h F (upd_s m (lens_fill (Z.to_nat copy) len)) (ent here);
       RA_break := !! (i_nlen (m_s m) + i_ndist (m_s m) < i_have (m_s m) + copy) &&
         loop_state_h F (set_bad m M_repeat) (ent here);
       RA_continue := FF;
       RA_return := fun _ _ => FF |}.

(* the while loop (CLWhile5.v), from the parts *)
Definition cl_while_stmt : Prop :=
  forall {Espec: OracleKind} (F: frame) (m: mst),
  frame_ok5 F -> mwf m -> m_mode m = CODELENS -> m_leave m = 0 ->
  semax Delta_cases5 (loop_state F m) cl_while
    (normal_ret_assert (EX m1: mst, EX hv: reptype t_code, !! cl_exit m m1 && loop_state_h F m1 hv)).

(* the DISTS table, LEN_, Z_TREES (CLDists5.v) *)
Definition cl_dists_stmt : Prop :=
  forall {Espec: OracleKind} (F: frame) (m0 mA: mst) (hv: reptype t_code),
  frame_ok5 F -> cl_dists_pre mA ->
  (fst (cl_dists_m mA) = 0 -> mwf3 (set_mode (snd (cl_dists_m mA)) LEN_)) ->
  stepf2 (f_flush F) lenfix_list distfix_list m0 = cl_dists_out (f_flush F) mA ->
  semax Delta_cases5 (loop_state_h F mA hv) cl_dists
    (overridePost (fall_post5 F m0 LEN_) (switch_ret_assert (case_post2 F m0))).

(* the LENS table (CLLens5.v), followed by any DISTS part satisfying cl_dists_stmt's conclusion *)
Definition cl_lens_stmt : Prop :=
  forall {Espec: OracleKind} (F: frame) (m0 m1: mst) (hv: reptype t_code),
  frame_ok5 F -> mwf m1 -> m_mode m1 = CODELENS -> m_leave m1 = 0 ->
  i_nlen (m_s m1) + i_ndist (m_s m1) <= i_have (m_s m1) ->
  stepf2 (f_flush F) lenfix_list distfix_list m0 = cl_lens_out (f_flush F) m1 ->
  (forall (mA: mst) (hv': reptype t_code), cl_lens_m m1 = (0, mA) ->
     semax Delta_cases5 (loop_state_h F mA hv') cl_dists
       (overridePost (fall_post5 F m0 LEN_) (switch_ret_assert (case_post2 F m0)))) ->
  semax Delta_cases5 (loop_state_h F m1 hv) cl_tables
    (overridePost (fall_post5 F m0 LEN_) (switch_ret_assert (case_post2 F m0))).

(* the pure facts of the tables (CLTabFacts5.v) *)
Definition cl_tab_facts_stmt : Prop :=
  cover3_stmt -> forall m1, mwf m1 -> m_mode m1 = CODELENS -> m_leave m1 = 0 ->
  i_nlen (m_s m1) + i_ndist (m_s m1) <= i_have (m_s m1) ->
  forall mA, cl_lens_m m1 = (0, mA) ->
  cl_dists_pre mA /\ (fst (cl_dists_m mA) = 0 -> mwf3 (set_mode (snd (cl_dists_m mA)) LEN_)).
