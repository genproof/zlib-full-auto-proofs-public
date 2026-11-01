(* LENEXT: the whole case from its NEEDBITS loop (part of the cases LENEXT/DIST, Cases5_LD.v; definitions and statements in LdKit5.v) *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate.LdKit5.
Require Import Zlib.proof.inflate.NeedKit5.
Require Import Zlib.proof.inflate.MwfLemmas.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* ---------------------------------------------------------------------------------------------- *)
(* the model                                                                                      *)

(* length += BITS(ex); DROPBITS(ex); back += ex *)
Definition le_m2 (ex: Z) (m: mst) : mst :=
  dropbits ex (upd_s m (fun s => set_i_length (set_i_back s (i_back s + ex)) (u32 (i_length (m_s m) + bitsn m ex)))).

(* was = length; mode = DIST *)
Definition le_fin_m (m: mst) : mst := set_mode (upd_s m (fun s => set_i_was s (i_length s))) DIST.

(* the machine after `if (state->extra) { ... }` (without leave) *)
Definition le_X (m: mst) : mst :=
  if i_extra (m_s m) =? 0 then m else le_m2 (i_extra (m_s m)) (needbits (i_extra (m_s m)) m).

Lemma le_c_eq: forall m,
  (i_extra (m_s m) = 0 \/ m_leave (needbits (i_extra (m_s m)) m) = 0) ->
  c_LENEXT lenfix_list distfix_list m = c_DIST lenfix_list distfix_list (le_fin_m (le_X m)).
Proof.
  intros m H. unfold c_LENEXT, le_X. cbv zeta.
  destruct (Z.eqb_spec (i_extra (m_s m)) 0) as [E | E]; cbn [negb]; [reflexivity | ].
  destruct H as [H | H]; [congruence | ]. rewrite H. reflexivity.
Qed.

Lemma le_leave_eq: forall m,
  i_extra (m_s m) <> 0 -> m_leave (needbits (i_extra (m_s m)) m) = 1 ->
  c_LENEXT lenfix_list distfix_list m = IBrk (needbits (i_extra (m_s m)) m).
Proof.
  intros m E H. unfold c_LENEXT. cbv zeta.
  rewrite (proj2 (Z.eqb_neq _ _) E). cbn [negb]. rewrite H. reflexivity.
Qed.

(* the invariant of the machine entering DIST *)
Lemma le_mwf3_0: forall m, mwf3 m -> m_mode m = LENEXT -> mwf3 (le_fin_m m).
Proof.
  intros m [W W3] HM.
  pose proof (md_length _ (mw_md _ W)) as ML.
  pose proof (md_back _ (mw_md _ W)) as MB.
  pose proof (sw_length _ (mw_s _ W)) as SL.
  unfold m_mode in HM.
  assert (Hne: forall P: Prop, i_mode (m_s m) = LENLENS \/ i_mode (m_s m) = CODELENS \/
               i_mode (m_s m) = DISTEXT \/ i_mode (m_s m) = MATCH \/ i_mode (m_s m) = DIST \/
               i_mode (m_s m) = HEAD -> P).
  { intros P X. exfalso. rewrite HM in X. unfold LENLENS, CODELENS, LENEXT, DIST, DISTEXT, MATCH, HEAD in *. lia. }
  assert (L1: 1 <= i_length (m_s m)) by (apply ML; left; exact HM).
  assert (B1: i_back (m_s m) <= 15) by (apply (proj1 MB); exact HM).
  assert (D: decode_mode (i_mode (m_s m))) by (rewrite HM; unfold decode_mode; auto).
  destruct (md_tables _ (mw_md _ W) D) as [TL TD].
  pose proof (s3_len _ W3 D) as XL.
  assert (O: m_out m = m_aout m).
  { apply mwf_out_eq; [exact W | ..]; unfold m_mode; rewrite HM; unfold LENEXT, LENGTH, DONE, BAD; lia. }
  destruct W as [MD SW HW A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16].
  split.
  - constructor; cbn [le_fin_m set_mode upd_s set_m_s m_s m_h m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out
                      m_ret m_leave m_adler m_msg m_tin m_tout m_snx m_sow m_mode]; try assumption.
    + constructor; cbn [i_mode set_i_mode set_i_was i_length i_back i_offset i_extra];
        try (intros X; unfold DIST, LENLENS, CODELENS, LENEXT, DISTEXT, MATCH in X; lia).
      all: first [ intros _; split; [exact TL | exact TD]
                 | split; [ | split]; intros X; unfold DIST, LENEXT, DISTEXT in X; lia ].
    + destruct SW; constructor; cbn [set_i_mode set_i_was i_mode i_last i_wrap i_havedict i_flags
        i_dmax i_check i_total i_head i_wbits i_wsize i_whave i_wnext i_win i_wdata i_hold i_bits i_length i_offset
        i_extra i_lencode i_distcode i_lenbits i_distbits i_ncode i_nlen i_ndist i_have i_next i_lens i_codes i_sane
        i_back i_was]; try assumption.
      unfold DIST, HEAD, SYNC; lia.
    + left. exact O.
  - constructor; cbn [le_fin_m set_mode upd_s set_m_s m_s set_i_mode set_i_was i_mode i_length i_offset
      i_lencode i_lenbits].
    + intros X; unfold DIST, HEAD in X; lia.
    + intros _. exact XL.
    + intros X; unfold DIST, LENEXT in X; lia.
    + intros X; unfold DIST, DISTEXT in X; lia.
Qed.

Lemma le_mwf3_g: forall X L d, mwf X -> swf3 (m_s X) -> i_mode (m_s X) = LENEXT -> 0 <= d ->
  i_back (m_s X) + d <= 20 -> 1 <= L <= Int.max_unsigned ->
  mwf3 (set_mode (upd_s X (fun s => set_i_was (set_i_length (set_i_back s (i_back s + d)) L) L)) DIST).
Proof.
  intros m L d W W3 HM Hd HB HL.
  pose proof (md_back _ (mw_md _ W)) as MB.
  pose proof (sw_back _ (mw_s _ W)) as SB.
  assert (B1: i_back (m_s m) <= 15) by (apply (proj1 MB); exact HM).
  assert (D: decode_mode (i_mode (m_s m))) by (rewrite HM; unfold decode_mode; auto).
  destruct (md_tables _ (mw_md _ W) D) as [TL TD].
  pose proof (s3_len _ W3 D) as XL.
  assert (O: m_out m = m_aout m).
  { apply mwf_out_eq; [exact W | ..]; unfold m_mode; rewrite HM; unfold LENEXT, LENGTH, DONE, BAD; lia. }
  destruct W as [MD SW HW A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16].
  split.
  - constructor; cbn [set_mode upd_s set_m_s m_s m_h m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out
                      m_ret m_leave m_adler m_msg m_tin m_tout m_snx m_sow m_mode]; try assumption.
    + constructor; cbn [i_mode set_i_mode set_i_was set_i_length set_i_back i_length i_back i_offset i_extra];
        try (intros X; unfold DIST, LENLENS, CODELENS, LENEXT, DISTEXT, MATCH in X; lia).
      all: first [ intros _; split; [exact TL | exact TD]
                 | split; [ | split]; intros X; unfold DIST, LENEXT, DISTEXT in X; lia ].
    + destruct SW; constructor; cbn [set_i_mode set_i_was set_i_length set_i_back i_mode i_last i_wrap i_havedict
        i_flags i_dmax i_check i_total i_head i_wbits i_wsize i_whave i_wnext i_win i_wdata i_hold i_bits i_length
        i_offset i_extra i_lencode i_distcode i_lenbits i_distbits i_ncode i_nlen i_ndist i_have i_next i_lens
        i_codes i_sane i_back i_was]; try assumption; unfold urange; try lia.
      unfold DIST, HEAD, SYNC; lia.
    + left. exact O.
  - constructor; cbn [set_mode upd_s set_m_s m_s set_i_mode set_i_was set_i_length set_i_back i_mode i_length
      i_offset i_lencode i_lenbits].
    + intros X; unfold DIST, HEAD in X; lia.
    + intros _. exact XL.
    + intros X; unfold DIST, LENEXT in X; lia.
    + intros X; unfold DIST, DISTEXT in X; lia.
Qed.

Lemma le_mwf3_1: forall m, mwf3 m -> m_mode m = LENEXT -> m_leave m = 0 -> i_extra (m_s m) <> 0 ->
  m_leave (needbits (i_extra (m_s m)) m) = 0 ->
  mwf3 (le_fin_m (le_m2 (i_extra (m_s m)) (needbits (i_extra (m_s m)) m))).
Proof.
  intros m [W W3] HM HL0 E0 L0.
  pose proof (md_lenext _ (mw_md _ W) HM) as XT.
  pose proof (sw_extra _ (mw_s _ W)) as XS.
  pose proof (proj1 (md_back _ (mw_md _ W)) HM) as BK.
  pose proof (md_length _ (mw_md _ W) (or_introl HM)) as LN.
  pose proof (s3_lenext _ W3 HM) as LN2.
  pose proof (needbits_s (i_extra (m_s m)) m) as S.
  set (ex := i_extra (m_s m)) in *.
  assert (W1: mwf (needbits ex m)) by (apply mwf_needbits; [exact W | lia]).
  destruct (needbits_ok ex m W HL0 ltac:(lia) ltac:(lia)) as [NB _].
  set (m1 := needbits ex m) in *. clearbody m1.
  pose proof (mw_bits _ W1) as BT1.
  pose proof (bitsn_range m1 ex ltac:(lia)) as BR.
  assert (P5: 2 ^ ex <= 2 ^ 5) by (apply Z.pow_le_mono_r; lia).
  change (2 ^ 5) with 32 in P5.
  replace (le_fin_m (le_m2 ex m1)) with
    (set_mode (upd_s (dropbits ex m1) (fun s => set_i_was (set_i_length (set_i_back s (i_back s + ex))
       (u32 (i_length (m_s m1) + bitsn m1 ex))) (u32 (i_length (m_s m1) + bitsn m1 ex)))) DIST) by reflexivity.
  assert (U: u32 (i_length (m_s m1) + bitsn m1 ex) = i_length (m_s m1) + bitsn m1 ex).
  { unfold u32. rewrite Z.mod_small; [reflexivity | ]. rewrite S. change (2 ^ 32) with 4294967296. lia. }
  rewrite U.
  apply le_mwf3_g; cbn [dropbits set_m_bits set_m_hold m_s]; rewrite ?S; try lia.
  - apply mwf_dropbits; [exact W1 | lia].
  - exact W3.
  - exact HM.
  - rep_lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the memory with the fields mode, length, extra, back, was apart                                *)

Definition le_state_r (gv: globals) (sp strmp headp winp: val) (s: istate) : mpred :=
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
  field_at Ews t_state (DOT _offset) (zv (i_offset s)) sp *
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
  field_at Ews t_state (DOT _codes) (map ent (i_codes s)) sp *
  field_at Ews t_state (DOT _sane) (zv (i_sane s)) sp.

Lemma le_pull5_35: forall a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35: mpred,
  a1 * a2 * a3 * a4 * a5 * a6 * a7 * a8 * a9 * a10 * a11 * a12 * a13 * a14 * a15 * a16 * a17 * a18 * a19 * a20 * a21 * a22 * a23 * a24 * a25 * a26 * a27 * a28 * a29 * a30 * a31 * a32 * a33 * a34 * a35 = a2 * a18 * a20 * a34 * a35 * (a1 * a3 * a4 * a5 * a6 * a7 * a8 * a9 * a10 * a11 * a12 * a13 * a14 * a15 * a16 * a17 * a19 * a21 * a22 * a23 * a24 * a25 * a26 * a27 * a28 * a29 * a30 * a31 * a32 * a33).
Proof. intros. apply pred_ext; cancel. Qed.

Lemma le_state_split: forall gv sp strmp headp winp s,
  state_rep gv sp strmp headp winp s =
  field_at Ews t_state (DOT _mode) (zv (i_mode s)) sp * field_at Ews t_state (DOT _length) (zv (i_length s)) sp *
  field_at Ews t_state (DOT _extra) (zv (i_extra s)) sp * field_at Ews t_state (DOT _back) (zv (i_back s)) sp *
  field_at Ews t_state (DOT _was) (zv (i_was s)) sp *
  le_state_r gv sp strmp headp winp s.
Proof. intros. unfold state_rep, le_state_r. apply le_pull5_35. Qed.

Definition le_mem_r (F: frame) (m: mst) : mpred :=
  le_state_r (f_gv F) (f_sp F) (f_strmp F) (f_headp F) (f_winp F) (m_s m) *
  win_rep (f_winp F) (m_s m) *
  head_part F m *
  strm_rep (f_gv F) (f_shs F) (f_strmp F)
    (in_ptr (f_ib F) (m_snx m)) (zv (Zlength (m_inp m) - m_snx m)) (m_tin m)
    (out_ptr (f_ob F) (m_sow m)) (zv (m_aout m - m_sow m)) (m_tout m)
    (msg_val (f_gv F) (m_msg m)) (f_sp F) (f_dt F) (m_adler m) (f_vres F) *
  in_rep (f_ib F) *
  out_rep (f_ob F) (m_ow m) *
  tables_rep (f_gsh F) (f_gv F) *
  crc_table_at (f_tsh F) (f_gv F).

Lemma le_mem_split: forall F m,
  mem_rep F m =
  field_at Ews t_state (DOT _mode) (zv (i_mode (m_s m))) (f_sp F) *
  field_at Ews t_state (DOT _length) (zv (i_length (m_s m))) (f_sp F) *
  field_at Ews t_state (DOT _extra) (zv (i_extra (m_s m))) (f_sp F) *
  field_at Ews t_state (DOT _back) (zv (i_back (m_s m))) (f_sp F) *
  field_at Ews t_state (DOT _was) (zv (i_was (m_s m))) (f_sp F) *
  le_mem_r F m.
Proof.
  intros. unfold mem_rep, le_mem_r. rewrite le_state_split.
  apply pred_ext; cancel.
Qed.

(* loop_state with the five fields apart, holding any values *)
Definition le_ls (F: frame) (m: mst) (vmd vln vex vbk vws: val) : environ -> mpred :=
  PROPx [in_ok (f_ib F) (m_inp m); out_ok (f_ob F) (m_aout m)]
  (LOCALx (ld_locals F m)
  (SEPx [field_at Ews t_state (DOT _mode) vmd (f_sp F); field_at Ews t_state (DOT _length) vln (f_sp F);
         field_at Ews t_state (DOT _extra) vex (f_sp F); field_at Ews t_state (DOT _back) vbk (f_sp F);
         field_at Ews t_state (DOT _was) vws (f_sp F); le_mem_r F m; locals_rep F])).

Lemma loop_state_le: forall F m,
  loop_state F m = le_ls F m (zv (i_mode (m_s m))) (zv (i_length (m_s m))) (zv (i_extra (m_s m)))
                     (zv (i_back (m_s m))) (zv (i_was (m_s m))).
Proof.
  intros. unfold loop_state, le_ls, ld_locals. f_equal. f_equal.
  unfold SEPx. extensionality rho. cbn [fold_right_sepcon]. rewrite le_mem_split.
  rewrite !sepcon_emp, !sepcon_assoc. reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the Clight pieces                                                                              *)

Definition le_sp : expr := Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr))) (Tstruct _inflate_state noattr).

Lemma le_fin_eq: le_fin =
  Ssequence
    (Ssequence (Sset _t'222 (Efield le_sp _length tuint))
       (Sassign (Efield le_sp _was tuint) (Etempvar _t'222 tuint)))
    (Sassign (Efield le_sp _mode tint) (Econst_int (Int.repr 16202) tint)).
Proof. reflexivity. Qed.

Lemma le_rest_eq: le_rest =
  Ssequence
    (Ssequence (Sset _t'228 (Efield le_sp _length tuint))
      (Ssequence (Sset _t'229 (Efield le_sp _extra tuint))
        (Sassign (Efield le_sp _length tuint)
          (Ebinop Oadd (Etempvar _t'228 tuint)
            (Ebinop Oand (Ecast (Etempvar _hold tulong) tuint)
              (Ebinop Osub (Ebinop Oshl (Econst_int (Int.repr 1) tuint) (Etempvar _t'229 tuint) tuint)
                (Econst_int (Int.repr 1) tint) tuint) tuint) tuint))))
    (Ssequence
      (Sloop
        (Ssequence
          (Ssequence (Sset _t'227 (Efield le_sp _extra tuint))
            (Sset _hold (Ebinop Oshr (Etempvar _hold tulong) (Etempvar _t'227 tuint) tulong)))
          (Ssequence (Sset _t'226 (Efield le_sp _extra tuint))
            (Sset _bits (Ebinop Osub (Etempvar _bits tuint) (Ecast (Etempvar _t'226 tuint) tuint) tuint))))
        Sbreak)
      (Ssequence (Sset _t'224 (Efield le_sp _back tint))
        (Ssequence (Sset _t'225 (Efield le_sp _extra tuint))
          (Sassign (Efield le_sp _back tint) (Ebinop Oadd (Etempvar _t'224 tint) (Etempvar _t'225 tuint) tuint))))).
Proof. reflexivity. Qed.

Lemma le_fin_ok {Espec: OracleKind} (F: frame) (X: mst):
  semax Delta_cases5 (loop_state F X) le_fin (normal_ret_assert (loop_state F (le_fin_m X))).
Proof.
  rewrite loop_state_le. rewrite le_fin_eq. unfold le_ls, ld_locals, le_sp. abbreviate_semax.
  forward. forward. forward.
  rewrite loop_state_le. change (le_mem_r F (le_fin_m X)) with (le_mem_r F X).
  unfold le_ls, ld_locals, le_fin_m. mnorm_goal. entailer!.
  apply derives_refl.
Qed.

(* the bit operations *)
Lemma le_len_val: forall L h ex, 0 <= h <= Int64.max_unsigned -> 0 <= ex <= 30 ->
  Int.add (Int.repr L) (Int.and (Int.repr (Int64.Z_mod_modulus h))
     (Int.sub (Int.shl (Int.repr 1) (Int.repr ex)) (Int.repr 1))) = Int.repr (L + h mod 2 ^ ex).
Proof.
  intros L h ex Hh Hx.
  rewrite Int64.Z_mod_modulus_eq, Z.mod_small by (unfold Int64.max_unsigned in Hh; lia).
  assert (S: Int.shl (Int.repr 1) (Int.repr ex) = Int.repr (2 ^ ex)).
  { unfold Int.shl. rewrite !Int.unsigned_repr by rep_lia. rewrite Z.shiftl_1_l. reflexivity. }
  rewrite S, sub_repr.
  assert (A: Int.and (Int.repr h) (Int.repr (2 ^ ex - 1)) = Int.repr (h mod 2 ^ ex)).
  { unfold Int.and. rewrite (Int.unsigned_repr_eq h).
    assert (P: 0 < 2 ^ ex <= 2 ^ 30) by (split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_le_mono_r; lia]).
    change (2 ^ 30) with 1073741824 in P.
    rewrite (Int.unsigned_repr (2 ^ ex - 1)) by rep_lia.
    f_equal. replace (2 ^ ex - 1) with (Z.ones ex) by (rewrite Z.ones_equiv; lia). rewrite Z.land_ones by lia.
    change Int.modulus with (2 ^ 32). symmetry. apply Znumtheory.Zmod_div_mod; [lia | lia | ].
    exists (2 ^ (32 - ex)). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  rewrite A, add_repr. reflexivity.
Qed.

Lemma le_long_shru_eq: forall h n, 0 <= h <= Int64.max_unsigned -> 0 <= n < 64 ->
  Int64.shru (Int64.repr h) (Int64.repr n) = Int64.repr (Z.shiftr h n).
Proof.
  intros h n Hh Hn. unfold Int64.shru.
  rewrite (Int64.unsigned_repr h) by lia. rewrite (Int64.unsigned_repr n) by rep_lia. reflexivity.
Qed.

Lemma le_u32_repr: forall x, Int.repr (u32 x) = Int.repr x.
Proof.
  intros. unfold u32. apply Int.eqm_samerepr. unfold Int.eqm. apply Zbits.eqmod_sym, Zbits.eqmod_mod.
  reflexivity.
Qed.

(* do { c } while (0) followed by rest *)
Lemma le_semax_dowhile0 {Espec: OracleKind} (Delta: tycontext) (P Q: environ -> mpred) (c rest: statement)
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

Lemma le_rest_ok {Espec: OracleKind} (F: frame) (m1: mst):
  mwf m1 -> 0 < i_extra (m_s m1) <= 5 -> i_extra (m_s m1) <= m_bits m1 -> i_length (m_s m1) <= 258 ->
  semax Delta_cases5 (loop_state F m1) le_rest
    (normal_ret_assert (loop_state F (le_m2 (i_extra (m_s m1)) m1))).
Proof.
  intros W HX EB EL.
  pose proof (mw_bits _ W) as WB. pose proof (mw_hold _ W) as WH. unfold lrange in WH.
  pose proof (sw_back _ (mw_s _ W)) as WK. pose proof (sw_length _ (mw_s _ W)) as WL. unfold urange in WL.
  rewrite loop_state_le, le_rest_eq. unfold le_ls, ld_locals, le_sp. abbreviate_semax.
  forward. forward. forward.
  { entailer!. change (Int.unsigned Int.iwordsize) with 32. lia. }
  rewrite le_len_val by lia.
  match goal with |- semax _ (PROPx ?P (LOCALx _ (SEPx ?S))) _ _ =>
    apply le_semax_dowhile0 with (Q := PROPx P (LOCALx
      (temp _t'229 (zv (i_extra (m_s m1))) :: temp _t'228 (zv (i_length (m_s m1))) ::
       ld_locals F (dropbits (i_extra (m_s m1)) m1)) (SEPx S))) end.
  { unfold ld_locals. forward. forward.
    { entailer!. change (Int.unsigned Int64.iwordsize') with 64. lia. }
    forward. forward.
    unfold dropbits, m_have, m_left. mnorm_goal.
    entailer!. split; [rewrite le_long_shru_eq by rep_lia; reflexivity | rewrite le_u32_repr; reflexivity]. }
  unfold ld_locals. abbreviate_semax. forward. forward. forward.
  rewrite add_repr. rewrite loop_state_le.
  unfold le_ls, ld_locals, le_m2, bitsn. mnorm_goal. entailer!. rewrite le_u32_repr. apply derives_refl.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the head: if (state->extra) { NEEDBITS(extra); if (leave) break; length, DROPBITS, back }       *)

Definition le_pure (F: frame) (m: mst) : Prop :=
  stepf2 (f_flush F) lenfix_list distfix_list m = stepf2 (f_flush F) lenfix_list distfix_list (le_fin_m (le_X m)) /\
  mwf3 (le_fin_m (le_X m)) /\ m_leave (le_X m) = 0.

Lemma le_pure_0: forall F m, mwf3 m -> m_mode m = LENEXT -> m_leave m = 0 -> i_extra (m_s m) = 0 -> le_pure F m.
Proof.
  intros F m W3 HM HL E.
  assert (X: le_X m = m) by (unfold le_X; rewrite E; reflexivity).
  split; [ | split].
  - rewrite (stepf2_LENEXT _ _ _ m HM). rewrite (le_c_eq m (or_introl E)).
    symmetry. apply stepf2_DIST. reflexivity.
  - rewrite X. apply le_mwf3_0; assumption.
  - rewrite X. exact HL.
Qed.

Lemma le_pure_1: forall F m, mwf3 m -> m_mode m = LENEXT -> m_leave m = 0 -> i_extra (m_s m) <> 0 ->
  m_leave (needbits (i_extra (m_s m)) m) = 0 -> le_pure F m.
Proof.
  intros F m W3 HM HL E L0.
  assert (X: le_X m = le_m2 (i_extra (m_s m)) (needbits (i_extra (m_s m)) m))
    by (unfold le_X; rewrite (proj2 (Z.eqb_neq _ _) E); reflexivity).
  split; [ | split].
  - rewrite (stepf2_LENEXT _ _ _ m HM). rewrite (le_c_eq m (or_intror L0)).
    symmetry. apply stepf2_DIST. reflexivity.
  - rewrite X. apply le_mwf3_1; assumption.
  - rewrite X. exact L0.
Qed.

Lemma le_head_eq: le_head =
  Ssequence (Sset _t'223 (Efield le_sp _extra tuint))
    (Sifthenelse (Etempvar _t'223 tuint) (Ssequence (Ssequence le_nb ld_ifleave) le_rest) Sskip).
Proof. reflexivity. Qed.

Lemma le_head_ok {Espec: OracleKind} (F: frame) (m: mst) (R: ret_assert):
  ld_nb_stmt -> mwf3 m -> m_mode m = LENEXT -> m_leave m = 0 ->
  RA_break R = RA_normal (case_post2 F m) ->
  semax Delta_cases5 (loop_state F m) le_head (overridePost (!! le_pure F m && loop_state F (le_X m)) R).
Proof.
  intros NB W3 HM HL HR.
  pose proof (mwf3_mwf _ W3) as W.
  pose proof (md_lenext _ (mw_md _ W) HM) as XT.
  pose proof (sw_extra _ (mw_s _ W)) as XS.
  pose proof (s3_lenext _ (proj2 W3) HM) as LN2.
  rewrite le_head_eq. rewrite loop_state_le. unfold le_ls, ld_locals, le_sp. abbreviate_semax.
  forward.
  forward_if.
  - rename H1' into E0.
    unfold abbreviate in MORE_COMMANDS. subst MORE_COMMANDS.
    unfold abbreviate in POSTCONDITION. subst POSTCONDITION.
    apply semax_pre with (P' := loop_state F m).
    { rewrite loop_state_le. unfold le_ls, ld_locals. entailer!. }
    apply (semax_needbits_seq5 F m m (i_extra (m_s m))).
    + apply NB; auto.
    + exact W.
    + lia.
    + rewrite <- HR. destruct R; reflexivity.
    + intro E. rewrite (stepf2_LENEXT _ _ _ m HM). apply le_leave_eq; assumption.
    + apply semax_extract_prop. intro L0.
      pose proof (le_pure_1 F m W3 HM HL E0 L0) as P.
      assert (W1: mwf (needbits (i_extra (m_s m)) m)) by (apply mwf_needbits; [exact W | lia]).
      destruct (needbits_ok (i_extra (m_s m)) m W HL ltac:(lia) ltac:(lia)) as [NB1 _].
      pose proof (le_rest_ok F (needbits (i_extra (m_s m)) m) W1) as RO. rewrite !needbits_s in RO.
      specialize (RO ltac:(lia) NB1 LN2).
      eapply semax_post; [ | | | | exact RO ].
      * intros. apply andp_left2. destruct R as [r1 r2 r3 r4]. cbn [RA_normal overridePost normal_ret_assert].
        apply andp_right; [apply prop_right; exact P | ].
        unfold le_X. rewrite (proj2 (Z.eqb_neq _ _) E0). apply derives_refl.
      * intros. apply andp_left2. destruct R as [r1 r2 r3 r4]. cbn [RA_break overridePost normal_ret_assert]. apply FF_left.
      * intros. apply andp_left2. destruct R as [r1 r2 r3 r4]. cbn [RA_continue overridePost normal_ret_assert]. apply FF_left.
      * intros. apply andp_left2. destruct R as [r1 r2 r3 r4]. cbn [RA_return overridePost normal_ret_assert]. apply FF_left.
  - forward.
    assert (E0: i_extra (m_s m) = 0).
    { apply repr_inj_unsigned in H1; rep_lia. }
    pose proof (le_pure_0 F m W3 HM HL E0) as P.
    assert (X: le_X m = m) by (unfold le_X; rewrite E0; reflexivity).
    destruct R as [r1 r2 r3 r4]. cbn [RA_normal]. rewrite X.
    apply andp_right; [apply prop_right; exact P | ].
    rewrite loop_state_le. unfold le_ls, ld_locals. entailer!.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the case                                                                                       *)

Lemma ld_lenext_ok : ld_nb_stmt -> ld_lenext_stmt.
Proof.
  intros NB Espec F HF HD m HM HL W3.
  apply (case_fallthrough5 F m DIST 21); [lia | exact HD | ].
  change (case_body 21) with le_body. rewrite le_body_eq.
  eapply semax_seq; [ apply le_head_ok; auto | ].
  apply semax_extract_prop. intros (E & W' & L').
  eapply semax_post; [ | | | | apply le_fin_ok ].
  - intros. apply andp_left2. cbn [RA_normal overridePost normal_ret_assert].
    unfold fall_post5. Exists (le_fin_m (le_X m)).
    apply andp_right; [ | apply derives_refl].
    apply prop_right. split; [exact E | ]. split; [reflexivity | ]. split; [exact L' | exact W'].
  - intros. apply andp_left2. cbn [RA_break overridePost normal_ret_assert]. apply FF_left.
  - intros. apply andp_left2. cbn [RA_continue overridePost normal_ret_assert]. apply FF_left.
  - intros. apply andp_left2. cbn [RA_return overridePost normal_ret_assert]. apply FF_left.
Qed.
