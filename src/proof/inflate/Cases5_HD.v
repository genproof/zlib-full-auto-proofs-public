(* inflate(), the switch cases HCRC, DICTID, DICT (8-10), in Delta_cases5 with the invariant mwf3 (CaseKit5.v) *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate.CaseHyps5.
Require Import Zlib.proof.inflate.NeedKit5 Zlib.proof.inflate.NeedBits Zlib.proof.inflate.NeedBits2_5.
Require Import Zlib.proof.inflate.Steps2 Zlib.proof.inflate.MwfLemmas Zlib.proof.inflate.ModeKit5.
Require Import Zlib.proof.inflate.CaseRet5.
Require Import Zlib.proof.crc32.Spec Zlib.proof.adler32.Spec.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* ---------------------------------------------------------------------------------------------- *)
(* the fields these cases read or write (mode, wrap, havedict, flags, check, head, hold, bits) apart
   from the 27 others (one opaque SEP item), as in Cases3_HEAD *)

Definition state_rest (gv: globals) (sp strmp headp winp: val) (s: istate) : mpred :=
  field_at Ews t_state (DOT _strm) strmp sp *
  field_at Ews t_state (DOT _last) (zv (i_last s)) sp *
  field_at Ews t_state (DOT _dmax) (zv (i_dmax s)) sp *
  field_at Ews t_state (DOT _total) (lv (i_total s)) sp *
  field_at Ews t_state (DOT _wbits) (zv (i_wbits s)) sp *
  field_at Ews t_state (DOT _wsize) (zv (i_wsize s)) sp *
  field_at Ews t_state (DOT _whave) (zv (i_whave s)) sp *
  field_at Ews t_state (DOT _wnext) (zv (i_wnext s)) sp *
  field_at Ews t_state (DOT _window) (if i_win s then winp else nullval) sp *
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
  field_at Ews t_state (DOT _codes) (map ent (i_codes s)) sp *
  field_at Ews t_state (DOT _sane) (zv (i_sane s)) sp *
  field_at Ews t_state (DOT _back) (zv (i_back s)) sp *
  field_at Ews t_state (DOT _was) (zv (i_was s)) sp.

Lemma sepcon_hd_35: forall a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35: mpred,
  a1 * a2 * a3 * a4 * a5 * a6 * a7 * a8 * a9 * a10 * a11 * a12 * a13 * a14 * a15 * a16 * a17 * a18 * a19 * a20 * a21 * a22 * a23 * a24 * a25 * a26 * a27 * a28 * a29 * a30 * a31 * a32 * a33 * a34 * a35 =
  a2 * a4 * a5 * a6 * a8 * a10 * a16 * a17 * (a1 * a3 * a7 * a9 * a11 * a12 * a13 * a14 * a15 * a18 * a19 * a20 * a21 * a22 * a23 * a24 * a25 * a26 * a27 * a28 * a29 * a30 * a31 * a32 * a33 * a34 * a35).
Proof. intros. apply pred_ext; cancel. Qed.

Lemma state_rep_hd: forall gv sp strmp headp winp s,
  state_rep gv sp strmp headp winp s =
  field_at Ews t_state (DOT _mode) (zv (i_mode s)) sp *
  field_at Ews t_state (DOT _wrap) (zv (i_wrap s)) sp *
  field_at Ews t_state (DOT _havedict) (zv (i_havedict s)) sp *
  field_at Ews t_state (DOT _flags) (zv (i_flags s)) sp *
  field_at Ews t_state (DOT _check) (lv (i_check s)) sp *
  field_at Ews t_state (DOT _head) (if i_head s then headp else nullval) sp *
  field_at Ews t_state (DOT _hold) (lv (i_hold s)) sp *
  field_at Ews t_state (DOT _bits) (zv (i_bits s)) sp *
  state_rest gv sp strmp headp winp s.
Proof. intros. unfold state_rep, state_rest. apply sepcon_hd_35. Qed.

(* loop_state with those fields apart *)
Definition loop_state_hd (F: frame) (m: mst) : environ -> mpred :=
  PROP (in_ok (f_ib F) (m_inp m); out_ok (f_ob F) (m_aout m))
  LOCAL (temp _strm (f_strmp F); temp _flush (zv (f_flush F)); temp _state (f_sp F);
         temp _next (in_ptr (f_ib F) (m_nx m)); temp _put (out_ptr (f_ob F) (Zlength (m_ow m)));
         temp _have (zv (m_have m)); temp _left (zv (m_left m)); temp _hold (lv (m_hold m));
         temp _bits (zv (m_bits m)); temp _in (zv (m_in m)); temp _out (zv (m_out m));
         temp _ret (zv (m_ret m)); temp _leave (zv (m_leave m));
         lvar _here t_code (f_vhere F); lvar _last t_code (f_vlast F);
         lvar _hbuf (tarray tuchar 4) (f_vhbuf F); gvars (f_gv F))
  SEP (field_at Ews t_state (DOT _mode) (zv (i_mode (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _wrap) (zv (i_wrap (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _havedict) (zv (i_havedict (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _flags) (zv (i_flags (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _check) (lv (i_check (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _head) (if i_head (m_s m) then f_headp F else nullval) (f_sp F);
       field_at Ews t_state (DOT _hold) (lv (i_hold (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _bits) (zv (i_bits (m_s m))) (f_sp F);
       state_rest (f_gv F) (f_sp F) (f_strmp F) (f_headp F) (f_winp F) (m_s m);
       win_rep (f_winp F) (m_s m);
       head_part F m;
       strm_rep (f_gv F) (f_shs F) (f_strmp F)
         (in_ptr (f_ib F) (m_snx m)) (zv (Zlength (m_inp m) - m_snx m)) (m_tin m)
         (out_ptr (f_ob F) (m_sow m)) (zv (m_aout m - m_sow m)) (m_tout m)
         (msg_val (f_gv F) (m_msg m)) (f_sp F) (f_dt F) (m_adler m) (f_vres F);
       in_rep (f_ib F);
       out_rep (f_ob F) (m_ow m);
       tables_rep (f_gsh F) (f_gv F);
       crc_table_at (f_tsh F) (f_gv F);
       locals_rep F).

Lemma loop_state_hd_eq: forall F m, loop_state F m = loop_state_hd F m.
Proof.
  intros. unfold loop_state, loop_state_hd, mem_rep. rewrite state_rep_hd.
  f_equal. unfold SEPx. simpl. rewrite !sepcon_assoc. reflexivity.
Qed.

(* the 27 other fields and the window do not see mode, check, hold, bits *)
Lemma state_rest_mode: forall gv sp strmp headp winp s v,
  state_rest gv sp strmp headp winp (set_i_mode s v) = state_rest gv sp strmp headp winp s.
Proof. reflexivity. Qed.
Lemma state_rest_check: forall gv sp strmp headp winp s v,
  state_rest gv sp strmp headp winp (set_i_check s v) = state_rest gv sp strmp headp winp s.
Proof. reflexivity. Qed.
Lemma state_rest_hold: forall gv sp strmp headp winp s v,
  state_rest gv sp strmp headp winp (set_i_hold s v) = state_rest gv sp strmp headp winp s.
Proof. reflexivity. Qed.
Lemma state_rest_bits: forall gv sp strmp headp winp s v,
  state_rest gv sp strmp headp winp (set_i_bits s v) = state_rest gv sp strmp headp winp s.
Proof. reflexivity. Qed.
Lemma win_rep_mode: forall winp s v, win_rep winp (set_i_mode s v) = win_rep winp s.
Proof. reflexivity. Qed.
Lemma win_rep_check: forall winp s v, win_rep winp (set_i_check s v) = win_rep winp s.
Proof. reflexivity. Qed.
Lemma win_rep_hold: forall winp s v, win_rep winp (set_i_hold s v) = win_rep winp s.
Proof. reflexivity. Qed.
Lemma win_rep_bits: forall winp s v, win_rep winp (set_i_bits s v) = win_rep winp s.
Proof. reflexivity. Qed.

Ltac rest_simpl :=
  repeat first [rewrite state_rest_mode | rewrite state_rest_check | rewrite state_rest_hold
               | rewrite state_rest_bits | rewrite win_rep_mode | rewrite win_rep_check
               | rewrite win_rep_hold | rewrite win_rep_bits].

Lemma int_hcrc: forall f, Int.min_signed <= f <= Int.max_signed ->
  Int.and (Int.shr (Int.repr f) (Int.repr 9)) (Int.repr 1) = Int.repr (Z.land (Z.shiftr f 9) 1).
Proof.
  intros f Hf. unfold Int.shr, Int.and.
  rewrite Int.signed_repr by lia. rewrite (Int.unsigned_repr 9) by rep_lia.
  rewrite (Int.unsigned_repr 1) by rep_lia.
  change 1 with (Z.ones 1). rewrite !Z.land_ones by lia.
  rewrite Int.unsigned_repr_eq. f_equal.
  rewrite <- Znumtheory.Zmod_div_mod; [reflexivity | lia | reflexivity | ].
  exists (2 ^ 31). reflexivity.
Qed.

(* the z_stream with its zalloc/zfree values abstracted (entailer! refuses gv of _zcalloc / _zcfree) *)
Lemma strm_rep_unfold: forall gv shs strmp ni ai tin no ao tout msg sp dt adler vres,
  strm_rep gv shs strmp ni ai tin no ao tout msg sp dt adler vres =
  data_at shs t_strm (ni, (ai, (lv tin, (no, (ao, (lv tout, (msg, (sp, (gv _zcalloc, (gv _zcfree,
     (nullval, (zv dt, (lv adler, vres))))))))))))) strmp.
Proof. reflexivity. Qed.

Lemma land_lt: forall x b k, 0 <= k -> 0 <= b < 2 ^ k -> 0 <= Z.land x b < 2 ^ k.
Proof.
  intros x b k Hk Hb.
  replace (Z.land x b) with (Z.land (Z.land x b) (Z.ones k)).
  - rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
  - rewrite <- Z.land_assoc. rewrite (Z.land_ones b k Hk). rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma int_and_eq: forall a b, 0 <= b < 2 ^ 31 -> Int.and (Int.repr a) (Int.repr b) = Int.repr (Z.land a b).
Proof.
  intros a b Hb. unfold Int.and. rewrite (Int.unsigned_repr b) by rep_lia.
  rewrite Int.unsigned_repr_eq. change Int.modulus with (2 ^ 32).
  rewrite <- Z.land_ones by lia. rewrite <- Z.land_assoc.
  rewrite (Z.land_comm (Z.ones 32) b), Z.land_ones by lia. rewrite (Z.mod_small b) by lia. reflexivity.
Qed.

Lemma int_and_nz: forall a b, 0 <= b < 2 ^ 31 ->
  Int.and (Int.repr a) (Int.repr b) <> Int.zero -> Z.land a b <> 0.
Proof.
  intros a b Hb H E. apply H. rewrite int_and_eq by lia. rewrite E. reflexivity.
Qed.

Lemma int_and_z: forall a b, 0 <= b < 2 ^ 31 ->
  Int.and (Int.repr a) (Int.repr b) = Int.zero -> Z.land a b = 0.
Proof.
  intros a b Hb H. rewrite int_and_eq in H by lia.
  pose proof (land_lt a b 31 ltac:(lia) Hb).
  apply (f_equal Int.unsigned) in H. rewrite Int.unsigned_repr in H by rep_lia. exact H.
Qed.

(* a do { c } while (0) (INITBITS, RESTORE): c once *)
Lemma semax_do0 {Espec: OracleKind} (Delta: tycontext) (P Q: environ -> mpred) (c k: statement) (R: ret_assert):
  semax Delta P c (normal_ret_assert Q) -> semax Delta Q k R ->
  semax Delta P (Ssequence (Sloop c Sbreak) k) R.
Proof.
  intros H1 H2. eapply semax_seq'; [ | exact H2].
  apply semax_loop with (Q' := Q).
  - eapply semax_post; [ | | | | exact H1];
      [ apply andp_left2; apply derives_refl | apply andp_left2; apply FF_left
      | apply andp_left2; apply FF_left | intros vl; apply andp_left2; apply FF_left ].
  - eapply semax_pre; [ | apply semax_break]. apply andp_left2. apply derives_refl.
Qed.

Lemma semax_do0_last {Espec: OracleKind} (Delta: tycontext) (P: environ -> mpred) (c: statement) (R: ret_assert):
  semax Delta P c (normal_ret_assert (RA_normal R)) ->
  semax Delta P (Sloop c Sbreak) R.
Proof.
  intros H1. destruct R as [Rn Rb Rc Rr]. apply semax_loop with (Q' := Rn).
  - eapply semax_post; [ | | | | exact H1];
      [ apply andp_left2; apply derives_refl | apply andp_left2; apply FF_left
      | apply andp_left2; apply FF_left | intros vl; apply andp_left2; apply FF_left ].
  - eapply semax_pre; [ | apply semax_break]. apply andp_left2. apply derives_refl.
Qed.

Lemma int64_and_eq: forall c b, 0 <= c <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
  Int64.and (Int64.repr c) (Int64.repr b) = Int64.repr (Z.land c b).
Proof. intros. unfold Int64.and. rewrite !Int64.unsigned_repr by lia. reflexivity. Qed.

Lemma hcrc_ne: forall h c, lrange h -> lrange c ->
  Int64.repr h <> Int64.and (Int64.repr c) (Int64.repr 65535) -> (h =? Z.land c 65535) = false.
Proof.
  intros h c Hh Hc N. apply Z.eqb_neq. intro E. apply N.
  rewrite int64_and_eq by (unfold lrange in Hc; rep_lia). rewrite E. reflexivity.
Qed.

Lemma hcrc_eqt: forall h c, lrange h -> lrange c ->
  Int64.eq (Int64.repr h) (Int64.and (Int64.repr c) (Int64.repr 65535)) = true -> (h =? Z.land c 65535) = true.
Proof.
  intros h c Hh Hc E. apply Int64.same_if_eq in E.
  rewrite int64_and_eq in E by (unfold lrange in Hc; rep_lia).
  pose proof (land_lt c 65535 16 ltac:(lia) ltac:(lia)).
  apply (f_equal Int64.unsigned) in E. unfold lrange in *.
  rewrite !Int64.unsigned_repr in E by rep_lia. apply Z.eqb_eq. exact E.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* case HCRC                                                                                       *)

Definition hcrc_fin (m: mst) : iout :=
  let m := if i_head (m_s m) then
             upd_h m (fun h => set_h_done (set_h_hcrc h (Z.land (Z.shiftr (i_flags (m_s m)) 9) 1)) 1)
           else m in
  IBrk (set_mode (set_m_adler (upd_s m (fun s => set_i_check s 0)) 0) Zlib.proof.inflate.Model.TYPE).

Lemma c_HCRC_eq: forall m, c_HCRC m =
  if negb (Z.land (i_flags (m_s m)) 512 =? 0) then
    let m := needbits 16 m in
    if m_leave m =? 1 then IBrk m else
    if (negb (Z.land (i_wrap (m_s m)) 4 =? 0) && negb (m_hold m =? Z.land (i_check (m_s m)) 65535))%bool
    then IBrk (set_bad m M_hcrc)
    else hcrc_fin (initbits m)
  else hcrc_fin m.
Proof. intros. reflexivity. Qed.

Ltac hcrc_norm_end m1 E1 W1 HL1 G :=
  Exists (initbits m1); apply andp_right;
  [ apply prop_right; split; [rewrite E1, G; reflexivity | split; [apply mwf_initbits, W1 | exact HL1]] | ];
  rewrite loop_state_hd_eq; unfold loop_state_hd, win_rep, head_part; unfold m_have, m_left; mnorm_goal;
  change (Int.signed (Int.repr 0)) with 0; entailer!.

Lemma case_HCRC5 {Espec: OracleKind} (F: frame) : frame_ok5 F -> case_ok5 F HCRC 8.
Proof.
  intros [HF HFl] m HM HL [W W3].
  rewrite seq_split by lia. eapply semax_seq; [ | apply semax_ff].
  pose proof (stepf2_HCRC (f_flush F) lenfix_list distfix_list m HM) as E0.
  rewrite c_HCRC_eq in E0.
  case_body_stmt.
  apply semax_seq with (Q := EX m2: mst,
    !! (stepf2 (f_flush F) lenfix_list distfix_list m = hcrc_fin m2 /\ mwf m2 /\ m_leave m2 = 0) &&
    loop_state F m2).
  - pose proof (sw_flags _ (mw_s _ W)) as Hfl.
    rewrite loop_state_hd_eq. unfold loop_state_hd. abbreviate_semax.
    forward.
    forward_if.
    + match goal with X: Int.and _ _ <> Int.zero |- _ => apply int_and_nz in X; [rename X into Hf | lia] end.
      apply semax_pre with (P' := loop_state F m); [rewrite loop_state_hd_eq; unfold loop_state_hd; entailer! | ].
      eapply (semax_needbits_seq5 F m m 16).
      { apply semax_needbits_HCRC5; [exact W | exact HL | lia]. }
      { exact W. } { lia. } { reflexivity. }
      { intro EL. rewrite E0. rewrite (proj2 (Z.eqb_neq _ _) Hf). cbv zeta. rewrite EL. reflexivity. }
      apply semax_extract_prop; intros HL1.
      pose proof (mwf_needbits 16 m W ltac:(lia)) as W1.
      assert (E1: stepf2 (f_flush F) lenfix_list distfix_list m =
        if (negb (Z.land (i_wrap (m_s (needbits 16 m))) 4 =? 0) &&
            negb (m_hold (needbits 16 m) =? Z.land (i_check (m_s (needbits 16 m))) 65535))%bool
        then IBrk (set_bad (needbits 16 m) M_hcrc) else hcrc_fin (initbits (needbits 16 m))).
      { rewrite E0. rewrite (proj2 (Z.eqb_neq _ _) Hf). cbv zeta. rewrite HL1. reflexivity. }
      clear E0. set (m1 := needbits 16 m) in *. clearbody m1.
      pose proof (sw_wrap_range _ (mw_s _ W1)) as Hw. pose proof (sw_check _ (mw_s _ W1)) as Hc.
      pose proof (mw_hold _ W1) as Hho.
      rewrite loop_state_hd_eq. unfold loop_state_hd. abbreviate_semax.
      forward.
      unfold abbreviate in MORE_COMMANDS. subst MORE_COMMANDS. apply semax_if_seq. forward_if.
      * forward. forward.
        unfold abbreviate in MORE_COMMANDS. subst MORE_COMMANDS. apply semax_if_seq. forward_if.
        { assert (G: (negb (Z.land (i_wrap (m_s m1)) 4 =? 0) &&
                      negb (m_hold m1 =? Z.land (i_check (m_s m1)) 65535))%bool = true).
          { match goal with X: Int.and _ _ <> Int.zero |- _ => apply int_and_nz in X; [ | lia] end.
            match goal with X: Int64.repr _ <> _ |- _ => apply hcrc_ne in X; [ | exact Hho | exact Hc] end.
            match goal with X: (_ =? _) = false |- _ => rewrite X end.
            rewrite (proj2 (Z.eqb_neq _ _)) by assumption. reflexivity. }
          pose proof (proj1 HF) as Hshs. unfold strm_rep. remember (f_gv F _zcalloc) as za eqn:Eza. remember (f_gv F _zcfree) as zf eqn:Ezf.
          forward. forward. forward.
          unfold switch_ret_assert, case_post2. cbn [RA_break RA_normal].
          Exists (set_bad m1 M_hcrc). apply andp_right; [apply prop_right; rewrite E1, G; reflexivity | ].
          rewrite loop_state_hd_eq. unfold loop_state_hd, win_rep, head_part. unfold m_have, m_left. mnorm_goal.
          cbn [msg_val msg_ident]. rewrite strm_rep_unfold. rewrite <- Eza, <- Ezf. rest_simpl. entailer!. }
        { assert (G: (negb (Z.land (i_wrap (m_s m1)) 4 =? 0) &&
                      negb (m_hold m1 =? Z.land (i_check (m_s m1)) 65535))%bool = false).
          { match goal with X: Int64.eq _ _ = true |- _ => apply hcrc_eqt in X; [ | exact Hho | exact Hc] end.
            match goal with X: (_ =? _) = true |- _ => rewrite X end. apply andb_false_r. }
          apply semax_do0_last. forward. forward. hcrc_norm_end m1 E1 W1 HL1 G. }
      * forward.
        unfold abbreviate in MORE_COMMANDS. subst MORE_COMMANDS. apply semax_if_seq. forward_if.
        { exfalso; congruence. }
        { assert (G: (negb (Z.land (i_wrap (m_s m1)) 4 =? 0) &&
                      negb (m_hold m1 =? Z.land (i_check (m_s m1)) 65535))%bool = false).
          { match goal with X: Int.and _ _ = Int.zero |- _ => apply int_and_z in X; [rewrite X | lia] end.
            reflexivity. }
          apply semax_do0_last. forward. forward. hcrc_norm_end m1 E1 W1 HL1 G. }
    + match goal with X: Int.and _ _ = Int.zero |- _ => apply int_and_z in X; [rename X into Hf | lia] end.
      forward.
      Exists m. apply andp_right.
      * apply prop_right. split; [ | split; [exact W | exact HL]].
        rewrite E0. rewrite (proj2 (Z.eqb_eq _ _) Hf). reflexivity.
      * rewrite loop_state_hd_eq. unfold loop_state_hd. entailer!.
  - Intros m2. apply semax_extract_prop; intros (E & W2 & HL2).
    destruct HF as (Hshs & Hhsh & Hgsh & Htsh).
    destruct F as [gv shs strmp sp headp winp hsh xb nb cb ib ob gsh tsh dt vres vhere vlast vhbuf flush].
    rewrite loop_state_hd_eq. unfold loop_state_hd. frame_simpl. unfold head_part. cbn [f_hsh f_headp f_xb f_nb f_cb] in *.
    abbreviate_semax.
    freeze FR := (field_at _ _ (DOT _wrap) _ _) (field_at _ _ (DOT _havedict) _ _) (field_at _ _ (DOT _hold) _ _)
      (field_at _ _ (DOT _bits) _ _) (state_rest _ _ _ _ _ _) (win_rep _ _) (in_rep _) (out_rep _ _)
      (tables_rep _ _) (locals_rep _).
    destruct (i_head (m_s m2)) eqn:Hh.
    + unfold head_rep. Intros. freeze FB := (hbuf_rep _ _ _) (hbuf_rep _ _ _) (hbuf_rep _ _ _). forward.
      unfold abbreviate in MORE_COMMANDS. subst MORE_COMMANDS. apply semax_if_seq. forward_if.
      * forward. forward. forward. forward. forward.
        match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
          apply semax_pre with (PROPx P (LOCALx Q (SEPx (emp :: emp :: R)))); [entailer! |] end.
        forward_call (0, nullval, 0, true, Ews, nullval, 0, 0, @nil val, @nil Z, false, Ews, gv, tsh).
        forward. unfold strm_rep. remember (gv _zcalloc) as za eqn:Eza. remember (gv _zcfree) as zf eqn:Ezf.
        forward. forward. forward.
        unfold switch_ret_assert, case_post2. cbn [RA_break RA_normal].
        Exists (set_mode (set_m_adler (upd_s (upd_h m2 (fun h => set_h_done (set_h_hcrc h
          (Z.land (Z.shiftr (i_flags (m_s m2)) 9) 1)) 1)) (fun s => set_i_check s 0)) 0) Zlib.proof.inflate.Model.TYPE).
        apply andp_right; [apply prop_right; cbn [f_flush]; rewrite E; unfold hcrc_fin; rewrite Hh; reflexivity | ].
        rewrite loop_state_hd_eq. unfold loop_state_hd. frame_simpl_goal. unfold m_have, m_left.
        mnorm_goal. cbn [f_gv f_hsh f_headp f_xb f_nb f_cb]. rewrite Hh. unfold head_rep. mnorm_goal.
        rewrite strm_rep_unfold. rewrite <- Eza, <- Ezf.
        rewrite int_hcrc by (apply (sw_flags _ (mw_s _ W2))).
        rest_simpl. thaw FB. thaw FR. unfold win_rep. entailer!.
      * match goal with X: headp = nullval |- _ => subst headp end.
        assert_PROP False by (sep_apply (data_at_local_facts hsh t_head); entailer!;
          match goal with X: field_compatible _ _ nullval |- _ => destruct X; contradiction end). contradiction.
    + forward.
      unfold abbreviate in MORE_COMMANDS. subst MORE_COMMANDS. apply semax_if_seq. forward_if.
      * exfalso; congruence.
      * match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
          apply semax_pre with (PROPx P (LOCALx Q (SEPx (emp :: emp :: R)))); [entailer! |] end.
        forward_call (0, nullval, 0, true, Ews, nullval, 0, 0, @nil val, @nil Z, false, Ews, gv, tsh).
        forward. unfold strm_rep. remember (gv _zcalloc) as za eqn:Eza. remember (gv _zcfree) as zf eqn:Ezf.
        forward. forward. forward.
        unfold switch_ret_assert, case_post2. cbn [RA_break RA_normal].
        Exists (set_mode (set_m_adler (upd_s m2 (fun s => set_i_check s 0)) 0) Zlib.proof.inflate.Model.TYPE).
        apply andp_right; [apply prop_right; cbn [f_flush]; rewrite E; unfold hcrc_fin; rewrite Hh; reflexivity | ].
        rewrite loop_state_hd_eq. unfold loop_state_hd. frame_simpl_goal. unfold m_have, m_left.
        mnorm_goal. cbn [f_gv f_hsh f_headp f_xb f_nb f_cb]. rewrite Hh.
        rewrite strm_rep_unfold. rewrite <- Eza, <- Ezf.
        rest_simpl. thaw FR. unfold win_rep. entailer!.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the machines DICTID and DICT fall through to                                                    *)

Lemma mwf_check_adler: forall m c, mwf m -> lrange c ->
  mwf (set_m_adler (upd_s m (fun s => set_i_check s c)) c).
Proof.
  intros m c W Hc. destruct W as [MD SW HW I A NX OW HO B IN OUT RET LV AD TI TO SNX SOW OE].
  destruct MD. destruct SW.
  constructor; simpl; auto; constructor; simpl; auto.
Qed.

Lemma swf3_plain: forall s md, md <> HEAD -> ~ decode_mode md -> md <> LENEXT -> md <> DISTEXT ->
  swf3 (set_i_mode s md).
Proof. intros s md A B C D. constructor; simpl; intros; contradiction. Qed.

Lemma mwf3_DICT: forall m c, mwf m -> lrange c -> m_mode m = DICTID ->
  mwf3 (set_mode (initbits (set_m_adler (upd_s m (fun s => set_i_check s c)) c)) DICT).
Proof.
  intros m c W Hc HM. split.
  - apply mwf_set_mode_plain.
    + apply mwf_initbits, mwf_check_adler; auto.
    + unfold HEAD, DICT, SYNC; lia.
    + unfold DICT, LENLENS; lia.
    + unfold DICT, CODELENS; lia.
    + unfold decode_mode, DICT, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT; lia.
    + left. apply (mwf_out_eq m W); rewrite HM; unfold DICTID, LENGTH, DONE, BAD; lia.
  - apply swf3_plain; unfold decode_mode, DICT, HEAD, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT; lia.
Qed.

Lemma mwf3_TYPE: forall m, mwf m -> m_mode m = DICT ->
  mwf3 (set_mode (set_m_adler (upd_s m (fun s => set_i_check s 1)) 1) Zlib.proof.inflate.Model.TYPE).
Proof.
  intros m W HM. split.
  - apply mwf_set_mode_plain.
    + apply mwf_check_adler; auto. unfold lrange; rep_lia.
    + unfold HEAD, Zlib.proof.inflate.Model.TYPE, SYNC; lia.
    + unfold Zlib.proof.inflate.Model.TYPE, LENLENS; lia.
    + unfold Zlib.proof.inflate.Model.TYPE, CODELENS; lia.
    + unfold decode_mode, Zlib.proof.inflate.Model.TYPE, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT; lia.
    + left. apply (mwf_out_eq m W); rewrite HM; unfold DICT, LENGTH, DONE, BAD; lia.
  - apply swf3_plain; unfold decode_mode, Zlib.proof.inflate.Model.TYPE, HEAD, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT; lia.
Qed.

Lemma land_65280: forall y, 0 <= y -> 0 <= Z.land y 65280 < 2 ^ 16.
Proof.
  intros y Hy. split; [apply Z.land_nonneg; right; lia | ].
  replace (Z.land y 65280) with (Z.land (Z.land y 65280) (Z.ones 16))
    by (rewrite <- Z.land_assoc; reflexivity).
  rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
Qed.

Lemma swap32_range: forall q, 0 <= q -> 0 <= swap32 q < 2 ^ 33.
Proof.
  intros q Hq. unfold swap32.
  assert (A: 0 <= Z.shiftr q 24 mod 256 < 256) by (apply Z.mod_pos_bound; lia).
  assert (B: 0 <= Z.land (Z.shiftr q 8) 65280 < 2 ^ 16) by (apply land_65280, Z.shiftr_nonneg; lia).
  assert (C: 0 <= Z.land q 65280 < 2 ^ 16) by (apply land_65280; lia).
  assert (D: 0 <= q mod 256 < 256) by (apply Z.mod_pos_bound; lia).
  rewrite !Z.shiftl_mul_pow2 by lia. simpl (2 ^ 8) in *. simpl (2 ^ 16) in *. simpl (2 ^ 24). simpl (2 ^ 33). lia.
Qed.

Lemma needbits_f_s: forall k n m, m_s (needbits_f k n m) = m_s m.
Proof.
  induction k; intros n m; simpl; auto.
  destruct (m_bits m <? n); auto. destruct (m_have m =? 0); auto. rewrite IHk. reflexivity.
Qed.

Lemma needbits_mode: forall n m, m_mode (needbits n m) = m_mode m.
Proof. intros. unfold m_mode, needbits. rewrite needbits_f_s. reflexivity. Qed.

Lemma i64_add_repr: forall a b, Int64.add (Int64.repr a) (Int64.repr b) = Int64.repr (a + b).
Proof.
  intros. apply Int64.eqm_samerepr. unfold Int64.add.
  apply Int64.eqm_add; apply Int64.eqm_sym, Int64.eqm_unsigned_repr.
Qed.

Lemma swap32_int64: forall h, 0 <= h <= Int64.max_unsigned ->
  Int64.add (Int64.add (Int64.add
    (Int64.and (Int64.shru (Int64.repr h) (Int64.repr (Int.unsigned (Int.repr 24)))) (Int64.repr (Int.signed (Int.repr 255))))
    (Int64.and (Int64.shru (Int64.repr h) (Int64.repr (Int.unsigned (Int.repr 8)))) (Int64.repr (Int.signed (Int.repr 65280)))))
    (Int64.shl (Int64.and (Int64.repr h) (Int64.repr (Int.signed (Int.repr 65280)))) (Int64.repr (Int.unsigned (Int.repr 8)))))
    (Int64.shl (Int64.and (Int64.repr h) (Int64.repr (Int.signed (Int.repr 255)))) (Int64.repr (Int.unsigned (Int.repr 24))))
  = Int64.repr (swap32 h).
Proof.
  intros h Hh.
  change (Int.unsigned (Int.repr 24)) with 24. change (Int.unsigned (Int.repr 8)) with 8.
  change (Int.signed (Int.repr 255)) with 255. change (Int.signed (Int.repr 65280)) with 65280.
  pose proof (Zshiftr_range h 24 Hh ltac:(lia)) as R24. pose proof (Zshiftr_range h 8 Hh ltac:(lia)) as R8.
  unfold Int64.shru. rewrite !(Int64.unsigned_repr h) by lia.
  rewrite !(Int64.unsigned_repr 24) by rep_lia. rewrite !(Int64.unsigned_repr 8) by rep_lia.
  rewrite !int64_and_eq by rep_lia.
  pose proof (land_65280 h ltac:(lia)) as L1.
  assert (L2: 0 <= Z.land h 255 < 2 ^ 8).
  { change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  unfold Int64.shl. rewrite !Int64.unsigned_repr by rep_lia.
  rewrite !i64_add_repr. f_equal. unfold swap32.
  change 255 with (Z.ones 8). rewrite !Z.land_ones by lia. reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* case DICTID                                                                                     *)

Lemma case_DICTID5 {Espec: OracleKind} (F: frame) : frame_ok5 F -> case_ok5 F DICT 10 -> case_ok5 F DICTID 9.
Proof.
  intros [HF _] HD m HM HL [W W3].
  pose proof (stepf2_DICTID (f_flush F) lenfix_list distfix_list m HM) as E0.
  apply (case_fallthrough5 F m DICT 9); [lia | exact HD | ].
  case_body_stmt.
  eapply (semax_needbits_seq_r5 F m m 32).
  - apply semax_needbits_DICTID5; [exact W | exact HL | lia].
  - exact W.
  - lia.
  - reflexivity.
  - intro EL. rewrite E0. unfold c_DICTID. cbv zeta. rewrite EL. reflexivity.
  - apply semax_extract_prop; intros HL1.
    pose proof (mwf_needbits 32 m W ltac:(lia)) as W1.
    pose proof (needbits_mode 32 m) as Hm1. rewrite HM in Hm1.
    assert (E1: stepf2 (f_flush F) lenfix_list distfix_list m =
      stepf2 (f_flush F) lenfix_list distfix_list
        (set_mode (initbits (set_m_adler (upd_s (needbits 32 m)
           (fun s => set_i_check s (swap32 (m_hold (needbits 32 m))))) (swap32 (m_hold (needbits 32 m))))) DICT)).
    { rewrite E0. unfold c_DICTID. cbv zeta. rewrite HL1. cbn iota. symmetry.
      apply stepf2_DICT. reflexivity. }
    clear E0. set (m1 := needbits 32 m) in *. clearbody m1.
    pose proof (mw_hold _ W1) as Hho.
    rewrite loop_state_hd_eq. unfold loop_state_hd. abbreviate_semax.
    forward.
    rewrite swap32_int64 by exact Hho.
    pose proof (proj1 HF) as Hshs.
    forward.
    unfold strm_rep. remember (f_gv F _zcalloc) as za eqn:Eza. remember (f_gv F _zcfree) as zf eqn:Ezf.
    forward.
    eapply semax_do0.
    { forward. forward. apply andp_left2; apply derives_refl. }
    unfold abbreviate in MORE_COMMANDS. subst MORE_COMMANDS.
    forward.
    assert (Hr: lrange (swap32 (m_hold m1))) by (pose proof (swap32_range (m_hold m1) ltac:(unfold lrange in Hho; lia)); unfold lrange; rep_lia).
    unfold fall_post5. Exists (set_mode (initbits (set_m_adler (upd_s m1
      (fun s => set_i_check s (swap32 (m_hold m1)))) (swap32 (m_hold m1)))) DICT).
    apply andp_right.
    { apply prop_right. split; [exact E1 | split; [reflexivity | split; [exact HL1 | ]]].
      apply mwf3_DICT; assumption. }
    rewrite loop_state_hd_eq. unfold loop_state_hd, win_rep, head_part. unfold m_have, m_left. mnorm_goal.
    rest_simpl. rewrite strm_rep_unfold. rewrite <- Eza, <- Ezf. change (Int.signed (Int.repr 0)) with 0.
    entailer!.
Qed.

Lemma totin_eq: forall t a b,
  Int64.add (Int64.repr t) (Int64.repr (Int.unsigned (Int.sub (Int.repr a) (Int.repr b)))) =
  Int64.repr (u64 (t + u32 (a - b))).
Proof.
  intros. rewrite i64_add_repr. unfold u64, u32.
  unfold Int.sub. rewrite !Int.unsigned_repr_eq. change Int.modulus with (2 ^ 32).
  rewrite <- Zminus_mod.
  change (2 ^ 64) with Int64.modulus. rewrite <- Int64.unsigned_repr_eq. rewrite Int64.repr_unsigned.
  reflexivity.
Qed.

(* CaseRet5's semax_case_return5 for any postcondition with case_post2's return part *)
Lemma semax_case_return5' {Espec: OracleKind} (F: frame) (m m': mst) (r: Z) (e: expr) (P: environ -> mpred)
    (c: statement) (R: ret_assert):
  RA_return R = RA_return (case_post2 F m) ->
  stepf2 (f_flush F) lenfix_list distfix_list m = IRet r m' ->
  (forall rho, eval_expr (Ecast e tint) rho = Vint (Int.repr r)) ->
  ENTAIL Delta_cases5, P |-- tc_expr Delta_cases5 (Ecast e tint) ->
  ENTAIL Delta_cases5, P |-- (fun _ => mem_rep F m' * locals_rep F) ->
  semax Delta_cases5 P (Ssequence (Sreturn (Some e)) c) R.
Proof.
  intros HR Hs He Htc HP.
  eapply semax_seq; [ | apply semax_ff].
  eapply semax_pre; [ | apply semax_return ].
  rewrite ret_type_inflate5.
  apply andp_right; [ exact Htc | ].
  intro rho. specialize (HP rho). cbv beta in HP.
  assert (E: cast_expropt (Some e) tint rho = Some (Vint (Int.repr r))).
  { change (cast_expropt (Some e) tint rho) with (Some (eval_expr (Ecast e tint) rho)). rewrite He. reflexivity. }
  change (liftx (RA_return (overridePost FF R)) (cast_expropt (Some e) tint) id rho)
    with (RA_return (overridePost FF R) (cast_expropt (Some e) tint rho) (id rho)).
  rewrite E.
  replace (RA_return (overridePost FF R)) with (RA_return (case_post2 F m))
    by (destruct R; simpl in *; congruence).
  simpl RA_return.
  apply exp_right with r. apply exp_right with m'.
  apply andp_right.
  - apply prop_right. split; auto.
  - exact HP.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* case DICT                                                                                       *)

Lemma case_DICT5 {Espec: OracleKind} (F: frame) : frame_ok5 F ->
  case_ok5 F Zlib.proof.inflate.Model.TYPE 11 -> case_ok5 F DICT 10.
Proof.
  intros [HF _] HT m HM HL [W W3].
  pose proof (stepf2_DICT (f_flush F) lenfix_list distfix_list m HM) as E0.
  pose proof (sw_havedict _ (mw_s _ W)) as Hhd.
  pose proof (proj1 HF) as Hshs.
  apply (case_fallthrough5 F m Zlib.proof.inflate.Model.TYPE 10); [lia | exact HT | ].
  case_body_stmt.
  rewrite loop_state_hd_eq. unfold loop_state_hd. abbreviate_semax.
  forward.
  unfold abbreviate in MORE_COMMANDS. subst MORE_COMMANDS. apply semax_if_seq. forward_if.
  - unfold strm_rep. remember (f_gv F _zcalloc) as za eqn:Eza. remember (f_gv F _zcfree) as zf eqn:Ezf.
    apply -> seq_assoc. eapply semax_do0.
    + forward. forward. forward. forward. forward. forward. apply andp_left2; apply derives_refl.
    + forward. forward. forward.
      apply (semax_case_return5' F m (set_m_tin (restore m) (u64 (m_tin m + u32 (m_in m - m_have m)))) 2).
      { reflexivity. }
      { rewrite E0. unfold c_DICT. rewrite H1. reflexivity. }
      { reflexivity. }
      { entailer!. }
      { unfold mem_rep. rewrite state_rep_hd. rewrite strm_rep_unfold. rewrite totin_eq.
        unfold m_have, m_left in *. mnorm_goal. rest_simpl. rewrite <- Eza, <- Ezf.
        go_lowerx. cancel. }
  - assert (Hd: i_havedict (m_s m) <> 0).
    { intro X. rewrite X in *. contradiction. }
    assert (E1: stepf2 (f_flush F) lenfix_list distfix_list m =
      stepf2 (f_flush F) lenfix_list distfix_list
        (set_mode (set_m_adler (upd_s m (fun s => set_i_check s 1)) 1) Zlib.proof.inflate.Model.TYPE)).
    { rewrite E0. unfold c_DICT. rewrite (proj2 (Z.eqb_neq _ _) Hd). symmetry. apply stepf2_TYPE. reflexivity. }
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      apply semax_pre with (PROPx P (LOCALx Q (SEPx (emp :: emp :: R)))); [entailer! |] end.
    forward_call (0, nullval, 0, true, Ews, nullval, 0, 0, @nil val, @nil Z, false, Ews).
    forward.
    unfold strm_rep. remember (f_gv F _zcalloc) as za eqn:Eza. remember (f_gv F _zcfree) as zf eqn:Ezf.
    forward. forward.
    unfold fall_post5. Exists (set_mode (set_m_adler (upd_s m (fun s => set_i_check s 1)) 1) Zlib.proof.inflate.Model.TYPE).
    apply andp_right.
    { apply prop_right. split; [exact E1 | split; [reflexivity | split; [exact HL | ]]].
      apply mwf3_TYPE; assumption. }
    rewrite loop_state_hd_eq. unfold loop_state_hd, win_rep, head_part. unfold m_have, m_left. mnorm_goal.
    rest_simpl. rewrite strm_rep_unfold. rewrite <- Eza, <- Ezf.
    entailer!.
Qed.

Lemma cases5_HD {Espec: OracleKind} (F: frame) : frame_ok5 F -> 
  case_ok5 F HCRC 8 /\ (case_ok5 F DICT 10 -> case_ok5 F DICTID 9) /\ (case_ok5 F Zlib.proof.inflate.Model.TYPE 11 -> case_ok5 F DICT 10).
Proof.
  intros HF. split; [ | split].
  - apply case_HCRC5; exact HF.
  - apply case_DICTID5; exact HF.
  - apply case_DICT5; exact HF.
Qed.
