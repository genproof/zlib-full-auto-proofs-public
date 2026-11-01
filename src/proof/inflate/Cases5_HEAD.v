(* inflate(), the switch cases HEAD (0), version 5 (Delta_cases5, case_post2 over Model2.v, mwf3; header cases
   FLAGS .. COMMENT with the header buffers' tokens: CaseHyps5.v, CaseKitT5.v).
   Port of the v3 proof: the body is cut along the code (HeadDefs5.v): the wrap test
   (here), NEEDBITS(16) (NeedKit5, NeedBits1_5), the gzip test (here), the gzip branch (HeadGzipW5.v) and the zlib
   branch (HeadZlib7.v, patch F7). *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate.CaseHyps5.
Require Import Zlib.proof.inflate.NeedKit5 Zlib.proof.inflate.NeedBits Zlib.proof.inflate.NeedBits1_5.
Require Import Zlib.proof.inflate.Steps2 Zlib.proof.inflate.MwfLemmas Zlib.proof.inflate.ModeKit5.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.inflate.HeadDefs5 Zlib.proof.inflate.HeadGzipW5 Zlib.proof.inflate.HeadZlib7.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* ---------------------------------------------------------------------------------------------- *)
(* the fields mode and wrap apart (ModeKit's split, one field more), so that the wrap test and the
   gzip test see 4 SEP items                                                                      *)

Definition state_rep_nmw (gv: globals) (sp strmp headp winp: val) (s: istate) : mpred :=
  field_at Ews t_state (DOT _strm) strmp sp *
  field_at Ews t_state (DOT _last) (zv (i_last s)) sp *
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

Lemma sepcon_third_34: forall a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34: mpred,
  a1 * a2 * a3 * a4 * a5 * a6 * a7 * a8 * a9 * a10 * a11 * a12 * a13 * a14 * a15 * a16 * a17 * a18 * a19 * a20 * a21 * a22 * a23 * a24 * a25 * a26 * a27 * a28 * a29 * a30 * a31 * a32 * a33 * a34 =
  a3 * (a1 * a2 * a4 * a5 * a6 * a7 * a8 * a9 * a10 * a11 * a12 * a13 * a14 * a15 * a16 * a17 * a18 * a19 * a20 * a21 * a22 * a23 * a24 * a25 * a26 * a27 * a28 * a29 * a30 * a31 * a32 * a33 * a34).
Proof. intros. apply pred_ext; cancel. Qed.

Lemma state_rep_nm_split: forall gv sp strmp headp winp s,
  state_rep_nm gv sp strmp headp winp s =
  field_at Ews t_state (DOT _wrap) (zv (i_wrap s)) sp * state_rep_nmw gv sp strmp headp winp s.
Proof. intros. unfold state_rep_nm, state_rep_nmw. apply sepcon_third_34. Qed.

Definition mem_rep_nmw (F: frame) (m: mst) : mpred :=
  state_rep_nmw (f_gv F) (f_sp F) (f_strmp F) (f_headp F) (f_winp F) (m_s m) *
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

Lemma mem_rep_nm_split: forall F m,
  mem_rep_nm F m = field_at Ews t_state (DOT _wrap) (zv (i_wrap (m_s m))) (f_sp F) * mem_rep_nmw F m.
Proof.
  intros. unfold mem_rep_nm, mem_rep_nmw. rewrite state_rep_nm_split. rewrite !sepcon_assoc. reflexivity.
Qed.

(* loop_state with the mode (value v) and wrap fields apart *)
Definition loop_state_mw (F: frame) (m: mst) (v: val) : environ -> mpred :=
  PROP (in_ok (f_ib F) (m_inp m); out_ok (f_ob F) (m_aout m))
  LOCAL (temp _strm (f_strmp F); temp _flush (zv (f_flush F)); temp _state (f_sp F);
         temp _next (in_ptr (f_ib F) (m_nx m)); temp _put (out_ptr (f_ob F) (Zlength (m_ow m)));
         temp _have (zv (m_have m)); temp _left (zv (m_left m)); temp _hold (lv (m_hold m));
         temp _bits (zv (m_bits m)); temp _in (zv (m_in m)); temp _out (zv (m_out m));
         temp _ret (zv (m_ret m)); temp _leave (zv (m_leave m));
         lvar _here t_code (f_vhere F); lvar _last t_code (f_vlast F);
         lvar _hbuf (tarray tuchar 4) (f_vhbuf F); gvars (f_gv F))
  SEP (field_at Ews t_state (DOT _mode) v (f_sp F);
       field_at Ews t_state (DOT _wrap) (zv (i_wrap (m_s m))) (f_sp F);
       mem_rep_nmw F m; locals_rep F).

Lemma loop_state_split_mw: forall F m, loop_state F m = loop_state_mw F m (zv (m_mode m)).
Proof.
  intros. rewrite loop_state_split. unfold loop_state_m, loop_state_mw. rewrite mem_rep_nm_split.
  f_equal. unfold SEPx. simpl. rewrite !sepcon_assoc. reflexivity.
Qed.

Lemma loop_state_set_mode_mw: forall F m md, loop_state F (set_mode m md) = loop_state_mw F m (zv md).
Proof. intros. rewrite loop_state_split_mw. reflexivity. Qed.

(* if (state->wrap == 0) { state->mode = TYPEDO; break; } *)
Lemma head_wrap5 {Espec: OracleKind} (F: frame) (m: mst) (R: ret_assert):
  m_mode m = HEAD -> mwf m ->
  RA_break R = RA_normal (case_post2 F m) ->
  semax Delta_cases5 (loop_state F m) head_WRAP
    (overridePost (!! (i_wrap (m_s m) <> 0) && loop_state F m) R).
Proof.
  intros HM W HR.
  pose proof (sw_wrap_range _ (mw_s _ W)) as Hw.
  destruct (Z.eq_dec (i_wrap (m_s m)) 0) as [Hw0 | Hw0].
  - assert (E: stepf2 (f_flush F) lenfix_list distfix_list m = IBrk (set_mode m TYPEDO)).
    { rewrite (stepf2_HEAD _ _ _ _ HM). unfold c_HEAD2. rewrite Hw0. reflexivity. }
    rewrite loop_state_split_mw. unfold loop_state_mw, head_WRAP.
    abbreviate_semax.
    forward. forward_if; [ | contradiction].
    forward. forward.
    match goal with |- context [RA_break ?X] =>
      replace (RA_break X) with (RA_break R) by (destruct R; reflexivity) end.
    rewrite HR. unfold case_post. unfold RA_normal at 1.
    Exists (set_mode m TYPEDO).
    apply andp_right; [apply prop_right; exact E | ].
    rewrite loop_state_set_mode_mw. unfold loop_state_mw.
    entailer!.
  - rewrite loop_state_split_mw. unfold loop_state_mw, head_WRAP.
    abbreviate_semax.
    forward. forward_if; [ contradiction | ].
    eapply ConseqFacts.semax_post''; [ | apply semax_skip].
    match goal with |- context [RA_normal ?X] =>
      replace (RA_normal X) with (!! (i_wrap (m_s m) <> 0) && loop_state_mw F m (zv (m_mode m)))
        by (destruct R; reflexivity) end.
    unfold loop_state_mw.
    entailer!.
Qed.

(* t'7 = (state->wrap & 2) && hold == 0x8b1f; if (t'7) <gzip>; <zlib> *)
Lemma head_rest5 {Espec: OracleKind} (F: frame) (m0 m1: mst) (R: ret_assert):
  frame_ok5 F -> mwf m1 -> m_leave m1 = 0 ->
  (i_wbits (m_s m1) = 0 -> i_win (m_s m1) = false) ->
  RA_break R = RA_normal (case_post2 F m0) ->
  stepf2 (f_flush F) lenfix_list distfix_list m0 =
    (if andb (negb (Z.land (i_wrap (m_s m1)) 2 =? 0)) (m_hold m1 =? 35615)
     then IBrk (head_gzip_m m1) else head_zlib_out m1) ->
  semax Delta_cases5 (loop_state F m1)
    (Ssequence (Ssequence head_W7 (Sifthenelse (Etempvar _t'7 tint) head_GZIP Sskip)) head_ZLIB) R.
Proof.
  intros HF W HL HN HR E.
  pose proof (sw_wrap_range _ (mw_s _ W)) as Hw. pose proof (mw_hold _ W) as Hh.
  rewrite loop_state_split_mw. unfold loop_state_mw, head_W7.
  abbreviate_semax.
  forward.
  unfold abbreviate in MORE_COMMANDS. subst MORE_COMMANDS. apply semax_if_seq.
  forward_if.
  - rewrite !Int.unsigned_repr in H1' by rep_lia.
    forward.
    unfold abbreviate in MORE_COMMANDS. subst MORE_COMMANDS. apply semax_if_seq.
    forward_if.
    + assert (G: andb (negb (Z.land (i_wrap (m_s m1)) 2 =? 0)) (m_hold m1 =? 35615) = true).
      { apply Int64.same_if_eq in H2. unfold lrange in Hh.
        apply repr_inj_unsigned64 in H2; [ | rep_lia | rep_lia].
        rewrite H2. apply andb_true_iff; split; [apply negb_true_iff, Z.eqb_neq; exact H1' | apply Z.eqb_refl]. }
      rewrite G in E.
      unfold abbreviate in MORE_COMMANDS. subst MORE_COMMANDS.
      eapply semax_seq; [ | apply semax_ff].
      eapply semax_pre; [ | apply (head_gzip5_w F m0 m1 _ HF W HL HN); [destruct R; exact HR | exact E]].
      rewrite loop_state_split_mw. unfold loop_state_mw. entailer!.
    + assert (G: andb (negb (Z.land (i_wrap (m_s m1)) 2 =? 0)) (m_hold m1 =? 35615) = false).
      { apply andb_false_iff; right. apply Z.eqb_neq. intro X. apply H2. rewrite X. reflexivity. }
      rewrite G in E.
      eapply semax_pre; [ | apply (head_zlib7_w F m0 m1 R HF W HL HN HR E)].
      rewrite loop_state_split_mw. unfold loop_state_mw. entailer!.
  - forward.
    unfold abbreviate in MORE_COMMANDS. subst MORE_COMMANDS. apply semax_if_seq.
    forward_if.
    + exfalso. apply H2. reflexivity.
    + assert (G: andb (negb (Z.land (i_wrap (m_s m1)) 2 =? 0)) (m_hold m1 =? 35615) = false).
      { apply andb_false_iff; left. apply negb_false_iff, Z.eqb_eq.
        unfold Int.and in H1. rewrite !Int.unsigned_repr in H1 by rep_lia.
        apply (f_equal Int.unsigned) in H1. revert H1.
        pose proof (wrap_cases _ (sw_wrap _ (mw_s _ W))) as Hc.
        destruct Hc as [X|[X|[X|[X|[X|[X|[X|[X|[X|[X|[X|[X|[X|X]]]]]]]]]]]]]; rewrite X; intro H1; vm_compute in H1;
          first [reflexivity | discriminate]. }
      rewrite G in E.
      eapply semax_pre; [ | apply (head_zlib7_w F m0 m1 R HF W HL HN HR E)].
      rewrite loop_state_split_mw. unfold loop_state_mw. entailer!.
Qed.

Lemma cases5_HEAD {Espec: OracleKind} (F: frame) : frame_ok5 F -> 
  case_ok5 F HEAD 0.
Proof.
  intros HF m HM HL [W W3].
  rewrite seq_split by lia.
  eapply semax_seq; [ | apply semax_ff].
  rewrite case_body0_eq.
  apply semax_seq with (Q := !! (i_wrap (m_s m) <> 0) && loop_state F m).
  { apply head_wrap5; [exact HM | exact W | reflexivity]. }
  apply semax_extract_prop; intros Hw.
  pose proof (stepf2_HEAD (f_flush F) lenfix_list distfix_list m HM) as E0.
  eapply (semax_needbits_seq_r5 F m m 16).
  - apply semax_needbits_HEAD5; [exact W | exact HL | lia].
  - exact W.
  - lia.
  - reflexivity.
  - intro E. rewrite E0. unfold c_HEAD2. rewrite (proj2 (Z.eqb_neq _ _) Hw). cbv zeta. rewrite E.
    reflexivity.
  - apply semax_extract_prop; intros HL1.
    pose proof (mwf_needbits 16 m W ltac:(lia)) as W1.
    assert (E1: stepf2 (f_flush F) lenfix_list distfix_list m =
      (if andb (negb (Z.land (i_wrap (m_s (needbits 16 m))) 2 =? 0)) (m_hold (needbits 16 m) =? 35615)
       then IBrk (head_gzip_m (needbits 16 m)) else head_zlib_out (needbits 16 m))).
    { rewrite E0. apply c_HEAD_split; [exact Hw | exact HL1]. }
    apply (head_rest5 F m (needbits 16 m));
      [exact HF | exact W1 | exact HL1 | exact (head_gzip_nowin m (conj W W3) HM Hw) | reflexivity | exact E1].
Qed.
