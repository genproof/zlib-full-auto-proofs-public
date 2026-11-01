(* RT-H: case HEAD in the header world.  The model fact (a call that passes the header from mode HEAD
   with done = 0 takes the gzip branch) and the headless HEAD case for such a machine: the wrap test, NEEDBITS(16),
   the gzip test and the gzip branch (RTHHeadGzipW5.head_gzip5_wH); the branches the model excludes are
   contradictions. *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.roundtrip.RTHSpec.
Require Import Zlib.proof.roundtrip.RTHCaseHyps5.
Require Import Zlib.proof.roundtrip.RTHNeedKit5 Zlib.proof.roundtrip.RTHNeedBits1_5 Zlib.proof.roundtrip.RTHModeKit5.
Require Import Zlib.proof.inflate.Steps2 Zlib.proof.inflate.MwfLemmas.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.inflate.HeadDefs5 Zlib.proof.inflate.Cases5_HEAD.
Require Import Zlib.proof.roundtrip.RTHHeadGzipW5.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* ---------------------------------------------------------------------------------------------- *)
(* the model                                                                                       *)

Lemma rthh_nb_sh: forall k n m, m_s (needbits_f k n m) = m_s m /\ m_h (needbits_f k n m) = m_h m.
Proof.
  induction k; intros n m; simpl; auto.
  destruct (m_bits m <? n); auto. destruct (m_have m =? 0); auto.
  destruct (IHk n (pull m)) as [A B]. rewrite A, B. auto.
Qed.

Lemma rthh_nopass: forall flush n m,
  hdr_mode (m_mode m) = false -> h_done (m_h m) <> 1 -> hpass flush n m -> False.
Proof.
  intros flush n m HM HD P. destruct n as [|n]; [exact P | ].
  cbn [hpass] in P. rewrite HM in P. destruct P as [P _]. exact (HD P).
Qed.

Lemma rthh_gzip: forall flush n m,
  m_mode m = Zlib.proof.inflate.Model.HEAD -> i_head (m_s m) = true -> h_done (m_h m) = 0 -> mwf m ->
  hpass flush (S n) m ->
  i_wrap (m_s m) <> 0 /\ m_leave (needbits 16 m) = 0 /\
  andb (negb (Z.land (i_wrap (m_s (needbits 16 m))) 2 =? 0)) (m_hold (needbits 16 m) =? 35615) = true.
Proof.
  intros flush n m HM HI HD W P.
  pose proof (mw_leave _ (mwf_needbits 16 m W ltac:(lia))) as WL.
  cbn [hpass] in P. rewrite HM in P. change (hdr_mode Zlib.proof.inflate.Model.HEAD) with true in P.
  rewrite (stepf2_HEAD _ _ _ _ HM) in P. unfold c_HEAD2 in P.
  destruct (i_wrap (m_s m) =? 0) eqn:Hw.
  { exfalso. destruct P as [_ P]. eapply rthh_nopass; [ | | exact P]; [reflexivity | cbn; rewrite HD; discriminate]. }
  destruct (rthh_nb_sh 4 16 m) as [S1 H1]. unfold needbits in *.
  destruct (m_leave (needbits_f 4 16 m) =? 1) eqn:Hl.
  { destruct P as [P _]. apply Z.eqb_eq in Hl. lia. }
  apply Z.eqb_neq in Hl.
  split; [apply Z.eqb_neq; exact Hw | split; [lia | ]].
  destruct (negb (Z.land (i_wrap (m_s (needbits_f 4 16 m))) 2 =? 0) && (m_hold (needbits_f 4 16 m) =? 35615))%bool
    eqn:G; [reflexivity | exfalso].
  rewrite S1, HI in P.
  set (m1 := upd_h (needbits_f 4 16 m) (fun h => set_h_done h (-1))) in P.
  assert (D: forall m', m_h m' = m_h m1 -> h_done (m_h m') <> 1) by (intros m' E; rewrite E; cbn; discriminate).
  clearbody m1.
  repeat match type of P with
  | context [if ?c then _ else _] => destruct c
  end;
  destruct P as [_ P]; (eapply rthh_nopass; [ | | exact P]);
  first [ reflexivity | apply D; reflexivity | unfold m_mode; cbn; destruct (Z.land _ 512 =? 0); reflexivity ].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the headless loop state with the fields mode and wrap apart (Cases5_HEAD.v's split)             *)

Definition mem_rep_nmwH (F: frame) (m: mst) : mpred :=
  state_rep_nmw (f_gv F) (f_sp F) (f_strmp F) (f_headp F) (f_winp F) (m_s m) *
  win_rep (f_winp F) (m_s m) *
  head_partH F m *
  strm_rep (f_gv F) (f_shs F) (f_strmp F)
    (in_ptr (f_ib F) (m_snx m)) (zv (Zlength (m_inp m) - m_snx m)) (m_tin m)
    (out_ptr (f_ob F) (m_sow m)) (zv (m_aout m - m_sow m)) (m_tout m)
    (msg_val (f_gv F) (m_msg m)) (f_sp F) (f_dt F) (m_adler m) (f_vres F) *
  in_rep (f_ib F) *
  out_rep (f_ob F) (m_ow m) *
  tables_rep (f_gsh F) (f_gv F) *
  crc_table_at (f_tsh F) (f_gv F).

Lemma mem_rep_nm_splitH: forall F m,
  mem_rep_nmH F m = field_at Ews t_state (DOT _wrap) (zv (i_wrap (m_s m))) (f_sp F) * mem_rep_nmwH F m.
Proof.
  intros. unfold mem_rep_nmH, mem_rep_nmwH. rewrite state_rep_nm_split. rewrite !sepcon_assoc. reflexivity.
Qed.

Definition loop_state_mwH (F: frame) (m: mst) (v: val) : environ -> mpred :=
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
       mem_rep_nmwH F m; locals_rep F).

Lemma loop_state_split_mwH: forall F m, loop_stateH F m = loop_state_mwH F m (zv (m_mode m)).
Proof.
  intros. rewrite loop_state_splitH. unfold loop_state_mH, loop_state_mwH. rewrite mem_rep_nm_splitH.
  f_equal. unfold SEPx. simpl. rewrite !sepcon_assoc. reflexivity.
Qed.

(* if (state->wrap == 0) { .. } with wrap <> 0 *)
Lemma head_wrapH {Espec: OracleKind} (F: frame) (m: mst) (R: ret_assert):
  mwf m -> i_wrap (m_s m) <> 0 ->
  semax Delta_cases5 (loop_stateH F m) head_WRAP (overridePost (loop_stateH F m) R).
Proof.
  intros W Hw0.
  pose proof (sw_wrap_range _ (mw_s _ W)) as Hw.
  rewrite loop_state_split_mwH. unfold loop_state_mwH, head_WRAP.
  abbreviate_semax.
  forward. forward_if; [ contradiction | ].
  eapply ConseqFacts.semax_post''; [ | apply semax_skip].
  match goal with |- context [RA_normal ?X] =>
    replace (RA_normal X) with (loop_state_mwH F m (zv (m_mode m))) by (destruct R; reflexivity) end.
  unfold loop_state_mwH.
  entailer!.
Qed.

(* t'7 = (state->wrap & 2) && hold == 0x8b1f; if (t'7) <gzip>; <zlib>, the gzip test true *)
Lemma head_restH {Espec: OracleKind} (F: frame) (m0 m1: mst) (R: ret_assert):
  frame_ok5 F -> mwf m1 -> m_leave m1 = 0 ->
  (i_wbits (m_s m1) = 0 -> i_win (m_s m1) = false) ->
  RA_break R = RA_normal (case_post2H F m0) ->
  andb (negb (Z.land (i_wrap (m_s m1)) 2 =? 0)) (m_hold m1 =? 35615) = true ->
  stepf2 (f_flush F) lenfix_list distfix_list m0 = IBrk (head_gzip_m m1) ->
  semax Delta_cases5 (loop_stateH F m1)
    (Ssequence (Ssequence head_W7 (Sifthenelse (Etempvar _t'7 tint) head_GZIP Sskip)) head_ZLIB) R.
Proof.
  intros HF W HL HN HR G E.
  pose proof (sw_wrap_range _ (mw_s _ W)) as Hw. pose proof (mw_hold _ W) as Hh.
  apply andb_true_iff in G. destruct G as [G1 G2].
  apply negb_true_iff, Z.eqb_neq in G1. apply Z.eqb_eq in G2.
  rewrite loop_state_split_mwH. unfold loop_state_mwH, head_W7.
  abbreviate_semax.
  forward.
  unfold abbreviate in MORE_COMMANDS. subst MORE_COMMANDS. apply semax_if_seq.
  forward_if.
  - forward.
    unfold abbreviate in MORE_COMMANDS. subst MORE_COMMANDS. apply semax_if_seq.
    forward_if.
    + unfold abbreviate in MORE_COMMANDS. subst MORE_COMMANDS.
      eapply semax_seq; [ | apply semax_ff].
      eapply semax_pre; [ | apply (head_gzip5_wH F m0 m1 _ HF W HL HN); [destruct R; exact HR | exact E]].
      rewrite loop_state_split_mwH. unfold loop_state_mwH. entailer!.
    + exfalso. apply H2. rewrite G2. reflexivity.
  - exfalso. apply G1.
    unfold Int.and in H1. rewrite !Int.unsigned_repr in H1 by rep_lia.
    apply (f_equal Int.unsigned) in H1. revert H1.
    pose proof (wrap_cases _ (sw_wrap _ (mw_s _ W))) as Hc.
    destruct Hc as [X|[X|[X|[X|[X|[X|[X|[X|[X|[X|[X|[X|[X|X]]]]]]]]]]]]]; rewrite X; intro H1; vm_compute in H1;
      first [reflexivity | discriminate].
Qed.

(* case HEAD, headless, for a machine the model sends into the gzip branch *)
Lemma head_caseH {Espec: OracleKind} (F: frame) (m: mst):
  frame_ok5 F -> m_mode m = Zlib.proof.inflate.Model.HEAD -> m_leave m = 0 -> mwf3 m ->
  i_wrap (m_s m) <> 0 -> m_leave (needbits 16 m) = 0 ->
  andb (negb (Z.land (i_wrap (m_s (needbits 16 m))) 2 =? 0)) (m_hold (needbits 16 m) =? 35615) = true ->
  semax Delta_cases5 (loop_stateH F m) (seq_of_labeled_statement (ls_drop 0 inflate_LS))
    (switch_ret_assert (case_post2H F m)).
Proof.
  intros HF HM HL [W W3] Hw HL1 G.
  rewrite seq_split by lia.
  eapply semax_seq; [ | apply semax_ff].
  rewrite case_body0_eq.
  apply semax_seq with (Q := loop_stateH F m).
  { apply head_wrapH; [exact W | exact Hw]. }
  pose proof (stepf2_HEAD (f_flush F) lenfix_list distfix_list m HM) as E0.
  eapply (semax_needbits_seq_r5H F m m 16).
  - apply semax_needbits_HEAD5H; [exact W | exact HL | lia].
  - exact W.
  - lia.
  - reflexivity.
  - intro E. rewrite HL1 in E. discriminate.
  - apply semax_extract_prop; intros _.
    pose proof (mwf_needbits 16 m W ltac:(lia)) as W1.
    assert (E1: stepf2 (f_flush F) lenfix_list distfix_list m = IBrk (head_gzip_m (needbits 16 m))).
    { rewrite E0, (c_HEAD_split m Hw HL1), G. reflexivity. }
    apply (head_restH F m (needbits 16 m));
      [exact HF | exact W1 | exact HL1 | exact (head_gzip_nowin m (conj W W3) HM Hw) | reflexivity | exact G
      | exact E1].
Qed.

(* the header is the same in HEAD and FLAGS (nothing written yet) *)
Lemma head_rep6_HEAD_FLAGS: forall hsh headp xb nb cb s s' h,
  i_mode s = Zlib.proof.inflate.Model.HEAD -> i_mode s' = Zlib.proof.inflate.Model.FLAGS ->
  i_flags s' = i_flags s ->
  head_rep6 hsh headp xb nb cb s h = head_rep6 hsh headp xb nb cb s' h.
Proof.
  intros hsh headp xb nb cb s s' h M M' Fl.
  unfold head_rep6, hph, cx6, cn6, cc6, fextra. rewrite M, M', Fl.
  f_equal. f_equal. apply prop_ext. unfold hinv6. rewrite M, M'.
  unfold Zlib.proof.inflate.Model.HEAD, Zlib.proof.inflate.Model.FLAGS, Zlib.proof.inflate.Model.EXTRA,
    Zlib.proof.inflate.Model.HCRC, Zlib.proof.inflate.Model.NAME, Zlib.proof.inflate.Model.COMMENT.
  cbn -[Z.le]. intuition (try discriminate).
Qed.
