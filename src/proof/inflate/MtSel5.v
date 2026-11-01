(* case MATCH (24) v5: the leave test (mt_lz_ok) and the source selection (mt_sel_ok) *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate.DmKit5 Zlib.proof.inflate.MtKit5 Zlib.proof.inflate.Steps2.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Lemma mt_sub_pi: forall p a d, isptr p -> 0 <= d <= Int.max_unsigned ->
  force_val (sem_sub_pi tuchar Unsigned (offset_val a p) (Vint (Int.repr d))) = offset_val (a - d) p.
Proof.
  intros p a d P D. destruct p; try contradiction. simpl. f_equal.
  unfold Ptrofs.of_intu, Ptrofs.of_int. rewrite Int.unsigned_repr by lia.
  rewrite Ptrofs.mul_commut, Ptrofs.mul_one.
  rewrite Ptrofs.sub_add_opp, Ptrofs.add_assoc. f_equal.
  rewrite <- Ptrofs.sub_add_opp. unfold Ptrofs.sub. apply Ptrofs.eqm_samerepr.
  apply Ptrofs.eqm_sub; apply Ptrofs.eqm_sym; apply Ptrofs.eqm_unsigned_repr.
Qed.

Lemma mt_add_pi: forall p k, isptr p -> 0 <= k <= Int.max_unsigned ->
  force_val (sem_add_ptr_int tuchar Unsigned p (Vint (Int.repr k))) = offset_val k p.
Proof.
  intros p k P K. destruct p; try contradiction. simpl. f_equal.
  unfold Ptrofs.of_intu, Ptrofs.of_int. rewrite Int.unsigned_repr by lia.
  rewrite Ptrofs.mul_commut, Ptrofs.mul_one. reflexivity.
Qed.

Lemma mt_from_win: forall p a b, isptr p -> 0 <= b <= a -> a <= Int.max_unsigned ->
  force_val (sem_binary_operation' Oadd (tptr tuchar) tuint p
    (eval_binop Osub tuint tuint (Vint (Int.repr a)) (Vint (Int.repr b)))) = offset_val (a - b) p.
Proof.
  intros p a b P B A. destruct p; try contradiction.
  unfold eval_binop, sem_binary_operation'. simpl. rewrite sub_repr. f_equal.
  unfold Ptrofs.of_intu, Ptrofs.of_int. rewrite Int.unsigned_repr by lia.
  rewrite Ptrofs.mul_commut, Ptrofs.mul_one. reflexivity.
Qed.

Ltac mt_ur := repeat match goal with H: context [Int.unsigned (Int.repr ?x)] |- _ =>
  rewrite (Int.unsigned_repr x) in H by rep_lia end.

(* if (left == 0) { leave = 1; break; } *)
Lemma mt_lz_ok {Espec: OracleKind} (F: frame) (m: mst) (R: ret_assert):
  m_mode m = MATCH -> mwf m ->
  RA_break R = RA_normal (case_post2 F m) ->
  semax Delta_cases5 (loop_state F m) mt_lz (overridePost (!! (m_left m <> 0) && loop_state F m) R).
Proof.
  intros HM W HR. rewrite mt_lz_eq.
  pose proof (mwf_left m W) as HLEFT.
  unfold loop_state. abbreviate_semax.
  forward_if.
  - forward. forward.
    match goal with |- _ |-- ?G => replace G with (RA_break R) by (destruct R; reflexivity) end.
    rewrite HR. unfold case_post2. cbn [RA_normal].
    assert (E: stepf2 (f_flush F) lenfix_list distfix_list m = IBrk (set_leave m)).
    { rewrite (stepf2_MATCH _ _ _ m HM). unfold c_MATCH. rewrite H. reflexivity. }
    Exists (set_leave m).
    apply andp_right; [apply prop_right; exact E | ].
    unfold loop_state. entailer!. apply derives_refl.
  - forward.
    match goal with |- _ |-- ?G => replace G with (!! (m_left m <> 0) && loop_state F m) by (destruct R; reflexivity) end.
    unfold loop_state. entailer!.
Qed.

Definition mt_pre_sel (F: frame) (m: mst) : environ -> mpred :=
  PROPx [in_ok (f_ib F) (m_inp m); out_ok (f_ob F) (m_aout m)]
  (LOCALx (temp _copy (zv (Zlength (m_ow m))) :: mt_locals F m) (SEPx (mt_seps F m))).

Ltac mt_src_tac C0 :=
  unfold mt_src; rewrite C0;
  repeat ((rewrite (proj2 (Z.ltb_lt _ _)) by lia) || (rewrite (proj2 (Z.ltb_ge _ _)) by lia));
  cbn [andb negb]; try (rewrite Z.min_r by lia); try (rewrite Z.min_l by lia); reflexivity.

Ltac mt_leaf FR m R sr cp C0 :=
  match goal with |- _ |-- ?G => replace G with
    (EX sr0: src, EX cp0: Z, !! (mt_src m = Some (sr0, cp0)) && mt_selq FR m sr0 cp0) by (destruct R; reflexivity) end;
  Exists sr cp;
  apply andp_right; [apply prop_right; mt_src_tac C0 | ];
  unfold mt_selq, mt_locals, mt_seps, src_ptr, FR; frame_simpl;
  try (match goal with WIN: i_win _ = true |- _ => rewrite WIN end);
  entailer!.

Lemma mt_sel_ok {Espec: OracleKind} (F: frame) (m: mst) (R: ret_assert):
  frame_ok5 F -> m_mode m = MATCH -> m_leave m = 0 -> mwf3 m -> m_left m <> 0 ->
  RA_break R = RA_normal (case_post2 F m) ->
  semax Delta_cases5 (mt_pre_sel F m) mt_sel
    (overridePost (EX sr: src, EX cp: Z, !! (mt_src m = Some (sr, cp)) && mt_selq F m sr cp) R).
Proof.
  intros HF HM HL [W X] HL0 HR.
  pose proof (mwf_left m W) as HLEFT.
  assert (OE: m_out m = m_aout m) by (apply mwf_out_eq; auto; rewrite HM; unfold MATCH, LENGTH, DONE, BAD; lia).
  pose proof (md_match _ (mw_md _ W) HM) as Hlen1.
  pose proof (md_offset _ (mw_md _ W) (or_intror HM)) as Hoff1.
  pose proof (sw_offset _ (mw_s _ W)) as Hoff2. pose proof (sw_length _ (mw_s _ W)) as Hlen2.
  pose proof (sw_whave _ (mw_s _ W)) as Hwh. pose proof (sw_wnext _ (mw_s _ W)) as Hwn.
  pose proof (sw_wsize _ (mw_s _ W)) as Hws. pose proof (sw_sane _ (mw_s _ W)) as Hsane.
  pose proof (sw_wbits _ (mw_s _ W)) as Hwb. pose proof (sw_wvalid _ (mw_s _ W)) as Hwv.
  pose proof (mw_ow _ W) as [How1 How2]. pose proof (Zlength_nonneg (m_ow m)) as How0.
  pose proof (mw_aout _ W) as Haout.
  unfold urange in *.
  assert (WSB: i_wsize (m_s m) <= 2 ^ 23).
  { destruct Hws as [E | [_ E]]; rewrite E; [lia | apply Z.pow_le_mono_r; lia]. }
  change (2 ^ 23) with 8388608 in WSB.
  assert (C0: u32 (m_out m - m_left m) = Zlength (m_ow m)).
  { unfold m_left, u32. rewrite OE. rewrite Z.mod_small by rep_lia. lia. }
  destruct F as [gv shs strmp sp headp winp hsh xb nb cb ib ob gsh tsh dt vres vhere vlast vhbuf flush].
  destruct ob as [osh op olo on oc].
  destruct HF as [[Hshs [_ [Hgsh Htsh]]] Hfl]. cbn [f_shs f_gsh f_tsh f_flush] in Hshs, Hgsh, Htsh, Hfl.
  pose (FR := Fr gv shs strmp sp headp winp hsh xb nb cb ib (OutBuf osh op olo on oc) gsh tsh dt vres vhere vlast
                 vhbuf flush).
  cbv beta iota zeta delta [mt_sel mt_r2 mt_r1 mt_body case_body inflate_LS find_switch f_inflate fn_body ls_drop].
  unfold mt_pre_sel, mt_locals, mt_seps. frame_simpl. abbreviate_semax.
  forward.
  forward_if.
  2: {
    forward. forward. forward.
    match goal with |- _ |-- ?G => replace G with
      (EX sr: src, EX cp: Z, !! (mt_src m = Some (sr, cp)) && mt_selq (Fr gv shs strmp sp headp winp hsh xb nb cb ib
         (OutBuf osh op olo on oc) gsh tsh dt vres vhere vlast vhbuf flush) m sr cp) by (destruct R; reflexivity) end.
    assert (ES: mt_src m = Some (SOut (Zlength (m_ow m) - i_offset (m_s m)), i_length (m_s m))).
    { unfold mt_src. rewrite C0. rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity. }
    Exists (SOut (Zlength (m_ow m) - i_offset (m_s m))) (i_length (m_s m)).
    apply andp_right; [apply prop_right; exact ES | ].
    unfold mt_selq, mt_locals, mt_seps, src_ptr. frame_simpl.
    entailer!.
    rewrite mt_sub_pi by (auto; lia). f_equal. lia.
  }
  forward. forward. forward.
  rewrite sub_repr.
  unfold abbreviate in MORE_COMMANDS. subst MORE_COMMANDS. apply semax_if_seq. forward_if.
  { (* too far back: BAD *)
    forward.
    forward_if.
    2: { exfalso. rewrite Hsane in *. discriminate. }
    assert (EB: stepf2 flush lenfix_list distfix_list m = IBrk (set_bad m M_far)).
    { rewrite (stepf2_MATCH _ _ _ m HM), (c_MATCH_eq m HL0). unfold mt_src. rewrite C0.
      rewrite (proj2 (Z.ltb_lt _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. rewrite Hsane. reflexivity. }
    unfold mt_strm, strm_rep. frame_simpl.
    remember (gv _zcalloc) as zca eqn:Hzca. remember (gv _zcfree) as zcf eqn:Hzcf.
    forward. forward. forward.
    match goal with |- _ |-- ?G => replace G with (RA_break R) by (destruct R; reflexivity) end.
    rewrite HR. unfold case_post2. cbn [RA_normal].
    Exists (set_bad m M_far).
    apply andp_right; [apply prop_right; exact EB | ].
    rewrite loop_state_mt_eq. unfold loop_state_mt, mt_locals, mt_seps, mt_strm, strm_rep. frame_simpl.
    rewrite <- Hzca, <- Hzcf.
    entailer!. apply derives_refl.
  }
  assert (WIN: i_win (m_s m) = true /\ i_wsize (m_s m) = 2 ^ i_wbits (m_s m)).
  { destruct Hws as [E | E]; [ | exact E]. lia. }
  destruct WIN as [WIN WSZ].
  assert_PROP (isptr winp) as Pwin by (unfold win_rep; rewrite WIN; entailer!).
  rewrite WIN.
  forward.
  unfold abbreviate in MORE_COMMANDS. subst MORE_COMMANDS. apply semax_if_seq. forward_if.
  - mt_ur. forward. forward. rewrite sub_repr. forward. forward. forward.
    assert (WHF: i_whave (m_s m) = i_wsize (m_s m)).
    { destruct (Z.lt_ge_cases (i_whave (m_s m)) (i_wsize (m_s m))) as [Lt | Ge]; [ | lia].
      specialize (Hwv Lt). lia. }
    rewrite mt_from_win by (auto; rep_lia).
    forward.
    forward_if.
    + forward.
      mt_leaf FR m R (SWin (i_wsize (m_s m) - (i_offset (m_s m) - Zlength (m_ow m) - i_wnext (m_s m))))
        (i_length (m_s m)) C0.
    + forward.
      mt_leaf FR m R (SWin (i_wsize (m_s m) - (i_offset (m_s m) - Zlength (m_ow m) - i_wnext (m_s m))))
        (i_offset (m_s m) - Zlength (m_ow m) - i_wnext (m_s m)) C0.
  - forward. forward. forward.
    rewrite mt_from_win by (auto; rep_lia).
    forward.
    forward_if.
    + forward.
      mt_leaf FR m R (SWin (i_wnext (m_s m) - (i_offset (m_s m) - Zlength (m_ow m))))
        (i_length (m_s m)) C0.
    + forward.
      mt_leaf FR m R (SWin (i_wnext (m_s m) - (i_offset (m_s m) - Zlength (m_ow m))))
        (i_offset (m_s m) - Zlength (m_ow m)) C0.
Qed.

