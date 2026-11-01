(** * deflate_rle's body against [deflate_rle_spec] (DSpec.compress_spec, model DModel2.c_deflate_rle).
    Shared lemmas: CompressKit.v; the worked pattern (refill, tally, FLUSH_BLOCK, tail): Body_huff.v. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.trees.TLemmas.
Require Import Zlib.proof.deflate.Obligations.
Require Import Zlib.proof.deflate.CompressKit.
Require Import Zlib.proof.deflate.FlushKit.
Require Import Zlib.proof.deflate.RleKit.
Require Import Zlib.proof.deflate.RleScan.
Require Import Zlib.proof.deflate.RleDist.
Require Import Zlib.proof.deflate.RleLit.
Require Import Zlib.proof.deflate.RleTailKit Zlib.proof.deflate.RlePartF Zlib.proof.deflate.RlePartT.
Require Import Zlib.deflate.code.
#[export] Existing Instance DCS.CS.
Open Scope cmodel_scope.

(** Kernel conversion hints (see Body_huff.v): without them Qed takes > 10 min. *)
Local Strategy expand [c_deflate_rle].
Local Strategy opaque [loop loop2].

Ltac rl_unfold X := let c := eval cbv [X RL rsub f_deflate_rle fn_body] in X in change X with c.

(** [s->match_length = 0;] on dfull (its own Qed: the closing entailment is heavy for the kernel). *)
Lemma rle_ml0_ok {Espec : OracleKind} (p : dptrs) (pin pout : val) (ish : share) (R : list val) (msgv : val)
    (gv : globals) (flush : Z) (s : dstate) (z : strm) :
  semax Delta_rle
    (PROP () LOCAL (gvars gv; temp _s (p_s p); temp _flush (vi flush))
     SEP (dfull s z p pin pout ish R msgv gv; deflate_globals gv))
    R_ml0
    (normal_ret_assert
      (PROP () LOCAL (gvars gv; temp _s (p_s p); temp _flush (vi flush))
       SEP (dfull (set_d_match_length s 0) z p pin pout ish R msgv gv; deflate_globals gv))).
Proof.
  unfold R_ml0, RL, Delta_rle. cbv [rsub f_deflate_rle fn_body]. unfold dfull, dstate_at. Intros. abbreviate_semax.
  unfold match_at. Intros.
  forward.
  assert (Hr3 : dstate_ranges (set_d_match_length s 0))
    by (match goal with H : dstate_ranges s |- _ => dranges_tac H end).
  dfull_close_entail.
Qed.

Lemma body_deflate_rle : ob_deflate_rle.
Proof.
  unfold ob_deflate_rle.
  start_function.
  match goal with |- semax ?D _ _ _ => assert (HT : tycontext_sub Delta_rle D)
    by (unfold abbreviate in *; subst; apply tycontext_sub_refl) end.
  unfold c_deflate_rle in H0.
  inv_bind H0. destruct x as [[s1 z1] rx].
  apply loop_runs in Ha.
  assert_PROP (Zlength rest = z_avail_out z) as Hrest by (unfold dfull, out_space; entailer!).
  match goal with |- semax ?D ?P (Ssequence (Sloop _ _) ?M) ?Q =>
    change (semax D P (Ssequence (Sloop (Ssequence Sskip R_iter) Sskip) M) Q) end.
  forward_loop (EX s' : dstate, EX z' : strm, EX msgv' : val,
     PROP (runs (rle_body flush) (s', z') (s1, z1, rx); out_grow z z')
     LOCAL (gvars gv; temp _s (p_s p); temp _flush (vi flush))
     SEP (dfull s' z' p pin pout ish (rest_after z z' rest) msgv' gv; deflate_globals gv))
   break: (EX msgv' : val,
     PROP (rx = None; out_grow z z1)
     LOCAL (gvars gv; temp _s (p_s p); temp _flush (vi flush))
     SEP (dfull s1 z1 p pin pout ish (rest_after z z1 rest) msgv' gv; deflate_globals gv)).
  { (Exists s z msgv; unfold dfull; Intros; unfold out_space; Intros;
    rewrite rest_after_refl by auto; entailer!; apply out_grow_refl). }
  Intros s' z' msgv'. rename H1 into Hrun, H2 into Hgrow.
  destruct (runs_some _ _ _ Hrun) as [o Hbody]. pose proof Hbody as Ho. unfold rle_body in Ho.
  inv_bind Ho. rename x into rf, Ha0 into Hrf.
  rewrite rle_iter_eq. rl_unfold R_refill.
  unfold dfull, dstate_at. Intros.
  unfold match_at. Intros.
  forward.
  pose proof Hrf as Hrf0.
  forward_if (EX s2 : dstate, EX z2 : strm, EX msgv2 : val,
     PROP (c_refill need_rle flush s' z' = Some (inl (s2, z2)); out_grow z z2)
     LOCAL (gvars gv; temp _s (p_s p); temp _flush (vi flush))
     SEP (dfull s2 z2 p pin pout ish (rest_after z z2 rest) msgv2 gv; deflate_globals gv)).
  - (* lookahead <= MAX_MATCH: fill_window *)
    assert (El : need_rle s' = true).
    { unfold need_rle. apply Z.leb_le. try unfold DState.MAX_MATCH.
      match goal with Hc : 258 >= Int.unsigned _ |- _ => rewrite Int.unsigned_repr in Hc by drange end. lia. }
    unfold c_refill in Hrf. rewrite El in Hrf.
    inv_bind Hrf. destruct x as [s2 z2]. rename Ha0 into Hfw.
    sep_apply (match_at_fold s' p).
    sep_apply (dfull_fold s' z' p pin pout ish (rest_after z z' rest) msgv' gv); auto.
    sep_apply (dfull_split_in s' z' p pin pout ish (rest_after z z' rest) msgv' gv).
    Intros. forward_call (s', z', p, pin, ish, msgv', (s2, z2), gv).
    destruct (c_fill_window_out _ _ _ Hfw) as (Eo1 & Eo2 & Eo3). cbn [snd] in Eo1, Eo2, Eo3.
    pose proof (c_fill_window_grow _ _ _ Hfw) as Hg2. cbn [snd] in Hg2.
    cbn [fst snd]. Intros msgv2.
    sep_apply (dfull_join_in s2 z' z2 p pin pout ish (rest_after z z' rest) msgv2 gv Eo1 Eo2 Eo3).
    rewrite <- (rest_after_out z z' z2 rest Eo1).
    unfold dfull, dstate_at. Intros.
    unfold match_at. Intros.
    forward.
    assert (Hl2 : 0 <= d_lookahead s2 <= Int.max_unsigned) by drange.
    unfold DState.Z_NO_FLUSH in Hrf.
    destruct (andb (need_rle s2) (flush =? 0)) eqn:Eb.
    + (* return need_more *)
      apply andb_true_iff in Eb. destruct Eb as [En Ef]. apply Z.eqb_eq in Ef. subst flush.
      unfold need_rle in En. apply Z.leb_le in En. try unfold DState.MAX_MATCH in En.
      match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?S))) _ _ =>
        forward_if (PROPx P (LOCALx (temp _t'1 (vi 1) :: L) (SEPx S))) end.
      { forward. entailer!. }
      { try match goal with Hc : 258 < Int.unsigned _ |- _ => rewrite Int.unsigned_repr in Hc by drange end. lia. }
      forward_if.
      2: { match goal with Hc : Int.repr 1 = _ |- _ => discriminate Hc end. }
      inversion Hrf; subst rf. inversion Ho; subst o.
      apply (runs_exit_eq _ _ _ _ Hrun) in Hbody. inversion Hbody; subst s1 z1 rx.
      cbn in H0. inversion H0; subst r.
      forward.
      unfold dfull_post. cbn [fst snd]. Exists msgv2.
      sep_apply (match_at_fold s2 p).
      sep_apply (dfull_fold s2 z2 p pin pout ish (rest_after z z2 rest) msgv2 gv); auto.
    + match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?S))) _ _ =>
        forward_if (PROPx P (LOCALx (temp _t'1 (vi 0) :: L) (SEPx S))) end.
      { assert (Hf : flush <> 0).
        { intro E; subst flush. rewrite andb_true_r in Eb. unfold need_rle in Eb. apply Z.leb_gt in Eb.
          try unfold DState.MAX_MATCH in Eb.
          try match goal with Hc : 258 >= Int.unsigned _ |- _ => rewrite Int.unsigned_repr in Hc by drange end. lia. }
        forward. entailer!.
        rewrite Int.eq_false; [reflexivity|].
        intro E. apply repr_inj_signed in E; rep_lia. }
      { forward. entailer!. }
      forward_if.
      { match goal with Hc : Int.repr 0 <> _ |- _ => contradiction Hc; reflexivity end. }
      forward.
      forward_if.
      * (* lookahead == 0: break *)
        assert (El2 : d_lookahead s2 = 0) by first [assumption | repr_eq].
        rewrite El2 in Hrf. cbn in Hrf. inversion Hrf; subst rf. inversion Ho; subst o.
        apply (runs_exit_eq _ _ _ _ Hrun) in Hbody. inversion Hbody; subst s1 z1 rx.
        forward.
        Exists msgv2.
        sep_apply (match_at_fold s2 p).
        sep_apply (dfull_fold s2 z2 p pin pout ish (rest_after z z2 rest) msgv2 gv); auto.
        entailer!. eapply out_grow_trans; eauto.
      * forward.
        assert (El2 : d_lookahead s2 <> 0) by (intro E; rewrite E in *; contradiction).
        rewrite (proj2 (Z.eqb_neq _ _) El2) in Hrf. inversion Hrf; subst rf.
        Exists s2 z2 msgv2.
        sep_apply (match_at_fold s2 p).
        sep_apply (dfull_fold s2 z2 p pin pout ish (rest_after z z2 rest) msgv2 gv); auto.
        entailer!. eapply out_grow_trans; eauto.
  - (* lookahead > MAX_MATCH *)
    forward.
    assert (El : need_rle s' = false).
    { unfold need_rle. apply Z.leb_gt. try unfold DState.MAX_MATCH.
      match goal with Hc : 258 < Int.unsigned _ |- _ => rewrite Int.unsigned_repr in Hc by drange end. lia. }
    unfold c_refill in Hrf. rewrite El in Hrf. inversion Hrf; subst rf.
    Exists s' z' msgv'.
    sep_apply (match_at_fold s' p).
    sep_apply (dfull_fold s' z' p pin pout ish (rest_after z z' rest) msgv' gv); auto.
    entailer!.
  - (* the rest of the iteration *)
    Intros s2 z2 msgv2.
    match goal with E : c_refill _ _ _ _ = Some (inl _) |- _ => rewrite E in Hrf0 end.
    inversion Hrf0; subst rf. clear Hrf0 Hrf.
    rewrite rle_step_eq in Ho. cbv zeta in Ho.
    inv_bind Ho. rename x into s4, Ha0 into Hscan.
    (* s->match_length = 0 *)
    unfold MORE_COMMANDS, abbreviate. apply -> seq_assoc.
    eapply rl_seq; [exact HT | apply andp_left2, derives_refl
                   | apply (rle_ml0_ok p pin pout ish _ msgv2 gv flush s2 z2) | ].
    (* the run scan *)
    apply -> seq_assoc.
    eapply rl_seq; [exact HT | apply andp_left2, derives_refl
                   | apply (rle_scan_ok _ p pin pout ish _ msgv2 gv flush _ s4 z2 Hscan) | ].
    (* the match or the literal *)
    apply -> seq_assoc.
    inv_bind Ho. destruct x as [sq bf]. rename Ha0 into Htl.
    rl_unfold R_tally.
    unfold dfull, dstate_at. Intros. unfold match_at. Intros.
    forward.
    assert (Hml : 0 <= d_match_length s4 <= Int.max_unsigned) by drange.
    sep_apply (match_at_fold s4 p).
    sep_apply (dfull_fold s4 z2 p pin pout ish (rest_after z z2 rest) msgv2 gv); auto.
    forward_if (PROP () LOCAL (temp _bflush (vi (Z.b2z bf)); gvars gv; temp _s (p_s p); temp _flush (vi flush))
                SEP (dfull sq z2 p pin pout ish (rest_after z z2 rest) msgv2 gv; deflate_globals gv)).
    + try rewrite Int.unsigned_repr in * by rep_lia.
      replace (d_match_length s4 >=? MIN_MATCH) with true in Htl
        by (symmetry; rewrite Z.geb_leb; apply Z.leb_le; unfold MIN_MATCH; lia).
      match goal with |- semax ?D ?P _ ?Q => change (semax D P R_dist Q) end.
      eapply semax_pre; [| eapply semax_Delta_subsumption; [exact HT | exact (rle_dist_ok _ p pin pout ish _ msgv2 gv flush s4 sq z2 bf Htl)]].
      entailer!.
    + try rewrite Int.unsigned_repr in * by rep_lia.
      replace (d_match_length s4 >=? MIN_MATCH) with false in Htl
        by (symmetry; rewrite Z.geb_leb; apply Z.leb_gt; unfold MIN_MATCH; lia).
      match goal with |- semax ?D ?P _ ?Q => change (semax D P R_lit Q) end.
      eapply semax_pre; [| eapply semax_Delta_subsumption; [exact HT | exact (rle_lit_ok _ p pin pout ish _ msgv2 gv flush s4 sq z2 bf Htl)]].
      entailer!.
    + (* if (bflush) FLUSH_BLOCK(s, 0); *)
      unfold abbreviate in MORE_COMMANDS; subst MORE_COMMANDS.
      repeat match goal with X := @abbreviate ret_assert _ |- _ => unfold abbreviate in X; subst X end.
      eapply semax_Delta_subsumption; [exact HT |].
      apply (rle_ifbf_part p pin pout ish rest gv flush z r s1 z1 rx s' z' o sq z2 msgv2 bf
               H Hrest H0 Hrun Hbody Ho ltac:(assumption)).
  - (* after the loop: s->insert = 0; the tail *)
    Intros msgv1. subst rx.
    change (c_deflate_tail (set_d_insert s1 0) z1 flush = Some r) in H0.
    repeat match goal with
    | X := @abbreviate statement _ |- _ => unfold abbreviate in X; subst X
    | X := @abbreviate ret_assert _ |- _ => unfold abbreviate in X; subst X
    end.
    eapply semax_Delta_subsumption; [exact HT |].
    eapply rle_tail_part; eassumption.
Qed.
