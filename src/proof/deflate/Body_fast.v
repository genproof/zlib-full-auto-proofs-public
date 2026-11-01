(** * deflate_fast's body against [deflate_fast_spec] (DSpec.compress_spec, model DModel2.c_deflate_fast).
    Shared lemmas: CompressKit.v; the worked pattern (refill, tally, FLUSH_BLOCK, tail): Body_huff.v.
    The statements of the loop body after the refill are parts (FastKit.v, proved in Fast*.v). *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.trees.TLemmas.
Require Import Zlib.proof.deflate.Obligations.
Require Import Zlib.proof.deflate.CompressKit.
Require Import Zlib.proof.deflate.FlushKit.
Require Import Zlib.proof.deflate.FastKit.
Require Import Zlib.proof.deflate.FastIns1 Zlib.proof.deflate.FastIns2 Zlib.proof.deflate.FastLm
  Zlib.proof.deflate.FastDist Zlib.proof.deflate.FastInsl Zlib.proof.deflate.FastUh Zlib.proof.deflate.FastAfter
  Zlib.proof.deflate.FastLit.
Require Import Zlib.proof.deflate.FastTailKit Zlib.proof.deflate.FastPartF Zlib.proof.deflate.FastPartT.
Require Import Zlib.deflate.code.
#[export] Existing Instance DCS.CS.
Open Scope cmodel_scope.

(** Kernel conversion hints (see Body_huff.v): without them Qed takes > 10 min. *)
Local Strategy expand [c_deflate_fast].
Local Strategy opaque [loop loop2].

(** ** The model of one iteration, cut as the parts *)
Definition fast_match_m (s : dstate) : option (dstate * bool) :=
  if d_match_length s >=? MIN_MATCH then
    let* (s, bf) := c_dtally_dist s (u32 (d_strstart s - d_match_start s)) (u32 (d_match_length s - MIN_MATCH)) in
    let* s := fast_after_m s in Some (s, bf)
  else fast_lit_m s.

Definition fast_step (s : dstate) (z : strm) : option ((dstate * strm) + dexit) :=
  let* (s, h) := c_insert_head s in
  let* s := fast_lm_m s h in
  let* (s, bf) := fast_match_m s in
  c_bflush s z bf.

Lemma df_step_eq s z : df_step s z = fast_step s z.
Proof.
  unfold df_step, fast_step, fast_match_m, fast_lm_m, fast_after_m, fast_insl_m, fast_uh_m, fast_lit_m.
  destruct (c_insert_head s) as [[s1 h]|]; cbn [bind]; auto.
  match goal with |- bind ?x _ = bind ?x _ => destruct x as [s2|]; cbn [bind]; auto end.
  match goal with |- bind ?x ?f = bind ?y ?g => assert (E : x = y); [|rewrite E; reflexivity] end.
  destruct (d_match_length s2 >=? MIN_MATCH); cbv beta iota; [|reflexivity].
  match goal with |- bind ?x _ = bind ?x _ => destruct x as [[s3 bf]|]; cbn [bind]; auto end.
  match goal with |- context [if ?b then _ else _] => destruct b end; cbv beta iota;
    repeat (match goal with |- context [bind ?x _] => destruct x; cbn [bind] end); reflexivity.
Qed.

Lemma df_body_eq flush s z : df_body flush (s, z) =
  let* r := c_refill need_min_lookahead flush s z in
  match r with inr e => Some (inr e) | inl (s, z) => fast_step s z end.
Proof.
  unfold df_body. destruct (c_refill _ _ _ _) as [[[s' z']|e]|]; cbn [bind]; auto. apply df_step_eq.
Qed.

Lemma fast_rd_inv l i x : rd l i = Some x -> 0 <= i < Zlength l /\ x = Znth i l.
Proof.
  unfold rd, in_range. destruct (andb (0 <=? i) (i <? Zlength l)) eqn:E; [|discriminate].
  apply andb_prop in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  intros H; inversion H; auto.
Qed.

Lemma c_insert_string_h s str s' h : dstate_ranges s -> c_insert_string s str = Some (s', h) -> 0 <= h < 65536.
Proof.
  intros Hr H. unfold c_insert_string in H.
  inv_bind H. inv_bind H. inv_bind H. cbn [d_head d_ins_h set_d_ins_h] in Ha1.
  apply fast_rd_inv in Ha1. destruct Ha1 as [Hi ->].
  inv_bind H. inv_bind H. inversion H; subst; clear H.
  open_dranges Hr.
  match goal with HF : Forall _ (d_head s) |- _ => rewrite Forall_forall in HF; apply HF end.
  apply Znth_In. lia.
Qed.

Lemma c_insert_head_h s s' h : dstate_ranges s -> c_insert_head s = Some (s', h) -> 0 <= h < 65536.
Proof.
  intros Hr H. unfold c_insert_head in H. destruct (d_lookahead s >=? MIN_MATCH).
  - eapply c_insert_string_h; eauto.
  - inversion H; subst. unfold NIL. lia.
Qed.

(** A part lemma as a whole branch, with a weaker postcondition. *)
Lemma fa_last2 {Espec : OracleKind} Delta P P' Q Q' c R :
  tycontext_sub Delta_fast Delta -> ENTAIL Delta, P |-- P' ->
  semax Delta_fast P' c (normal_ret_assert Q) -> ENTAIL Delta, Q |-- Q' -> semax Delta P c (overridePost Q' R).
Proof.
  intros HT HP H1 HQ. apply (fa_apply Delta P P' c Q' R HP).
  eapply semax_post_flipped'; [eapply semax_Delta_subsumption; eauto | exact HQ].
Qed.

Lemma fa_last_n {Espec : OracleKind} Delta P P' Q Q' c :
  tycontext_sub Delta_fast Delta -> ENTAIL Delta, P |-- P' ->
  semax Delta_fast P' c (normal_ret_assert Q) -> ENTAIL Delta, Q |-- Q' -> semax Delta P c (normal_ret_assert Q').
Proof.
  intros HT HP H1 HQ. eapply semax_pre; [exact HP|].
  eapply semax_post_flipped'; [eapply semax_Delta_subsumption; eauto | exact HQ].
Qed.

(** Apply a part lemma [H] to a whole branch (normal or overridden postcondition). *)
Ltac fa_last HT H :=
  first [ eapply fa_last_n; [exact HT | | exact H | ]
        | eapply fa_last2; [exact HT | | exact H | ] ].

(** The impossible branch of an [if] on a constant-valued temp. *)
Ltac fa_contra :=
  exfalso; first [ discriminate | match goal with Hc : _ <> _ |- _ => exact (Hc eq_refl) end ].

(** Expose the statement and postcondition abbreviated by Floyd (to apply a part lemma). *)
Ltac fa_unabbrev :=
  repeat match goal with
  | X := @abbreviate statement _ |- _ => unfold abbreviate in X; subst X
  | X := @abbreviate ret_assert _ |- _ => unfold abbreviate in X; subst X
  end.

Lemma body_deflate_fast : ob_deflate_fast.
Proof.
  unfold ob_deflate_fast.
  start_function.
  match goal with |- semax ?D _ _ _ => assert (HT : tycontext_sub Delta_fast D)
    by (unfold abbreviate in *; subst; apply tycontext_sub_refl) end.
  unfold c_deflate_fast in H0.
  inv_bind H0. destruct x as [[s1 z1] rx].
  apply loop_runs in Ha.
  assert_PROP (Zlength rest = z_avail_out z) as Hrest by (unfold dfull, out_space; entailer!).
  forward_loop (EX s' : dstate, EX z' : strm, EX msgv' : val,
     PROP (runs (df_body flush) (s', z') (s1, z1, rx); out_grow z z')
     LOCAL (gvars gv; temp _s (p_s p); temp _flush (vi flush))
     SEP (dfull s' z' p pin pout ish (rest_after z z' rest) msgv' gv; deflate_globals gv))
   break: (EX msgv' : val,
     PROP (rx = None; out_grow z z1)
     LOCAL (gvars gv; temp _s (p_s p); temp _flush (vi flush))
     SEP (dfull s1 z1 p pin pout ish (rest_after z z1 rest) msgv' gv; deflate_globals gv)).
  { (Exists s z msgv; unfold dfull; Intros; unfold out_space; Intros;
    rewrite rest_after_refl by auto; entailer!; apply out_grow_refl). }
  Intros s' z' msgv'. rename H1 into Hrun, H2 into Hgrow.
  destruct (runs_some _ _ _ Hrun) as [o Hbody]. pose proof Hbody as Ho. rewrite df_body_eq in Ho.
  inv_bind Ho. rename x into rf, Ha0 into Hrf.
  unfold dfull, dstate_at. Intros.
  unfold match_at. Intros.
  forward.
  forward_if (EX s2 : dstate, EX z2 : strm, EX msgv2 : val,
     PROP (c_refill need_min_lookahead flush s' z' = Some (inl (s2, z2)); out_grow z z2)
     LOCAL (gvars gv; temp _s (p_s p); temp _flush (vi flush))
     SEP (dfull s2 z2 p pin pout ish (rest_after z z2 rest) msgv2 gv; deflate_globals gv)).
  - (* lookahead < MIN_LOOKAHEAD: fill_window *)
    assert (En : need_min_lookahead s' = true).
    { unfold need_min_lookahead. change DState.MIN_LOOKAHEAD with 262. apply Z.ltb_lt.
      rewrite Int.unsigned_repr in * by drange. lia. }
    unfold c_refill in Hrf. rewrite En in Hrf.
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
    assert (Hla2 : 0 <= d_lookahead s2 <= Int.max_unsigned) by drange.
    match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?S))) _ _ =>
      forward_if (PROPx P (LOCALx (temp _t'1 (Vint (Int.repr (Z.b2z (andb (need_min_lookahead s2) (flush =? 0)))))
        :: L) (SEPx S))) end.
    { forward. entailer!. unfold need_min_lookahead. change DState.MIN_LOOKAHEAD with 262.
      rewrite (proj2 (Z.ltb_lt _ 262)) by lia. cbn [andb]. rewrite f5_int_eq0 by assumption.
      destruct (flush =? 0); reflexivity. }
    { forward. entailer!. unfold need_min_lookahead. change DState.MIN_LOOKAHEAD with 262.
      rewrite (proj2 (Z.ltb_ge _ 262)) by lia. reflexivity. }
    change DState.Z_NO_FLUSH with 0 in Hrf.
    destruct (andb (need_min_lookahead s2) (flush =? 0)) eqn:EB.
    + (* return need_more *)
      cbv iota in Hrf. inversion Hrf; subst rf. inversion Ho; subst o.
      apply (runs_exit_eq _ _ _ _ Hrun) in Hbody. inversion Hbody; subst s1 z1 rx.
      cbn in H0. inversion H0; subst r.
      forward_if.
      * forward.
        unfold dfull_post. cbn [fst snd]. Exists msgv2.
        sep_apply (match_at_fold s2 p).
        sep_apply (dfull_fold s2 z2 p pin pout ish (rest_after z z2 rest) msgv2 gv); auto.
      * exfalso. match goal with Hc : Int.repr 1 = Int.zero |- _ => discriminate Hc end.
    + cbv iota in Hrf.
      forward_if.
      { exfalso. match goal with Hc : Int.repr 0 <> Int.zero |- _ => apply Hc; reflexivity end. }
      forward.
      forward_if.
      * (* lookahead still 0: break *)
        assert (El2 : d_lookahead s2 = 0) by (first [assumption | repr_eq]).
        rewrite El2 in Hrf. cbn in Hrf. inversion Hrf; subst rf. inversion Ho; subst o.
        apply (runs_exit_eq _ _ _ _ Hrun) in Hbody. inversion Hbody; subst s1 z1 rx.
        forward.
        Exists msgv2.
        sep_apply (match_at_fold s2 p).
        sep_apply (dfull_fold s2 z2 p pin pout ish (rest_after z z2 rest) msgv2 gv); auto.
        entailer!. eapply out_grow_trans; eauto.
      * forward.
        assert (El2 : d_lookahead s2 <> 0) by (first [assumption | intro E; rewrite E in *; contradiction]).
        rewrite (proj2 (Z.eqb_neq _ _) El2) in Hrf.
        Exists s2 z2 msgv2.
        sep_apply (match_at_fold s2 p).
        sep_apply (dfull_fold s2 z2 p pin pout ish (rest_after z z2 rest) msgv2 gv); auto.
        entailer!. split; [unfold c_refill; rewrite En, Hfw; cbn; change DState.Z_NO_FLUSH with 0;
          rewrite EB, (proj2 (Z.eqb_neq _ _) El2); auto|].
        eapply out_grow_trans; eauto.
  - (* lookahead >= MIN_LOOKAHEAD *)
    forward.
    assert (En : need_min_lookahead s' = false).
    { unfold need_min_lookahead. change DState.MIN_LOOKAHEAD with 262. apply Z.ltb_ge.
      rewrite Int.unsigned_repr in * by drange. lia. }
    Exists s' z' msgv'.
    sep_apply (match_at_fold s' p).
    sep_apply (dfull_fold s' z' p pin pout ish (rest_after z z' rest) msgv' gv); auto.
    entailer!. unfold c_refill. rewrite En. auto.
  - (* the rest of the iteration *)
    Intros s2 z2 msgv2.
    match goal with E : c_refill _ _ _ _ = Some (inl _) |- _ => rewrite E in Hrf end.
    inversion Hrf; subst rf. clear Hrf. cbv iota in Ho.
    unfold fast_step in Ho.
    inv_bind Ho. destruct x as [s3 h]. rename Ha0 into Hins.
    inv_bind Ho. rename x into s4, Ha0 into Hlm.
    inv_bind Ho. destruct x as [s5 bf]. rename Ha0 into Hm.
    assert_PROP (dstate_ranges s2) as Hr2 by (unfold dfull, dstate_at; entailer!).
    pose proof (c_insert_head_h _ _ _ Hr2 Hins) as Hh.
    forward.
    unfold dfull, dstate_at. Intros. unfold match_at. Intros.
    forward.
    forward_if (fa (temp _hash_head (vi h) :: fa_base p flush gv) s3 z2 p pin pout ish (rest_after z z2 rest) msgv2 gv).
    + (* lookahead >= MIN_MATCH: INSERT_STRING *)
      assert (Ei : c_insert_string s2 (d_strstart s2) = Some (s3, h)).
      { unfold c_insert_head in Hins. rewrite (proj2 (Z.geb_le _ _)) in Hins; [exact Hins|].
        rewrite Int.unsigned_repr in * by drange. unfold MIN_MATCH. lia. }
      sep_apply (match_at_fold s2 p).
      sep_apply (dfull_fold s2 z2 p pin pout ish (rest_after z z2 rest) msgv2 gv); auto.
      fa_unabbrev.
      eapply fa_last_n; [exact HT | | exact (fast_ins1_ok Espec s2 s3 z2 p pin pout ish (rest_after z z2 rest)
                                               msgv2 gv flush h Ei) | apply ENTAIL_refl].
      unfold fa, fa_base. entailer!.
    + (* no insertion *)
      assert (Hl : d_lookahead s2 < 3) by (rewrite Int.unsigned_repr in * by drange; lia).
      unfold c_insert_head in Hins. destruct (Z.geb_spec (d_lookahead s2) MIN_MATCH) as [Hge|Hlt];
        [unfold MIN_MATCH in Hge; lia|].
      inversion Hins; subst s3 h. clear Hins.
      forward.
      sep_apply (match_at_fold s2 p).
      sep_apply (dfull_fold s2 z2 p pin pout ish (rest_after z z2 rest) msgv2 gv); auto.
      unfold fa, fa_base, NIL. entailer!.
    + (* the longest_match call *)
      fa_unabbrev. apply -> seq_assoc.
      eapply fa_seq; [exact HT | |
        exact (fast_lm_ok Espec s3 s4 z2 p pin pout ish (rest_after z z2 rest) msgv2 gv flush h Hh Hlm) | ];
        [unfold fa, fa_base; entailer! | ].
      unfold fa, fa_base. abbreviate_semax.
      unfold dfull, dstate_at. Intros. unfold match_at. Intros.
      forward.
      forward_if (fa (temp _bflush (vi (Z.b2z bf)) :: fa_base p flush gv) s5 z2 p pin pout ish (rest_after z z2 rest)
                    msgv2 gv).
      * (* a match *)
        unfold fast_match_m in Hm. rewrite (proj2 (Z.geb_le _ _)) in Hm
          by (rewrite Int.unsigned_repr in * by drange; unfold MIN_MATCH; lia).
        inv_bind Hm. destruct x as [s4' bf']. rename Ha0 into Hd.
        inv_bind Hm. rename x into s5', Ha0 into Haf. inversion Hm; subst s5' bf'; clear Hm.
        sep_apply (match_at_fold s4 p).
        sep_apply (dfull_fold s4 z2 p pin pout ish (rest_after z z2 rest) msgv2 gv); auto.
        fa_unabbrev.
        eapply fa_seq; [exact HT | |
          exact (fast_dist_ok Espec s4 s4' z2 p pin pout ish (rest_after z z2 rest) msgv2 gv flush bf Hd) | ];
          [unfold fa, fa_base; entailer! | ].
        fa_last HT (fast_after_ok (fast_insl_ok fast_ins2_ok) fast_uh_ok Espec s4' s5 z2 p pin pout ish
                      (rest_after z z2 rest) msgv2 gv flush (vi (Z.b2z bf)) Haf);
          apply ENTAIL_refl.
      * (* a literal *)
        unfold fast_match_m in Hm. destruct (Z.geb_spec (d_match_length s4) MIN_MATCH) as [Hge|Hlt];
          [rewrite Int.unsigned_repr in * by drange; unfold MIN_MATCH in Hge; lia|].
        sep_apply (match_at_fold s4 p).
        sep_apply (dfull_fold s4 z2 p pin pout ish (rest_after z z2 rest) msgv2 gv); auto.
        fa_unabbrev.
        fa_last HT (fast_lit_ok Espec s4 s5 z2 p pin pout ish (rest_after z z2 rest) msgv2 gv flush bf Hm);
          [unfold fa, fa_base; entailer! | apply ENTAIL_refl].
      * (* if (bflush) FLUSH_BLOCK(s, 0); *)
        fa_unabbrev.
        rewrite <- semax_seq_skip.
        apply (fast_ifbf_part p pin pout ish rest gv flush z r s1 z1 rx s' z' o s5 z2 msgv2 bf
                 H Hrest H0 Hrun Hbody Ho ltac:(assumption)).
  - (* after the loop: s->insert = strstart < MIN_MATCH-1 ? strstart : MIN_MATCH-1; the tail *)
    Intros msgv1. subst rx.
    change (c_deflate_tail (set_insert_end s1) z1 flush = Some r) in H0.
    fa_unabbrev.
    eapply fast_tail_part; eassumption.
Qed.
