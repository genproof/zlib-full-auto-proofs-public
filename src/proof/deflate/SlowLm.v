(** * deflate_slow: prev_length / prev_match / match_length, longest_match and the FILTERED / TOO_FAR test
    ([S_prev; S_ml; S_lmb], model [dsl_prep]). Kit: SlowKit.v. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.trees.TLemmas.
Require Import Zlib.proof.deflate.CompressKit.
Require Import Zlib.proof.deflate.SlowKit.
Require Import Zlib.deflate.code.
#[export] Existing Instance DCS.CS.
Open Scope cmodel_scope.


Definition lm_s1 (s : dstate) : dstate :=
  set_d_match_length (set_d_prev_match (set_d_prev_length s (d_match_length s)) (d_match_start s)) (MIN_MATCH - 1).

Lemma lm_prev_frag {Espec : OracleKind} (p : dptrs) (pin pout : val) (ish : share) (R : list val) (msgv : val)
    (gv : globals) (flush : Z) (s : dstate) (z : strm) (hh : Z) :
  semax Delta_sl
    (PROP () LOCAL (temp _hash_head (vi hh); gvars gv; temp _s (p_s p); temp _flush (vi flush))
     SEP (dfull s z p pin pout ish R msgv gv; deflate_globals gv))
    (Ssequence S_prev S_ml)
    (normal_ret_assert
      (PROP () LOCAL (temp _hash_head (vi hh); gvars gv; temp _s (p_s p); temp _flush (vi flush))
       SEP (dfull (lm_s1 s) z p pin pout ish R msgv gv; deflate_globals gv))).
Proof.
  unfold dfull, dstate_at. Intros. unfold match_at. Intros.
  show_sl. abbreviate_semax.
  forward. forward. forward. forward. forward.
  assert (Hr : dstate_ranges (lm_s1 s)) by (unfold lm_s1, MIN_MATCH; dranges_tac H2).
  replace (d_trm (lm_s1 s)) with (d_trm s) by reflexivity.
  unfold lm_s1, win_at, hash_at, cfg_at, stat_at, MIN_MATCH. dsimpl. entailer!.
Qed.


Lemma lm_ltu_bool a b : 0 <= a <= Int.max_unsigned -> 0 <= b <= Int.max_unsigned ->
  bool2val (Int.ltu (Int.repr a) (Int.repr b)) = Val.of_bool (a <? b).
Proof.
  intros. unfold Int.ltu. rewrite !Int.unsigned_repr by lia.
  destruct (zlt a b) as [E|E]; [rewrite (proj2 (Z.ltb_lt _ _) E) | rewrite (proj2 (Z.ltb_ge _ _) (Z.ge_le _ _ E))]; reflexivity.
Qed.

Lemma lm_test6 s h :
  bool2val (negb (Int.ltu (Int.repr (d_w_size s - (258 + 3 + 1))) (Int.repr (d_strstart s - h)))) =
  Val.of_bool (u32 (d_strstart s - h) <=? max_dist s).
Proof.
  unfold max_dist, MAX_DIST. change DState.MIN_LOOKAHEAD with (258 + 3 + 1).
  unfold Int.ltu. rewrite <- (repr_u32 (d_w_size s - _)), <- (repr_u32 (d_strstart s - h)), !unsigned_repr_u32.
  destruct (zlt _ _) as [E|E]; [rewrite (proj2 (Z.leb_gt _ _) E) | rewrite (proj2 (Z.leb_le _ _) (Z.ge_le _ _ E))];
  reflexivity.
Qed.

Lemma lm_gt_bool x : bool2val (Int.ltu (Int.repr 4096) (Int.repr x)) = Val.of_bool (u32 x >? 4096).
Proof.
  unfold Int.ltu. rewrite <- (repr_u32 x), unsigned_repr_u32. rewrite Int.unsigned_repr by rep_lia.
  destruct (zlt 4096 (u32 x)) as [E|E];
    [rewrite (proj2 (Z.gtb_lt _ _) E) | rewrite Z.gtb_ltb, (proj2 (Z.ltb_ge _ _) (Z.ge_le _ _ E))]; reflexivity.
Qed.

Definition lm_b5 (s1 : dstate) (hh : Z) : bool :=
  negb (hh =? NIL) && (d_prev_length s1 <? d_max_lazy_match s1).
Definition lm_b6 (s1 : dstate) (hh : Z) : bool :=
  lm_b5 s1 hh && (u32 (d_strstart s1 - hh) <=? max_dist s1).
Definition lm_b4 (s3 : dstate) : bool :=
  (d_match_length s3 <=? 5) &&
  ((d_strategy s3 =? Z_FILTERED) ||
   ((d_match_length s3 =? MIN_MATCH) && (u32 (d_strstart s3 - d_match_start s3) >? TOO_FAR))).
Definition lm_post (s2 : dstate) (ml : Z) : option dstate :=
  let s := set_d_match_length s2 ml in
  if lm_b4 s then Some (set_d_match_length s (MIN_MATCH - 1)) else Some s.

Lemma dsl_prep_eq s hh : dsl_prep s hh =
  if lm_b6 (lm_s1 s) hh then let* (s2, ml) := c_longest_match (lm_s1 s) hh in lm_post s2 ml else Some (lm_s1 s).
Proof. reflexivity. Qed.

Lemma lm_dstate_fold s p gv : dstate_ranges s ->
  trees_at (d_trm s) (p_s p) (p_pbuf p) (p_strm p) gv * win_at s p * hash_at s p * match_at s p * cfg_at s p *
  stat_at s p |-- dstate_at s p gv.
Proof. intros. unfold dstate_at. entailer!. Qed.

Ltac lm_crush E :=
  repeat match type of E with
  | bind ?x _ = _ => let Ex := fresh "Ex" in destruct x eqn:Ex; cbn [bind] in E; [|discriminate E]
  | (if ?b then _ else _) = _ => let Eb := fresh "Eb" in destruct b eqn:Eb
  | (match ?v with pair _ _ => _ end) = _ => destruct v
  | Some _ = Some _ => inversion E; subst; clear E
  end.

Lemma lm_body_best' nice limit a o : lm_body nice limit a = Some o -> 0 <= lm_best a ->
  match o with inl a' => 0 <= lm_best a' | inr (b, _) => 0 <= b end.
Proof.
  intros E H0. unfold lm_body in E. cbv zeta in E. lm_crush E; cbn [lm_best] in *; try lia;
  repeat match goal with Eb : (_ >? _) = true |- _ => apply Z.gtb_lt in Eb end; lia.
Qed.

Lemma lm_runs_best' nice limit a r : runs (lm_body nice limit) a r -> 0 <= lm_best a -> 0 <= fst r.
Proof.
  induction 1 as [a r E|a a' r E _ IH]; intros H0; pose proof (lm_body_best' _ _ _ _ E H0) as Hb.
  - destruct r; exact Hb.
  - exact (IH Hb).
Qed.

Lemma lm_range s h s2 ml : c_longest_match s h = Some (s2, ml) -> dstate_ranges s -> dstate_ranges s2 ->
  0 <= ml <= Int.max_unsigned.
Proof.
  intros E Hr Hr2. unfold c_longest_match in E.
  inv_bind E. inv_bind E. inv_bind E. inv_bind E. inv_bind E. inv_bind E. destruct x4 as [best s3].
  apply loop_runs, lm_runs_best' in Ha4; cbn [lm_best fst] in Ha4; [|cbn [lm_best]; clear Hr2; drange].
  inversion E; subst. clear Hr. destruct (best <=? d_lookahead s2) eqn:Eb; [apply Z.leb_le in Eb|]; drange.
Qed.

(** trees_rest without the level / strategy fields (kept folded: it mentions trees.c's descriptors). *)
Definition lm_tr_rest (t : tstate) (sp : val) (gv : globals) : mpred :=
  (bltree_at (tr_bltree t) sp *
   ldesc_at (field_address t_ds (DOT Zlib.trees.code._dyn_ltree) sp) (tr_lmax t) (gv Zlib.trees.code._static_l_desc) sp *
   ddesc_at (field_address t_ds (DOT Zlib.trees.code._dyn_dtree) sp) (tr_dmax t) (gv Zlib.trees.code._static_d_desc) sp *
   bldesc_at (field_address t_ds (DOT Zlib.trees.code._bl_tree) sp) (tr_blmax t) (gv Zlib.trees.code._static_bl_desc) sp *
   work_at (tr_wk t) sp)%logic.

Lemma lm_trees_rest_split t sp strmp gv : trees_rest t sp strmp gv = (lm_tr_rest t sp gv * lvl_at t sp)%logic.
Proof. reflexivity. Qed.

(** The tail of the then-branch: [if (s->match_length <= 5 && (...)) s->match_length = MIN_MATCH-1;] *)
Definition S_lmt := SL [0;0;1;1;1;1;1;1;0;1;1;1]%nat.

Lemma lm_tail_frag {Espec : OracleKind} (p : dptrs) (pin pout : val) (ish : share) (R : list val) (msgv : val)
    (gv : globals) (flush : Z) (s3 : dstate) (z : strm) (hh : Z) :
  semax Delta_sl
    (PROP () LOCAL (temp _hash_head (vi hh); gvars gv; temp _s (p_s p); temp _flush (vi flush))
     SEP (dfull s3 z p pin pout ish R msgv gv; deflate_globals gv))
    S_lmt
    (normal_ret_assert
      (PROP () LOCAL (temp _hash_head (vi hh); gvars gv; temp _s (p_s p); temp _flush (vi flush))
       SEP (dfull (if lm_b4 s3 then set_d_match_length s3 (MIN_MATCH - 1) else s3) z p pin pout ish R msgv gv;
            deflate_globals gv))).
Proof.
  unfold dfull, dstate_at. Intros.
  unfold S_lmt. show_sl. abbreviate_semax.
  unfold match_at. Intros. forward.
  forward_if (PROP ()
     LOCAL (temp _t'4 (Val.of_bool (lm_b4 s3)); temp _hash_head (vi hh); gvars gv; temp _s (p_s p);
            temp _flush (vi flush))
     SEP (trees_at (d_trm s3) (p_s p) (p_pbuf p) (p_strm p) gv; win_at s3 p; hash_at s3 p; match_at s3 p;
          cfg_at s3 p; stat_at s3 p; strm_at z (p_s p) (p_strm p) pin pout msgv gv; in_obj ish z pin;
          out_space z pout R; deflate_globals gv)).
  - rewrite trees_at_open, lm_trees_rest_split. unfold lvl_at. Intros.
    forward.
    assert (Hml5 : d_match_length s3 <= 5) by (rewrite Int.unsigned_repr in H3 by drange; lia).
    change (tr_strategy (fst (d_trm s3))) with (d_strategy s3) in *.
    change (tr_strategy (d_tr s3)) with (d_strategy s3) in *.
    forward_if.
    + forward.
      assert (Eb : lm_b4 s3 = true).
      { unfold lm_b4, Z_FILTERED. rewrite H6, (proj2 (Z.leb_le _ _) Hml5). reflexivity. }
      rewrite Eb. rewrite trees_at_open, lm_trees_rest_split. unfold lvl_at, match_at. entailer!.
    + forward. forward_if.
      * forward. forward. forward. forward. forward.
        apply repr_inj_unsigned in H7; [|drange|rep_lia].
        rewrite lm_gt_bool.
        assert (Eb : lm_b4 s3 = (u32 (d_strstart s3 - d_match_start s3) >? 4096)).
        { unfold lm_b4, Z_FILTERED, MIN_MATCH, TOO_FAR.
          rewrite (proj2 (Z.leb_le _ _) Hml5), (proj2 (Z.eqb_neq _ _) H6), H7. reflexivity. }
        rewrite Eb. rewrite trees_at_open, lm_trees_rest_split. unfold lvl_at, match_at. entailer!.
      * forward. forward.
        assert (Eb : lm_b4 s3 = false).
        { unfold lm_b4, Z_FILTERED, MIN_MATCH, TOO_FAR.
          rewrite (proj2 (Z.leb_le _ _) Hml5), (proj2 (Z.eqb_neq _ _) H6).
          rewrite (proj2 (Z.eqb_neq (d_match_length s3) 3)) by (intro E; apply H7; rewrite E; reflexivity).
          reflexivity. }
        rewrite Eb. rewrite trees_at_open, lm_trees_rest_split. unfold lvl_at, match_at. entailer!.
  - forward.
    assert (Eb : lm_b4 s3 = false).
    { unfold lm_b4. rewrite Int.unsigned_repr in H3 by drange.
      assert (Hg : 5 < d_match_length s3) by lia. rewrite (proj2 (Z.leb_gt _ _) Hg). reflexivity. }
    rewrite Eb. unfold match_at. entailer!.
  - unfold match_at. Intros. forward_if.
    + forward.
      destruct (lm_b4 s3) eqn:Eb; [|inversion H3].
      assert (Hr : dstate_ranges (set_d_match_length s3 (MIN_MATCH - 1))) by (unfold MIN_MATCH; dranges_tac H2).
      replace (d_trm (set_d_match_length s3 (MIN_MATCH - 1))) with (d_trm s3) by reflexivity.
      unfold win_at, hash_at, cfg_at, stat_at, match_at, MIN_MATCH. dsimpl. entailer!.
    + forward.
      destruct (lm_b4 s3) eqn:Eb; [inversion H3|].
      unfold match_at. entailer!.
Qed.

Lemma lm_cond_frag {Espec : OracleKind} (p : dptrs) (pin pout : val) (ish : share) (R : list val) (msgv : val)
    (gv : globals) (flush : Z) (s1 s' : dstate) (z : strm) (hh : Z) :
  0 <= hh < 65536 ->
  (if lm_b6 s1 hh then let* (s2, ml) := c_longest_match s1 hh in lm_post s2 ml else Some s1) = Some s' ->
  semax Delta_sl
    (PROP () LOCAL (temp _hash_head (vi hh); gvars gv; temp _s (p_s p); temp _flush (vi flush))
     SEP (dfull s1 z p pin pout ish R msgv gv; deflate_globals gv))
    S_lmb
    (normal_ret_assert
      (PROP () LOCAL (temp _hash_head (vi hh); gvars gv; temp _s (p_s p); temp _flush (vi flush))
       SEP (dfull s' z p pin pout ish R msgv gv; deflate_globals gv))).
Proof.
  intros Hhh H. unfold dfull, dstate_at. Intros.
  show_sl. abbreviate_semax.
  forward_if (PROP ()
     LOCAL (temp _t'5 (Val.of_bool (lm_b5 s1 hh)); temp _hash_head (vi hh); gvars gv; temp _s (p_s p);
            temp _flush (vi flush))
     SEP (trees_at (d_trm s1) (p_s p) (p_pbuf p) (p_strm p) gv; win_at s1 p; hash_at s1 p; match_at s1 p;
          cfg_at s1 p; stat_at s1 p; strm_at z (p_s p) (p_strm p) pin pout msgv gv; in_obj ish z pin;
          out_space z pout R; deflate_globals gv)).
  - unfold match_at, cfg_at. Intros. forward. forward. forward.
    rewrite lm_ltu_bool by drange.
    unfold lm_b5, NIL. rewrite (proj2 (Z.eqb_neq hh 0) H4). cbn [negb andb].
    unfold match_at, cfg_at. entailer!.
  - forward. unfold lm_b5, NIL. rewrite H4. cbn [negb andb]. entailer!.
  - forward_if (PROP ()
     LOCAL (temp _t'6 (Val.of_bool (lm_b6 s1 hh)); temp _hash_head (vi hh); gvars gv; temp _s (p_s p);
            temp _flush (vi flush))
     SEP (trees_at (d_trm s1) (p_s p) (p_pbuf p) (p_strm p) gv; win_at s1 p; hash_at s1 p; match_at s1 p;
          cfg_at s1 p; stat_at s1 p; strm_at z (p_s p) (p_strm p) pin pout msgv gv; in_obj ish z pin;
          out_space z pout R; deflate_globals gv)).
    + unfold match_at, win_at. Intros. forward. forward. forward.
      destruct (lm_b5 s1 hh) eqn:E5; [|inversion H4].
      rewrite lm_test6. unfold lm_b6. rewrite E5. cbn [andb].
      unfold match_at, win_at. entailer!.
    + forward. destruct (lm_b5 s1 hh) eqn:E5; [inversion H4|].
      unfold lm_b6. rewrite E5. cbn [andb]. entailer!.
    + forward_if.
      * destruct (lm_b6 s1 hh) eqn:E6; [|inversion H4].
        destruct (c_longest_match s1 hh) as [[s2 ml]|] eqn:Elm; cbn [bind] in H; [|discriminate H].
        sep_apply (lm_dstate_fold s1 p gv H3).
        forward_call (s1, p, hh, (s2, ml), gv).
        cbn [fst snd]. unfold dstate_at. Intros.
        assert (Hr2 : dstate_ranges s2) by assumption.
        pose proof (lm_range _ _ _ _ Elm H3 Hr2) as Hml.
        unfold match_at. Intros. forward.
        assert (Hr3 : dstate_ranges (set_d_match_length s2 ml)) by dranges_tac Hr2.
        assert (Es' : s' = if lm_b4 (set_d_match_length s2 ml)
                           then set_d_match_length (set_d_match_length s2 ml) (MIN_MATCH - 1)
                           else set_d_match_length s2 ml)
          by (unfold lm_post in H; destruct (lm_b4 _); inversion H; reflexivity).
        subst s'. clear H.
        unfold POSTCONDITION, abbreviate.
        eapply semax_post'; [|eapply semax_pre; [|apply (lm_tail_frag p pin pout ish R msgv gv flush (set_d_match_length s2 ml) z hh)]].
        { unfold dfull, dstate_at. entailer!. }
        unfold dfull, dstate_at.
        replace (d_trm (set_d_match_length s2 ml)) with (d_trm s2) by reflexivity.
        unfold win_at, hash_at, match_at, cfg_at, stat_at. dsimpl. entailer!.
      * forward. destruct (lm_b6 s1 hh) eqn:E6; [inversion H4|]. inversion H; subst s'. entailer!.
Qed.

Lemma lm_frag {Espec : OracleKind} (p : dptrs) (pin pout : val) (ish : share) (R : list val) (msgv : val)
    (gv : globals) (flush : Z) (s s' : dstate) (z : strm) (hh : Z) :
  0 <= hh < 65536 ->
  dsl_prep s hh = Some s' ->
  semax Delta_sl
    (PROP () LOCAL (temp _hash_head (vi hh); gvars gv; temp _s (p_s p); temp _flush (vi flush))
     SEP (dfull s z p pin pout ish R msgv gv; deflate_globals gv))
    (Ssequence (Ssequence S_prev S_ml) S_lmb)
    (normal_ret_assert
      (PROP () LOCAL (temp _hash_head (vi hh); gvars gv; temp _s (p_s p); temp _flush (vi flush))
       SEP (dfull s' z p pin pout ish R msgv gv; deflate_globals gv))).
Proof.
  intros Hhh H. rewrite dsl_prep_eq in H.
  eapply semax_seq'; [apply lm_prev_frag|].
  apply (lm_cond_frag p pin pout ish R msgv gv flush (lm_s1 s) s' z hh Hhh H).
Qed.
