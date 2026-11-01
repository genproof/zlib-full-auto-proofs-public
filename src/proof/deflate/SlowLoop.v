(** * deflate_slow: the insert loop of the previous-match branch ([S_insloop]: lookahead / prev_length updates,
    the do-while of INSERT_STRINGs, match_available = 0, match_length = MIN_MATCH-1, strstart++). Kit: SlowKit.v;
    the INSERT_STRING inside is the hypothesis [ins2_ok] (proved in SlowIns.v). *)
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

Local Strategy opaque [loop loop2].

(** The end of one iteration of [dsl_insert_body] after its [if]: [--s->prev_length != 0]. *)
Definition slp_next (b : dstate) : dstate + dstate :=
  let b := set_d_prev_length b (u32 (d_prev_length b - 1)) in
  if d_prev_length b =? 0 then inr b else inl b.

(** The continue-assertion's fact: from [b] (after the [if]) the loop ends in [s2]. *)
Definition slp_cont (mi : Z) (s2 b : dstate) : Prop :=
  match slp_next b with inl a => runs (dsl_insert_body mi) a s2 | inr r => r = s2 end.

Lemma slp_body_ins mi a b h :
  d_strstart (set_d_strstart a (u32 (d_strstart a + 1))) <=? mi = true ->
  c_insert_string (set_d_strstart a (u32 (d_strstart a + 1))) (u32 (d_strstart a + 1)) = Some (b, h) ->
  dsl_insert_body mi a = Some (slp_next b).
Proof.
  intros C E. unfold dsl_insert_body. rewrite C. cbn [d_strstart set_d_strstart]. rewrite E. cbn.
  unfold slp_next. cbn. destruct (_ =? 0); reflexivity.
Qed.

Lemma slp_body_skip mi a :
  d_strstart (set_d_strstart a (u32 (d_strstart a + 1))) <=? mi = false ->
  dsl_insert_body mi a = Some (slp_next (set_d_strstart a (u32 (d_strstart a + 1)))).
Proof.
  intros C. unfold dsl_insert_body. rewrite C. cbn. unfold slp_next. cbn. destruct (_ =? 0); reflexivity.
Qed.

Lemma slp_cont_of mi a s2 b : runs (dsl_insert_body mi) a s2 -> dsl_insert_body mi a = Some (slp_next b) ->
  slp_cont mi s2 b.
Proof.
  intros Hr E. unfold slp_cont.
  destruct (runs_inv _ _ _ Hr) as [E'|(a' & E' & Hr')]; rewrite E in E'; inversion E'; subst.
  - destruct (slp_next b); inversion H0; auto.
  - destruct (slp_next b); inversion H0; subst; auto.
Qed.

(** A part lemma (in [Delta_sl]) as a whole statement under any postcondition. *)
Lemma slp_any {Espec : OracleKind} Delta P P' c Q (R' : ret_assert) :
  tycontext_sub Delta_sl Delta -> ENTAIL Delta, P |-- P' ->
  semax Delta_sl P' c (normal_ret_assert Q) -> (Q |-- RA_normal R') -> semax Delta P c R'.
Proof.
  intros HT HP H1 HQ. eapply semax_pre; [exact HP|].
  eapply semax_post; [| | | | eapply semax_Delta_subsumption; [exact HT|exact H1]]; destruct R'; simpl.
  - intros x. apply andp_left2, HQ.
  - intros x. apply andp_left2. apply prop_left. intros [].
  - intros x. apply andp_left2. apply prop_left. intros [].
  - intros vl x. apply andp_left2. apply prop_left. intros [].
Qed.

Lemma slp_sub_u32 a b : Int.repr (a - u32 b) = Int.repr (a - b).
Proof. rewrite <- sub_repr32, repr_u32, sub_repr32. reflexivity. Qed.

(** Closing the opened state (named lemmas, not [abstract]). *)
Lemma slp_close_pre s z p pin pout ish R msgv gv :
  strm_ranges z -> msg_ok (z_msg z) msgv -> readable_share ish -> dstate_ranges (dsl_pre_loop s) ->
  trees_at (d_trm s) (p_s p) (p_pbuf p) (p_strm p) gv * win_at s p * hash_at s p *
  field_at Ews t_ds (DOT _block_start) (vl (d_block_start s)) (p_s p) *
  field_at Ews t_ds (DOT _match_length) (vi (d_match_length s)) (p_s p) *
  field_at Ews t_ds (DOT _prev_match) (vi (d_prev_match s)) (p_s p) *
  field_at Ews t_ds (DOT _match_available) (vi (d_match_available s)) (p_s p) *
  field_at Ews t_ds (DOT _strstart) (vi (d_strstart s)) (p_s p) *
  field_at Ews t_ds (DOT _match_start) (vi (d_match_start s)) (p_s p) *
  field_at Ews t_ds (DOT _lookahead)
    (Vint (Int.sub (Int.repr (d_lookahead s)) (Int.sub (Int.repr (d_prev_length s)) (Int.repr 1)))) (p_s p) *
  field_at Ews t_ds (DOT _prev_length) (Vint (Int.sub (Int.repr (d_prev_length s)) (Int.repr 2))) (p_s p) *
  field_at Ews t_ds (DOT _insert) (vi (d_insert s)) (p_s p) *
  field_at Ews t_ds (DOT _slid) (vi (d_slid s)) (p_s p) *
  cfg_at s p * stat_at s p * strm_at z (p_s p) (p_strm p) pin pout msgv gv * in_obj ish z pin * out_space z pout R
  |-- dfull (dsl_pre_loop s) z p pin pout ish R msgv gv.
Proof. intros. unfold dsl_pre_loop. dfull_close_entail. rewrite slp_sub_u32. cancel. Qed.

Lemma slp_close_st s z p pin pout ish R msgv gv :
  strm_ranges z -> msg_ok (z_msg z) msgv -> readable_share ish -> dstate_ranges (set_d_strstart s (u32 (d_strstart s + 1))) ->
  trees_at (d_trm s) (p_s p) (p_pbuf p) (p_strm p) gv * win_at s p * hash_at s p *
  field_at Ews t_ds (DOT _block_start) (vl (d_block_start s)) (p_s p) *
  field_at Ews t_ds (DOT _match_length) (vi (d_match_length s)) (p_s p) *
  field_at Ews t_ds (DOT _prev_match) (vi (d_prev_match s)) (p_s p) *
  field_at Ews t_ds (DOT _match_available) (vi (d_match_available s)) (p_s p) *
  field_at Ews t_ds (DOT _strstart) (Vint (Int.add (Int.repr (d_strstart s)) (Int.repr 1))) (p_s p) *
  field_at Ews t_ds (DOT _match_start) (vi (d_match_start s)) (p_s p) *
  field_at Ews t_ds (DOT _lookahead) (vi (d_lookahead s)) (p_s p) *
  field_at Ews t_ds (DOT _prev_length) (vi (d_prev_length s)) (p_s p) *
  field_at Ews t_ds (DOT _insert) (vi (d_insert s)) (p_s p) *
  field_at Ews t_ds (DOT _slid) (vi (d_slid s)) (p_s p) *
  cfg_at s p * stat_at s p * strm_at z (p_s p) (p_strm p) pin pout msgv gv * in_obj ish z pin * out_space z pout R
  |-- dfull (set_d_strstart s (u32 (d_strstart s + 1))) z p pin pout ish R msgv gv.
Proof. intros. dfull_close_entail. Qed.

Lemma slp_close_pl s z p pin pout ish R msgv gv :
  strm_ranges z -> msg_ok (z_msg z) msgv -> readable_share ish ->
  dstate_ranges (set_d_prev_length s (u32 (d_prev_length s - 1))) ->
  trees_at (d_trm s) (p_s p) (p_pbuf p) (p_strm p) gv * win_at s p * hash_at s p *
  field_at Ews t_ds (DOT _block_start) (vl (d_block_start s)) (p_s p) *
  field_at Ews t_ds (DOT _match_length) (vi (d_match_length s)) (p_s p) *
  field_at Ews t_ds (DOT _prev_match) (vi (d_prev_match s)) (p_s p) *
  field_at Ews t_ds (DOT _match_available) (vi (d_match_available s)) (p_s p) *
  field_at Ews t_ds (DOT _strstart) (vi (d_strstart s)) (p_s p) *
  field_at Ews t_ds (DOT _match_start) (vi (d_match_start s)) (p_s p) *
  field_at Ews t_ds (DOT _lookahead) (vi (d_lookahead s)) (p_s p) *
  field_at Ews t_ds (DOT _prev_length) (Vint (Int.sub (Int.repr (d_prev_length s)) (Int.repr 1))) (p_s p) *
  field_at Ews t_ds (DOT _insert) (vi (d_insert s)) (p_s p) *
  field_at Ews t_ds (DOT _slid) (vi (d_slid s)) (p_s p) *
  cfg_at s p * stat_at s p * strm_at z (p_s p) (p_strm p) pin pout msgv gv * in_obj ish z pin * out_space z pout R
  |-- dfull (set_d_prev_length s (u32 (d_prev_length s - 1))) z p pin pout ish R msgv gv.
Proof. intros. dfull_close_entail. Qed.

Lemma slp_close_post s z p pin pout ish R msgv gv :
  strm_ranges z -> msg_ok (z_msg z) msgv -> readable_share ish -> dstate_ranges (dsl_post_loop s) ->
  trees_at (d_trm s) (p_s p) (p_pbuf p) (p_strm p) gv * win_at s p * hash_at s p *
  field_at Ews t_ds (DOT _block_start) (vl (d_block_start s)) (p_s p) *
  field_at Ews t_ds (DOT _match_length) (Vint (Int.sub (Int.repr 3) (Int.repr 1))) (p_s p) *
  field_at Ews t_ds (DOT _prev_match) (vi (d_prev_match s)) (p_s p) *
  field_at Ews t_ds (DOT _match_available) (Vint (Int.repr 0)) (p_s p) *
  field_at Ews t_ds (DOT _strstart) (Vint (Int.add (Int.repr (d_strstart s)) (Int.repr 1))) (p_s p) *
  field_at Ews t_ds (DOT _match_start) (vi (d_match_start s)) (p_s p) *
  field_at Ews t_ds (DOT _lookahead) (vi (d_lookahead s)) (p_s p) *
  field_at Ews t_ds (DOT _prev_length) (vi (d_prev_length s)) (p_s p) *
  field_at Ews t_ds (DOT _insert) (vi (d_insert s)) (p_s p) *
  field_at Ews t_ds (DOT _slid) (vi (d_slid s)) (p_s p) *
  cfg_at s p * stat_at s p * strm_at z (p_s p) (p_strm p) pin pout msgv gv * in_obj ish z pin * out_space z pout R
  |-- dfull (dsl_post_loop s) z p pin pout ish R msgv gv.
Proof. intros. unfold dsl_post_loop. dfull_close_entail. Qed.

Lemma insloop_frag {Espec : OracleKind} (p : dptrs) (pin pout : val) (ish : share) (R : list val) (msgv : val)
    (gv : globals) (flush : Z) (s s2 : dstate) (z : strm) (b : val) (mi : Z) :
  ins2_ok ->
  0 <= mi <= Int.max_unsigned ->
  loop FUEL (dsl_insert_body mi) (dsl_pre_loop s) = Some s2 ->
  semax Delta_sl
    (PROP () LOCAL (temp _bflush b; temp _max_insert (vi mi); gvars gv; temp _s (p_s p);
                    temp _flush (vi flush))
     SEP (dfull s z p pin pout ish R msgv gv; deflate_globals gv))
    S_insloop
    (normal_ret_assert
      (PROP () LOCAL (temp _bflush b; gvars gv; temp _s (p_s p); temp _flush (vi flush))
       SEP (dfull (dsl_post_loop s2) z p pin pout ish R msgv gv; deflate_globals gv))).
Proof.
  intros Hins2 Hmi H.
  unfold S_insloop. unfold dfull at 1. unfold dstate_at. Intros.
  cbv [S_lookst S_plst S_ma0 S_ml2 S_ssinc SL ssub f_deflate_slow fn_body].
  abbreviate_semax.
  unfold match_at. Intros.
  forward. forward. forward. forward. forward.
  apply loop_runs in H.
  set (s0 := dsl_pre_loop s) in H.
  assert (Hr0 : dstate_ranges s0) by (subst s0; unfold dsl_pre_loop; dranges_tac H3).
  pre_dfull s0 z p pin pout ish R msgv gv.
  { subst s0. sep_apply (slp_close_pre s z p pin pout ish R msgv gv H0 H1 H2 Hr0). entailer!. }
  clearbody s0.
  cbv [S_dowhile SL ssub f_deflate_slow fn_body].
  match goal with |- semax ?D _ _ _ => assert (HT : tycontext_sub Delta_sl D) by (unfold abbreviate in *; subst; apply tycontext_sub_refl) end.
  forward_loop (EX a : dstate,
     PROP (runs (dsl_insert_body mi) a s2)
     LOCAL (temp _bflush b; temp _max_insert (vi mi); gvars gv; temp _s (p_s p); temp _flush (vi flush))
     SEP (dfull a z p pin pout ish R msgv gv; deflate_globals gv))
   continue: (EX c : dstate,
     PROP (slp_cont mi s2 c)
     LOCAL (temp _bflush b; temp _max_insert (vi mi); gvars gv; temp _s (p_s p); temp _flush (vi flush))
     SEP (dfull c z p pin pout ish R msgv gv; deflate_globals gv))
   break: (PROP ()
     LOCAL (temp _bflush b; temp _max_insert (vi mi); gvars gv; temp _s (p_s p); temp _flush (vi flush))
     SEP (dfull s2 z p pin pout ish R msgv gv; deflate_globals gv)).
  { Exists s0. entailer!. }
  - (* body *)
    Intros a. rename H into Hrun.
    unfold dfull, dstate_at. Intros. unfold match_at. Intros.
    forward. forward. forward.
    set (a1 := set_d_strstart a (u32 (d_strstart a + 1))).
    assert (Hr1 : dstate_ranges a1) by (subst a1; dranges_tac H).
    pre_dfull a1 z p pin pout ish R msgv gv.
    { subst a1. sep_apply (slp_close_st a z p pin pout ish R msgv gv H0 H1 H2 Hr1). entailer!. }
    forward_if.
    + (* INSERT_STRING *)
      assert (C : d_strstart a1 <=? mi = true).
      { unfold a1. cbn [d_strstart set_d_strstart].
        rewrite <- (repr_u32 (d_strstart a + 1)), unsigned_repr_u32 in H5. apply Z.leb_le. lia. }
      destruct (c_insert_string a1 (d_strstart a1)) as [[c h]|] eqn:Ec.
      2: { exfalso. destruct (runs_some _ _ _ H4) as [o Ho]. unfold dsl_insert_body in Ho. fold a1 in Ho.
           rewrite C, Ec in Ho. discriminate. }
      assert (Hc : slp_cont mi s2 c) by (eapply slp_cont_of; [exact H4 | apply (slp_body_ins mi a c h C Ec)]).
      unfold MORE_COMMANDS, abbreviate.
      apply (slp_any _ _ (PROP () LOCAL (temp _bflush b; temp _max_insert (vi mi); gvars gv; temp _s (p_s p);
                                         temp _flush (vi flush))
                          SEP (dfull a1 z p pin pout ish R msgv gv; deflate_globals gv)) S_ins2
                         (PROP () LOCAL (temp _bflush b; temp _max_insert (vi mi); gvars gv; temp _s (p_s p);
                                         temp _flush (vi flush))
                          SEP (dfull c z p pin pout ish R msgv gv; deflate_globals gv))).
      { exact HT. }
      { entailer!. }
      { exact (Hins2 Espec p pin pout ish R msgv gv flush b mi a1 c z h Ec). }
      unfold POSTCONDITION, abbreviate. cbn [RA_normal loop1_ret_assert].
      Exists c. go_lowerx. entailer!.
    + (* skip *)
      assert (C : d_strstart a1 <=? mi = false).
      { unfold a1. cbn [d_strstart set_d_strstart].
        rewrite <- (repr_u32 (d_strstart a + 1)), unsigned_repr_u32 in H5. apply Z.leb_gt. lia. }
      assert (Hc : slp_cont mi s2 a1) by (eapply slp_cont_of; [exact H4 | apply (slp_body_skip mi a C)]).
      forward. Exists a1. entailer!.
  - (* incr: --s->prev_length != 0 *)
    Intros c.
    match goal with Hx : slp_cont _ _ _ |- _ => rename Hx into Hcc end.
    unfold dfull, dstate_at. Intros. unfold match_at. Intros.
    match goal with Hx : dstate_ranges c |- _ => rename Hx into Hrc end.
    forward. forward. forward.
    unfold slp_cont, slp_next in Hcc. set (c' := set_d_prev_length c (u32 (d_prev_length c - 1))) in Hcc.
    assert (Hrb : dstate_ranges c') by (subst c'; dranges_tac Hrc).
    forward_if.
    + (* go on *)
      assert (Enz : d_prev_length c' <> 0).
      { subst c'; cbn [d_prev_length set_d_prev_length]. intro E.
        match goal with Hx : Int.sub _ _ <> _ |- _ => apply Hx end.
        rewrite sub_repr, <- repr_u32, E. reflexivity. }
      rewrite (proj2 (Z.eqb_neq _ _) Enz) in Hcc.
      forward. Exists c'. subst c'. sep_apply (slp_close_pl c z p pin pout ish R msgv gv H0 H1 H2 Hrb). entailer!.
    + (* break *)
      assert (Ez : d_prev_length c' = 0).
      { subst c'; cbn [d_prev_length set_d_prev_length].
        match goal with Hx : Int.sub _ _ = _ |- _ => rename Hx into E end.
        rewrite sub_repr, <- repr_u32 in E.
        apply repr_eq_u32 in E; [exact E | apply u32_range | rep_lia]. }
      rewrite Ez in Hcc. cbn in Hcc. subst s2.
      forward. subst c'. sep_apply (slp_close_pl c z p pin pout ish R msgv gv H0 H1 H2 Hrb). entailer!.
  - unfold dfull, dstate_at. Intros. unfold match_at. Intros.
    forward. forward. forward. forward.
    match goal with Hx : dstate_ranges s2 |- _ => rename Hx into Hr2 end.
    assert (Hr3 : dstate_ranges (dsl_post_loop s2)) by (unfold dsl_post_loop; dranges_tac Hr2; unfold MIN_MATCH; rep_lia).
    sep_apply (slp_close_post s2 z p pin pout ish R msgv gv H0 H1 H2 Hr3). entailer!.
Qed.
