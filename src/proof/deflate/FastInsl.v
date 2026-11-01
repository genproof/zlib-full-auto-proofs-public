(** * deflate_fast part: the insertion loop [fast_insl] (from the INSERT_STRING part [fast_ins2]) (statement in FastKit.v). *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.trees.TLemmas.
Require Import Zlib.proof.deflate.CompressKit.
Require Import Zlib.proof.deflate.FastKit.
Require Import Zlib.deflate.code.
#[export] Existing Instance DCS.CS.
Open Scope cmodel_scope.

(** Kernel conversion hints (as in Body_huff.v): the Qed must not reduce the 40-deep [loop2]. *)
Local Strategy expand [fast_insl_m].
Local Strategy opaque [loop loop2].

(** The end of one iteration of [df_insert_body] after its INSERT_STRING: [--s->match_length != 0]. *)
Definition insl_next (b : dstate) : dstate + dstate :=
  let b := set_d_match_length b (u32 (d_match_length b - 1)) in
  if d_match_length b =? 0 then inr b else inl b.

(** The continue-assertion's fact: from [b] (after INSERT_STRING) the loop ends in [s1]. *)
Definition insl_cont (s1 b : dstate) : Prop :=
  match insl_next b with inl a => runs df_insert_body a s1 | inr r => r = s1 end.

Lemma df_insert_body_eq a b h :
  c_insert_string (set_d_strstart a (u32 (d_strstart a + 1))) (u32 (d_strstart a + 1)) = Some (b, h) ->
  df_insert_body a = Some (insl_next b).
Proof. intros E. unfold df_insert_body. cbn [d_strstart set_d_strstart]. rewrite E. cbn. unfold insl_next. cbn. destruct (_ =? 0); reflexivity. Qed.

Lemma insl_cont_of a s1 b h : runs df_insert_body a s1 ->
  c_insert_string (set_d_strstart a (u32 (d_strstart a + 1))) (u32 (d_strstart a + 1)) = Some (b, h) ->
  insl_cont s1 b.
Proof.
  intros Hr E. apply df_insert_body_eq in E. unfold insl_cont.
  destruct (runs_inv _ _ _ Hr) as [E'|(a' & E' & Hr')]; rewrite E in E'; inversion E'; subst.
  - destruct (insl_next b); inversion H0; auto.
  - destruct (insl_next b); inversion H0; subst; auto.
Qed.

Lemma fast_insl_m_inv s s' : fast_insl_m s = Some s' ->
  exists s1, runs df_insert_body (set_d_match_length s (u32 (d_match_length s - 1))) s1 /\
             s' = set_d_strstart s1 (u32 (d_strstart s1 + 1)).
Proof.
  unfold fast_insl_m. intros H. inv_bind H. exists x. split; [eapply loop_runs; exact Ha|].
  inversion H; reflexivity.
Qed.

(** A part lemma (in [Delta_fast]) as a whole statement under any postcondition. *)
Lemma fa_any {Espec : OracleKind} Delta P P' c Q (R' : ret_assert) :
  tycontext_sub Delta_fast Delta -> ENTAIL Delta, P |-- P' ->
  semax Delta_fast P' c (normal_ret_assert Q) -> (Q |-- RA_normal R') -> semax Delta P c R'.
Proof.
  intros HT HP H1 HQ. eapply semax_pre; [exact HP|].
  eapply semax_post; [| | | | eapply semax_Delta_subsumption; [exact HT|exact H1]]; destruct R'; simpl.
  - intros x. apply andp_left2, HQ.
  - intros x. apply andp_left2. apply prop_left. intros [].
  - intros x. apply andp_left2. apply prop_left. intros [].
  - intros vl x. apply andp_left2. apply prop_left. intros [].
Qed.

(** Closing the opened state after [s->match_length--] / after [s->strstart++] (named lemmas, not [abstract]). *)
Lemma insl_close_ml s z p pin pout ish R msgv gv :
  strm_ranges z -> msg_ok (z_msg z) msgv -> readable_share ish -> dstate_ranges (set_d_match_length s (u32 (d_match_length s - 1))) ->
  trees_at (d_trm s) (p_s p) (p_pbuf p) (p_strm p) gv * win_at s p * hash_at s p *
  field_at Ews t_ds (DOT _block_start) (vl (d_block_start s)) (p_s p) *
  field_at Ews t_ds (DOT _match_length) (Vint (Int.sub (Int.repr (d_match_length s)) (Int.repr 1))) (p_s p) *
  field_at Ews t_ds (DOT _prev_match) (vi (d_prev_match s)) (p_s p) *
  field_at Ews t_ds (DOT _match_available) (vi (d_match_available s)) (p_s p) *
  field_at Ews t_ds (DOT _strstart) (vi (d_strstart s)) (p_s p) *
  field_at Ews t_ds (DOT _match_start) (vi (d_match_start s)) (p_s p) *
  field_at Ews t_ds (DOT _lookahead) (vi (d_lookahead s)) (p_s p) *
  field_at Ews t_ds (DOT _prev_length) (vi (d_prev_length s)) (p_s p) *
  field_at Ews t_ds (DOT _insert) (vi (d_insert s)) (p_s p) *
  field_at Ews t_ds (DOT _slid) (vi (d_slid s)) (p_s p) *
  cfg_at s p * stat_at s p * strm_at z (p_s p) (p_strm p) pin pout msgv gv * in_obj ish z pin * out_space z pout R
  |-- dfull (set_d_match_length s (u32 (d_match_length s - 1))) z p pin pout ish R msgv gv.
Proof. intros. dfull_close_entail. Qed.

Lemma insl_close_st s z p pin pout ish R msgv gv :
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

Lemma fast_insl_ok : fast_ins2_stmt -> fast_insl_stmt.
Proof.
  intros Hins2 Espec s s' z p pin pout ish R msgv gv flush vb H.
  unfold fa, fa_base, Delta_fast, fast_insl. unfold dfull at 1. unfold dstate_at. Intros. abbreviate_semax.
  match goal with |- semax ?D _ _ _ => assert (HT : tycontext_sub Delta_fast D) by (unfold abbreviate in *; subst; apply tycontext_sub_refl) end.
  unfold match_at. Intros.
  forward. forward.
  apply fast_insl_m_inv in H. destruct H as (s1 & Ha & ->).
  set (s0 := set_d_match_length s (u32 (d_match_length s - 1))) in Ha.
  assert (Hr0 : dstate_ranges s0) by (subst s0; dranges_tac H3).
  pre_dfull s0 z p pin pout ish R msgv gv.
  { subst s0. sep_apply (insl_close_ml s z p pin pout ish R msgv gv H0 H1 H2 Hr0). entailer!. }
  clearbody s0.
  forward_loop (EX a : dstate,
     PROP (runs df_insert_body a s1)
     LOCAL (temp _bflush vb; gvars gv; temp _s (p_s p); temp _flush (vi flush))
     SEP (dfull a z p pin pout ish R msgv gv; deflate_globals gv))
   continue: (EX b : dstate,
     PROP (insl_cont s1 b)
     LOCAL (temp _bflush vb; gvars gv; temp _s (p_s p); temp _flush (vi flush))
     SEP (dfull b z p pin pout ish R msgv gv; deflate_globals gv))
   break: (PROP ()
     LOCAL (temp _bflush vb; gvars gv; temp _s (p_s p); temp _flush (vi flush))
     SEP (dfull s1 z p pin pout ish R msgv gv; deflate_globals gv)).
  { Exists s0. entailer!. }
  - (* body *)
    Intros a. rename H into Hrun.
    destruct (runs_some _ _ _ Hrun) as [o Hb].
    pose proof Hb as Hb'. unfold df_insert_body in Hb'. cbn [d_strstart set_d_strstart] in Hb'.
    inv_bind Hb'. destruct x as [b h]. rename Ha0 into Hcis.
    unfold dfull, dstate_at. Intros. unfold match_at. Intros.
    forward. forward.
    set (a1 := set_d_strstart a (u32 (d_strstart a + 1))) in Hcis.
    assert (Hr1 : dstate_ranges a1) by (subst a1; dranges_tac H).
    subst MORE_COMMANDS. unfold abbreviate.
    apply (fa_any _ _ (fa (temp _bflush vb :: fa_base p flush gv) a1 z p pin pout ish R msgv gv) fast_ins2
             (fa (temp _bflush vb :: fa_base p flush gv) b z p pin pout ish R msgv gv)).
    { exact HT. }
    { subst a1. sep_apply (insl_close_st a z p pin pout ish R msgv gv H0 H1 H2 Hr1). unfold fa, fa_base. entailer!. }
    { exact (Hins2 Espec a1 b z p pin pout ish R msgv gv flush h vb Hcis). }
    unfold POSTCONDITION, abbreviate. cbn [RA_normal loop1_ret_assert].
    assert (Hc : insl_cont s1 b) by (eapply insl_cont_of; eauto).
    Exists b. unfold fa, fa_base. go_lowerx. entailer!.
  - (* incr: --s->match_length != 0 *)
    Intros b. rename H into Hc.
    unfold dfull, dstate_at. Intros. unfold match_at. Intros.
    forward. forward. forward.
    unfold insl_cont, insl_next in Hc. set (b' := set_d_match_length b (u32 (d_match_length b - 1))) in Hc.
    assert (Hrb : dstate_ranges b') by (subst b'; dranges_tac H).
    forward_if.
    + (* go on *)
      assert (Enz : d_match_length b' <> 0).
      { subst b'; cbn [d_match_length set_d_match_length]. intro E. apply H4. rewrite sub_repr, <- repr_u32, E. reflexivity. }
      rewrite (proj2 (Z.eqb_neq _ _) Enz) in Hc.
      forward. Exists b'. subst b'. sep_apply (insl_close_ml b z p pin pout ish R msgv gv H0 H1 H2 Hrb). entailer!.
    + (* break *)
      assert (Ez : d_match_length b' = 0).
      { subst b'; cbn [d_match_length set_d_match_length]. rewrite sub_repr, <- repr_u32 in H4.
        apply repr_eq_u32 in H4; [exact H4| apply u32_range | rep_lia]. }
      rewrite Ez in Hc. cbn in Hc. subst s1.
      forward. subst b'. sep_apply (insl_close_ml b z p pin pout ish R msgv gv H0 H1 H2 Hrb). entailer!.
  - (* s->strstart++ *)
    unfold dfull, dstate_at. Intros. unfold match_at. Intros.
    forward. forward.
    assert (Hr2 : dstate_ranges (set_d_strstart s1 (u32 (d_strstart s1 + 1)))) by dranges_tac H.
    sep_apply (insl_close_st s1 z p pin pout ish R msgv gv H0 H1 H2 Hr2). entailer!.
Qed.
