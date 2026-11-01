(** * deflate_fast part: the longest_match call [fast_lm] (statement in FastKit.v). *)
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

Lemma lm_test_eq s h : h <> 0 ->
  bool2val (negb (Int.ltu (Int.repr (d_w_size s - (258 + 3 + 1))) (Int.repr (d_strstart s - h)))) =
  Val.of_bool (andb (negb (h =? NIL)) (u32 (d_strstart s - h) <=? max_dist s)).
Proof.
  intros Hh. unfold max_dist, MAX_DIST, NIL. change DState.MIN_LOOKAHEAD with (258 + 3 + 1).
  rewrite (proj2 (Z.eqb_neq h 0) Hh). cbn [negb andb].
  unfold Int.ltu. rewrite <- (repr_u32 (d_w_size s - _)), <- (repr_u32 (d_strstart s - h)), !unsigned_repr_u32.
  destruct (zlt _ _) as [E|E]; [rewrite (proj2 (Z.leb_gt _ _) E) | rewrite (proj2 (Z.leb_le _ _) (Z.ge_le _ _ E))];
  reflexivity.
Qed.

Lemma dstate_fold s p gv : dstate_ranges s ->
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

Lemma lm_body_best nice limit a o : lm_body nice limit a = Some o -> 0 <= lm_best a ->
  match o with inl a' => 0 <= lm_best a' | inr (b, _) => 0 <= b end.
Proof.
  intros E H0. unfold lm_body in E. cbv zeta in E. lm_crush E; cbn [lm_best] in *; try lia;
  repeat match goal with Eb : (_ >? _) = true |- _ => apply Z.gtb_lt in Eb end; lia.
Qed.

Lemma lm_runs_best nice limit a r : runs (lm_body nice limit) a r -> 0 <= lm_best a -> 0 <= fst r.
Proof.
  induction 1 as [a r E|a a' r E _ IH]; intros H0; pose proof (lm_body_best _ _ _ _ E H0) as Hb.
  - destruct r; exact Hb.
  - exact (IH Hb).
Qed.

Lemma c_longest_match_range s h s2 ml : c_longest_match s h = Some (s2, ml) -> dstate_ranges s -> dstate_ranges s2 ->
  0 <= ml <= Int.max_unsigned.
Proof.
  intros E Hr Hr2. unfold c_longest_match in E.
  inv_bind E. inv_bind E. inv_bind E. inv_bind E. inv_bind E. inv_bind E. destruct x4 as [best s3].
  apply loop_runs, lm_runs_best in Ha4; cbn [lm_best fst] in Ha4; [|cbn [lm_best]; clear Hr2; drange].
  inversion E; subst. clear Hr. destruct (best <=? d_lookahead s2) eqn:Eb; [apply Z.leb_le in Eb|]; drange.
Qed.

Lemma fast_lm_ok : fast_lm_stmt.
Proof.
  intros Espec s s' z p pin pout ish R msgv gv flush h Hh H.
  unfold fa, fa_base, Delta_fast, fast_lm. unfold dfull, dstate_at. Intros.
  abbreviate_semax.
  set (b := andb (negb (h =? NIL)) (u32 (d_strstart s - h) <=? max_dist s)).
  forward_if (PROP ()
     LOCAL (temp _t'4 (Val.of_bool b); temp _hash_head (vi h); gvars gv; temp _s (p_s p); temp _flush (vi flush))
     SEP (trees_at (d_trm s) (p_s p) (p_pbuf p) (p_strm p) gv; win_at s p; hash_at s p; match_at s p; cfg_at s p;
          stat_at s p; strm_at z (p_s p) (p_strm p) pin pout msgv gv; in_obj ish z pin; out_space z pout R;
          deflate_globals gv)).
  - unfold match_at, win_at. Intros.
    forward. forward. forward.
    rewrite (lm_test_eq s h H4). fold b.
    unfold win_at, match_at. entailer!.
  - forward.
    assert (Eb : b = false) by (subst b h; reflexivity). rewrite Eb. entailer!.
  - forward_if.
    + assert (Eb : b = true) by (destruct b; [reflexivity | inversion H4]).
      unfold fast_lm_m in H. fold b in H. rewrite Eb in H.
      inv_bind H. destruct x as [s2 ml]. inversion H; subst s'; clear H.
      sep_apply (dstate_fold s p gv H3).
      forward_call (s, p, h, (s2, ml), gv).
      cbn [fst snd]. unfold dstate_at. Intros.
      assert (Hr2 : dstate_ranges s2) by assumption.
      pose proof (c_longest_match_range _ _ _ _ Ha H3 Hr2) as Hml.
      unfold match_at. Intros. forward.
      assert (Hr3 : dstate_ranges (set_d_match_length s2 ml)) by dranges_tac Hr2.
      replace (d_trm (set_d_match_length s2 ml)) with (d_trm s2) by reflexivity.
      unfold win_at, hash_at, match_at, cfg_at, stat_at. dsimpl. entailer!.
    + assert (Eb : b = false) by (destruct b; [inversion H4 | reflexivity]).
      unfold fast_lm_m in H. fold b in H. rewrite Eb in H. inversion H; subst s'; clear H.
      forward. entailer!.
Qed.
