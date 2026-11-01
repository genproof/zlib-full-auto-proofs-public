(** * deflate_fast part: the rest of the match case [fast_after] (from the parts [fast_insl], [fast_uh]) (statement in FastKit.v). *)
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

(** Close a branch with its part lemma [Hs] (in [Delta_fast]). *)
Ltac fa_close Hs :=
  match goal with HT : tycontext_sub Delta_fast _ |- _ =>
    match goal with M := @abbreviate statement _, P := @abbreviate ret_assert _ |- _ =>
      unfold abbreviate in M, P; subst M P end;
    eapply semax_Delta_subsumption in Hs; [|exact HT];
    unfold fa, fa_base, fast_insl, fast_uh in Hs;
    eapply semax_pre; [|eapply semax_post; [| | | | exact Hs]];
    [ entailer!
    | simpl RA_normal; unfold dfull, dstate_at; entailer!
    | ..];
    try (simpl; intros; apply andp_left2, derives_refl);
    try (simpl; intros; intros x; apply andp_left2, derives_refl)
  end.

Lemma fast_after_ok : fast_insl_stmt -> fast_uh_stmt -> fast_after_stmt.
Proof.
  intros Hinsl Huh. unfold fast_after_stmt. intros Espec s s' z p pin pout ish R msgv gv flush vb H.
  unfold fa, fa_base, Delta_fast, fast_after. unfold dfull, dstate_at. Intros. abbreviate_semax.
  match goal with |- semax ?D _ _ _ => assert (HT : tycontext_sub Delta_fast D) by (unfold abbreviate in *; subst; apply tycontext_sub_refl) end.
  unfold match_at, cfg_at. Intros.
  forward. forward. forward.
  rewrite sub_repr32, <- (repr_u32 (d_lookahead s - d_match_length s)).
  unfold fast_after_m in H.
  set (s1 := set_d_lookahead s (u32 (d_lookahead s - d_match_length s))) in H.
  assert (Hr1 : dstate_ranges s1) by (subst s1; dranges_tac H3).
  forward. forward.
  change ((d_match_length s1 <=? d_max_lazy_match s1) && (d_lookahead s1 >=? MIN_MATCH))%bool with
    ((d_match_length s <=? d_max_lazy_match s) && (u32 (d_lookahead s - d_match_length s) >=? 3))%bool in H.
  assert (Hml : 0 <= d_match_length s <= Int.max_unsigned) by drange.
  assert (Hmx : 0 <= d_max_lazy_match s <= Int.max_unsigned) by drange.
  pose proof (u32_range (d_lookahead s - d_match_length s)) as Hla.
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?S))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _t'11 (Vint (Int.repr (Z.b2z
      ((d_match_length s <=? d_max_lazy_match s) && (u32 (d_lookahead s - d_match_length s) >=? 3))%bool))) :: L)
      (SEPx S))) end.
  - forward. forward.
    replace (d_match_length s <=? d_max_lazy_match s) with true by (symmetry; apply Z.leb_le; lia). cbn [andb].
    replace (bool2val (negb (zlt (u32 (d_lookahead s - d_match_length s)) 3)))
      with (Vint (Int.repr (Z.b2z (u32 (d_lookahead s - d_match_length s) >=? 3)))) by
      (destruct (zlt (u32 (d_lookahead s - d_match_length s)) 3);
       [replace (_ >=? 3) with false by (symmetry; rewrite Z.geb_leb; apply Z.leb_gt; lia)
       |replace (_ >=? 3) with true by (symmetry; rewrite Z.geb_leb; apply Z.leb_le; lia)]; reflexivity).
    entailer!.
  - forward.
    replace (d_match_length s <=? d_max_lazy_match s) with false by (symmetry; apply Z.leb_gt; lia). cbn [andb].
    entailer!.
  - set (b := ((d_match_length s <=? d_max_lazy_match s) && (u32 (d_lookahead s - d_match_length s) >=? 3))%bool) in *.
    apply semax_pre with (PROP () LOCAL (temp _t'11 (Vint (Int.repr (Z.b2z b))); temp _bflush vb; gvars gv;
      temp _s (p_s p); temp _flush (vi flush)) SEP (dfull s1 z p pin pout ish R msgv gv; deflate_globals gv)).
    { unfold dfull, dstate_at.
      change (d_trm s) with (d_trm s1). change (win_at s p) with (win_at s1 p).
      change (hash_at s p) with (hash_at s1 p). change (stat_at s p) with (stat_at s1 p).
      unfold match_at, cfg_at.
      change (Vint (Int.repr (u32 (d_lookahead s - d_match_length s)))) with (vi (d_lookahead s1)).
      change (d_block_start s) with (d_block_start s1).
      change (d_match_length s) with (d_match_length s1) at 2.
      entailer!. }
    unfold abbreviate in POSTCONDITION. subst POSTCONDITION.
    forward_if.
    + destruct b; [|discriminate].
      pose proof (Hinsl Espec s1 s' z p pin pout ish R msgv gv flush vb H) as Hs. fa_close Hs.
    + destruct b; [discriminate|].
      pose proof (Huh Espec s1 s' z p pin pout ish R msgv gv flush vb H) as Hs. fa_close Hs.
Qed.
