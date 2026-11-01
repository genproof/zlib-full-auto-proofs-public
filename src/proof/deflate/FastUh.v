(** * deflate_fast part: skipping a long match [fast_uh] (statement in FastKit.v). *)
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

Lemma fu_temp_head {cs : compspecs} {Espec : OracleKind} Delta P i v v' Q R c Post :
  v = v' -> semax Delta (PROPx P (LOCALx (temp i v' :: Q) R)) c Post ->
  semax Delta (PROPx P (LOCALx (temp i v :: Q) R)) c Post.
Proof. intros ->; auto. Qed.

Lemma fu_vi_wrap x : vi x = Vint (Int.repr (u32 (x + 1) - 1)).
Proof.
  unfold vi. f_equal. apply Int.eqm_samerepr. unfold Int.eqm, u32.
  apply Zbits.eqmod_sym. eapply Zbits.eqmod_trans.
  - apply Zbits.eqmod_sub; [apply Zbits.eqmod_sym, Zbits.eqmod_mod; reflexivity|apply Zbits.eqmod_refl].
  - replace (x + 1 - 1) with x by lia. apply Zbits.eqmod_refl.
Qed.

Lemma fu_xor_repr a b : Int.xor (Int.repr a) (Int.repr b) = Int.repr (Z.lxor a b).
Proof.
  apply Int.same_bits_eq. intros i Hi.
  rewrite Int.bits_xor by auto. rewrite !Int.testbit_repr by auto.
  rewrite Z.lxor_spec. reflexivity.
Qed.

Lemma fu_hash s a c :
  0 <= a <= Int.max_unsigned -> 0 <= d_hash_shift s < 32 ->
  Int.and (Int.xor (Int.shl (Int.repr a) (Int.repr (d_hash_shift s))) (Int.repr c)) (Int.repr (d_hash_mask s)) =
  Int.repr (update_hash s a c).
Proof.
  intros Ha Hk. unfold update_hash. rewrite repr_u32, <- and_repr32, <- fu_xor_repr. f_equal. f_equal.
  unfold Int.shl. rewrite !Int.unsigned_repr by rep_lia. rewrite repr_u32. reflexivity.
Qed.

Lemma fu_ranges s a b c e : dstate_ranges s -> 0 <= a <= Int.max_unsigned -> 0 <= b <= Int.max_unsigned ->
  0 <= c <= Int.max_unsigned -> 0 <= e <= Int.max_unsigned ->
  dstate_ranges (set_d_ins_h (set_d_ins_h (set_d_match_length (set_d_strstart s a) b) c) e).
Proof.
  intros Hs Ha Hb Hc He. unfold dstate_ranges, u32_ok, u64_ok, s32_ok, s64_ok in *. dsimpl.
  decompose [and] Hs.
  repeat match goal with |- _ /\ _ => split end; try assumption; lia.
Qed.

Lemma fast_uh_ok : fast_uh_stmt.
Proof.
  unfold fast_uh_stmt. intros Espec s s' z p pin pout ish R msgv gv flush vb H.
  unfold fa, fa_base, Delta_fast, fast_uh. unfold dfull, dstate_at. Intros. abbreviate_semax.
  unfold hash_at, match_at, win_at. Intros.
  unfold fast_uh_m in H. inv_bind H. inv_bind H. inv_bind H.
  inversion H; subst s'; clear H.
  rename x into c0, x1 into c1.
  unfold guard in Ha0. case_if_as Ha0 Esh; [|discriminate]. clear Ha0.
  dsimpl in Ha. dsimpl in Ha1. dsimpl in Esh. apply Z.ltb_lt in Esh.
  assert (Hwok : mb_ok (d_window s)) by (open_dranges H3; assumption).
  forward. forward. forward. forward.
  forward. forward.
  rewrite add_repr, <- (repr_u32 (d_strstart s + d_match_length s)).
  set (u := u32 (d_strstart s + d_match_length s)) in *.
  pose proof (u32_range (d_strstart s + d_match_length s)) as Hu. fold u in Hu.
  destruct (mb_rd_vals _ _ _ Hwok Ha) as (Hi0 & Hz0 & Hc0).
  destruct (mb_rd_vals _ _ _ Hwok Ha1) as (Hi1 & Hz1 & Hc1).
  pose proof (Zlength_mb_vals _ Hwok) as Hwl.
  forward.
  { go_lower. apply prop_right.
    replace (Znth u (mb_vals (d_window s))) with (vi c0) by (symmetry; exact Hz0).
    exact (tc_val_tuchar_repr c0 ltac:(lia)). }
  replace (Znth u (mb_vals (d_window s))) with (vi c0) by (symmetry; exact Hz0).
  forward. forward. forward. forward. forward.
  apply (fu_temp_head _ _ _ _ _ _ _ _ _ (fu_vi_wrap u)).
  pose proof (u32_range (u + 1)).
  forward.
  { go_lower. apply prop_right.
    replace (Znth (u32 (u + 1) - 1 + 1) (mb_vals (d_window s))) with (vi c1)
      by (replace (u32 (u + 1) - 1 + 1) with (u32 (u + 1)) by lia; symmetry; exact Hz1).
    exact (tc_val_tuchar_repr c1 ltac:(lia)). }
  replace (Znth (u32 (u + 1) - 1 + 1) (mb_vals (d_window s))) with (vi c1)
    by (replace (u32 (u + 1) - 1 + 1) with (u32 (u + 1)) by lia; symmetry; exact Hz1).
  assert (0 <= d_hash_shift s < 32) by (split; [drange|lia]).
  forward. forward.
  rewrite (fu_hash s c0 c1) by (auto; rep_lia).
  pose proof (fu_ranges s u 0 c0 (update_hash s c0 c1) H3 Hu ltac:(rep_lia) ltac:(rep_lia)
    (u32_range _)) as Hr.
  match goal with |- context [update_hash ?t c0 c1] => lazymatch t with s => fail | _ =>
    replace (update_hash t c0 c1) with (update_hash s c0 c1) by reflexivity end end.
  set (uh := update_hash s c0 c1) in *. clearbody uh.
  match goal with |- context [d_trm ?t] => lazymatch t with s => fail | _ =>
    replace (d_trm t) with (d_trm s) by reflexivity end end.
  unfold win_at, hash_at, match_at, cfg_at, stat_at. dsimpl.
  unfold vi. entailer!.
Qed.
