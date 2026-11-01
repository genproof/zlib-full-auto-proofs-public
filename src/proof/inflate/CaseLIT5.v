(* inflate(), case LIT in Delta_cases5 *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate.Callees5.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Lemma case_LIT5 {Espec: OracleKind} (F: frame) (m: mst):
  m_mode m = LIT -> m_leave m = 0 -> mwf m ->
  semax Delta_cases5 (loop_state F m)
    (seq_of_labeled_statement (ls_drop 25 inflate_LS)) (switch_ret_assert (case_post2 F m)).
Proof.
  intros HM HL W. case_stmt.
  pose proof (mwf_left m W) as HLEFT.
  destruct F as [gv shs strmp sp headp winp hsh xb nb cb ib ob gsh tsh dt vres vhere vlast vhbuf flush].
  destruct ob as [osh op olo on oc].
  unfold loop_state, mem_rep. frame_simpl.
  abbreviate_semax.
  Intros.
  forward_if.
  - (* no output space: leave *)
    forward. forward.
    Exists (set_leave m).
    unfold loop_state, mem_rep. frame_simpl.
    entailer!.
    + unfold stepf2, step2. rewrite HM. unfold c_LIT. rewrite H1. reflexivity.
    + mnorm_goal. cancel.
  - (* write the literal *)
    pose proof (mw_ow _ W) as WOW. destruct WOW as [WOW1 WOW2].
    unfold out_ok in H0. destruct H0 as (Hosh & Hop & Holo & Haout & Hlo & Hoc & Hon).
    assert (HJ: olo + Zlength (m_ow m) < on) by (unfold m_left in H1, HLEFT; lia).
    pose proof (Zlength_nonneg (m_ow m)) as HZ.
    assert_PROP (field_compatible (tarray tuchar on) [] op) by entailer!.
    forward. forward.
    unfold state_rep. Intros.
    forward.
    rewrite (offset_val_field_address_tuchar on (olo + Zlength (m_ow m)) op) by (auto; pose proof (Zlength_nonneg (m_ow m)); lia).
    forward.
    rewrite <- (offset_val_field_address_tuchar on (olo + Zlength (m_ow m)) op) by (auto; pose proof (Zlength_nonneg (m_ow m)); lia).
    forward. forward. forward.
    Exists (set_mode (set_m_ow m (m_ow m ++ [i_length (m_s m) mod 256])) LEN).
    unfold loop_state, mem_rep, state_rep. frame_simpl. mnorm_goal.
    rewrite !zext8, Zmod_mod.
    rewrite (out_rep_snoc osh op olo on oc (m_ow m)) by lia.
    entailer!.
    + assert (HL1: Zlength (m_ow m ++ [i_length (m_s m) mod 256]) = Zlength (m_ow m) + 1)
        by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
      split3; [ | | split].
      * unfold stepf2, step2. rewrite HM. unfold c_LIT. rewrite (proj2 (Z.eqb_neq _ _) H1). reflexivity.
      * unfold out_ok. split; [exact Hosh|]. split; [exact Hop|]. repeat split; auto; lia.
      * rewrite HL1. f_equal. lia.
      * unfold m_left. mnorm_goal. rewrite HL1. f_equal. f_equal. lia.
    + unfold win_rep, out_rep. mnorm_goal. cancel.
Qed.
