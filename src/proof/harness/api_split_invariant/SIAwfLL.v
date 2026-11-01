(* The abstract steps of TABLE and LENLENS keep the invariant awfx (SIAwfKit.v): the counts of the
   dynamic block header, the code length code lengths, and the code length code's table built by
   inflate_table (valid by the covering fact, replicated by tabrep_stmt). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.api_split_invariant.SIDefs.
Require Import Zlib.proof.harness.api_split_invariant.SIAwfKit.
Require Zlib.proof.inflate.MwfLemmas Zlib.proof.inflate.Step3Tables Zlib.proof.inflate.Cover2.
Import ListNotations.
Local Open Scope Z_scope.

(* a goal whose hypotheses give a known mode another value: only those hypotheses are kept *)
Ltac ll_neq := intros; exfalso; repeat match goal with H: ?T |- _ =>
  lazymatch T with _ = _ => revert H | _ \/ _ => revert H | decode_mode _ => revert H
  | hdr_mode _ => revert H | data_mode _ => revert H | _ => clear H end end;
  unfold decode_mode, hdr_mode, data_mode; mdc; intros; lia.

(* TABLE reads the three counts: to LENLENS when they are in range, else to BAD (the counts set fit
   the struct's fields either way) *)
Lemma awf_table : case_ok TABLE.
Proof.
  intros src a W Md. rewrite astep_TABLE by exact Md. unfold a_TABLE.
  destruct (ax_frame _ _ W) as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
  pose proof (ax_src _ _ W) as B. pose proof (ax_swf _ _ W) as S.
  pose proof (aw_chk _ _ (ax_w _ _ W)) as CK.
  pose proof (sbits_range src (a_q a) 5 ltac:(lia)) as R1.
  pose proof (sbits_range src (a_q a + 5) 5 ltac:(lia)) as R2.
  pose proof (sbits_range src (a_q a + 10) 4 ltac:(lia)) as R3.
  change (2 ^ 5) with 32 in *. change (2 ^ 4) with 16 in *.
  cbv zeta.
  set (s := set_i_ncode (set_i_ndist (set_i_nlen (a_s a) (sbits src (a_q a) 5 + 257)) (sbits src (a_q a + 5) 5 + 1))
              (sbits src (a_q a + 10) 4 + 4)).
  assert (S': swf s) by (destruct S; constructor; simpl; auto; lia).
  destruct (orb (286 <? sbits src (a_q a) 5 + 257) (30 <? sbits src (a_q a + 5) 5 + 1)) eqn:T.
  - unfold abad, go_ok; simpl. split; [|split; [lia | split; [auto | left; auto]]].
    apply awfx_bad; simpl; auto; lia.
  - apply orb_false_iff in T. destruct T as [T1 T2]. apply Z.ltb_ge in T1. apply Z.ltb_ge in T2.
    apply go_ago; [|lia]. apply awfx_intro; simpl; auto; try ll_neq.
    + apply MwfLemmas.swf_set_mode; [|mdc; lia]. destruct S'; constructor; simpl; auto; lia.
    + constructor; simpl; intros; try ll_neq; [|repeat split; ll_neq].
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. intros; lia.
    + constructor; simpl; intros; try ll_neq.
    + split; simpl; intros; ll_neq.
    + mdc; lia.
    + lia.
    + intros _ NZ. apply CK; [rewrite Md; unfold data_mode; tauto | exact NZ].
    + intros HH. exfalso. revert HH. clear. mdc. lia.
Qed.

(* LENLENS reads one code length code length (at most 7), or, when all are read, zeroes the others and
   builds the code length code's table at codes[0 ..): to CODELENS with a valid, replicated table, or to
   BAD when inflate_table rejects the lengths *)
Lemma awf_lenlens : tabrep_stmt -> case_ok LENLENS.
Proof.
  intros TR src a W Md. rewrite astep_LENLENS by exact Md. unfold a_LENLENS.
  destruct (ax_frame _ _ W) as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
  pose proof (ax_src _ _ W) as B. pose proof (ax_swf _ _ W) as S.
  pose proof (aw_chk _ _ (ax_w _ _ W)) as CK. rewrite Md in CK.
  assert (CK': i_wrap (a_s a) <> 0 -> (i_flags (a_s a) = 0 /\ i_check (a_s a) = 1) \/
                                    (i_flags (a_s a) <> 0 /\ i_check (a_s a) = 0))
    by (apply CK; unfold data_mode; tauto).
  clear CK.
  assert (Md': i_mode (a_s a) = LENLENS) by exact Md.
  destruct (md_lenlens _ (ax_md _ _ W) Md') as (Hc & H0 & Hnl & Hnd & LE).
  destruct (sw_lens _ S) as [ZL FL]. destruct (sw_codes _ S) as [ZC FC].
  destruct (Z.ltb_spec (i_have (a_s a)) (i_ncode (a_s a))) as [Hh|Hh].
  - (* one more code length code length, of 3 bits *)
    pose proof (sbits_range src (a_q a) 3 ltac:(lia)) as R. change (2 ^ 3) with 8 in R.
    pose proof (Step3Tables.tb_order_range (i_have (a_s a)) ltac:(lia)) as OR.
    apply go_ago; [|lia]. apply awfx_intro; simpl; rewrite ?Md'; auto; try ll_neq.
    + apply Step3Tables.tb_swf_lens; auto; [rewrite upd_Znth_Zlength; lia | apply Forall_upd_Znth; auto; lia | lia].
    + constructor; simpl; rewrite ?Md'; intros; try ll_neq; [|repeat split; ll_neq].
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
      intros k Hk. destruct (Z.eq_dec k (i_have (a_s a))).
      * subst k. rewrite upd_Znth_same by lia. lia.
      * pose proof (Step3Tables.tb_order_range k ltac:(lia)).
        rewrite upd_Znth_diff by (try lia; intros E; apply n; apply Step3Tables.tb_order_inj; auto; lia).
        apply LE; lia.
    + constructor; simpl; rewrite ?Md'; intros; ll_neq.
    + split; simpl; rewrite ?Md'; intros; ll_neq.
    + mdc; lia.
    + lia.
    + intros HH. exfalso. revert HH. clear. mdc. lia.
  - (* the code length code's table *)
    destruct (Step3Tables.tb_lenlens_zero 19 (a_s a) ltac:(lia) ltac:(simpl; lia) ZL FL LE)
      as (L0 & EZ & ZL0 & FL0 & LE0).
    rewrite EZ.
    assert (LE7: forall x, 0 <= x < 19 -> 0 <= Znth x L0 <= 7).
    { intros x Hx. destruct (Step3Tables.tb_order_surj x Hx) as (k & Hk & <-). split; [|apply LE0; auto].
      rewrite Forall_forall in FL0. apply FL0. apply Znth_In. pose proof (Step3Tables.tb_order_range k Hk). lia. }
    set (s0 := set_i_lenbits (set_i_distcode (set_i_lencode (set_i_next (set_i_have (set_i_lens (a_s a) L0) 19) 0)
                  (TCodes 0)) (TCodes 0)) 7).
    assert (S0: swf s0) by (destruct S; constructor; simpl; auto; unfold tref_ok, ENOUGH_CODES; lia).
    assert (F07: Forall (fun x => 0 <= x <= 7) (sublist 0 (0 + 19) (i_lens s0))).
    { apply Step3Tables.tb_forall_sublist; simpl; try lia. intros k Hk. apply LE7; lia. }
    assert (IN0: inputs_ok CODES (sublist 0 (0 + 19) (i_lens s0)) 7).
    { unfold inputs_ok. simpl. rewrite Zlength_sublist by lia. split; [unfold CODES; lia|].
      split; [unfold max_codes; simpl; lia|]. split; [|lia].
      eapply Forall_impl; [|exact F07]. unfold MAXBITS; simpl; intros; lia. }
    assert (CAP0: cap_ok CODES (sublist 0 (0 + 19) (i_lens s0)) 7 (ENOUGH_CODES - i_next s0)).
    { pose proof (Step3Tables.tb_maxlen_le _ F07) as ML. change (i_lens s0) with L0 in *.
      change (0 + 19) with 19 in *.
      unfold cap_ok. change (i_next s0) with 0. unfold LENS, CODES, DISTS, ENOUGH_CODES.
      split; [|split; intros; lia].
      intros _. split; [lia|]. split; [lia|]. rewrite Z.shiftl_1_l.
      assert (2 ^ maxlen (sublist 0 19 L0) <= 2 ^ 7) by (apply Z.pow_le_mono_r; lia).
      change (2 ^ 7) with 128 in *. lia. }
    cbv zeta. fold s0.
    destruct (call_table CODES 0 19 7 s0) as [[[r c] n] b] eqn:CT.
    destruct (Step3Tables.tb_call_table CODES 0 19 7 s0 r c n b Cover2.cover2_proof S0 ltac:(lia) ltac:(lia)
                ltac:(lia) IN0 CAP0 ltac:(intros; lia) CT) as (ZC1 & FC1 & R1 & Rn1 & Ry1).
    destruct (Z.eqb_spec r 0) as [R0|R0].
    2:{ cbn [negb]. destruct (Rn1 R0) as [-> ->].
        unfold abad, go_ok; simpl. split; [|split; [lia | split; [auto | left; auto]]].
        apply awfx_bad; simpl; auto; try lia.
        destruct S0; constructor; simpl; auto. }
    subst r. cbn [negb].
    destruct (Ry1 eq_refl) as (used & t & M & En & Ec & Zt & T & U & _).
    change (i_next s0) with 0 in *. rewrite sublist_nil in Ec. simpl app in Ec. subst c n.
    pose proof (tv_rb _ _ _ _ T) as RB.
    assert (RP: trep (fun i => Znth i t) b no_link).
    { assert (Z19: Zlength (sublist 0 (0 + 19) (i_lens s0)) = 19)
        by (rewrite Zlength_sublist; simpl; lia).
      assert (ZO: Zlength (sublist 0 ENOUGH_CODES (i_codes s0)) = ENOUGH_CODES - 0)
        by (rewrite Zlength_sublist; simpl; unfold ENOUGH_CODES in *; lia).
      rewrite <- ZO in CAP0.
      exact (proj1 TR CODES _ _ _ _ _ _ IN0 ltac:(intros; lia) CAP0
               ltac:(apply Forall_sublist; simpl; auto) M). }
    apply go_ago; [|lia]. apply awfx_intro; simpl; auto; try ll_neq.
    + apply MwfLemmas.swf_set_mode; [|mdc; lia].
      destruct S0; constructor; simpl; auto; unfold ENOUGH_CODES in *; lia.
    + constructor; simpl; intros; try ll_neq; [|repeat split; ll_neq].
      split; [lia|]. split; [lia|]. split; [lia|]. split; [reflexivity|]. split; [|intros; lia].
      apply Step3Tables.tb_tvalid_at with used t; simpl; auto; unfold ENOUGH_CODES in *; try lia.
    + constructor; simpl; intros; ll_neq.
    + split; simpl; intros; [ll_neq | exact RP].
    + mdc; lia.
Qed.
