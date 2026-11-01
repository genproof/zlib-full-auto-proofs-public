(* Part: fact_decode (facts.v): the model's table is the canonical decoder. Reuse fact_result.v by Require, never by copy. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.inftrees.facts.
Require Import Zlib.proof.inftrees.fact_result.
Require Import Zlib.proof.inftrees.model_inv.
Require Import Zlib.proof.inftrees.decode_defs.
Require Import Zlib.proof.inftrees.decode_step.
Require Import Zlib.proof.inftrees.decode_run.
Require Import Zlib.proof.inftrees.decode_walk.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* The Section Loop hypotheses for an accepted code (decode_defs.v dsetup_stmt).                  *)

Lemma left_loop_nonneg : forall k len left cnt x, 0 <= left -> left_loop k len left cnt = Some x -> 0 <= x.
Proof.
  induction k; intros len left cnt x H0 H; cbn [left_loop] in H.
  - inversion H; subst; auto.
  - destruct (2 * left - Znth len cnt <? 0) eqn:E; [discriminate|].
    apply Z.ltb_ge in E. eapply IHk; [|exact H]. lia.
Qed.

Lemma dsetup_ok : dsetup_stmt.
Proof.
  intros type lens req old lft Hsorted Hin Hcap Hold Hmx Hleft Htest Hover.
  destruct Hin as (Ht & Hcodes & Hl & Hreq).
  destruct (Hsorted lens Hl) as (SW & Sr & Ss & Sin & Scnt & Scl & Sk & Snil & Sends).
  destruct (classify_ok lens Hl) as (C1 & C2 & C3). rewrite Hleft in C3.
  assert (Hne: sl lens <> []) by (intro E; apply Snil in E; contradiction).
  destruct (Sends Hne) as (E0 & EN).
  assert (HN: 0 < Zlength (sl lens)).
  { destruct (sl lens) eqn:E; [contradiction|]. rewrite Zlength_cons. pose proof (Zlength_nonneg l). lia. }
  assert (HWl: Zlength (sl lens) = Zlength (sorted_syms lens)) by (unfold sl; apply Zlength_map).
  assert (Hmm: minlen lens <= maxlen lens) by (rewrite <- E0, <- EN; apply Ss; lia).
  assert (Hlft: 0 <= lft) by (eapply left_loop_nonneg; [|exact Hleft]; lia).
  assert (Hmn1: 1 <= minlen lens).
  { rewrite <- E0. rewrite Forall_forall in Sr. apply Sr. apply Znth_In. lia. }
  assert (Hinc: ksum (sl lens) < 2 ^ MAXBITS -> type <> CODES /\ maxlen lens = 1).
  { intros. rewrite Sk in H. assert (0 < lft) by lia.
    apply Z.ltb_lt in H0. rewrite H0 in Htest. cbn in Htest.
    apply orb_false_iff in Htest. destruct Htest as [T1 T2].
    apply Z.eqb_neq in T1. apply negb_false_iff, Z.eqb_eq in T2. auto. }
  unfold root_of in *.
  unfold dhyps. rewrite EN, E0.
  split; [auto|]. split; [auto|]. split; [auto|]. split.
  { intros. unfold sl. rewrite Znth_map by lia. auto. }
  split.
  { rewrite Forall_forall in SW |- *. intros x Hx. specialize (SW x Hx).
    unfold max_codes in Hcodes. destruct (type =? CODES); [|destruct (type =? LENS)]; lia. }
  split; [lia|]. split; [lia|]. split.
  { intros. destruct (Hinc H). lia. }
  split; [auto|]. split.
  { intros. destruct Hcap as (Hc & _). destruct (Hc H) as (A & _). lia. }
  destruct Hcap as (Hc & HL & HD). split; [auto|]. split.
  - rewrite <- pow2_shiftl by lia.
    destruct (Z.eq_dec type CODES) as [EC|EC].
    + destruct (Hc EC) as (A & B & D).
      replace (Z.max (Z.min req (maxlen lens)) (minlen lens)) with (maxlen lens) by lia. auto.
    + unfold over in Hover. apply orb_false_iff in Hover. destruct Hover as [O1 O2].
      unfold CODES, LENS, DISTS in *.
      assert (type = 1 \/ type = 2) as [-> | ->] by lia.
      * cbn in O1. apply Z.ltb_ge in O1. specialize (HL eq_refl). lia.
      * cbn in O2. apply Z.ltb_ge in O2. specialize (HD eq_refl). lia.
  - split; [auto|]. intros. destruct (Hinc H). auto.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The entry of a symbol means that symbol and is never a link.                                  *)

Lemma sym_entry_bits : forall type s b,
  e_op (sym_entry type s b) = e_op (sym_entry type s 0) /\ e_val (sym_entry type s b) = e_val (sym_entry type s 0).
Proof.
  intros. unfold sym_entry.
  destruct (s + 1 <? match_of type); [|destruct (match_of type <=? s)]; cbn; auto.
Qed.

Definition sym_chk (type: Z) (n: nat) : bool :=
  forallb (fun s => means_symbol type s (e_op (sym_entry type s 0)) (e_val (sym_entry type s 0)) &&
                    negb (is_link (e_op (sym_entry type s 0)))) (zseq 0 n).

Lemma sym_chk_0 : sym_chk 0 19 = true. Proof. vm_compute. reflexivity. Qed.
Lemma sym_chk_1 : sym_chk 1 288 = true. Proof. vm_compute. reflexivity. Qed.
Lemma sym_chk_2 : sym_chk 2 32 = true. Proof. vm_compute. reflexivity. Qed.

Lemma sym_chk_use : forall type n s, sym_chk type n = true -> 0 <= s < Z.of_nat n ->
  means_symbol type s (e_op (sym_entry type s 0)) (e_val (sym_entry type s 0)) = true /\
  is_link (e_op (sym_entry type s 0)) = false.
Proof.
  intros. unfold sym_chk in H. rewrite forallb_forall in H.
  specialize (H s ltac:(apply In_zseq; lia)). apply andb_prop in H. destruct H as [H1 H2].
  apply negb_true_iff in H2. auto.
Qed.

Lemma sym_means : forall type s b, 0 <= type <= 2 -> 0 <= s < max_codes type -> (type = CODES -> s < 19) ->
  means_symbol type s (e_op (sym_entry type s 0)) (e_val (sym_entry type s 0)) = true /\
  is_link (e_op (sym_entry type s b)) = false.
Proof.
  intros. rewrite (proj1 (sym_entry_bits type s b)).
  unfold max_codes, CODES in *.
  assert (type = 0 \/ type = 1 \/ type = 2) as [-> | [-> | ->]] by lia; cbn in H0.
  - apply (sym_chk_use 0 19); [apply sym_chk_0 | cbn; lia].
  - apply (sym_chk_use 1 288); [apply sym_chk_1 | cbn; lia].
  - apply (sym_chk_use 2 32); [apply sym_chk_2 | cbn; lia].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Assembly.                                                                                      *)

Lemma Znth_le_maxlen : forall lens s, 0 <= s < Zlength lens -> Znth s lens <= maxlen lens.
Proof.
  induction lens; intros.
  - rewrite Zlength_nil in H. lia.
  - rewrite Zlength_cons in H. unfold maxlen; cbn [fold_right]. fold (maxlen lens).
    destruct (Z.eq_dec s 0).
    + subst. rewrite Znth_0_cons. lia.
    + rewrite Znth_pos_cons by lia. specialize (IHlens (s - 1) ltac:(lia)). lia.
Qed.

Lemma fact_decode_ok : loop_facts -> sorted_stmt -> rfc_stmt -> bits_stmt -> subbits_stmt -> size_stmt -> fact_decode.
Proof.
  intros HL Hsorted Hrfc Hbits Hsub Hsize.
  intros type lens req old root used t Hin Hcap Hold H19 Hmodel.
  pose proof Hin as Hin'. destruct Hin' as (Ht & Hcodes & Hl & Hreq).
  rewrite <- maxlen_longest.
  unfold inflate_table_model in Hmodel.
  destruct (maxlen lens =? 0) eqn:Emx.
  - (* no symbol *)
    apply Z.eqb_eq in Emx. inversion Hmodel; subst root used t; clear Hmodel.
    assert (Hc2: 2 <= Zlength old).
    { destruct Hcap as (Hc & HL' & HD). unfold CODES, LENS, DISTS, ENOUGH_LENS, ENOUGH_DISTS in *.
      assert (type = 0 \/ type = 1 \/ type = 2) as [-> | [-> | ->]] by lia.
      - destruct (Hc eq_refl) as (_ & A & _). lia.
      - specialize (HL' eq_refl). lia.
      - specialize (HD eq_refl). lia. }
    split.
    + intros s Hs Hnz. exfalso. pose proof (Znth_le_maxlen lens s Hs).
      rewrite Forall_forall in Hl. pose proof (Hl (Znth s lens) (Znth_In _ _ Hs)). lia.
    + intros _ pat Hpat.
      assert (pat = 0 \/ pat = 1) as [-> | ->] by lia.
      * unfold walk. cbn - [Znth]. rewrite upd_Znth_diff by (rewrite ?upd_Znth_Zlength; lia).
        rewrite upd_Znth_same by lia. reflexivity.
      * unfold walk. cbn - [Znth]. rewrite upd_Znth_same by (rewrite ?upd_Znth_Zlength; lia). reflexivity.
  - apply Z.eqb_neq in Emx.
    destruct (left_final (counts lens)) as [lft|] eqn:Eleft; [|discriminate].
    destruct ((0 <? lft) && ((type =? CODES) || negb (maxlen lens =? 1))) eqn:Etest; [discriminate|].
    destruct (over type (Z.shiftl 1 (root_of req lens))) eqn:Eover; [discriminate|].
    assert (Hd: dhyps type lens (sorted_syms lens) (sl lens) (root_of req lens) old)
      by (eapply dsetup_ok; eauto).
    assert (Hfin: exists s, used = s_used s /\ t = finish s /\ root = root_of req lens /\
      (run type lens (sorted_syms lens) (root_of req lens) (maxlen lens) (length (sorted_syms lens))
         (init_state lens (root_of req lens) old) = Break s \/
       run type lens (sorted_syms lens) (root_of req lens) (maxlen lens) (length (sorted_syms lens))
         (init_state lens (root_of req lens) old) = Continue s)).
    { destruct (run type lens (sorted_syms lens) (root_of req lens) (maxlen lens) (length (sorted_syms lens))
                  (init_state lens (root_of req lens) old)) eqn:Er;
        inversion Hmodel; subst; eexists; eauto. }
    destruct Hfin as (s & -> & -> & -> & Hrun).
    destruct dstep_last_ok as [Hstep Hlast].
    pose proof (drun_ok type lens req old s Hsorted Hbits Hsub Hstep Hlast Hl Emx Hd Hrun) as Hf.
    destruct (Hsorted lens Hl) as (SW & Sr & Ss & Sin & Scnt & Scl & Sk & Snil & Sends).
    assert (Hne: sl lens <> []) by (intro E; apply Snil in E; contradiction).
    destruct (Sends Hne) as (E0 & EN).
    assert (HWl: Zlength (sl lens) = Zlength (sorted_syms lens)) by (unfold sl; apply Zlength_map).
    split.
    + intros s0 Hs0 Hnz x Hx.
      destruct (In_Znth _ _ (Sin s0 Hs0 Hnz)) as (j & Hj & Ej).
      assert (Hlj: Znth j (sl lens) = Znth s0 lens) by (unfold sl; rewrite Znth_map by lia; congruence).
      assert (Hcode: rfc_code lens s0 = dcode (sl lens) j).
      { pose proof (Hrfc lens Hl j ltac:(lia)) as R. rewrite Ej, Hlj in R. unfold dcode. rewrite Hlj, <- R.
        rewrite Z.div_mul; auto. apply Z.pow_nonzero; [lia|].
        rewrite Forall_forall in Hl. pose proof (Hl _ (Znth_In _ _ Hs0)). unfold MAXBITS in *. lia. }
      assert (Hlr: 1 <= Znth j (sl lens) <= MAXBITS).
      { rewrite Forall_forall in Sr. apply Sr. apply Znth_In. lia. }
      assert (Hnl: forall j' b, 0 <= j' < Zlength (sl lens) ->
                 is_link (e_op (sym_entry type (Znth j' (sorted_syms lens)) b)) = false).
      { intros. rewrite Forall_forall in SW. pose proof (SW _ (Znth_In j' (sorted_syms lens) ltac:(lia))).
        apply (sym_means type _ b); auto; lia. }
      pose proof (dwalk_ok type lens (sorted_syms lens) (sl lens) (root_of req lens) old (s_used s) (finish s)
                    Hd Hbits Hnl Hf j x) as Hw.
      assert (Hj': 0 <= j < Zlength (sl lens)) by lia. specialize (Hw Hj').
      rewrite EN, Hlj in Hw. pose proof (Znth_le_maxlen lens s0 Hs0).
      rewrite pow2_shiftl in Hx by lia. specialize (Hw Hx).
      unfold dhuff in Hw. rewrite Hlj, <- Hcode, Ej in Hw.
      do 2 eexists. split; [exact Hw|].
      rewrite Forall_forall in SW. pose proof (SW _ (Znth_In j (sorted_syms lens) ltac:(lia))). try rewrite Ej in H.
      apply (sym_means type s0 0); auto; lia.
    + intros Hk pat Hpat.
      rewrite <- Sk in Hk. change GP_KRAFT_ONE with (2 ^ MAXBITS) in Hk.
      destruct Hf as (_ & _ & _ & Hinc). destruct (Hinc Hk) as (_ & _ & -> & -> & Hent).
      destruct (maxlen lens =? 0) eqn:E; [apply Z.eqb_eq in E; contradiction|].
      assert (pat = 1) by lia. subst pat.
      unfold walk. cbn - [Znth]. rewrite Hent. reflexivity.
Qed.
