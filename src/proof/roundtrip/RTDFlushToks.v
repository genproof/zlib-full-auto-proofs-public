(* RT-D part FLUSH: send_tree's tokens expand to the code lengths and are valid (interface: RTDFlushDefs.v). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDFlushDefs.
Import ListNotations.
Local Open Scope Z_scope.

Lemma rtdk_expand_app : forall a b E, F.tok_expand E (a ++ b) = F.tok_expand (F.tok_expand E a) b.
Proof. induction a; intros; simpl; auto. Qed.

Lemma rtdk_ok_app : forall cl a b E,
  F.toks_ok cl E a -> F.toks_ok cl (F.tok_expand E a) b -> F.toks_ok cl E (a ++ b).
Proof. induction a; intros b E H1 H2; simpl in *; [auto|]. destruct H1; split; auto. Qed.

Lemma rtdk_expand_lens : forall x k E, F.tok_expand E (repeat (F.CLen x) k) = E ++ repeat x k.
Proof.
  induction k; intros; simpl; [rewrite app_nil_r; auto|].
  rewrite IHk, <- app_assoc. reflexivity.
Qed.

Lemma rtdk_ok_lens : forall cl x k E, 0 <= x <= 15 -> Znth x cl <> 0 -> F.toks_ok cl E (repeat (F.CLen x) k).
Proof. induction k; intros; simpl; auto. Qed.

Lemma rtdk_last_app : forall (E : list Z) x d, last (E ++ [x]) d = x.
Proof. intros. apply last_last. Qed.

Lemma rtdk_repeat_S : forall (x : Z) k, x :: repeat x k = repeat x (S k).
Proof. reflexivity. Qed.

Lemma rtdk_out : forall E nl p cnt mx mn,
  1 <= cnt <= mx -> 0 <= nl <= 15 ->
  ((mx = 138 /\ mn = 3 /\ nl = 0) \/ (mx = 6 /\ mn = 3 /\ nl = p /\ nl <> 0) \/
   (mx = 7 /\ mn = 4 /\ nl <> 0 /\ nl <> p)) ->
  (nl = p -> E <> [] /\ last E 0 = nl) ->
  F.tok_expand E
    (if cnt <? mn then repeat (F.CLen nl) (Z.to_nat cnt)
     else if negb (nl =? 0) then
       (if negb (nl =? p) then [F.CLen nl; F.CRep (cnt - 1)] else [F.CRep cnt])
     else [F.CZeros cnt]) = E ++ repeat nl (Z.to_nat cnt) /\
  forall cl,
    (forall q, In q
       (if cnt <? mn then repeat (nl, 0) (Z.to_nat cnt)
        else if negb (nl =? 0) then
          (if negb (nl =? p) then [(nl, 0)] else []) ++ [(REP_3_6, 2)]
        else if cnt <=? 10 then [(REPZ_3_10, 3)]
        else [(REPZ_11_138, 7)]) -> Znth (fst q) cl <> 0) ->
    F.toks_ok cl E
      (if cnt <? mn then repeat (F.CLen nl) (Z.to_nat cnt)
       else if negb (nl =? 0) then
         (if negb (nl =? p) then [F.CLen nl; F.CRep (cnt - 1)] else [F.CRep cnt])
       else [F.CZeros cnt]).
Proof.
  intros E nl p cnt mx mn Hc Hnl Hm Hp.
  destruct (Z.ltb_spec cnt mn).
  - split; [apply rtdk_expand_lens|]. intros cl Hq. apply rtdk_ok_lens; auto.
    apply (Hq (nl, 0)). destruct (Z.to_nat cnt) eqn:E1; [lia|]. left; auto.
  - destruct (Z.eqb_spec nl 0); cbn [negb].
    + subst nl. assert (mx = 138 /\ mn = 3) as [-> ->] by lia.
      cbn [F.tok_expand F.tok_vals]. split; [rewrite ?app_nil_r; reflexivity|].
      intros cl Hq. cbn [F.toks_ok F.tok_ok]. split; auto. split; [lia|].
      destruct (Z.leb_spec cnt 10).
      * apply (Hq (REPZ_3_10, 3)); left; auto.
      * apply (Hq (REPZ_11_138, 7)); left; auto.
    + destruct (Z.eqb_spec nl p); cbn [negb].
      * subst p. assert (mx = 6 /\ mn = 3) as [-> ->] by lia. destruct (Hp eq_refl) as [HE HL].
        cbn [F.tok_expand F.tok_vals]. rewrite HL. split; [rewrite ?app_nil_r; reflexivity|].
        intros cl Hq. cbn [F.toks_ok F.tok_ok]. split; auto. split; auto. split; [lia|].
        apply (Hq (REP_3_6, 2)); left; auto.
      * assert (mx = 7 /\ mn = 4) as [-> ->] by lia.
        cbn [F.tok_expand F.tok_vals]. rewrite rtdk_last_app. split.
        { rewrite ?app_nil_r, <- ?app_assoc. cbn [app]. rewrite rtdk_repeat_S. do 2 f_equal. lia. }
        intros cl Hq. cbn [F.toks_ok F.tok_ok]. split; [split; [lia|]; apply (Hq (nl, 0)); left; auto|].
        split; auto. split; [destruct E; discriminate|]. split; [lia|].
        apply (Hq (REP_3_6, 2)); right; left; auto.
Qed.

Section Loop.
Variables (lens : list Z) (mc : Z).
Hypotheses (Hmc : 0 <= mc) (Hlen : mc + 1 < Zlength lens) (Hg : Znth (mc + 1) lens = 65535)
  (Hr : forall i, 0 <= i <= mc -> 0 <= Znth i lens <= 15).

Definition rtdk_inv (n p nl c mx mn : Z) : Prop :=
  0 <= c <= n /\ n <= mc + 1 /\ nl = Znth n lens /\ (forall i, n - c <= i < n -> Znth i lens = nl) /\
  ((n - c = 0 /\ p = -1) \/ (0 < n - c /\ p = Znth (n - c - 1) lens)) /\ c < mx /\
  ((mx = 138 /\ mn = 3 /\ nl = 0) \/ (mx = 6 /\ mn = 3 /\ nl = p /\ nl <> 0) \/
   (mx = 7 /\ mn = 4 /\ nl <> 0 /\ nl <> p)).

Lemma rtdk_run : forall n c x, 0 <= c -> 0 <= n - c -> n + 1 <= Zlength lens ->
  (forall i, n - c <= i <= n -> Znth i lens = x) ->
  sublist 0 (n + 1) lens = sublist 0 (n - c) lens ++ repeat x (Z.to_nat (c + 1)).
Proof.
  intros n c x Hc Hn Hl Hi.
  rewrite (sublist_split 0 (n - c) (n + 1)) by lia. f_equal.
  apply list_solver.Znth_eq_ext; rewrite ?Zlength_sublist, ?Zlength_repeat by lia; try lia.
  intros i Hi'. rewrite Znth_sublist, Znth_repeat' by lia. apply Hi. lia.
Qed.

Lemma rtdk_loop : forall fuel n p nl c mx mn prev,
  rtdk_inv n p nl c mx mn -> mc + 1 - n <= Z.of_nat fuel ->
  F.tok_expand (prev ++ sublist 0 (n - c) lens) (tl_loop fuel lens mc n p nl c mx mn) =
    prev ++ sublist 0 (mc + 1) lens /\
  (forall cl, (forall q, In q (Header.syms_loop fuel lens mc n p nl c mx mn) -> Znth (fst q) cl <> 0) ->
    F.toks_ok cl (prev ++ sublist 0 (n - c) lens) (tl_loop fuel lens mc n p nl c mx mn)).
Proof.
  induction fuel as [|fuel IH]; intros n p nl c mx mn prev Hinv Hf.
  - destruct Hinv as (Hc & Hn & Hnl & Hrun & _).
    assert (n = mc + 1) by lia. subst n.
    assert (c = 0).
    { destruct (Z.eq_dec c 0); auto. pose proof (Hrun mc ltac:(lia)). pose proof (Hr mc ltac:(lia)). lia. }
    subst c. cbn [tl_loop Header.syms_loop F.tok_expand F.toks_ok]. rewrite Z.sub_0_r. auto.
  - cbn [tl_loop Header.syms_loop].
    destruct (Z.leb_spec n mc) as [Hle|Hgt].
    2:{ destruct Hinv as (Hc & Hn & Hnl & Hrun & _).
        assert (n = mc + 1) by lia. subst n.
        assert (c = 0).
        { destruct (Z.eq_dec c 0); auto. pose proof (Hrun mc ltac:(lia)). pose proof (Hr mc ltac:(lia)). lia. }
        subst c. cbn [F.tok_expand F.toks_ok]. rewrite Z.sub_0_r. auto. }
    pose proof Hinv as (Hc & Hn & Hnl & Hrun & Hp & Hcm & Hm).
    pose proof (Hr n ltac:(lia)) as Hrn.
    destruct ((c + 1 <? mx) && (nl =? Znth (n + 1) lens)) eqn:Hcont.
    + apply andb_true_iff in Hcont as [Hc1 Hc2]. apply Z.ltb_lt in Hc1. apply Z.eqb_eq in Hc2.
      replace (n - c) with (n + 1 - (c + 1)) by lia.
      apply IH; [|lia].
      unfold rtdk_inv. replace (n + 1 - (c + 1)) with (n - c) by lia.
      repeat split; try lia; auto.
      intros i Hi. destruct (Z.eq_dec i n); [subst; congruence|]. rewrite Hrun by lia. auto.
    + assert (Hcnt : c + 1 <= mx) by lia.
      assert (Hsub : sublist 0 (n + 1) lens = sublist 0 (n - c) lens ++ repeat nl (Z.to_nat (c + 1))).
      { apply rtdk_run; try lia. intros i Hi. destruct (Z.eq_dec i n); [subst; auto|]. apply Hrun; lia. }
      assert (Hcnt' : c + 1 = mx \/ nl <> Znth (n + 1) lens).
      { apply andb_false_iff in Hcont as [H|H]; [apply Z.ltb_ge in H; lia|apply Z.eqb_neq in H; auto]. }
      destruct (rtdk_out (prev ++ sublist 0 (n - c) lens) nl p (c + 1) mx mn ltac:(lia) ltac:(lia) Hm)
        as [Hout1 Hout2].
      { intros ->. destruct Hp as [[_ Hp]|[Hp1 Hp2]]; [lia|]. split.
        - intro HE. apply (f_equal (@Zlength Z)) in HE. rewrite Zlength_app, Zlength_sublist in HE by lia.
          pose proof (Zlength_nonneg prev). rewrite Zlength_nil in HE. lia.
        - rewrite (sublist_split 0 (n - c - 1) (n - c)) by lia. replace (sublist (n - c - 1) (n - c) lens) with [Znth (n - c - 1) lens]
            by (rewrite <- sublist_len_1 by lia; f_equal; lia).
          rewrite app_assoc. rewrite rtdk_last_app. auto. }
      set (out := if c + 1 <? mn then _ else _) in *.
      set (sout := if c + 1 <? mn then _ else _) in *.
      assert (Hinv' : forall mx' mn',
         (mx', mn') = (if Znth (n + 1) lens =? 0 then (138, 3)
                       else if nl =? Znth (n + 1) lens then (6, 3) else (7, 4)) ->
         rtdk_inv (n + 1) nl (Znth (n + 1) lens) 0 mx' mn').
      { intros mx' mn' Heq. unfold rtdk_inv. rewrite Z.sub_0_r.
        replace (n + 1 - 1) with n by lia.
        destruct (Z.eqb_spec (Znth (n + 1) lens) 0);
          [|destruct (Z.eqb_spec nl (Znth (n + 1) lens))]; inversion Heq; subst mx' mn';
          repeat split; try lia; auto. }
      destruct (if Znth (n + 1) lens =? 0 then _ else _) as [mx' mn'] eqn:Hmm.
      destruct (IH (n + 1) nl (Znth (n + 1) lens) 0 mx' mn' prev (Hinv' mx' mn' eq_refl) ltac:(lia))
        as [IH1 IH2].
      rewrite Z.sub_0_r in IH1, IH2. rewrite Hsub, app_assoc in IH1, IH2.
      split.
      * rewrite rtdk_expand_app, Hout1. auto.
      * intros cl Hq. apply rtdk_ok_app.
        -- apply Hout2. intros q Hin. apply Hq. apply in_or_app; auto.
        -- rewrite Hout1. apply IH2. intros q Hin. apply Hq. apply in_or_app; auto.
Qed.

End Loop.

Theorem rtd_toks_ok : toks_stmt.
Proof.
  unfold toks_stmt, tree_toks, Header.tree_syms, Header.init_counts. intros lens mc Hmc Hlen Hg Hr.
  assert (Hinv : rtdk_inv lens mc 0 (-1) (Znth 0 lens) 0
                   (fst (if Znth 0 lens =? 0 then (138, 3) else (7, 4)))
                   (snd (if Znth 0 lens =? 0 then (138, 3) else (7, 4)))).
  { pose proof (Hr 0 ltac:(lia)). unfold rtdk_inv.
    destruct (Z.eqb_spec (Znth 0 lens) 0); simpl; repeat split; try lia; auto. }
  destruct (Znth 0 lens =? 0); simpl in Hinv;
  (split; [intros prev | intros cl prev Hq]);
  (destruct (rtdk_loop lens mc Hmc Hlen Hg Hr (Z.to_nat (mc + 1)) _ _ _ _ _ _ prev Hinv ltac:(lia)) as [H1 H2]);
  rewrite Z.sub_0_r, sublist_nil, app_nil_r in H1, H2; auto.
Qed.
