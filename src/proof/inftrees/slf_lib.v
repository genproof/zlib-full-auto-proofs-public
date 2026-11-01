(* Part of loop_facts: the loop invariants of the model (model_inv.v, loop_facts) from the
   sibling facts sorted_stmt / bits_stmt / subbits_stmt and fact_result.v's Section Loop (step_inv).
   Pure Coq. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.inftrees.model_inv.
Require Import Zlib.proof.inftrees.facts.
Require Import Zlib.proof.inftrees.fact_result.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* The loop: unfolding at the end, composition.                                                    *)

Lemma slf_run_S : forall type lens W root mx k s,
  run type lens W root mx (S k) s =
  match run type lens W root mx k s with Continue s' => step type lens W root mx s' | o => o end.
Proof.
  induction k; intros s.
  - cbn [run]. destruct (step type lens W root mx s); reflexivity.
  - change (run type lens W root mx (S (S k)) s) with
      (match step type lens W root mx s with Continue s' => run type lens W root mx (S k) s' | o => o end).
    cbn [run]. destruct (step type lens W root mx s); auto. exact (IHk _).
Qed.

Lemma slf_run_add : forall type lens W root mx a b s,
  run type lens W root mx (a + b) s =
  match run type lens W root mx a s with Continue s' => run type lens W root mx b s' | o => o end.
Proof.
  induction a; intros b s; [reflexivity|].
  cbn [Nat.add run]. destruct (step type lens W root mx s); auto.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The table is never read by the control flow: the run without the table only depends on the
   state without the table.                                                                       *)

Definition slf_nt (s: state) : state :=
  mkSt (s_huff s) (s_sym s) (s_len s) (s_curr s) (s_drop s) (s_low s) (s_used s) (s_next s) (s_cnt s) [].
Definition slf_set (s: state) (t: list entry) : state :=
  mkSt (s_huff s) (s_sym s) (s_len s) (s_curr s) (s_drop s) (s_low s) (s_used s) (s_next s) (s_cnt s) t.
Definition slf_onl (o: outcome) : outcome :=
  match o with Continue s => Continue (slf_nt s) | Break s => Break (slf_nt s) | Full s => Full (slf_nt s) end.
Definition slf_otab (o: outcome) : list entry :=
  match o with Continue s => s_tab s | Break s => s_tab s | Full s => s_tab s end.

Lemma slf_step_nt : forall type lens W root mx s t,
  slf_onl (step type lens W root mx (slf_set s t)) = slf_onl (step type lens W root mx s).
Proof.
  intros. destruct s as [h0 y0 l0 c0 d0 lo0 u0 n0 cn0 t0]. unfold step, slf_set. cbn [s_huff s_sym s_len s_curr s_drop s_low s_used s_next s_cnt s_tab].
  destruct (_ && _); [reflexivity|]. destruct (_ && _); [destruct (over _ _)|]; reflexivity.
Qed.

Lemma slf_nt_eq : forall s1 s2, slf_nt s1 = slf_nt s2 -> s1 = slf_set s2 (s_tab s1).
Proof. intros [] [] H; unfold slf_nt, slf_set in *; cbn in *; inversion H; subst; reflexivity. Qed.

Lemma slf_set_set : forall s t u, slf_set (slf_set s t) u = slf_set s u.
Proof. reflexivity. Qed.

Lemma slf_set_tab : forall s, slf_set s (s_tab s) = s.
Proof. intros []; reflexivity. Qed.

Lemma slf_run_nt : forall type lens W root mx k s t,
  slf_onl (run type lens W root mx k (slf_set s t)) = slf_onl (run type lens W root mx k s).
Proof.
  induction k; intros s t; [reflexivity|].
  cbn [run]. pose proof (slf_step_nt type lens W root mx s t) as E.
  destruct (step type lens W root mx (slf_set s t)) as [a|a|a];
  destruct (step type lens W root mx s) as [b|b|b]; cbn [slf_onl] in E; try discriminate;
    try exact E.
  assert (E2: slf_nt a = slf_nt b).
  { change (slf_nt a) with (match Continue (slf_nt a) with Continue x => x | _ => slf_nt a end).
    rewrite E. reflexivity. }
  apply slf_nt_eq in E2. rewrite E2. apply IHk.
Qed.

Lemma slf_upd_len : forall {A} i (l: list A) x, Zlength (upd_Znth i l x) = Zlength l.
Proof. intros. exact (upd_len 0 i l x). Qed.

Lemma slf_rep_fill_len : forall n t base incr e, Zlength (rep_fill t base incr n e) = Zlength t.
Proof.
  induction n; intros; cbn [rep_fill]; auto. rewrite IHn, slf_upd_len. reflexivity.
Qed.

Lemma slf_step_len : forall type lens W root mx s,
  Zlength (slf_otab (step type lens W root mx s)) = Zlength (s_tab s).
Proof.
  intros. destruct s as [h0 y0 l0 c0 d0 lo0 u0 n0 cn0 t0]. unfold step. cbn [s_huff s_sym s_len s_curr s_drop s_low s_used s_next s_cnt s_tab].
  destruct (_ && _); [cbn [slf_otab s_tab]; apply slf_rep_fill_len|].
  destruct (_ && _); [destruct (over _ _)|]; cbn [slf_otab s_tab]; rewrite ?slf_upd_len; apply slf_rep_fill_len.
Qed.

Lemma slf_run_len : forall type lens W root mx k s,
  Zlength (slf_otab (run type lens W root mx k s)) = Zlength (s_tab s).
Proof.
  induction k; intros; [reflexivity|]. cbn [run].
  pose proof (slf_step_len type lens W root mx s).
  destruct (step type lens W root mx s); auto. rewrite IHk. auto.
Qed.

(* What one Continue step does to the fields the invariants need. *)
Lemma slf_step_cont : forall type lens W root mx s s',
  step type lens W root mx s = Continue s' ->
  s_cnt s' = upd_Znth (s_len s) (s_cnt s) (Znth (s_len s) (s_cnt s) - 1) /\
  (s_used s' = s_used s \/ over type (s_used s') = false).
Proof.
  intros. destruct s as [h0 y0 l0 c0 d0 lo0 u0 n0 cn0 t0]. unfold step in H. cbn [s_huff s_sym s_len s_curr s_drop s_low s_used s_next s_cnt s_tab] in *.
  destruct (_ && _); [discriminate|].
  destruct (_ && _); [destruct (over _ _) eqn:Eo|]; inversion H; subst; cbn [s_cnt s_used s_len]; auto.
Qed.

(* sub_loop never goes beyond max - drop (or its start). *)
Lemma slf_sub_loop_le : forall k curr drop mx left cnt,
  sub_loop k curr drop mx left cnt <= Z.max curr (mx - drop).
Proof.
  induction k; intros; cbn [sub_loop]; [lia|].
  destruct (curr + drop <? mx) eqn:E; [|lia]. apply Z.ltb_lt in E.
  destruct (_ <=? 0); [lia|]. specialize (IHk (curr + 1) drop mx (2 * (left - Znth (curr + drop) cnt)) cnt). lia.
Qed.

Lemma slf_left_loop_nonneg : forall k len left cnt x, 0 <= left -> left_loop k len left cnt = Some x -> 0 <= x.
Proof.
  induction k; intros; cbn [left_loop] in H0; [inversion H0; lia|].
  destruct (2 * left - Znth len cnt <? 0) eqn:E; [discriminate|]. apply Z.ltb_ge in E. eapply IHk; eauto.
Qed.

Lemma slf_count_le : forall l x, 0 <= count_len l x <= Zlength l.
Proof.
  intros. unfold count_len. split; [apply Zlength_nonneg|].
  induction l; cbn [filter]; [lia|]. rewrite Zlength_cons. destruct (x =? a); [rewrite Zlength_cons|]; lia.
Qed.

Lemma slf_Forall_Znth : forall {A} {d: Inhabitant A} (P: A -> Prop) l,
  (forall i, 0 <= i < Zlength l -> P (Znth i l)) -> Forall P l.
Proof.
  intros. apply Forall_forall. intros x Hx. apply In_Znth in Hx. destruct Hx as [i [Hi <-]]. auto.
Qed.

Lemma slf_step_break : forall type lens W root mx s s',
  step type lens W root mx s = Break s' ->
  Znth (s_len s) (s_cnt s) - 1 = 0 /\ s_len s = mx /\ s_huff s' = next_huff (s_huff s) (s_len s) /\
  s_next s' = s_next s /\ s_used s' = s_used s.
Proof.
  intros. destruct s as [h0 y0 l0 c0 d0 lo0 u0 n0 cn0 t0]. unfold step in H.
  cbn [s_huff s_sym s_len s_curr s_drop s_low s_used s_next s_cnt s_tab] in *.
  destruct (_ && _) eqn:E.
  - apply andb_prop in E. destruct E as [E1 E2]. apply Z.eqb_eq in E1, E2.
    inversion H; subst; cbn [s_huff s_used s_next]. auto.
  - repeat match type of H with context [if ?b then _ else _] => destruct b end; discriminate.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* An accepted code: the hypotheses of fact_result.v's Section Loop.                               *)

Section Main.
Variables (type: Z) (lens: list Z) (req: Z) (old: list entry).
Hypothesis HS : sorted_stmt.
Hypothesis HB : bits_stmt.
Hypothesis HSB : subbits_stmt.
Hypothesis HSS : sorted_syms_ok_stmt.
Hypothesis Hacc : acc_ok type lens req (Zlength old).

Local Notation ls := (sl lens).
Local Notation W := (sorted_syms lens).
Local Notation root := (root_of req lens).
Local Notation mx := (maxlen lens).
Local Notation old' := (map (fun _ : entry => mkE 0 0 0) old).

Lemma slf_lens : Forall (fun l => 0 <= l <= MAXBITS) lens.
Proof. destruct Hacc as ((_ & _ & H & _) & _). auto. Qed.

Lemma slf_lens_len : Zlength lens <= 288.
Proof.
  destruct Hacc as ((Ht & H & _) & _). unfold max_codes, CODES, LENS in H.
  destruct (type =? 0); [lia|]. destruct (type =? 1); lia.
Qed.

Lemma slf_type : 0 <= type <= 2.
Proof. destruct Hacc as ((Ht & _) & _). auto. Qed.

Lemma slf_mx : 1 <= mx.
Proof. destruct Hacc as (_ & _ & H & _). auto. Qed.

Lemma slf_HS : 
  Forall (fun s => 0 <= s < Zlength lens) W /\
  Forall (fun l => 1 <= l <= MAXBITS) ls /\
  (forall a b, 0 <= a -> a <= b < Zlength ls -> Znth a ls <= Znth b ls) /\
  (forall l, 1 <= l <= MAXBITS -> Znth l (counts lens) = count_len ls l) /\
  Zlength (counts lens) = 16 /\
  ksum ls = kraft lens /\
  (ls = [] <-> mx = 0) /\
  (ls <> [] -> Znth 0 ls = minlen lens /\ Znth (Zlength ls - 1) ls = mx).
Proof.
  destruct (HS lens slf_lens) as (H1 & H2 & H3 & _ & H5 & H6 & H7 & H8 & H9). tauto.
Qed.

Lemma slf_range : Forall (fun l => 1 <= l <= MAXBITS) ls.
Proof. apply slf_HS. Qed.
Lemma slf_sorted : forall a b, 0 <= a -> a <= b < Zlength ls -> Znth a ls <= Znth b ls.
Proof. apply slf_HS. Qed.
Lemma slf_N : 0 < Zlength ls.
Proof.
  destruct slf_HS as (_ & _ & _ & _ & _ & _ & H & _). pose proof slf_mx.
  destruct ls eqn:E; [destruct H as [H _]; specialize (H eq_refl); lia|].
  rewrite Zlength_cons. pose proof (Zlength_nonneg l). lia.
Qed.
Lemma slf_ends : Znth 0 ls = minlen lens /\ Znth (Zlength ls - 1) ls = mx.
Proof.
  destruct slf_HS as (_ & _ & _ & _ & _ & _ & _ & H). apply H.
  intro E. pose proof slf_N. rewrite E in H0. rewrite Zlength_nil in H0. lia.
Qed.
Lemma slf_len_W : Zlength W = Zlength ls.
Proof. unfold sl. rewrite Zlength_map. auto. Qed.
Lemma slf_W_le : Zlength W <= Zlength lens.
Proof. apply (HSS lens slf_lens). Qed.
Lemma slf_Wls : forall i, 0 <= i < Zlength ls -> Znth (Znth i W) lens = Znth i ls.
Proof. intros. unfold sl. rewrite Znth_map; auto. rewrite <- slf_len_W in H. auto. Qed.
Lemma slf_Wr : Forall (fun s => 0 <= s <= 65535) W.
Proof.
  destruct slf_HS as (H & _). pose proof slf_lens_len.
  eapply Forall_impl; [|exact H]. intros. cbv beta in H1. lia.
Qed.
Lemma slf_mx15 : mx <= 15.
Proof.
  destruct slf_ends as [_ E]. rewrite <- E. pose proof slf_N.
  pose proof (Forall_Znth _ (sl lens) (Zlength ls - 1) ltac:(lia) slf_range). cbv beta in H0. unfold MAXBITS in H0. lia.
Qed.
Lemma slf_min_le : 1 <= minlen lens <= mx.
Proof.
  destruct slf_ends as [E1 E2]. rewrite <- E1, <- E2. pose proof slf_N.
  pose proof (Forall_Znth _ (sl lens) 0 ltac:(lia) slf_range). cbv beta in H0; unfold MAXBITS in H0.
  pose proof (slf_sorted 0 (Zlength ls - 1)). lia.
Qed.
Lemma slf_root : minlen lens <= root <= mx.
Proof. pose proof slf_min_le. unfold root_of. lia. Qed.
Lemma slf_Hroot : Znth 0 ls <= root <= Znth (Zlength ls - 1) ls.
Proof. destruct slf_ends as [-> ->]. apply slf_root. Qed.
Lemma slf_lft : exists lft, left_final (counts lens) = Some lft /\ 0 <= lft /\ lft = 2 ^ MAXBITS - kraft lens /\
  ((0 <? lft) && ((type =? CODES) || negb (mx =? 1))) = false.
Proof.
  destruct Hacc as (_ & _ & _ & (lft & E & B) & _). exists lft. split; [auto|]. split.
  - eapply slf_left_loop_nonneg; [|exact E]. lia.
  - split; [|auto]. destruct (classify_proof lens slf_lens) as (_ & _ & C). rewrite E in C. auto.
Qed.
Lemma slf_k : ksum ls <= 2 ^ MAXBITS.
Proof.
  destruct slf_lft as (lft & _ & H1 & H2 & _). destruct slf_HS as (_ & _ & _ & _ & _ & K & _). lia.
Qed.
Lemma slf_inc : ksum ls < 2 ^ MAXBITS -> Znth (Zlength ls - 1) ls <= root.
Proof.
  intros. destruct slf_lft as (lft & _ & H1 & H2 & B). destruct slf_HS as (_ & _ & _ & _ & _ & K & _).
  assert (0 < lft) by lia. apply Z.ltb_lt in H0. rewrite H0 in B. cbn [andb] in B.
  apply orb_false_iff in B. destruct B as [_ B]. apply negb_false_iff, Z.eqb_eq in B.
  destruct slf_ends as [_ ->]. pose proof slf_root. pose proof slf_min_le. lia.
Qed.
Lemma slf_codes_root : type = CODES -> root = mx.
Proof.
  intros. destruct Hacc as (_ & (Hc & _) & _). destruct (Hc H) as (H1 & _).
  pose proof slf_min_le. unfold root_of. lia.
Qed.
Lemma slf_codes : type = CODES -> Znth (Zlength ls - 1) ls <= root.
Proof. intros. rewrite slf_codes_root by auto. destruct slf_ends as [_ ->]. lia. Qed.
Lemma slf_cap : (type = LENS -> ENOUGH_LENS <= Zlength old') /\ (type = DISTS -> ENOUGH_DISTS <= Zlength old').
Proof. rewrite Zlength_map. destruct Hacc as (_ & (_ & H1 & H2) & _). auto. Qed.
Lemma slf_cap0 : 2 ^ root <= Zlength old.
Proof.
  destruct Hacc as (_ & (Hc & H1 & H2) & _ & _ & Ho). pose proof slf_type. pose proof slf_root.
  pose proof slf_min_le.
  rewrite pow2_shiftl in Ho by lia.
  unfold over, CODES, LENS, DISTS, ENOUGH_LENS, ENOUGH_DISTS in *.
  assert (type = 0 \/ type = 1 \/ type = 2) as [Et | [Et | Et]] by lia; rewrite Et in Ho; cbn in Ho; rewrite ?orb_false_r, ?orb_false_l in Ho.
  - rewrite slf_codes_root by auto. destruct (Hc Et) as (_ & _ & Hc3).
    rewrite pow2_shiftl in Hc3 by lia. auto.
  - apply Z.ltb_ge in Ho. specialize (H1 Et). lia.
  - apply Z.ltb_ge in Ho. specialize (H2 Et). lia.
Qed.

Lemma slf_step_inv : forall i s, inv ls root old' i s -> i + 1 < Zlength ls ->
  (exists s', step type lens W root mx s = Continue s' /\ inv ls root old' (i + 1) s') \/
  (exists s', step type lens W root mx s = Full s').
Proof.
  intros. destruct slf_ends as [_ E]. rewrite <- E.
  destruct (step_inv type lens W ls root old' slf_range slf_sorted slf_N slf_Wls slf_Wr slf_Hroot
              slf_k slf_inc slf_type slf_codes slf_cap HB HSB i s H H0) as [(s' & A & B)|(s' & A & _)].
  - left; eauto.
  - right; eauto.
Qed.

Lemma slf_last_break : forall i s, inv ls root old' i s -> i = Zlength ls - 1 ->
  exists s', step type lens W root mx s = Break s'.
Proof.
  intros i s Hinv Hi.
  destruct Hinv as (Hi0 & Hsym & Hlen & Hhuff & Hcl & Hcnt & _).
  pose proof (Forall_Znth _ (sl lens) i Hi0 slf_range) as Hl. cbv beta in Hl.
  assert (Hc: Znth (s_len s) (s_cnt s) = 1).
  { rewrite Hcnt by (rewrite Hlen; auto). subst i.
    rewrite sublist_one by lia. unfold count_len; cbn [filter]. rewrite Hlen, Z.eqb_refl. reflexivity. }
  unfold step. rewrite Hc. cbn [Z.sub Z.eqb andb].
  replace (s_len s =? mx) with true.
  - eexists. reflexivity.
  - symmetry. apply Z.eqb_eq. rewrite Hlen. subst i. rewrite Hi. apply slf_ends.
Qed.

Lemma slf_reach_inv : forall k s, reach type lens req old k s ->
  Z.of_nat k < Zlength ls /\ (exists t, inv ls root old' (Z.of_nat k) (slf_set s t)) /\
  Znth 0 (s_cnt s) = count_len lens 0 /\ over type (s_used s) = false.
Proof.
  pose proof slf_N as HN. pose proof slf_root as Hr. pose proof slf_min_le as Hm.
  destruct slf_ends as [E0 E1].
  induction k; intros s H.
  - unfold reach in H. cbn [run] in H. injection H as <-.
    change (Z.of_nat 0) with 0. split; [lia|]. split; [exists old'|].
    + unfold inv, slf_set, init_state. cbn [s_huff s_sym s_len s_curr s_drop s_low s_used s_next s_cnt s_tab].
      change (Z.of_nat 0) with 0.
      destruct slf_HS as (_ & _ & _ & Hc & Hc16 & _).
      split; [lia|]. split; [auto|]. split; [auto|]. split.
      { rewrite kpre_0, Z.div_0_l, reverse_bits_0; auto. apply Z.pow_nonzero; [lia|].
        pose proof (Forall_Znth _ (sl lens) 0 ltac:(lia) slf_range). cbv beta in H; unfold MAXBITS in *. lia. }
      split; [auto|]. split.
      { intros. rewrite sublist_same by lia. auto. }
      split; [intros; split; [auto|]; split; [auto|]; split; [auto|]; split; [apply pow2_shiftl; lia|auto]|].
      split; [intros; lia|].
      split; [auto|]. split.
      { apply Forall_map. apply Forall_forall. intros. unfold Basics.compose, entry_ok; cbn [e_op e_bits e_val]. lia. }
      split; [auto|]. rewrite Zlength_map, pow2_shiftl by lia. apply slf_cap0.
    + destruct Hacc as (_ & _ & _ & _ & Ho). cbn [s_cnt s_used init_state]. split; [|auto]. apply Znth_counts. lia.
  - unfold reach in H. rewrite slf_run_S in H. fold (reach type lens req old k) in IHk.
    destruct (run type lens W root mx k (init_state lens root old)) as [s0|s0|s0] eqn:Er; try discriminate.
    destruct (IHk s0 Er) as (Hk & (t0 & Hinv) & H0 & Hov).
    pose proof (slf_step_nt type lens W root mx s0 t0) as Ent.
    assert (Hcont: forall s', step type lens W root mx (slf_set s0 t0) = Continue s' -> s' = slf_set s (s_tab s')).
    { intros s' Es. rewrite Es, H in Ent. cbn [slf_onl] in Ent. apply slf_nt_eq.
      change (slf_nt s') with (match Continue (slf_nt s') with Continue x => x | _ => slf_nt s' end).
      rewrite Ent. reflexivity. }
    destruct (slf_step_cont _ _ _ _ _ _ _ H) as [Hcnt' Hu'].
    pose proof Hinv as Hinv'. destruct Hinv' as (Hi0 & Hsym & Hlen & _ & Hcl & _).
    cbn [slf_set s_len s_cnt] in Hlen, Hcl.
    pose proof (Forall_Znth _ (sl lens) (Z.of_nat k) Hi0 slf_range) as Hl. cbv beta in Hl. unfold MAXBITS in Hl.
    destruct (Z_lt_le_dec (Z.of_nat k + 1) (Zlength ls)) as [Hlt|Hge].
    + destruct (slf_step_inv _ _ Hinv Hlt) as [(s' & Es & Hs')|(s' & Es)].
      * rewrite Nat2Z.inj_succ, <- Z.add_1_r. split; [lia|]. split.
        -- exists (s_tab s'). rewrite <- (Hcont s' Es). auto.
        -- split.
           ++ rewrite Hcnt'. rewrite upd_Znth_diff by lia. auto.
           ++ destruct Hu' as [-> | ?]; auto.
      * rewrite Es, H in Ent. discriminate.
    + destruct (slf_last_break _ _ Hinv ltac:(lia)) as (s' & Es).
      rewrite Es, H in Ent. discriminate.
Qed.

Lemma slf_rinv : forall k s, reach type lens req old k s ->
  let i := Z.of_nat k in
  0 <= i < Zlength ls /\ s_sym s = i /\ s_len s = Znth i ls /\
  s_huff s = reverse_bits (kpre ls i / 2 ^ (MAXBITS - Znth i ls)) (Znth i ls) /\
  Zlength (s_cnt s) = 16 /\
  (forall l, 1 <= l <= MAXBITS -> Znth l (s_cnt s) = count_len (sublist i (Zlength ls) ls) l) /\
  (Znth i ls <= root -> s_drop s = 0 /\ s_curr s = root /\ s_next s = 0 /\ s_used s = 2 ^ root /\
                        s_low s = Z.ones 32) /\
  (root < Znth i ls -> s_drop s = root /\ s_low s = reverse_bits (pfx ls root i) root /\
     s_curr s = gmax ls root (pfx ls root i) - root /\
     s_next s = 2 ^ root + sumq ls root (pfx ls root i) /\ s_used s = s_next s + 2 ^ s_curr s) /\
  s_used s <= Zlength old /\ Zlength (s_tab s) = Zlength old /\
  Znth 0 (s_cnt s) = count_len lens 0 /\ over type (s_used s) = false.
Proof.
  intros k s H i.
  pose proof (slf_run_len type lens W root mx k (init_state lens root old)) as Hlen.
  unfold reach in H. rewrite H in Hlen. cbn [slf_otab init_state s_tab] in Hlen.
  destruct (slf_reach_inv k s H) as (_ & (t & Hinv) & H0 & Hov).
  destruct Hinv as (Hi & Hsym & Hl & Hhuff & Hcl & Hcnt & Hlow & Hhigh & _ & _ & _ & Hucap).
  cbn [slf_set s_huff s_sym s_len s_curr s_drop s_low s_used s_next s_cnt s_tab] in *.
  rewrite Zlength_map in Hucap. fold i in Hi, Hsym, Hl, Hhuff, Hcnt, Hlow, Hhigh.
  repeat (split; [solve [auto]|]). auto.
Qed.

Lemma slf_used_bound : forall u, type <> CODES -> over type u = false -> u <= 852.
Proof.
  intros. pose proof slf_type. unfold over, CODES, LENS, DISTS, ENOUGH_LENS, ENOUGH_DISTS in *.
  assert (type = 1 \/ type = 2) as [Et | Et] by lia; rewrite Et in H0; cbn in H0;
    rewrite ?orb_false_r, ?orb_false_l in H0; apply Z.ltb_ge in H0; lia.
Qed.

Lemma slf_reach_ok : forall k s, reach type lens req old k s ->
  iter_ok lens (Zlength old) s /\ s_sym s = Z.of_nat k.
Proof.
  intros k s H.
  destruct (slf_rinv k s H) as (Hi & Hsym & Hlen & Hhuff & Hcl & Hcnt & Hlow & Hhigh & Hucap & Htl & H0 & Hov).
  set (i := Z.of_nat k) in *.
  pose proof (Forall_Znth _ (sl lens) i Hi slf_range) as Hl. cbv beta in Hl. unfold MAXBITS in *.
  destruct HB as (B1 & _).
  pose proof slf_root. pose proof slf_min_le. pose proof slf_mx15.
  assert (Hhb: 0 <= s_huff s < Z.shiftl 1 (s_len s)).
  { rewrite pow2_shiftl by lia. rewrite Hhuff, Hlen. apply B1. lia. }
  assert (Hcnts: Forall (fun c => 0 <= c <= 288) (s_cnt s)).
  { apply slf_Forall_Znth. intros j Hj. rewrite Hcl in Hj. pose proof slf_lens_len.
    destruct (Z.eq_dec j 0) as [->|Hj0].
    - rewrite H0. pose proof (slf_count_le lens 0). lia.
    - rewrite Hcnt by lia. pose proof (slf_count_le (sublist i (Zlength ls) ls) j).
      rewrite Zlength_sublist in H5 by lia. pose proof slf_len_W. pose proof slf_W_le. lia. }
  assert (Hc1: 1 <= Znth (s_len s) (s_cnt s)).
  { rewrite Hcnt by lia. rewrite count_len_sublist_cons by lia. rewrite Hlen, Z.eqb_refl.
    pose proof (slf_count_le (sublist (i + 1) (Zlength ls) ls) (Znth i ls)). lia. }
  assert (Hsy: 0 <= s_sym s < Zlength W) by (rewrite slf_len_W; lia).
  split; [|auto].
  unfold iter_ok.
  destruct (Z_lt_le_dec root (Znth i ls)) as [L|L]; swap 1 2.
  - destruct (Hlow L) as (Ed & Ec & En & Eu & Elo).
    rewrite Ed, Ec, En, Eu, Elo, ones32. rewrite !pow2_shiftl by lia.
    assert (2 ^ root <= 2 ^ 15) by (apply Z.pow_le_mono_r; lia).
    rewrite pow2_shiftl in Hhb by lia.
    repeat (split; [solve [auto | lia]|]). lia.
  - destruct (Hhigh L) as (Ed & Elo & Ec & En & Eu).
    pose proof (gmax_long ls root slf_range i Hi L) as Hg. unfold MAXBITS in Hg.
    pose proof (pfx_range ls root slf_range slf_N slf_Hroot slf_k i Hi) as Hp.
    pose proof (sumq_nonneg ls root (pfx ls root i) ltac:(lia)).
    pose proof (B1 (pfx ls root i) root ltac:(lia)).
    assert (2 ^ root <= 2 ^ 15) by (apply Z.pow_le_mono_r; lia).
    assert (Hnc: type <> CODES).
    { intro Ec'. pose proof (slf_codes Ec'). pose proof (slf_sorted i (Zlength ls - 1)). lia. }
    pose proof (slf_used_bound _ Hnc Hov).
    rewrite pow2_shiftl in Hhb by lia.
    rewrite Ed, Elo, Ec, ?pow2_shiftl by lia. rewrite Ec in Eu.
    repeat (split; [solve [auto | lia]|]). lia.
Qed.

Lemma slf_read_ok : forall k s, reach type lens req old k s ->
  st_c s = 0 -> s_len s <> mx -> s_sym s + 1 < Zlength W.
Proof.
  intros k s H Hc Hm.
  destruct (slf_rinv k s H) as (Hi & Hsym & Hlen & _).
  rewrite slf_len_W, Hsym. destruct slf_ends as [_ E1].
  destruct (Z_lt_le_dec (Z.of_nat k + 1) (Zlength ls)); [auto|].
  exfalso. apply Hm. rewrite Hlen, <- E1. f_equal. lia.
Qed.

Lemma slf_sub_ok : forall k s, reach type lens req old k s ->
  ~ (st_c s = 0 /\ s_len s = mx) ->
  root < st_len' lens s ->
  type <> CODES /\
  st_drop' root s <= st_len' lens s /\
  sub_bits (st_len' lens s) (st_drop' root s) mx (st_cnt' s) <= 15.
Proof.
  intros k s H Hnb Hlt.
  destruct (slf_rinv k s H) as (Hi & Hsym & Hlen & Hhuff & Hcl & Hcnt & Hlow & Hhigh & _).
  set (i := Z.of_nat k) in *.
  pose proof slf_root. pose proof slf_min_le. pose proof slf_mx15. destruct slf_ends as [E0 E1].
  assert (Hl': st_len' lens s <= mx).
  { unfold st_len'. destruct (st_c s =? 0) eqn:Ec.
    - apply Z.eqb_eq in Ec.
      assert (s_len s <> mx) by (intro; apply Hnb; auto).
      pose proof (slf_read_ok k s H Ec H3) as Hr. rewrite slf_len_W, Hsym in Hr.
      rewrite Hsym, slf_Wls by lia. rewrite <- E1. apply slf_sorted; lia.
    - rewrite Hlen, <- E1. apply slf_sorted; lia. }
  assert (Hd: st_drop' root s = root).
  { unfold st_drop'. destruct (Z_lt_le_dec root (Znth i ls)) as [L|L]; swap 1 2.
    - rewrite (proj1 (Hlow L)). reflexivity.
    - rewrite (proj1 (Hhigh L)). destruct (root =? 0) eqn:E; [apply Z.eqb_eq in E|]; lia. }
  split; [intro Ec; pose proof (slf_codes_root Ec); lia|].
  rewrite Hd. split; [lia|].
  unfold sub_bits. pose proof (slf_sub_loop_le 16 (st_len' lens s - root) root mx
    (Z.shiftl 1 (st_len' lens s - root)) (st_cnt' s)). lia.
Qed.

Lemma slf_break_ok : forall k s s', reach type lens req old k s ->
  step type lens W root mx s = Break s' -> s_huff s' <> 0 -> 0 <= s_next s' + s_huff s' < s_used s'.
Proof.
  intros k s s' H Hs Hh.
  destruct (slf_step_break _ _ _ _ _ _ _ Hs) as (Hc0 & Hlm & Hh' & Hn' & Hu').
  destruct (slf_rinv k s H) as (Hi & Hsym & Hlen & Hhuff & Hcl & Hcnt & Hlow & Hhigh & _).
  set (i := Z.of_nat k) in *.
  pose proof slf_root. pose proof slf_min_le. pose proof slf_mx15. destruct slf_ends as [E0 E1].
  pose proof (Forall_Znth _ (sl lens) i Hi slf_range) as Hl. cbv beta in Hl. unfold MAXBITS in Hl.
  assert (Hlast: i = Zlength ls - 1).
  { destruct (Z_lt_le_dec (i + 1) (Zlength ls)); [|lia]. exfalso.
    rewrite Hcnt in Hc0 by (rewrite Hlen; unfold MAXBITS; lia).
    rewrite count_len_sublist_cons in Hc0 by lia. rewrite Hlen, Z.eqb_refl in Hc0.
    rewrite count_len_sublist_cons in Hc0 by lia.
    assert (Znth (i + 1) ls = Znth i ls).
    { pose proof (slf_sorted i (i + 1)). pose proof (slf_sorted (i + 1) (Zlength ls - 1)). lia. }
    rewrite H3, Z.eqb_refl in Hc0.
    pose proof (slf_count_le (sublist (i + 1 + 1) (Zlength ls) ls) (Znth i ls)). lia. }
  pose proof (C_facts type ls root slf_range slf_sorted slf_N slf_k slf_type i Hi) as HCF.
  cbv zeta in HCF. destruct HCF as (HC0 & HK & HS1 & HC1 & _).
  destruct HB as (B1 & _ & _ & _ & B5).
  set (l := Znth i ls) in *. set (C := kpre ls i / 2 ^ (MAXBITS - l)) in *.
  rewrite Hh', Hhuff, Hlen in Hh. rewrite Hlen in Hh'. fold l in Hh'.
  rewrite B5 in Hh by (unfold MAXBITS; lia).
  assert (HCl: C + 1 < 2 ^ l).
  { destruct (Z.eq_dec (C + 1) (2 ^ l)); [|lia]. exfalso. apply Hh.
    rewrite e, Z.mod_same by (apply Z.pow_nonzero; lia). apply reverse_bits_0. }
  assert (Hks: ksum ls < 2 ^ MAXBITS).
  { rewrite <- kpre_full. replace (Zlength ls) with (i + 1) by lia. rewrite HS1.
    assert (Hp: 2 ^ MAXBITS = 2 ^ l * 2 ^ (MAXBITS - l)) by (rewrite <- Z.pow_add_r by (unfold MAXBITS; lia); f_equal; lia).
    rewrite Hp. apply Z.mul_lt_mono_pos_r; [apply Z.pow_pos_nonneg; unfold MAXBITS; lia | lia]. }
  pose proof (slf_inc Hks) as Hroot. rewrite E1 in Hroot.
  assert (L: l <= root) by (rewrite <- Hlen, Hlm; lia).
  destruct (Hlow L) as (Ed & Ec & En & Eu & Elo).
  rewrite Hn', Hu', En, Eu, Hh', Hhuff.
  rewrite B5 by (unfold MAXBITS; lia).
  pose proof (B1 ((C + 1) mod 2 ^ l) l ltac:(lia)).
  assert (2 ^ l <= 2 ^ root) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

Lemma slf_final : forall k s, reach type lens req old k s ->
  forall o, step type lens W root mx s = o ->
  (match o with Continue _ => False | _ => True end) ->
  run type lens W root mx (length W) (init_state lens root old) = o.
Proof.
  intros k s H o Hs Ho.
  destruct (slf_reach_ok k s H) as ((Hy & _) & Hsym).
  rewrite Hsym, Zlength_correct in Hy.
  replace (length W) with (S k + (length W - S k))%nat by lia.
  rewrite slf_run_add, slf_run_S. unfold reach in H. rewrite H, Hs.
  destruct o; [contradiction | reflexivity | reflexivity].
Qed.

Lemma slf_root_ok : 1 <= minlen lens <= root /\ root <= mx <= 15 /\ (type = CODES -> root = mx).
Proof.
  pose proof slf_root. pose proof slf_min_le. pose proof slf_mx15.
  split; [lia|]. split; [lia|]. apply slf_codes_root.
Qed.

End Main.

Lemma slf_reach_step : reach_step_stmt.
Proof.
  intros type lens req old k s s' H Hs. unfold reach in *. rewrite slf_run_S, H. auto.
Qed.

Lemma slf_loop_facts : sorted_stmt -> bits_stmt -> subbits_stmt -> sorted_syms_ok_stmt -> loop_facts.
Proof.
  intros HS HB HSB HSS.
  refine (conj HSS (conj _ (conj _ (conj _ (conj _ (conj _ (conj slf_reach_step _))))))).
  - intros type lens req cap Hacc.
    assert (Hc: 0 <= cap).
    { destruct Hacc as ((Ht & _) & (H1 & H2 & H3) & _). unfold CODES, LENS, DISTS, ENOUGH_LENS, ENOUGH_DISTS in *.
      assert (type = 0 \/ type = 1 \/ type = 2) as [E|[E|E]] by lia;
        [destruct (H1 E) as (_ & ? & _) | specialize (H2 E) | specialize (H3 E)]; lia. }
    assert (Hz: Zlength (Zrepeat (mkE 0 0 0) cap) = cap) by (apply Zlength_Zrepeat; auto).
    rewrite <- Hz in Hacc. apply (slf_root_ok type lens req (Zrepeat (mkE 0 0 0) cap)); auto.
  - intros type lens req old k s Hacc H. eapply slf_reach_ok; eauto.
  - intros type lens req old k s Hacc H Hc Hm. eapply slf_read_ok; eauto.
  - intros type lens req old k s Hacc H Hnb Hlt _. eapply slf_sub_ok; eauto.
  - intros type lens req old k s s' Hacc H Hs Hh. eapply slf_break_ok; eauto.
  - intros type lens req old k s Hacc H o Hs Ho. eapply slf_final; eauto.
Qed.
