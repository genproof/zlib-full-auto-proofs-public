(** * deflate_fast, part: the insertion loop (df_insert_body).  Statement and definitions: LTCFastKit.v. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTCFastKit.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** A loop terminates when a measure >= 0 decreases on every continuing iteration and starts below 2^d
    (copy of LTCLmKit.loop_measure) *)
Definition il_step_ok {A B : Type} (body : A -> option (A + B)) (P : A -> Prop) (Q : B -> Prop) (m : A -> Z)
    : Prop :=
  forall a, P a -> 0 <= m a /\
  ((exists r, body a = Some (inr r) /\ Q r) \/ (exists a', body a = Some (inl a') /\ P a' /\ m a' < m a)).

Lemma il_loop2_measure {A B : Type} (body : A -> option (A + B)) (P : A -> Prop) (Q : B -> Prop) (m : A -> Z)
    (Hstep : il_step_ok body P Q m) : forall d a, P a ->
  (exists r, loop2 d body a = Some (inr r) /\ Q r) \/
  (exists a', loop2 d body a = Some (inl a') /\ P a' /\ m a' + 2 ^ Z.of_nat d <= m a).
Proof.
  induction d as [|d IH]; intros a Ha; cbn [loop2].
  - destruct (Hstep a Ha) as [_ [[r [E HQ]]|[a' [E [HP Hm]]]]]; rewrite E.
    + left; eauto.
    + right; exists a'; split; [reflexivity|]; split; [exact HP|]. simpl. lia.
  - destruct (IH a Ha) as [[r [E HQ]]|[a' [E [HP Hm]]]]; rewrite E.
    + left; eauto.
    + destruct (IH a' HP) as [[r [E' HQ]]|[a'' [E' [HP' Hm']]]]; rewrite E'.
      * left; eauto.
      * right. exists a''. split; [reflexivity|]. split; [exact HP'|].
        rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia.
Qed.

Lemma il_loop_measure {A B : Type} (body : A -> option (A + B)) (P : A -> Prop) (Q : B -> Prop) (m : A -> Z)
    (Hstep : il_step_ok body P Q m) :
  forall d a, P a -> m a < 2 ^ Z.of_nat d -> exists r, loop d body a = Some r /\ Q r.
Proof.
  intros d a Ha Hm. unfold loop.
  destruct (il_loop2_measure body P Q m Hstep d a Ha) as [[r [E HQ]]|[a' [E [HP Hm']]]]; rewrite E.
  - eauto.
  - destruct (Hstep a' HP) as [H0 _]. lia.
Qed.

Lemma il_u32_id x : 0 <= x < 4294967296 -> u32 x = x.
Proof. intros; unfold u32; apply Z.mod_small; lia. Qed.

(** il_keep through hc_keep (conversion). *)
Definition il_keep' (y : dstate) : dstate := set_d_strstart (set_d_match_length y 0) 0.
Lemma il_keep_hc x : il_keep x = il_keep' (hc_keep x).
Proof. reflexivity. Qed.

Lemma il_wstruct_ss a x : wstruct a -> wstruct (set_d_strstart a x).
Proof. intros H. exact H. Qed.
Lemma il_wstruct_ml a x : wstruct a -> wstruct (set_d_match_length a x).
Proof. intros H. exact H. Qed.
Lemma il_prm_ss a x : prm a -> prm (set_d_strstart a x).
Proof. intros H. exact H. Qed.
Lemma il_prm_ml a x : prm a -> prm (set_d_match_length a x).
Proof. intros H. exact H. Qed.
Lemma il_chain_ss a x n l G : chain_with a n l G -> chain_with (set_d_strstart a x) n l G.
Proof. intros H. exact H. Qed.
Lemma il_chain_ml a x n l G : chain_with a n l G -> chain_with (set_d_match_length a x) n l G.
Proof. intros H. exact H. Qed.

(** prm and the fields read from il_keep. *)
Lemma il_prm_hc a b : hc_keep a = hc_keep b -> prm b -> prm a.
Proof.
  intros E H. unfold prm in *.
  assert (E1 : d_w_bits a = d_w_bits b) by (exact (f_equal d_w_bits E)).
  assert (E2 : d_w_size a = d_w_size b) by (exact (f_equal d_w_size E)).
  assert (E3 : d_w_mask a = d_w_mask b) by (exact (f_equal d_w_mask E)).
  assert (E4 : d_hash_bits a = d_hash_bits b) by (exact (f_equal d_hash_bits E)).
  assert (E5 : d_hash_size a = d_hash_size b) by (exact (f_equal d_hash_size E)).
  assert (E6 : d_hash_mask a = d_hash_mask b) by (exact (f_equal d_hash_mask E)).
  assert (E7 : d_hash_shift a = d_hash_shift b) by (exact (f_equal d_hash_shift E)).
  assert (E8 : d_tr a = d_tr b) by (exact (f_equal d_tr E)).
  assert (E9 : d_pbm a = d_pbm b) by (exact (f_equal d_pbm E)).
  assert (E10 : d_pending_buf_size a = d_pending_buf_size b) by (exact (f_equal d_pending_buf_size E)).
  assert (E11 : d_method a = d_method b) by (exact (f_equal d_method E)).
  assert (E12 : d_tr a = d_tr b) by (exact (f_equal d_tr E)).
  unfold d_L, d_level, d_strategy in *.
  rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9, E10, E11. exact H.
Qed.

Definition ilP (s : dstate) (l : Z) (a : dstate) : Prop :=
  prm a /\ wstruct a /\ il_keep a = il_keep s /\
  d_strstart s <= d_strstart a /\ 1 <= d_match_length a /\
  d_strstart a + d_match_length a = d_strstart s + d_match_length s /\
  exists G, chain_with a (d_strstart a + 1) l G.

Definition ilQ (s : dstate) (l : Z) (r : dstate) : Prop :=
  il_keep r = il_keep s /\ wstruct r /\
  d_strstart r = d_strstart s + d_match_length s /\ d_match_length r = 0 /\
  exists G', chain_with r (d_strstart r + 1) l G'.

Theorem insloop_ok : ins_spec -> insloop_stmt.
Proof.
  intros Hins s l G Hp Hw Hc Hk H0 H64 Hlen Hdef Hl.
  assert (Hwin : forall a, il_keep a = il_keep s -> d_window a = d_window s)
    by (intros a E; exact (f_equal d_window E)).
  assert (Hws : forall a, il_keep a = il_keep s -> d_w_size a = d_w_size s)
    by (intros a E; exact (f_equal d_w_size E)).
  assert (Hwp : 0 < d_w_size s).
  { destruct Hp as (Hb & Hp2 & _). rewrite Hp2. apply Z.pow_pos_nonneg; lia. }
  destruct (il_loop_measure df_insert_body (ilP s l) (ilQ s l) d_match_length) with (d := FUEL) (a := s)
    as [r [Er HQ]].
  - intros a (Pp & Pw & Pk & P1 & P2 & P3 & Ga & Pc). split; [lia|].
    set (a1 := set_d_strstart a (d_strstart a + 1)).
    destruct (Hins a1 (d_strstart a + 1) (d_strstart a + 1) l Ga) as (s2 & h & E2 & K2 & W2 & _ & C2 & _).
    + apply il_prm_ss; exact Pp.
    + apply il_wstruct_ss; exact Pw.
    + apply il_chain_ss; exact Pc.
    + lia.
    + unfold a1. change (d_window (set_d_strstart a (d_strstart a + 1))) with (d_window a).
      rewrite (Hwin a Pk). lia.
    + unfold a1. change (d_window (set_d_strstart a (d_strstart a + 1))) with (d_window a).
      rewrite (Hwin a Pk). apply Hdef. lia.
    + unfold a1. change (d_w_size (set_d_strstart a (d_strstart a + 1))) with (d_w_size a).
      rewrite (Hws a Pk). lia.
    + unfold a1. change (d_w_size (set_d_strstart a (d_strstart a + 1))) with (d_w_size a).
      rewrite (Hws a Pk). lia.
    + assert (Ess : d_strstart s2 = d_strstart a + 1) by (exact (f_equal d_strstart K2)).
      assert (Eml : d_match_length s2 = d_match_length a) by (exact (f_equal d_match_length K2)).
      assert (Ebody : df_insert_body a =
                if d_match_length a - 1 =? 0 then Some (inr (set_d_match_length s2 (d_match_length a - 1)))
                else Some (inl (set_d_match_length s2 (d_match_length a - 1)))).
      { unfold df_insert_body. rewrite (il_u32_id (d_strstart a + 1)) by lia.
        fold a1. change (d_strstart a1) with (d_strstart a + 1). rewrite E2. cbn [bind].
        rewrite Eml, (il_u32_id (d_match_length a - 1)) by lia. reflexivity. }
      rewrite Z.max_r in C2 by lia.
      assert (Kk : il_keep (set_d_match_length s2 (d_match_length a - 1)) = il_keep s).
      { rewrite <- Pk. change (il_keep' (hc_keep s2) = il_keep' (hc_keep a1)). rewrite K2. reflexivity. }
      assert (Pp2 : prm s2) by (apply (il_prm_hc s2 a1 K2); apply il_prm_ss; exact Pp).
      rewrite Ebody. destruct (Z.eqb_spec (d_match_length a - 1) 0) as [Z0|Z0].
      * left. eexists; split; [reflexivity|]. unfold ilQ.
        split; [exact Kk|]. split; [apply il_wstruct_ml; exact W2|].
        change (d_strstart (set_d_match_length s2 (d_match_length a - 1))) with (d_strstart s2).
        change (d_match_length (set_d_match_length s2 (d_match_length a - 1))) with (d_match_length a - 1).
        split; [lia|]. split; [lia|].
        eexists. apply il_chain_ml. rewrite Ess. exact C2.
      * right. eexists; split; [reflexivity|]. unfold ilP.
        change (d_strstart (set_d_match_length s2 (d_match_length a - 1))) with (d_strstart s2).
        change (d_match_length (set_d_match_length s2 (d_match_length a - 1))) with (d_match_length a - 1).
        split; [|lia].
        split; [apply il_prm_ml; exact Pp2|]. split; [apply il_wstruct_ml; exact W2|].
        split; [exact Kk|]. split; [lia|]. split; [lia|]. split; [lia|].
        eexists. apply il_chain_ml. rewrite Ess. exact C2.
  - split; [exact Hp|]. split; [exact Hw|]. split; [reflexivity|]. split; [lia|]. split; [lia|].
    split; [lia|]. exists G. exact Hc.
  - unfold FUEL. change (2 ^ Z.of_nat 40) with 1099511627776. lia.
  - destruct HQ as (Q1 & Q2 & Q3 & Q4 & G' & Q5).
    exists r, G'. split; [exact Er|]. split; [exact Q1|]. split; [exact Q2|].
    split; [exact Q3|]. split; [exact Q4|]. exact Q5.
Qed.
