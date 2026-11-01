(** * deflate_fast: the glue.  From the part statements of RTDLTCFastKit.v to fast_spec:
    composition of [crel] / [FI] / [bpost], the step (df_step_eq), the main loop by the measure
    avail_in + lookahead, the tail. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDLTCFastKit.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** Composition *)

Lemma ev_chain_app g e1 g' e2 g'' :
  ev_chain g e1 g' -> ev_chain g' e2 g'' -> ev_chain g (e1 ++ e2) g''.
Proof.
  revert g. induction e1 as [|e e1 IH]; intros g H1 H2; cbn [app ev_chain] in *.
  - subst. exact H2.
  - destruct H1 as [Hg H1]. split; [exact Hg|]. eapply IH; eauto.
Qed.

Lemma sum_len_app e1 e2 : sum_len (e1 ++ e2) = sum_len e1 + sum_len e2.
Proof.
  unfold sum_len. induction e1 as [|e e1 IH]; cbn [app fold_right]; lia.
Qed.

Lemma same_prm_trans a b c : same_prm a b -> same_prm b c -> same_prm a c.
Proof.
  intros (A1 & A2 & A3 & A4 & A5 & A6 & A7) (B1 & B2 & B3 & B4 & B5 & B6 & B7).
  unfold same_prm. rewrite B1, B2, B3, B4, B5, B6, B7. auto 10.
Qed.

Lemma api_eq_trans a b c : api_eq a b -> api_eq b c -> api_eq a c.
Proof.
  intros (A1 & A2 & A3 & A4 & A5 & A6) (B1 & B2 & B3 & B4 & B5 & B6).
  unfold api_eq. rewrite B1, B2, B3, B4, B5, B6. auto 10.
Qed.

Lemma ev_ok_same_prm s s1 flush e : same_prm s s1 -> ev_ok s1 flush e -> ev_ok s flush e.
Proof.
  intros (_ & E2 & _ & E4 & E5 & E6 & E7) H. destruct e; unfold ev_ok in *.
  - rewrite E2, E4, E6, E7 in H. exact H.
  - rewrite E2, E5, E6 in H. exact H.
Qed.

Lemma crel_trans s z f s1 z1 e1 s2 z2 e2 :
  zall z -> adler_ok (d_wrap s) (z_adler z) ->
  crel s z f s1 z1 e1 -> crel s1 z1 f s2 z2 e2 -> crel s z f s2 z2 (e1 ++ e2).
Proof.
  intros [Hzi _] Ha (A1 & A2 & A3 & A4 & (k1 & x1 & Z1 & X1 & U1) & C1 & F1)
    (B1 & B2 & B3 & B4 & (k2 & x2 & Z2 & X2 & U2) & C2 & F2).
  assert (Ew : d_wrap s1 = d_wrap s) by (destruct A4 as (_ & E & _); exact E).
  rewrite Ew in Z2.
  unfold crel. split; [exact B1|]. split; [exact B2|].
  split; [eapply same_prm_trans; eauto|]. split; [eapply api_eq_trans; eauto|].
  split.
  - exists (k1 + k2), (x1 ++ x2). split; [eapply zstep_trans; eauto|].
    split; [apply Forall_app; auto|]. rewrite sum_len_app. lia.
  - split; [eapply ev_chain_app; eauto|].
    apply Forall_app. split; [exact F1|].
    eapply Forall_impl; [|exact F2]. intros e He. eapply ev_ok_same_prm; eauto.
Qed.

Lemma FI_trans s z f s1 z1 e1 s2 z2 e2 :
  zall z -> adler_ok (d_wrap s) (z_adler z) ->
  FI s z f s1 z1 e1 -> FI s1 z1 f s2 z2 e2 -> FI s z f s2 z2 (e1 ++ e2).
Proof.
  intros Hz Ha (C1 & Q1 & Z1 & A1 & L1) (C2 & Q2 & Z2 & A2 & L2).
  split; [eapply crel_trans; eauto|]. split; [exact Q2|]. split; [exact Z2|]. split; [exact A2|].
  apply Forall_app. auto.
Qed.

Lemma last_ev_app e1 e2 : Forall (fun e => ev_last e = 0) e1 -> last_ev e2 -> last_ev (e1 ++ e2).
Proof.
  intros H (e0 & e & -> & He & H0). exists (e1 ++ e0), e. split; [rewrite app_assoc; reflexivity|].
  split; [exact He|]. apply Forall_app. auto.
Qed.

(** [bpost] only looks at level and wrap of the start state. *)
Lemma bpost_start s s1 z z1 f s2 z2 bs e1 e2 :
  same_prm s s1 -> api_eq s s1 -> Forall (fun e => ev_last e = 0) e1 ->
  bpost s1 z1 f s2 z2 bs e2 -> bpost s z f s2 z2 bs (e1 ++ e2).
Proof.
  intros (_ & _ & _ & _ & _ & El & _) (_ & Ew & _) H1 H2.
  destruct bs; cbn [bpost] in *.
  - destruct H2 as (H2 & H3). split; [apply Forall_app; auto|]. rewrite El in H3. exact H3.
  - destruct H2 as (H2 & H3). split; [apply Forall_app; auto|]. exact H3.
  - destruct H2 as (H2 & H3). split; [apply last_ev_app; auto|].
    rewrite El, Ew in H3. exact H3.
  - destruct H2 as (H2 & H3). split; [apply last_ev_app; auto|]. exact H3.
Qed.

(** A step [fr] that does not touch the stream, followed by a piece. *)
Lemma crel_fr s s3 z f s' z' e : fr s s3 -> crel s3 z f s' z' e -> crel s z f s' z' e.
Proof.
  intros (P & A & U & G) (B1 & B2 & B3 & B4 & (k & x & Z & X & Ub) & C & F).
  assert (Ew : d_wrap s3 = d_wrap s) by (destruct A as (_ & E & _); exact E).
  rewrite Ew in Z. rewrite G in C. rewrite U in Ub.
  unfold crel. split; [exact B1|]. split; [exact B2|].
  split; [eapply same_prm_trans; eauto|]. split; [eapply api_eq_trans; eauto|].
  split; [exists k, x; auto|]. split; [exact C|].
  eapply Forall_impl; [|exact F]. intros e0 He. eapply ev_ok_same_prm; eauto.
Qed.

Lemma FI_fr s s3 z f s' z' e : fr s s3 -> FI s3 z f s' z' e -> FI s z f s' z' e.
Proof.
  intros Hf (C & Q & Z & A & L). split; [eapply crel_fr; eauto|]. auto.
Qed.

Lemma bpost_fr s s3 z f s' z' bs e : fr s s3 -> bpost s3 z f s' z' bs e -> bpost s z f s' z' bs e.
Proof.
  intros (P & A & _ & _) H. rewrite <- (app_nil_l e). eapply bpost_start; eauto.
Qed.

(** ** A loop terminates when a measure >= 0 decreases on every continuing iteration and starts below 2^d
    (copy of RTDLTCLmKit.loop_measure) *)
Section LoopMeasure.
Context {A B : Type} (body : A -> option (A + B)) (P : A -> Prop) (Q : B -> Prop) (m : A -> Z).
Hypothesis Hstep : forall a, P a -> 0 <= m a /\
  ((exists r, body a = Some (inr r) /\ Q r) \/ (exists a', body a = Some (inl a') /\ P a' /\ m a' < m a)).

Lemma fg_loop2_measure : forall d a, P a ->
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

Lemma fg_loop_measure : forall d a, P a -> m a < 2 ^ Z.of_nat d -> exists r, loop d body a = Some r /\ Q r.
Proof.
  intros d a Ha Hm. unfold loop.
  destruct (fg_loop2_measure d a Ha) as [[r [E HQ]]|[a' [E [HP Hm']]]]; rewrite E.
  - eauto.
  - destruct (Hstep a' HP) as [H0 _]. lia.
Qed.
End LoopMeasure.

(** ** One iteration after the refill *)
Definition step_res (s : dstate) (z : strm) (flush : Z) (r : (dstate * strm) + dexit) : Prop :=
  match r with
  | inl (s', z') =>
      (exists evs, FI s z flush s' z' evs) /\ z_avail_in z' + d_lookahead s' < z_avail_in z + d_lookahead s
  | inr (s', z', o) =>
      o = Some need_more /\ exists evs, crel s z flush s' z' evs /\ bpost s z flush s' z' need_more evs
  end.

Lemma step_ok : search_stmt -> lit_stmt -> match_stmt -> bflush_stmt ->
  forall s z flush,
    W s -> outok s -> quiet s -> zall z -> adler_ok (d_wrap s) (z_adler z) -> fn_of s = 1 -> 0 <= flush <= 5 ->
    ready s -> 1 <= d_lookahead s ->
    exists r, df_step s z = Some r /\ step_res s z flush r.
Proof.
  intros Hse Hli Hma Hbf s z flush HW Ho Hq Hz Ha Hfn Hfl Hr Hla.
  destruct (Hse s HW Hfn Hr Hla) as (s2 & E2 & HSR).
  assert (Hb : exists s3 bf syms3,
             fbranch s2 = Some (s3, bf) /\ TS s3 syms3 bf /\ fr s s3 /\ d_lookahead s3 < d_lookahead s).
  { unfold fbranch. destruct (d_match_length s2 >=? MIN_MATCH) eqn:Em.
    - apply (Hma s s2); auto. apply Z.geb_le in Em. lia.
    - apply (Hli s s2); auto. rewrite Z.geb_leb in Em. apply Z.leb_gt in Em. lia. }
  destruct Hb as (s3 & bf & syms3 & E3 & HTS & Hfr & Hlt).
  assert (Hwr : d_wrap s3 = d_wrap s) by (destruct Hfr as (_ & (_ & E & _) & _); exact E).
  assert (Ha3 : adler_ok (d_wrap s3) (z_adler z)) by (rewrite Hwr; exact Ha).
  destruct (Hbf s3 z flush syms3 bf HTS Hz Ha3 Hfl) as (r & Er & Hr').
  exists r. split.
  { rewrite df_step_eq, E2. cbn [bind]. rewrite E3. exact Er. }
  unfold step_res. destruct r as [[s' z']|[[s' z'] o]].
  - destruct Hr' as ((evs & HFI) & El & Ea). split; [exists evs; eapply FI_fr; eauto|]. lia.
  - destruct Hr' as (Ho' & evs & Hc & Hb'). split; [exact Ho'|]. exists evs.
    split; [eapply crel_fr; eauto|eapply bpost_fr; eauto].
Qed.

(** ** The main loop *)
Definition loop_res (s0 : dstate) (z0 : strm) (flush : Z) (r : dexit) : Prop :=
  let '(s, z, o) := r in
  match o with
  | Some bs => exists evs, crel s0 z0 flush s z evs /\ bpost s0 z0 flush s z bs evs
  | None =>
      exists evs, FI s0 z0 flush s z evs /\ d_lookahead s = 0 /\ z_avail_in z = 0 /\ flush <> Z_NO_FLUSH /\
                  d_strstart s < d_w_size s + MAX_DIST s
  end.

Lemma FI_parts s0 z0 flush s z evs :
  FI s0 z0 flush s z evs -> fn_of s0 = 1 ->
  W s /\ outok s /\ quiet s /\ zall z /\ adler_ok (d_wrap s) (z_adler z) /\ fn_of s = 1.
Proof.
  intros ((HW & Ho & Hp & _) & Hq & Hz & Ha & _) Hfn.
  split; [exact HW|]. split; [exact Ho|]. split; [exact Hq|]. split; [exact Hz|]. split; [exact Ha|].
  rewrite (fn_of_same_prm s0 s Hp). exact Hfn.
Qed.

Lemma FI_crel s0 z0 flush s z evs : FI s0 z0 flush s z evs -> crel s0 z0 flush s z evs.
Proof. intros (C & _). exact C. Qed.

Lemma FI_last s0 z0 flush s z evs : FI s0 z0 flush s z evs -> Forall (fun e => ev_last e = 0) evs.
Proof. intros (_ & _ & _ & _ & L). exact L. Qed.

Lemma FI_sp s0 z0 flush s z evs : FI s0 z0 flush s z evs -> same_prm s0 s /\ api_eq s0 s.
Proof. intros ((_ & _ & P & A & _) & _). auto. Qed.

Lemma prm_w_bound s : prm s -> d_w_size s <= 32768.
Proof.
  intros (Hb & Hs & _). rewrite Hs. change 32768 with (2 ^ 15). apply Z.pow_le_mono_r; lia.
Qed.

Lemma loop_ok : refill_stmt -> search_stmt -> lit_stmt -> match_stmt -> bflush_stmt ->
  forall s0 z0 flush,
    W s0 -> outok s0 -> quiet s0 -> zall z0 -> adler_ok (d_wrap s0) (z_adler z0) -> fn_of s0 = 1 ->
    0 <= flush <= 5 ->
    exists r, loop FUEL (df_body flush) (s0, z0) = Some r /\ loop_res s0 z0 flush r.
Proof.
  intros Hre Hse Hli Hma Hbf s0 z0 flush HW0 Ho0 Hq0 Hz0 Ha0 Hfn0 Hfl.
  apply (fg_loop_measure (df_body flush) (fun a => exists evs, FI s0 z0 flush (fst a) (snd a) evs)
           (loop_res s0 z0 flush) (fun a => z_avail_in (snd a) + d_lookahead (fst a))).
  - intros [s z] (evs & HFI). cbn [fst snd] in *.
    destruct (FI_parts _ _ _ _ _ _ HFI Hfn0) as (HW & Ho & Hq & Hz & Ha & Hfn).
    split.
    { destruct HW as (_ & _ & (Hl & _) & _). destruct Hz as ((_ & _ & Hai & _) & _). lia. }
    destruct (Hre s z flush HW Ho Hq Hz Ha Hfn Hfl) as (r1 & E1 & H1).
    unfold df_body. rewrite E1. cbn [bind].
    destruct r1 as [[s1 z1]|[[s1 z1] [bs|]]].
    + destruct H1 as (HFI1 & Hr1 & Hla1 & Hm1).
      destruct (FI_parts _ _ _ _ _ _ HFI1 Hfn) as (HW1 & Ho1 & Hq1 & Hz1 & Ha1 & Hfn1).
      destruct (step_ok Hse Hli Hma Hbf s1 z1 flush HW1 Ho1 Hq1 Hz1 Ha1 Hfn1 Hfl Hr1 Hla1)
        as (r2 & E2 & H2).
      rewrite E2. unfold step_res in H2.
      destruct r2 as [[s2 z2]|[[s2 z2] o]].
      * destruct H2 as ((evs2 & HFI2) & Hm2). right. exists (s2, z2). split; [reflexivity|].
        cbn [fst snd]. split; [|lia].
        exists (evs ++ ([] ++ evs2)).
        eapply FI_trans; [exact Hz0|exact Ha0|exact HFI|].
        eapply FI_trans; [exact Hz|exact Ha|exact HFI1|exact HFI2].
      * destruct H2 as (-> & evs2 & Hc2 & Hb2). left. exists (s2, z2, Some need_more). split; [reflexivity|].
        cbv beta iota delta [loop_res]. exists (evs ++ ([] ++ evs2)). split.
        -- eapply crel_trans; [exact Hz0|exact Ha0|apply FI_crel; exact HFI|].
           eapply crel_trans; [exact Hz|exact Ha|apply FI_crel; exact HFI1|exact Hc2].
        -- destruct (FI_sp _ _ _ _ _ _ HFI) as (P1 & A1). destruct (FI_sp _ _ _ _ _ _ HFI1) as (P2 & A2).
           eapply (bpost_start s0 s z0 z); [exact P1|exact A1|apply (FI_last _ _ _ _ _ _ HFI)|].
           eapply bpost_start; [exact P2|exact A2|constructor|exact Hb2].
    + destruct H1 as (-> & Hc1 & Hb1). left. exists (s1, z1, Some need_more). split; [reflexivity|].
      cbv beta iota delta [loop_res]. exists (evs ++ []). split.
      * eapply crel_trans; [exact Hz0|exact Ha0|apply FI_crel; exact HFI|exact Hc1].
      * destruct (FI_sp _ _ _ _ _ _ HFI) as (P1 & A1).
        eapply bpost_start; [exact P1|exact A1|apply (FI_last _ _ _ _ _ _ HFI)|exact Hb1].
    + destruct H1 as (HFI1 & H1). left. exists (s1, z1, None). split; [reflexivity|].
      cbv beta iota delta [loop_res]. exists (evs ++ []). split; [|exact H1].
      eapply FI_trans; [exact Hz0|exact Ha0|exact HFI|exact HFI1].
  - exists []. cbn [fst snd]. apply FI_refl; auto.
  - cbn [fst snd]. destruct HW0 as (Hp & (_ & _ & Hws & _) & (_ & Hss & Hsl & _) & _).
    pose proof (prm_w_bound s0 Hp) as Hw.
    destruct Hz0 as ((_ & _ & Hai & _) & _). change (Z.of_nat FUEL) with 40. lia.
Qed.

(** ** deflate_fast from its parts *)
Theorem fast_from_parts :
  refill_stmt -> search_stmt -> lit_stmt -> match_stmt -> bflush_stmt -> tail_stmt -> fast_spec.
Proof.
  intros Hre Hse Hli Hma Hbf Hta s z flush (HW & Ho & Hq & Hfl & Hzi & Hwr & Ha) Hfn.
  pose proof (zin_ok_zall z Hzi) as Hz.
  destruct (loop_ok Hre Hse Hli Hma Hbf s z flush HW Ho Hq Hz Ha Hfn Hfl) as (r & Er & Hr).
  unfold c_deflate_fast. rewrite Er. cbn [bind].
  destruct r as [[s1 z1] [bs|]]; cbv beta iota delta [loop_res] in Hr.
  - destruct Hr as (evs & Hc & Hb). exists s1, z1, bs, evs. split; [reflexivity|].
    apply cpost_of; assumption.
  - destruct Hr as (evs & HFI & Hla & Hai & Hnf & Hss).
    destruct (FI_parts _ _ _ _ _ _ HFI Hfn) as (HW1 & Ho1 & Hq1 & Hz1 & Ha1 & Hfn1).
    destruct (Hta s1 z1 flush HW1 Ho1 Hq1 Hz1 Ha1 Hfn1 Hfl Hnf Hla Hai Hss)
      as (s' & z' & bs & evs2 & Et & Hc & Hb).
    exists s', z', bs, (evs ++ evs2). split; [exact Et|].
    apply cpost_of.
    + eapply crel_trans; [exact Hz|exact Ha|apply FI_crel; exact HFI|exact Hc].
    + destruct (FI_sp _ _ _ _ _ _ HFI) as (P1 & A1).
      eapply (bpost_start s s1 z z1); [exact P1|exact A1|apply (FI_last _ _ _ _ _ _ HFI)|exact Hb].
Qed.
