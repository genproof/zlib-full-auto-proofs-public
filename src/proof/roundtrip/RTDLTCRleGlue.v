(** * deflate_rle: the glue.  From the part statements of RTDLTCRleKit.v to rle_spec:
    composition of [crel] / [FI] / [bpost] (copied from RTDLTCFastGlue.v, prefixed rg_), the step
    (rle_step_eq), the main loop by the measure avail_in + lookahead, the tail. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDLTCRleKit.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** Composition *)

Lemma rg_ev_chain_app g e1 g' e2 g'' :
  ev_chain g e1 g' -> ev_chain g' e2 g'' -> ev_chain g (e1 ++ e2) g''.
Proof.
  revert g. induction e1 as [|e e1 IH]; intros g H1 H2; cbn [app ev_chain] in *.
  - subst. exact H2.
  - destruct H1 as [Hg H1]. split; [exact Hg|]. eapply IH; eauto.
Qed.

Lemma rg_sum_len_app e1 e2 : sum_len (e1 ++ e2) = sum_len e1 + sum_len e2.
Proof.
  unfold sum_len. induction e1 as [|e e1 IH]; cbn [app fold_right]; lia.
Qed.

Lemma rg_same_prm_trans a b c : same_prm a b -> same_prm b c -> same_prm a c.
Proof.
  intros (A1 & A2 & A3 & A4 & A5 & A6 & A7) (B1 & B2 & B3 & B4 & B5 & B6 & B7).
  unfold same_prm. rewrite B1, B2, B3, B4, B5, B6, B7. auto 10.
Qed.

Lemma rg_api_eq_trans a b c : api_eq a b -> api_eq b c -> api_eq a c.
Proof.
  intros (A1 & A2 & A3 & A4 & A5 & A6) (B1 & B2 & B3 & B4 & B5 & B6).
  unfold api_eq. rewrite B1, B2, B3, B4, B5, B6. auto 10.
Qed.

Lemma rg_ev_ok_same_prm s s1 flush e : same_prm s s1 -> ev_ok s1 flush e -> ev_ok s flush e.
Proof.
  intros (_ & E2 & _ & E4 & E5 & E6 & E7) H. destruct e; unfold ev_ok in *.
  - rewrite E2, E4, E6, E7 in H. exact H.
  - rewrite E2, E5, E6 in H. exact H.
Qed.

Lemma rg_crel_trans s z f s1 z1 e1 s2 z2 e2 :
  zall z -> adler_ok (d_wrap s) (z_adler z) ->
  crel s z f s1 z1 e1 -> crel s1 z1 f s2 z2 e2 -> crel s z f s2 z2 (e1 ++ e2).
Proof.
  intros [Hzi _] Ha (A1 & A2 & A3 & A4 & (k1 & x1 & Z1 & X1 & U1) & C1 & F1)
    (B1 & B2 & B3 & B4 & (k2 & x2 & Z2 & X2 & U2) & C2 & F2).
  assert (Ew : d_wrap s1 = d_wrap s) by (destruct A4 as (_ & E & _); exact E).
  rewrite Ew in Z2.
  unfold crel. split; [exact B1|]. split; [exact B2|].
  split; [eapply rg_same_prm_trans; eauto|]. split; [eapply rg_api_eq_trans; eauto|].
  split.
  - exists (k1 + k2), (x1 ++ x2). split; [eapply zstep_trans; eauto|].
    split; [apply Forall_app; auto|]. rewrite rg_sum_len_app. lia.
  - split; [eapply rg_ev_chain_app; eauto|].
    apply Forall_app. split; [exact F1|].
    eapply Forall_impl; [|exact F2]. intros e He. eapply rg_ev_ok_same_prm; eauto.
Qed.

Lemma rg_FI_trans s z f s1 z1 e1 s2 z2 e2 :
  zall z -> adler_ok (d_wrap s) (z_adler z) ->
  FI s z f s1 z1 e1 -> FI s1 z1 f s2 z2 e2 -> FI s z f s2 z2 (e1 ++ e2).
Proof.
  intros Hz Ha (C1 & Q1 & Z1 & A1 & L1) (C2 & Q2 & Z2 & A2 & L2).
  split; [eapply rg_crel_trans; eauto|]. split; [exact Q2|]. split; [exact Z2|]. split; [exact A2|].
  apply Forall_app. auto.
Qed.

Lemma rg_last_ev_app e1 e2 : Forall (fun e => ev_last e = 0) e1 -> last_ev e2 -> last_ev (e1 ++ e2).
Proof.
  intros H (e0 & e & -> & He & H0). exists (e1 ++ e0), e. split; [rewrite app_assoc; reflexivity|].
  split; [exact He|]. apply Forall_app. auto.
Qed.

(** [bpost] only looks at level and wrap of the start state. *)
Lemma rg_bpost_start s s1 z z1 f s2 z2 bs e1 e2 :
  same_prm s s1 -> api_eq s s1 -> Forall (fun e => ev_last e = 0) e1 ->
  bpost s1 z1 f s2 z2 bs e2 -> bpost s z f s2 z2 bs (e1 ++ e2).
Proof.
  intros (_ & _ & _ & _ & _ & El & _) (_ & Ew & _) H1 H2.
  destruct bs; cbn [bpost] in *.
  - destruct H2 as (H2 & H3). split; [apply Forall_app; auto|]. rewrite El in H3. exact H3.
  - destruct H2 as (H2 & H3). split; [apply Forall_app; auto|]. exact H3.
  - destruct H2 as (H2 & H3). split; [apply rg_last_ev_app; auto|].
    rewrite El, Ew in H3. exact H3.
  - destruct H2 as (H2 & H3). split; [apply rg_last_ev_app; auto|]. exact H3.
Qed.

(** A step [fr] that does not touch the stream, followed by a piece. *)
Lemma rg_crel_fr s s3 z f s' z' e : fr s s3 -> crel s3 z f s' z' e -> crel s z f s' z' e.
Proof.
  intros (P & A & U & G) (B1 & B2 & B3 & B4 & (k & x & Z & X & Ub) & C & F).
  assert (Ew : d_wrap s3 = d_wrap s) by (destruct A as (_ & E & _); exact E).
  rewrite Ew in Z. rewrite G in C. rewrite U in Ub.
  unfold crel. split; [exact B1|]. split; [exact B2|].
  split; [eapply rg_same_prm_trans; eauto|]. split; [eapply rg_api_eq_trans; eauto|].
  split; [exists k, x; auto|]. split; [exact C|].
  eapply Forall_impl; [|exact F]. intros e0 He. eapply rg_ev_ok_same_prm; eauto.
Qed.

Lemma rg_FI_fr s s3 z f s' z' e : fr s s3 -> FI s3 z f s' z' e -> FI s z f s' z' e.
Proof.
  intros Hf (C & Q & Z & A & L). split; [eapply rg_crel_fr; eauto|]. auto.
Qed.

Lemma rg_bpost_fr s s3 z f s' z' bs e : fr s s3 -> bpost s3 z f s' z' bs e -> bpost s z f s' z' bs e.
Proof.
  intros (P & A & _ & _) H. rewrite <- (app_nil_l e). eapply rg_bpost_start; eauto.
Qed.

(** ** A loop terminates when a measure >= 0 decreases on every continuing iteration and starts below 2^d
    (copy of RTDLTCLmKit.loop_measure) *)
Section RLoopMeasure.
Context {A B : Type} (body : A -> option (A + B)) (P : A -> Prop) (Q : B -> Prop) (m : A -> Z).
Hypothesis Hstep : forall a, P a -> 0 <= m a /\
  ((exists r, body a = Some (inr r) /\ Q r) \/ (exists a', body a = Some (inl a') /\ P a' /\ m a' < m a)).

Lemma rg_loop2_measure : forall d a, P a ->
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

Lemma rg_loop_measure : forall d a, P a -> m a < 2 ^ Z.of_nat d -> exists r, loop d body a = Some r /\ Q r.
Proof.
  intros d a Ha Hm. unfold loop.
  destruct (rg_loop2_measure d a Ha) as [[r [E HQ]]|[a' [E [HP Hm']]]]; rewrite E.
  - eauto.
  - destruct (Hstep a' HP) as [H0 _]. lia.
Qed.
End RLoopMeasure.

(** ** One iteration after the refill *)
Definition rstep_res (s : dstate) (z : strm) (flush : Z) (r : (dstate * strm) + dexit) : Prop :=
  match r with
  | inl (s', z') =>
      (exists evs, FI s z flush s' z' evs) /\ z_avail_in z' + d_lookahead s' < z_avail_in z + d_lookahead s
  | inr (s', z', o) =>
      o = Some need_more /\ exists evs, crel s z flush s' z' evs /\ bpost s z flush s' z' need_more evs
  end.

Lemma rstep_ok : rscan_stmt -> rlit_stmt -> rdist_stmt -> rbflush_stmt ->
  forall s z flush,
    W s -> outok s -> quiet s -> zall z -> adler_ok (d_wrap s) (z_adler z) -> fn_of s = 4 -> 0 <= flush <= 5 ->
    rready s -> 1 <= d_lookahead s ->
    exists r, rle_step s z = Some r /\ rstep_res s z flush r.
Proof.
  intros Hsc Hli Hdi Hbf s z flush HW Ho Hq Hz Ha Hfn Hfl Hr Hla.
  destruct (Hsc s HW Hfn Hr Hla) as (s2 & E2 & ml & -> & Hml & Hmll & Hms).
  assert (Hb : exists s3 bf syms3,
             rbranch (set_d_match_length s ml) = Some (s3, bf) /\ RTS s3 syms3 bf /\ fr s s3 /\
             d_lookahead s3 < d_lookahead s).
  { unfold rbranch. rewrite fk_match_length_match_length.
    destruct (ml >=? MIN_MATCH) eqn:Em.
    - apply Z.geb_le in Em. apply (Hdi s ml); auto. lia.
    - rewrite Z.geb_leb in Em. apply Z.leb_gt in Em. apply (Hli s ml); auto. lia. }
  destruct Hb as (s3 & bf & syms3 & E3 & HTS & Hfr & Hlt).
  assert (Hwr : d_wrap s3 = d_wrap s) by (destruct Hfr as (_ & (_ & E & _) & _); exact E).
  assert (Ha3 : adler_ok (d_wrap s3) (z_adler z)) by (rewrite Hwr; exact Ha).
  destruct (Hbf s3 z flush syms3 bf HTS Hz Ha3 Hfl) as (r & Er & Hr').
  exists r. split.
  { rewrite rle_step_eq, E2. cbn [bind]. rewrite E3. exact Er. }
  unfold rstep_res. destruct r as [[s' z']|[[s' z'] o]].
  - destruct Hr' as ((evs & HFI) & El & Ea). split; [exists evs; eapply rg_FI_fr; eauto|]. lia.
  - destruct Hr' as (Ho' & evs & Hc & Hb'). split; [exact Ho'|]. exists evs.
    split; [eapply rg_crel_fr; eauto|eapply rg_bpost_fr; eauto].
Qed.

(** ** The main loop *)
Definition rloop_res (s0 : dstate) (z0 : strm) (flush : Z) (r : dexit) : Prop :=
  let '(s, z, o) := r in
  match o with
  | Some bs => exists evs, crel s0 z0 flush s z evs /\ bpost s0 z0 flush s z bs evs
  | None =>
      exists evs, FI s0 z0 flush s z evs /\ d_lookahead s = 0 /\ z_avail_in z = 0 /\ flush <> Z_NO_FLUSH /\
                  d_strstart s < d_w_size s + MAX_DIST s
  end.

Lemma rFI_parts s0 z0 flush s z evs :
  FI s0 z0 flush s z evs -> fn_of s0 = 4 ->
  W s /\ outok s /\ quiet s /\ zall z /\ adler_ok (d_wrap s) (z_adler z) /\ fn_of s = 4.
Proof.
  intros ((HW & Ho & Hp & _) & Hq & Hz & Ha & _) Hfn.
  split; [exact HW|]. split; [exact Ho|]. split; [exact Hq|]. split; [exact Hz|]. split; [exact Ha|].
  rewrite (fn_of_same_prm s0 s Hp). exact Hfn.
Qed.

Lemma rFI_crel s0 z0 flush s z evs : FI s0 z0 flush s z evs -> crel s0 z0 flush s z evs.
Proof. intros (C & _). exact C. Qed.

Lemma rFI_last s0 z0 flush s z evs : FI s0 z0 flush s z evs -> Forall (fun e => ev_last e = 0) evs.
Proof. intros (_ & _ & _ & _ & L). exact L. Qed.

Lemma rFI_sp s0 z0 flush s z evs : FI s0 z0 flush s z evs -> same_prm s0 s /\ api_eq s0 s.
Proof. intros ((_ & _ & P & A & _) & _). auto. Qed.

Lemma rprm_w_bound s : prm s -> d_w_size s <= 32768.
Proof.
  intros (Hb & Hs & _). rewrite Hs. change 32768 with (2 ^ 15). apply Z.pow_le_mono_r; lia.
Qed.

Lemma rloop_ok : rrefill_stmt -> rscan_stmt -> rlit_stmt -> rdist_stmt -> rbflush_stmt ->
  forall s0 z0 flush,
    W s0 -> outok s0 -> quiet s0 -> zall z0 -> adler_ok (d_wrap s0) (z_adler z0) -> fn_of s0 = 4 ->
    0 <= flush <= 5 ->
    exists r, loop FUEL (rle_body flush) (s0, z0) = Some r /\ rloop_res s0 z0 flush r.
Proof.
  intros Hre Hsc Hli Hdi Hbf s0 z0 flush HW0 Ho0 Hq0 Hz0 Ha0 Hfn0 Hfl.
  apply (rg_loop_measure (rle_body flush) (fun a => exists evs, FI s0 z0 flush (fst a) (snd a) evs)
           (rloop_res s0 z0 flush) (fun a => z_avail_in (snd a) + d_lookahead (fst a))).
  - intros [s z] (evs & HFI). cbn [fst snd] in *.
    destruct (rFI_parts _ _ _ _ _ _ HFI Hfn0) as (HW & Ho & Hq & Hz & Ha & Hfn).
    split.
    { destruct HW as (_ & _ & (Hl & _) & _). destruct Hz as ((_ & _ & Hai & _) & _). lia. }
    destruct (Hre s z flush HW Ho Hq Hz Ha Hfn Hfl) as (r1 & E1 & H1).
    unfold rle_body. rewrite E1. cbn [bind].
    destruct r1 as [[s1 z1]|[[s1 z1] [bs|]]].
    + destruct H1 as (HFI1 & Hr1 & Hla1 & Hm1).
      destruct (rFI_parts _ _ _ _ _ _ HFI1 Hfn) as (HW1 & Ho1 & Hq1 & Hz1 & Ha1 & Hfn1).
      destruct (rstep_ok Hsc Hli Hdi Hbf s1 z1 flush HW1 Ho1 Hq1 Hz1 Ha1 Hfn1 Hfl Hr1 Hla1)
        as (r2 & E2 & H2).
      rewrite E2. unfold rstep_res in H2.
      destruct r2 as [[s2 z2]|[[s2 z2] o]].
      * destruct H2 as ((evs2 & HFI2) & Hm2). right. exists (s2, z2). split; [reflexivity|].
        cbn [fst snd]. split; [|lia].
        exists (evs ++ ([] ++ evs2)).
        eapply rg_FI_trans; [exact Hz0|exact Ha0|exact HFI|].
        eapply rg_FI_trans; [exact Hz|exact Ha|exact HFI1|exact HFI2].
      * destruct H2 as (-> & evs2 & Hc2 & Hb2). left. exists (s2, z2, Some need_more). split; [reflexivity|].
        cbv beta iota delta [rloop_res]. exists (evs ++ ([] ++ evs2)). split.
        -- eapply rg_crel_trans; [exact Hz0|exact Ha0|apply rFI_crel; exact HFI|].
           eapply rg_crel_trans; [exact Hz|exact Ha|apply rFI_crel; exact HFI1|exact Hc2].
        -- destruct (rFI_sp _ _ _ _ _ _ HFI) as (P1 & A1). destruct (rFI_sp _ _ _ _ _ _ HFI1) as (P2 & A2).
           eapply (rg_bpost_start s0 s z0 z); [exact P1|exact A1|apply (rFI_last _ _ _ _ _ _ HFI)|].
           eapply rg_bpost_start; [exact P2|exact A2|constructor|exact Hb2].
    + destruct H1 as (-> & Hc1 & Hb1). left. exists (s1, z1, Some need_more). split; [reflexivity|].
      cbv beta iota delta [rloop_res]. exists (evs ++ []). split.
      * eapply rg_crel_trans; [exact Hz0|exact Ha0|apply rFI_crel; exact HFI|exact Hc1].
      * destruct (rFI_sp _ _ _ _ _ _ HFI) as (P1 & A1).
        eapply rg_bpost_start; [exact P1|exact A1|apply (rFI_last _ _ _ _ _ _ HFI)|exact Hb1].
    + destruct H1 as (HFI1 & H1). left. exists (s1, z1, None). split; [reflexivity|].
      cbv beta iota delta [rloop_res]. exists (evs ++ []). split; [|exact H1].
      eapply rg_FI_trans; [exact Hz0|exact Ha0|exact HFI|exact HFI1].
  - exists []. cbn [fst snd]. apply FI_refl; auto.
  - cbn [fst snd]. destruct HW0 as (Hp & (_ & _ & Hws & _) & (_ & Hss & Hsl & _) & _).
    pose proof (rprm_w_bound s0 Hp) as Hw.
    destruct Hz0 as ((_ & _ & Hai & _) & _). change (Z.of_nat FUEL) with 40. lia.
Qed.

(** ** deflate_rle from its parts *)
Theorem rle_from_parts :
  rrefill_stmt -> rscan_stmt -> rlit_stmt -> rdist_stmt -> rbflush_stmt -> rtail_stmt -> rle_spec.
Proof.
  intros Hre Hsc Hli Hdi Hbf Hta s z flush (HW & Ho & Hq & Hfl & Hzi & Hwr & Ha) Hfn.
  pose proof (zin_ok_zall z Hzi) as Hz.
  destruct (rloop_ok Hre Hsc Hli Hdi Hbf s z flush HW Ho Hq Hz Ha Hfn Hfl) as ([[s1 z1] o] & E & H).
  unfold c_deflate_rle. rewrite E. cbn [bind].
  destruct o as [bs|].
  - destruct H as (evs & Hc & Hb). exists s1, z1, bs, evs. split; [reflexivity|].
    apply cpost_of; assumption.
  - destruct H as (evs & HFI & Hl & Hai & Hf & Hss).
    destruct (rFI_parts _ _ _ _ _ _ HFI Hfn) as (HW1 & Ho1 & Hq1 & Hz1 & Ha1 & Hfn1).
    destruct (Hta s1 z1 flush HW1 Ho1 Hq1 Hz1 Ha1 Hfn1 Hfl Hf Hl Hai Hss) as (s2 & z2 & bs & evs2 & E2 & Hc2 & Hb2).
    exists s2, z2, bs, (evs ++ evs2). split; [exact E2|].
    apply cpost_of.
    + eapply rg_crel_trans; [exact Hz|exact Ha|apply rFI_crel; exact HFI|exact Hc2].
    + destruct (rFI_sp _ _ _ _ _ _ HFI) as (P1 & A1).
      eapply rg_bpost_start; [exact P1|exact A1|apply (rFI_last _ _ _ _ _ _ HFI)|exact Hb2].
Qed.
