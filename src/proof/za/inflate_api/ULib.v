(* The bodies of the allocator-generic port against one specification per function (USpec.v): VST's
   semax_body_generalintersection over the bodies of the members, each moved to the context of uspecs
   (generalintersection_sub: a uspec is a funspec_sub of each member). *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.za.inflate_api.USpec.
Require Zlib.proof.inflate_api.LibProof5.

(* Two contexts with the same functions in the same order, each specification of the second a funspec_sub
   of the first's: a body proved in the first context holds in the second. *)
Definition ctx_pw (G G' : funspecs) : Prop :=
  Forall2 (fun a b => fst a = fst b /\ funspec_sub (snd b) (snd a)) G G'.

Lemma funspec_sub_type_eq : forall phi1 phi2, funspec_sub phi1 phi2 -> type_of_funspec phi1 = type_of_funspec phi2.
Proof.
  intros [sig1 cc1 A1 P1 Q1 P1ne Q1ne] [sig2 cc2 A2 P2 Q2 P2ne Q2ne] [[E1 E2] _].
  subst; reflexivity.
Qed.

Lemma ctx_pw_tycontext_g : forall V G G', ctx_pw G G' -> make_tycontext_g V G = make_tycontext_g V G'.
Proof.
  intros V G G' H. induction H as [|a b G G' [E S] _ IH]; [reflexivity|].
  unfold make_tycontext_g in *; simpl. rewrite IH, E, (funspec_sub_type_eq _ _ S). reflexivity.
Qed.

Lemma ctx_pw_find_id : forall G G', ctx_pw G G' -> forall i, subsumespec (initial_world.find_id i G) (initial_world.find_id i G').
Proof.
  intros G G' H i. induction H as [|[j phi] [j' phi'] G G' [E S] _ IH]; [exact I|].
  simpl in E, S |- *. subst j'. destruct (Memory.EqDec_ident i j).
  - exists phi'. split; [reflexivity|]. apply seplog.funspec_sub_sub_si, funspec_sub_iff; exact S.
  - exact IH.
Qed.

Lemma semax_body_ctx_pw {cs : compspecs} V G G' f spec :
  @semax_body V G cs f spec -> ctx_pw G G' -> @semax_body V G' cs f spec.
Proof.
  intros SB H. eapply Component.semax_body_subsumespec; [exact SB | | apply ctx_pw_find_id; exact H].
  intros i. rewrite (ctx_pw_tycontext_g V G G' H). destruct (Maps.PTree.get i (make_tycontext_g V G')); simpl; auto.
Qed.

(* a body against a declared specification (a pair) is a body against its name and its funspec *)
Lemma semax_body_pair {cs : compspecs} V G f (X : ident * funspec) id :
  fst X = id -> @semax_body V G cs f X -> @semax_body V G cs f (id, snd X).
Proof. destruct X; simpl; intros; subst; assumption. Qed.

(* VST's semax_body_generalintersection without the inhabitant of the index: the signature conjuncts come
   from one body of a specification with the same signature (in any context) *)
Lemma semax_body_gi {cs : compspecs} V G G0 f iden {I sig cc} (phi : I -> funspec)
  (H1 : forall i, typesig_of_funspec (phi i) = sig) (H2 : forall i, callingconvention_of_funspec (phi i) = cc)
  (spec0 : funspec) (E0 : typesig_of_funspec spec0 = sig) (B0 : @semax_body V G0 cs f (iden, spec0))
  (H : forall i, @semax_body V G cs f (iden, phi i)) :
  @semax_body V G cs f (iden, @general_intersection I sig cc phi H1 H2).
Proof.
  assert (S0 : fst sig = map snd (fst (fn_funsig f)) /\ snd sig = snd (fn_funsig f)).
  { destruct spec0; simpl in E0; subst; destruct B0 as [? [? _]]; auto. }
  destruct S0 as [S1 S2]. split3; [exact S1 | exact S2 |].
  intros Espec ts x. destruct x as [i Hi].
  pose proof (semax_body_generalintersection (cs := cs) (V := V) (G := G) (f := f) (iden := iden)
                H1 H2 (inhabits i) H) as SB.
  destruct SB as [_ [_ SB]]. exact (SB Espec ts (existT _ i Hi)).
Qed.

(* the uspec [U] of the member family of [S]: a funspec_sub of each member *)
Ltac gsub i S C := apply funspec_sub_iff; exact (generalintersection_sub _ S C _ eq_refl i).

(* one entry of two pointwise related contexts: the same specification, or a uspec and its member *)
Ltac pw_refl := apply Forall2_cons; [split; [reflexivity | apply funspec_sub_refl] |].
Ltac pw_sub H := apply Forall2_cons; [split; [reflexivity | exact H] |].

Lemma za_ulib : forall (K : Type) (A : K -> zallocator),
  za_uspec_sub_stmt A /\
  (za_cases_stmt -> za_body_inflate_stmt -> stepf2_mwf3_stmt_za -> za_fast_stmt -> za_api_stmt ->
   za_inflate_ulib_stmt A).
Proof.
  intros K A.
  assert (HSub : za_uspec_sub_stmt A).
  { intros i. cbv zeta.
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))).
    - gsub i (inflate_sig A) (inflate_cc A).
    - gsub i (inflate_fast_sig A) (inflate_fast_cc A).
    - gsub i (updatewindow_sig A) (updatewindow_cc A).
    - gsub i (inflateStateCheck_sig A) (inflateStateCheck_cc A).
    - gsub i (inflateSetDictionary_sig A) (inflateSetDictionary_cc A).
    - gsub i (inflateInit2__sig A) (inflateInit2__cc A).
    - gsub i (inflateResetKeep_sig A) (inflateResetKeep_cc A).
    - gsub i (inflateReset_sig A) (inflateReset_cc A).
    - gsub i (inflateReset2_sig A) (inflateReset2_cc A).
    - gsub i (inflateEnd_sig A) (inflateEnd_cc A). }
  split; [exact HSub |].
  intros HC HB HS HF HA Espec.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))).
  - (* inflate: its member's context Gprog_inflate3_za *)
    unfold inflate_uspec, uspec.
    eapply (semax_body_gi _ _ _ _ _ _ _ _ (snd (@inflate_spec_za za0 av_defined)) eq_refl).
    + apply semax_body_pair; [reflexivity |].
      exact (HB za0 av_defined (HC _ _) HS Zlib.proof.inflate_api.LibProof5.stepf2_hd_proof Espec).
    + intros i. destruct (HSub i) as (S_inf & S_fast & S_uw & S_chk & _).
      eapply semax_body_ctx_pw.
      * apply semax_body_pair; [reflexivity |].
        exact (HB (zai_a A i) (zai_v i) (HC _ _) HS Zlib.proof.inflate_api.LibProof5.stepf2_hd_proof Espec).
      * unfold Gprog_inflate3_za, Gprog_cases3_za, GU_inflate. cbn [app].
        pw_refl. pw_refl. pw_sub S_fast. pw_refl. pw_refl. pw_refl. pw_sub S_chk. pw_sub S_uw.
        apply Forall2_nil.
  - (* inflate_fast: no callees *)
    unfold inflate_fast_uspec, uspec.
    eapply (semax_body_gi _ _ _ _ _ _ _ _ (snd (@inflate_fast_spec3_za za0 av_defined)) eq_refl).
    + apply semax_body_pair; [reflexivity | exact (HF za0 av_defined Espec)].
    + intros i. apply semax_body_pair; [reflexivity | exact (HF (zai_a A i) (zai_v i) Espec)].
  - (* updatewindow: its callee memcpy is the same in both contexts *)
    unfold updatewindow_uspec, uspec.
    eapply (semax_body_gi _ _ _ _ _ _ _ _ (snd (@updatewindow_spec3_za za0)) eq_refl).
    + apply semax_body_pair; [reflexivity | exact (proj1 (HA za0 av_defined Espec))].
    + intros i. apply semax_body_pair; [reflexivity | exact (proj1 (HA (zai_a A i) (zai_v i) Espec))].
  - (* inflateStateCheck: no callees *)
    unfold inflateStateCheck_uspec, uspec.
    eapply (semax_body_gi _ _ _ _ _ _ _ _ (snd (@inflateStateCheck_spec_za za0)) eq_refl).
    + apply semax_body_pair; [reflexivity | exact (proj1 (proj2 (HA za0 av_defined Espec)))].
    + intros i. apply semax_body_pair; [reflexivity |].
      exact (proj1 (proj2 (HA (zai_a A i) (zai_v i) Espec))).
  - (* inflateSetDictionary *)
    unfold inflateSetDictionary_uspec, uspec.
    eapply (semax_body_gi _ _ _ _ _ _ _ _ (snd (@inflateSetDictionary_spec_za za0 av_defined)) eq_refl).
    + destruct (HA za0 av_defined Espec) as (_ & _ & B & _).
      apply semax_body_pair; [reflexivity | exact B].
    + intros i. destruct (HSub i) as (_ & _ & S_uw & S_chk & _).
      destruct (HA (zai_a A i) (zai_v i) Espec) as (_ & _ & B & _).
      eapply semax_body_ctx_pw; [apply semax_body_pair; [reflexivity | exact B] |].
      unfold Gp_setdict_za, GU_setdict. pw_sub S_chk. pw_refl. pw_sub S_uw. apply Forall2_nil.
  - (* inflateInit2_ *)
    unfold inflateInit2__uspec, uspec.
    eapply (semax_body_gi _ _ _ _ _ _ _ _ (snd (@inflateInit2__spec_za za0)) eq_refl).
    + destruct (HA za0 av_defined Espec) as (_ & _ & _ & B & _).
      apply semax_body_pair; [reflexivity | exact B].
    + intros i. destruct (HSub i) as (_ & _ & _ & _ & _ & _ & _ & _ & S_r2 & _).
      destruct (HA (zai_a A i) (zai_v i) Espec) as (_ & _ & _ & B & _).
      eapply semax_body_ctx_pw; [apply semax_body_pair; [reflexivity | exact B] |].
      unfold Gp_init2_za, GU_init2. pw_sub S_r2. pw_refl. apply Forall2_nil.
  - (* inflateResetKeep *)
    unfold inflateResetKeep_uspec, uspec.
    eapply (semax_body_gi _ _ _ _ _ _ _ _ (snd (@inflateResetKeep_spec_za za0 av_defined)) eq_refl).
    + destruct (HA za0 av_defined Espec) as (_ & _ & _ & _ & B & _).
      apply semax_body_pair; [reflexivity | exact B].
    + intros i. destruct (HSub i) as (_ & _ & _ & S_chk & _).
      destruct (HA (zai_a A i) (zai_v i) Espec) as (_ & _ & _ & _ & B & _).
      eapply semax_body_ctx_pw; [apply semax_body_pair; [reflexivity | exact B] |].
      unfold Gp_resetkeep_za, GU_resetkeep. pw_sub S_chk. apply Forall2_nil.
  - (* inflateReset *)
    unfold inflateReset_uspec, uspec.
    eapply (semax_body_gi _ _ _ _ _ _ _ _ (snd (@inflateReset_spec_za za0 av_defined)) eq_refl).
    + destruct (HA za0 av_defined Espec) as (_ & _ & _ & _ & _ & B & _).
      apply semax_body_pair; [reflexivity | exact B].
    + intros i. destruct (HSub i) as (_ & _ & _ & S_chk & _ & _ & S_rk & _).
      destruct (HA (zai_a A i) (zai_v i) Espec) as (_ & _ & _ & _ & _ & B & _).
      eapply semax_body_ctx_pw; [apply semax_body_pair; [reflexivity | exact B] |].
      unfold Gp_reset_za, GU_reset. pw_sub S_chk. pw_sub S_rk. apply Forall2_nil.
  - (* inflateReset2 *)
    unfold inflateReset2_uspec, uspec.
    eapply (semax_body_gi _ _ _ _ _ _ _ _ (snd (@inflateReset2_spec_za za0 av_defined)) eq_refl).
    + destruct (HA za0 av_defined Espec) as (_ & _ & _ & _ & _ & _ & B & _).
      apply semax_body_pair; [reflexivity | exact B].
    + intros i. destruct (HSub i) as (_ & _ & _ & S_chk & _ & _ & _ & S_r & _).
      destruct (HA (zai_a A i) (zai_v i) Espec) as (_ & _ & _ & _ & _ & _ & B & _).
      eapply semax_body_ctx_pw; [apply semax_body_pair; [reflexivity | exact B] |].
      unfold Gp_reset2_za, GU_reset2. pw_sub S_chk. pw_sub S_r. apply Forall2_nil.
  - (* inflateEnd *)
    unfold inflateEnd_uspec, uspec.
    eapply (semax_body_gi _ _ _ _ _ _ _ _ (snd (@inflateEnd_spec_za za0 av_defined)) eq_refl).
    + destruct (HA za0 av_defined Espec) as (_ & _ & _ & _ & _ & _ & _ & B).
      apply semax_body_pair; [reflexivity | exact B].
    + intros i. destruct (HSub i) as (_ & _ & _ & S_chk & _).
      destruct (HA (zai_a A i) (zai_v i) Espec) as (_ & _ & _ & _ & _ & _ & _ & B).
      eapply semax_body_ctx_pw; [apply semax_body_pair; [reflexivity | exact B] |].
      unfold Gp_end_za, GU_end. pw_sub S_chk. apply Forall2_nil.
Qed.
