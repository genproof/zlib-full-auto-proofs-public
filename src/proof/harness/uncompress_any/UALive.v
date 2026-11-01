(* Law uncompress_any, theory part: one inflate() call keeps live_ok and zf_ok (UATheoryDefs.ua_live_stmt).
   The pure content of inflate()'s body proof (inflate_api/Body5_inflate.v): along Model2.loop2 one pass keeps
   mwf3 (UAStepMwf), out_inv / the window flag / win_inv5 (UALiveStep, case HEAD = c_HEAD2 of contract fix F7)
   and the header's presence and buffers (UAHdrKit); the exit inf_leave gives a final machine (Body5Fin), which
   is a live stream (Body5Conv's fin_ok5). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.uncompress_any.UATheoryDefs.
Require Import Zlib.proof.inflate_api.Body5Parts.
Require Import Zlib.proof.inflate_api.Body5Conv.
Require Import Zlib.proof.inflate_api.Body5Fin.
Require Zlib.proof.harness.uncompress_any.UAHdrKit.
Require Import Zlib.proof.harness.uncompress_any.UALiveStep.
Require Import Zlib.proof.harness.uncompress_any.UAStepMwf.
Import ListNotations.
Local Open Scope Z_scope.

(* the invariant of the loop head, relative to the first machine m0 *)
Definition ua_linv (m0 m: mst) : Prop :=
  mwf3 m /\ out_inv m /\ win_inv5 (m_s m) /\ i_win (m_s m) = i_win (m_s m0) /\ UAHdrKit.hrel m0 m.

Lemma ua_pass: forall flush m0 m, ua_linv m0 m -> m_leave m = 0 ->
  match stepf2 flush lenfix_list distfix_list m with
  | IBrk m' => ua_linv m0 m'
  | IRet _ m' => mwf3 m' /\ win_inv5 (m_s m') /\ i_win (m_s m') = i_win (m_s m0) /\ UAHdrKit.hrel m0 m'
  end.
Proof.
  intros flush m0 m (W & O & V & I & H) L.
  pose proof (ua_stepf2_mwf3 flush m W L) as HW.
  pose proof (ua_stepf_inv5 flush m W L O V) as HV.
  pose proof (UAHdrKit.stepf2_hrel flush lenfix_list distfix_list m) as HH.
  destruct (stepf2 flush lenfix_list distfix_list m) as [m'|r m'].
  - destruct HV as (O' & I' & V'). unfold ua_linv.
    split; [exact HW|]. split; [exact O'|]. split; [exact V'|]. split; [congruence|].
    eapply UAHdrKit.hrel_trans; eassumption.
  - destruct HV as (I' & V').
    split; [exact HW|]. split; [exact V'|]. split; [congruence|].
    eapply UAHdrKit.hrel_trans; eassumption.
Qed.

Lemma ua_loop: forall flush m o, loop2 flush lenfix_list distfix_list m o ->
  forall m0, ua_linv m0 m -> m_leave m = 0 ->
  match o with
  | IBrk m' => ua_linv m0 m' /\ m_leave m' = 1
  | IRet _ m' => mwf3 m' /\ win_inv5 (m_s m') /\ i_win (m_s m') = i_win (m_s m0) /\ UAHdrKit.hrel m0 m'
  end.
Proof.
  induction 1 as [m r m' E | m m' E L1 | m m' o E L1 Hl IH]; intros m0 HI L0;
    pose proof (ua_pass flush m0 m HI L0) as P; rewrite E in P.
  - exact P.
  - split; assumption.
  - apply IH; [exact P|]. destruct P as (W & _).
    pose proof (mw_leave _ (mwf3_mwf _ W)). lia.
Qed.

(* the live part after the call *)
Lemma ua_live_fin: forall (L: live) winp m,
  live_ok L -> fin_ok5 m ->
  (i_head (m_s m) = true ->
     (h_xp (m_h m) = true -> l_xb L <> nullval) /\ (h_np (m_h m) = true -> l_nb L <> nullval) /\
     (h_cp (m_h m) = true -> l_cb L <> nullval)) ->
  live_ok (Live (l_sp L) winp (m_s m) (m_h m) (l_headp L) (l_hsh L) (l_xb L) (l_nb L) (l_cb L)).
Proof.
  intros L winp m (LP & _ & _ & _ & _ & LW & _) (A & B & C & D & [W1 W2] & _) H.
  unfold live_ok; simpl. auto 10.
Qed.

Lemma ua_zf_fin: forall z ib o res,
  fin_ok5 (r_m res) -> srange (zf_dt z) -> (forall d, r_dtype res = Some d -> srange d) ->
  zf_ok (z_after z ib o res).
Proof.
  intros z ib o res (_ & _ & _ & _ & _ & E1 & E2 & E3 & E4 & E5 & E6 & E7) DT DR.
  unfold zf_ok, z_after, srange, lrange in *; simpl.
  destruct (r_dtype res) as [d|] eqn:ED; [specialize (DR d eq_refl) | ]; rep_lia.
Qed.

Lemma ua_live : ua_live_stmt.
Proof.
  intros flush strmp z L ib inp o r z' st' ow LOK ZOK NN NI AI IL BI AO REL NM.
  destruct REL as [(_ & _ & -> & -> & _) | (NB & L1 & o1 & res & winp & EL & EO & RUN & SNX & ER & EOW & EZ & EW & ES)].
  { exists L. auto. }
  injection EL as <-. injection EO as <-. subst st' z'.
  eexists; split; [reflexivity|].
  set (m0 := m_init z L inp).
  assert (MW: mwf3 m0) by (apply m_init_mwf3; auto).
  assert (OI: out_inv m0) by (apply m_init_out_inv; destruct ZOK as (_ & ? & _); lia).
  assert (WI0: win_inv5 (m_s m0)) by (unfold m0; rewrite m_init_s; apply s_typedo_win_inv5, live_win_inv5, LOK).
  assert (HI0: ua_linv m0 m0).
  { split; [exact MW|]. split; [exact OI|]. split; [exact WI0|]. split; [reflexivity|]. apply UAHdrKit.hrel_refl. }
  assert (HD0: i_head (m_s m0) = true ->
     (h_xp (m_h m0) = true -> l_xb L <> nullval) /\ (h_np (m_h m0) = true -> l_nb L <> nullval) /\
     (h_cp (m_h m0) = true -> l_cb L <> nullval)).
  { unfold m0. rewrite m_init_s. cbn [m_h m_init]. unfold s_typedo.
    pose proof LOK as (_ & _ & _ & _ & _ & _ & _ & LHD & _).
    destruct (i_mode (l_s L) =? Zlib.proof.inflate.Model.TYPE); exact LHD. }
  assert (HDT: forall m, UAHdrKit.hrel m0 m ->
     i_head (m_s m) = true ->
     (h_xp (m_h m) = true -> l_xb L <> nullval) /\ (h_np (m_h m) = true -> l_nb L <> nullval) /\
     (h_cp (m_h m) = true -> l_cb L <> nullval)).
  { intros m (_ & E1 & _ & _ & _ & X & N & C) Hh. rewrite E1 in Hh.
    destruct (HD0 Hh) as (X0 & N0 & C0). auto. }
  assert (DT: srange (zf_dt z)) by (destruct ZOK as (_&_&_&_&?&_); exact H).
  destruct RUN as (out & LP & HO).
  pose proof (ua_loop flush m0 out LP m0 HI0 eq_refl) as HL.
  destruct out as [m | r1 m].
  - destruct HL as ((W & O & V & I & H) & L1).
    destruct (leave_fin5 flush m res W O V HO) as (FO & DR & EH & EHd & _).
    split.
    + eapply ua_live_fin; [exact LOK | exact FO | ].
      rewrite EH, EHd. apply HDT, H.
    + apply ua_zf_fin; assumption.
  - destruct HL as (W & V & I & H). subst res.
    pose proof (mwf3_fin_ok5 m W V) as FO.
    split.
    + eapply ua_live_fin; [exact LOK | exact FO | ]. apply HDT, H.
    + apply ua_zf_fin; [exact FO | exact DT | discriminate].
Qed.
