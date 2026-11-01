(* Law inflate_dict, theory part: the frame of one inflate() call. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.inflate_dict.ITTheoryDefs.
Import ListNotations.
Local Open Scope Z_scope.

Require Import Zlib.proof.inflate_api.Body5Parts.
Require Import Zlib.proof.inflate_api.Body5Conv.
Require Zlib.proof.rfc1951.DecMwf.
Require Zlib.proof.inflate_api.StepInv5Kit.
Require Zlib.proof.inflate_api.Body5HdrKit.
Require Import Zlib.proof.harness.inflate_dict.ITFrameStep.
Require Import Zlib.proof.harness.inflate_dict.ITFrameFin.
Local Open Scope Z_scope.

(* the invariant of the loop head (K: wbits is tracked) and what a returning pass keeps *)
Section ITFrameLoop.
Variables (flush: Z) (inp: list Z) (A w0: Z) (K: Prop).

Definition itf_inv (m: mst) : Prop :=
  mwf3 m /\ out_inv m /\ win_inv5 (m_s m) /\ m_inp m = inp /\ m_aout m = A /\
  (K -> i_wbits (m_s m) = w0 /\ (i_mode (m_s m) <> HEAD \/ i_wrap (m_s m) = 0)).

Definition itf_ret (m: mst) : Prop :=
  mwf3 m /\ m_inp m = inp /\ m_aout m = A /\ (K -> i_wbits (m_s m) = w0).

Lemma itf_step_frame m : itf_inv m ->
  match stepf2 flush lenfix_list distfix_list m with
  | IBrk m' => m_aout m' = m_aout m /\ (K -> i_wbits (m_s m') = w0 /\ i_mode (m_s m') <> HEAD)
  | IRet _ m' => m_aout m' = m_aout m /\ (K -> i_wbits (m_s m') = w0)
  end.
Proof.
  intros (M & O & W & Ei & Ea & Kw).
  destruct (Z.eq_dec (m_mode m) HEAD) as [Hh|Hh].
  - assert (E: stepf2 flush lenfix_list distfix_list m = c_HEAD2 m)
      by (unfold stepf2, step2; rewrite Hh; reflexivity).
    rewrite E. destruct (itf_c_HEAD_frame m) as [F1 F2].
    destruct (c_HEAD2 m) as [m'|r m'] eqn:C.
    + split; [exact F1|]. intros k. destruct (Kw k) as [Hw [Hm|Hr]].
      * unfold m_mode in Hh. contradiction.
      * pose proof (F2 Hr) as E2. injection E2 as E2. rewrite E2. simpl. split; [exact Hw|].
        unfold HEAD, TYPEDO. lia.
    + split; [exact F1|]. intros k. destruct (Kw k) as [Hw [Hm|Hr]].
      * unfold m_mode in Hh. contradiction.
      * pose proof (F2 Hr) as E2. discriminate.
  - pose proof (StepInv5Kit.stepf2_wgood flush lenfix_list distfix_list m Hh) as G.
    destruct (stepf2 flush lenfix_list distfix_list m) as [m'|r m'];
      unfold StepInv5Kit.wgood, StepInv5Kit.wrel in G; destruct G as (G1 & G2 & G3 & G4 & G5 & G6).
    + split; [exact G3|]. intros k. destruct (Kw k) as [Hw _]. split; [congruence | exact G6].
    + split; [exact G3|]. intros k. destruct (Kw k) as [Hw _]. congruence.
Qed.

Lemma itf_step m : itf_inv m -> m_leave m = 0 ->
  match stepf2 flush lenfix_list distfix_list m with IBrk m' => itf_inv m' | IRet _ m' => itf_ret m' end.
Proof.
  intros I L0. pose proof I as (M & O & W & Ei & Ea & Kw).
  pose proof (DecMwf.dm_stepf2_mwf3 flush m M L0) as HM.
  pose proof (itf_stepf_inv5 flush m M L0 O W) as HI.
  pose proof (Body5HdrKit.stepf2_hrel flush lenfix_list distfix_list m) as HH.
  pose proof (itf_step_frame m I) as HA.
  destruct (stepf2 flush lenfix_list distfix_list m) as [m'|r m'];
    destruct HH as (H1 & _); destruct HA as [A1 A2].
  - destruct HI as (I1 & _ & I3).
    unfold itf_inv. refine (conj HM (conj I1 (conj I3 (conj _ (conj _ _))))); [congruence | congruence |].
    intros k. destruct (A2 k) as [B1 B2]. split; [exact B1 | left; exact B2].
  - unfold itf_ret. refine (conj HM (conj _ (conj _ A2))); congruence.
Qed.

Lemma itf_loop m o : loop2 flush lenfix_list distfix_list m o -> itf_inv m -> m_leave m = 0 ->
  match o with IBrk m' => itf_inv m' | IRet _ m' => itf_ret m' end.
Proof.
  induction 1 as [m r m' S | m m' S Lv | m m' o S Lv Lp IH]; intros I L0;
    pose proof (itf_step m I L0) as T; rewrite S in T.
  - exact T.
  - exact T.
  - apply IH; [exact T|]. destruct T as ((Wm & _) & _).
    pose proof (mw_leave _ Wm). lia.
Qed.

End ITFrameLoop.

Lemma itf_init z L inp : live_ok L -> zf_ok z -> zf_ao z <= Int.max_signed ->
  Zlength inp <= Int.max_signed -> bytes_ok inp ->
  itf_inv inp (zf_ao z) (i_wbits (l_s L)) (i_mode (l_s L) <> HEAD \/ i_wrap (l_s L) = 0) (m_init z L inp).
Proof.
  intros HL HZ HA HI HB.
  pose proof HZ as (_ & Z2 & _).
  unfold itf_inv. split; [apply m_init_mwf3; auto|].
  split; [apply m_init_out_inv; lia|].
  rewrite m_init_s.
  split; [apply s_typedo_win_inv5, live_win_inv5; exact HL|].
  split; [reflexivity|]. split; [reflexivity|].
  intros k. unfold s_typedo.
  destruct (Z.eqb_spec (i_mode (l_s L)) Zlib.proof.inflate.Model.TYPE) as [T|T]; simpl.
  - split; [reflexivity|]. left. unfold HEAD, TYPEDO. lia.
  - split; [reflexivity|exact k].
Qed.

Lemma itf_frame : frame_stmt.
Proof.
  intros flush z L inp res HL HZ HA HI HB (o & Lp & Ho).
  pose proof (itf_init z L inp HL HZ HA HI HB) as I0.
  pose proof (itf_loop flush inp _ _ _ _ _ Lp I0 eq_refl) as T.
  destruct o as [m|r m].
  - destruct T as (M & O & W & Ei & Ea & Kw).
    destruct (itf_leave_fin5 flush m res M O W Ho) as (F & _ & _ & _ & Fi).
    destruct (itf_leave_keep flush m res Ho) as [K1 K2].
    split; [congruence|]. split; [congruence|].
    split; [intros k; destruct (Kw k) as [Hw _]; congruence|].
    intros _. destruct F as (F1 & _ & _ & _ & _ & _ & _ & F8 & _). split; [exact F1 | exact F8].
  - subst res. simpl. destruct T as ((Wm & _) & Ei & Ea & Kw).
    split; [exact Ei|]. split; [exact Ea|]. split; [exact Kw|].
    intros _. pose proof (mw_sow _ Wm). pose proof (mw_ow _ Wm) as [Ow _].
    split; [exact (mw_s _ Wm) | lia].
Qed.
