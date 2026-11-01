(* Law inflate_buffers, theory: the counters of one inflate() call in the model (IBFacts.ib_run_stmt): Model2.run2
   from Spec5.m_init keeps the input and avail_out, advances next_out by exactly the bytes written (which fit the
   space), keeps the gz_header flag, and (unless Z_MEM_ERROR) total_in/total_out grow by the bytes consumed/produced. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.inflate_buffers.IBFacts.
Require Import Zlib.proof.inflate.Inv3.
Require Zlib.proof.inflate.Cover2 Zlib.proof.inflate.Cover3 Zlib.proof.inflate.Cover3Len.
Require Zlib.proof.inflate.StepMwf5 Zlib.proof.inflate.StepHd5.
Require Import Zlib.proof.harness.inflate_buffers.IBStepKit.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* One pass keeps mwf3 (InvQ5.v's proof)                                                          *)

Lemma ib_cover3 : Zlib.proof.inflate.Cover3.cover3_stmt.
Proof.
  intros type lens req old root used t A B C D E.
  destruct (Zlib.proof.inflate.Cover2.cover2_proof type lens req old root used t A B C D E) as [T U].
  split; [exact T|]. split; [exact U|].
  intros ->. eapply Zlib.proof.inflate.Cover3Len.cover3_len_inv2; eauto.
Qed.

Lemma ib_stepf2_mwf3 : forall flush m, mwf3 m -> m_leave m = 0 ->
  match stepf2 flush lenfix_list distfix_list m with IBrk m' => mwf3 m' | IRet _ m' => mwf3 m' end.
Proof. exact (proj1 (Zlib.proof.inflate.StepMwf5.stepf2_inv ib_cover3)). Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The machine at the loop head (Body5Conv.v's proof)                                             *)

Definition ib_typedo (s: istate) : istate :=
  if i_mode s =? Zlib.proof.inflate.Model.TYPE then set_i_mode s TYPEDO else s.

Ltac ib_consts := unfold HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC, DICTID, DICT,
  Zlib.proof.inflate.Model.TYPE, TYPEDO, STORED, COPY_, COPY, TABLE, LENLENS, CODELENS, LEN_, LEN,
  LENEXT, DIST, DISTEXT, MATCH, LIT, CHECK, LENGTH, DONE, BAD, MEM, SYNC in *.

Lemma ib_typedo_swf: forall s, swf s -> swf (ib_typedo s).
Proof.
  intros s H. unfold ib_typedo. destruct (Z.eqb_spec (i_mode s) Zlib.proof.inflate.Model.TYPE); [ | exact H].
  destruct H; constructor; simpl; auto. ib_consts. lia.
Qed.

Lemma ib_typedo_modewf: forall s, modewf s -> modewf (ib_typedo s).
Proof.
  intros s H. unfold ib_typedo. destruct (Z.eqb_spec (i_mode s) Zlib.proof.inflate.Model.TYPE); [ | exact H].
  constructor; simpl; unfold decode_mode; ib_consts; intros; lia.
Qed.

Lemma ib_typedo_swf3: forall s, swf3 s -> swf3 (ib_typedo s).
Proof.
  intros s H. unfold ib_typedo. destruct (Z.eqb_spec (i_mode s) Zlib.proof.inflate.Model.TYPE); [ | exact H].
  destruct H; constructor; simpl; auto; unfold decode_mode; ib_consts; intros; lia.
Qed.

Lemma ib_typedo_head: forall s, i_head (ib_typedo s) = i_head s.
Proof. intros s. unfold ib_typedo. destruct (_ =? _); reflexivity. Qed.

Lemma ib_m_init_mwf3: forall z L inp,
  live_ok L -> zf_ok z -> zf_ao z <= Int.max_signed ->
  Zlength inp <= Int.max_signed -> bytes_ok inp ->
  mwf3 (m_init z L inp).
Proof.
  intros z L inp (HP & HS & HM & HH & HS3 & _) HZ HA HI HB.
  destruct HZ as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6).
  pose proof (Zlength_nonneg inp).
  split.
  - pose proof (sw_hold _ HS). pose proof (sw_bits _ HS).
    constructor; unfold m_init; simpl;
      try (fold (ib_typedo (l_s L)));
      try (apply ib_typedo_modewf; exact HM);
      try (apply ib_typedo_swf; exact HS);
      try exact HH;
      unfold urange, lrange, Z_OK in *; rewrite ?Zlength_nil;
      try solve [lia | split; [lia | auto] | split; [lia | constructor] | left; reflexivity].
  - apply ib_typedo_swf3. exact HS3.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* inf_leave                                                                                      *)

Lemma ib_uw_head s d : i_head (updatewindow s d) = i_head s.
Proof. unfold updatewindow. cbv zeta. repeat (destruct (_ =? _) || destruct (_ <=? _) || destruct (_ <? _)); reflexivity. Qed.

Lemma ib_leave_fin fl m : let m2 := r_m (leave_fin fl m) in
  m_inp m2 = m_inp m /\ m_aout m2 = m_aout m /\ m_ow m2 = m_ow m /\ m_sow m2 = Zlength (m_ow m) /\
  m_snx m2 = m_nx m /\ i_head (m_s m2) = i_head (m_s m) /\
  m_tin m2 = u64 (m_tin m + u32 (m_in m - m_have m)) /\
  m_tout m2 = u64 (m_tout m + u32 (m_out m - m_left m)).
Proof.
  unfold leave_fin. cbv zeta.
  destruct (leave_ok fl m); cbn -[updatewindow u32 u64];
    repeat match goal with |- context [if ?b then _ else _] => destruct b end;
    cbn -[updatewindow u32 u64]; rewrite ?ib_uw_head; repeat split.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The loop invariant                                                                             *)

Section Run.
Variables (flush: Z) (z: zfields) (L: live) (inp: list Z).

Definition ib_post (res: result) : Prop :=
  let m := r_m res in
  m_inp m = inp /\ m_aout m = zf_ao z /\
  m_sow m = Zlength (m_ow m) /\ Zlength (m_ow m) <= zf_ao z /\
  i_head (m_s m) = i_head (l_s L) /\
  (r_ret res <> Z_MEM_ERROR ->
     m_tin m = u64 (zf_tin z + m_snx m) /\ m_tout m = u64 (zf_tout z + m_sow m)).

Definition ib_J (m: mst) : Prop :=
  mwf3 m /\ m_leave m = 0 /\ m_inp m = inp /\ m_aout m = zf_ao z /\ m_tin m = zf_tin z /\
  (m_tout m + m_out m) mod 2 ^ 64 = (zf_tout z + zf_ao z) mod 2 ^ 64 /\ m_left m <= m_out m /\
  (hdr_md (m_mode m) -> Zlength (m_ow m) = 0 /\ m_out m = zf_ao z /\ m_tout m = zf_tout z) /\
  i_head (m_s m) = i_head (l_s L) /\
  (m = m_init z L inp \/ md_rng m).

Context (Hz : zf_ok z).
Context (Hinp : Zlength inp <= 2 ^ 24).

Lemma ib_u64_small x : 0 <= x <= Int64.max_unsigned -> u64 x = x.
Proof. intros H. unfold u64. apply Z.mod_small. unfold Int64.max_unsigned in H. rep_lia. Qed.

Lemma ib_mode_cases m : mwf3 m -> md_rng m \/ m_mode m = MEM \/ m_mode m = SYNC.
Proof.
  intros [W _]. pose proof (sw_mode _ (mw_s _ W)) as H. unfold md_rng, m_mode. wmodes. lia.
Qed.

Lemma ib_init_ret r m' : stepf2 flush lenfix_list distfix_list (m_init z L inp) = IRet r m' ->
  ib_J (m_init z L inp) -> ~ md_rng (m_init z L inp) -> ib_post (Res r m' None).
Proof.
  intros E J N. destruct J as (W & _).
  assert (Em: m' = m_init z L inp).
  { destruct (ib_mode_cases _ W) as [A | [A | A]]; [contradiction|..];
      unfold stepf2, step2 in E; rewrite A in E; cbn in E; inversion E; reflexivity. }
  subst m'. destruct Hz as (Z1 & Z2 & Z3 & Z4 & _).
  unfold ib_post, m_init; cbn [r_m r_ret m_inp m_aout m_sow m_ow m_s m_tin m_tout m_snx].
  rewrite Zlength_nil, !Z.add_0_r, !ib_u64_small by lia.
  fold (ib_typedo (l_s L)). rewrite ib_typedo_head.
  repeat split; auto; lia.
Qed.

Lemma ib_step_pre m : ib_J m -> md_rng m -> 0 <= m_left m <= m_out m /\ m_out m < 2 ^ 32.
Proof.
  intros (W & _ & _ & _ & _ & _ & J7 & _) _.
  pose proof (mwf_left _ (mwf3_mwf _ W)). pose proof (mw_out _ (mwf3_mwf _ W)) as O.
  unfold urange in O. rep_lia.
Qed.

Lemma ib_brk m m' : ib_J m -> stepf2 flush lenfix_list distfix_list m = IBrk m' ->
  trel m m' /\ mwf3 m' /\ i_head (m_s m') = i_head (m_s m).
Proof.
  intros J E. pose proof J as (W & Lv & _).
  destruct (ib_mode_cases m W) as [Hr | [A | A]];
    [| unfold stepf2, step2 in E; rewrite A in E; cbn in E; discriminate ..].
  destruct (ib_step_pre m J Hr) as [P1 P2].
  pose proof (stepf2_tgood flush lenfix_list distfix_list m Hr P1 P2) as G. rewrite E in G.
  pose proof (ib_stepf2_mwf3 flush m W Lv) as W'. rewrite E in W'.
  pose proof (Zlib.proof.inflate.StepHd5.stepf2_hrel flush lenfix_list distfix_list m) as H. rewrite E in H.
  split; [exact G|]. split; [exact W'|]. apply H.
Qed.

Lemma ib_mod_shift a b c M : a mod M = b mod M -> (a - c) mod M = (b - c) mod M.
Proof. intros H. rewrite Zminus_mod, H, <- Zminus_mod. reflexivity. Qed.

Lemma ib_loop m o : loop2 flush lenfix_list distfix_list m o -> ib_J m ->
  match o with
  | IRet r m' => ib_post (Res r m' None)
  | IBrk m' => forall res, inf_leave flush m' res -> ib_post res
  end.
Proof.
  intros HL. induction HL as [m r m' E | m m' E Hlv | m m' o E Hlv HL IH]; intros J.
  - pose proof J as (W & Lv & J1 & J2 & J3 & J4 & J5 & J6 & J7 & J8).
    destruct (ib_mode_cases m W) as [Hr | Hm].
    + destruct (ib_step_pre m J Hr) as [P1 P2].
      pose proof (stepf2_tgood flush lenfix_list distfix_list m Hr P1 P2) as G. rewrite E in G.
      pose proof (ib_stepf2_mwf3 flush m W Lv) as W'. rewrite E in W'.
      pose proof (Zlib.proof.inflate.StepHd5.stepf2_hrel flush lenfix_list distfix_list m) as H. rewrite E in H.
      destruct G as (Rr & Th & T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
      destruct (J6 Th) as (K1 & K2 & K3).
      pose proof (mw_nx _ (mwf3_mwf _ W')) as Nx. pose proof (mw_in _ (mwf3_mwf _ W)) as In.
      destruct Hz as (Z1 & Z2 & Z3 & Z4 & _).
      unfold ib_post; cbn [r_m r_ret].
      split; [congruence|]. split; [congruence|]. split; [exact T5|]. split; [lia|].
      split; [destruct H as (H & _); congruence|].
      intros _. rewrite T9, J3, T4, In, J1.
      replace (Zlength inp - (Zlength inp - m_nx m')) with (m_nx m') by lia.
      unfold u32; rewrite (Z.mod_small (m_nx m')) by (rewrite T1, J1 in Nx; lia).
      split; [reflexivity|]. rewrite T8, K3, T5, T6, K1, Z.add_0_r, ib_u64_small by lia. reflexivity.
    + assert (Em: m = m_init z L inp).
      { destruct J8 as [Em | Hr]; [exact Em|]. unfold md_rng in Hr. wmodes. lia. }
      subst m. eapply ib_init_ret; eauto. unfold md_rng. wmodes. lia.
  - destruct (ib_brk m m' J E) as (T & W' & Hh).
    pose proof J as (W & Lv & J1 & J2 & J3 & J4 & J5 & J6 & J7 & J8).
    destruct T as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
    pose proof (mwf_left _ (mwf3_mwf _ W')) as Lf'. pose proof (mw_out _ (mwf3_mwf _ W')) as O'.
    pose proof (mw_ow _ (mwf3_mwf _ W')) as Ow'. pose proof (mw_nx _ (mwf3_mwf _ W')) as Nx.
    pose proof (mw_in _ (mwf3_mwf _ W')) as In'.
    destruct Hz as (Z1 & Z2 & Z3 & Z4 & _).
    intros res Hres. inversion Hres; subst.
    + unfold ib_post; cbn. split; [congruence|]. split; [congruence|]. split; [reflexivity|].
      split; [lia|]. split; [congruence|]. intros N; contradiction.
    + destruct (ib_leave_fin flush m') as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8).
      unfold ib_post. rewrite F1, F2, F3, F4, F5, F6, F7, F8.
      split; [congruence|]. split; [congruence|]. split; [reflexivity|]. split; [lia|].
      split; [congruence|]. intros _.
      unfold m_have, m_left in *. rewrite In', T4, J3.
      replace (Zlength (m_inp m') - (Zlength (m_inp m') - m_nx m')) with (m_nx m') by lia.
      unfold urange in O'.
      split; [unfold u32; rewrite (Z.mod_small (m_nx m')) by (rewrite T1, J1 in Nx; lia); reflexivity|].
      specialize (T7 J5).
      unfold u32; rewrite Z.mod_small by rep_lia.
      unfold u64. replace (m_tout m' + (m_out m' - (m_aout m' - Zlength (m_ow m'))))
        with (m_tout m' + m_out m' - (m_aout m' - Zlength (m_ow m'))) by lia.
      rewrite (ib_mod_shift _ _ _ _ T6), (ib_mod_shift _ _ _ _ J4), T2, J2. f_equal. lia.
  - destruct (ib_brk m m' J E) as (T & W' & Hh).
    pose proof J as (W & Lv & J1 & J2 & J3 & J4 & J5 & J6 & J7 & J8).
    destruct T as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
    pose proof (mw_leave _ (mwf3_mwf _ W')) as Lv'.
    apply IH. unfold ib_J.
    split; [exact W'|]. split; [lia|]. split; [congruence|]. split; [congruence|]. split; [congruence|].
    split; [congruence|]. split; [auto|].
    split; [intros Hd; destruct (T8 Hd) as (K1 & K2 & K3 & K4); destruct (J6 K1) as (L1 & L2 & L3);
            split; [congruence|]; split; congruence|].
    split; [congruence|]. right; exact T9.
Qed.

End Run.

Lemma ib_J_init z L inp : live_ok L -> zf_ok z -> bytes_ok inp -> Zlength inp <= 2 ^ 24 ->
  0 <= zf_ao z <= 2 ^ 20 -> ib_J z L inp (m_init z L inp).
Proof.
  intros HL Hz Hb Hn Ha.
  assert (W: mwf3 (m_init z L inp)) by (apply ib_m_init_mwf3; auto; rep_lia).
  unfold ib_J, m_left, m_init; cbn [m_leave m_inp m_aout m_tin m_tout m_out m_ow m_s].
  rewrite Zlength_nil. fold (ib_typedo (l_s L)). rewrite ib_typedo_head.
  split; [exact W|]. repeat split; try reflexivity; try lia. left; reflexivity.
Qed.

Lemma ib_run : ib_run_stmt.
Proof.
  intros flush z L inp res HL Hz Hb Hn Ha (o & Hlo & Hres).
  pose proof (ib_loop flush z L inp Hz Hn _ _ Hlo (ib_J_init z L inp HL Hz Hb Hn Ha)) as H.
  destruct o as [m'|r m'].
  - exact (H res Hres).
  - subst res. exact H.
Qed.
