(* One inflate() call of uncompress2_z's loop keeps the stream live, for calls of up to 2^32 - 1 bytes of input
   and of output space.

   The decode theory (rfc1951/Decode7.v, decode_call7_stmt) takes the stream before a call as a live state
   (Spec5.live_ok) with the fields of the application (Spec5.zf_ok).  In the model of uncompr.c
   (UModel.m_next) the stream between two calls is the machine the previous call left; [uw_mlive m] says that
   it is such a live stream: its state and header are those of a live state, the state satisfies InvW.swfW
   (what inflate() needs in case EXTRA for calls of up to 2^32 - 1 bytes: SpecW.inflate_specW), no gzip header
   is requested (i_head false: uncompress2 never calls inflateGetHeader), and the totals and the check value
   are 64-bit values.  [uw_live]: a call that does not run out of memory keeps it, and writes at most the
   space offered (round 1's UALive.ua_live, for calls of up to 2^31 - 1 bytes). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Export Zlib.proof.inflate_api.Spec5.
Require Export Zlib.proof.inflate.InvW.
Require Import Zlib.proof.uncompr.UModel.
Require Import Zlib.proof.uncompr.URunFrame.
Require Import Zlib.proof.inflate_api.Body5Parts.
Require Import Zlib.proof.za.inflate_api.Body5Parts.
Require Import Zlib.proof.za.inflate_api.Body5Conv.
Require Import Zlib.proof.za.inflate_api.Body5Fin.
Require Import Zlib.proof.za.inflate_api.Body5StepInv.
Require Import Zlib.proof.za.inflate_api.Body5StepHdr.
Require Import Zlib.proof.za.inflate_api.BodyKitZ.
Require Import Zlib.proof.za.inflate.StepZ.
Require Import Zlib.proof.inflate.StepW.
Import ListNotations.
Local Open Scope Z_scope.

Definition uw_mlive (m: mst) : Prop :=
  (exists L, live_ok L /\ l_s L = m_s m /\ l_h L = m_h m) /\ swfW (m_s m) /\ i_head (m_s m) = false /\
  lrange (m_tin m) /\ lrange (m_tout m) /\ lrange (m_adler m).

(* The invariant of inflate()'s loop head along one call (as in inflate()'s body proof,
   za/inflate_api/Body5_inflate.v): the wide machine invariant, the output and window facts, no header. *)
Definition uw_linv (m: mst) : Prop :=
  mwf3_za m /\ out_inv m /\ win_inv5 (m_s m) /\ i_head (m_s m) = false.

(* a return from inside the switch: what the end of the call needs of the returned machine *)
Definition uw_rinv (m: mst) : Prop :=
  mwf3_za m /\ win_inv5 (m_s m) /\ i_head (m_s m) = false /\ swfW (m_s m).

Lemma uw_pass: forall flush m, uw_linv m -> m_leave m = 0 ->
  match stepf2 flush lenfix_list distfix_list m with
  | IBrk m' => uw_linv m'
  | IRet _ m' => uw_rinv m'
  end.
Proof.
  intros flush m (W & O & V & H) L.
  pose proof (za_step_proof stepf2_mwf3W flush m W L) as HW.
  pose proof (stepf_inv5_za flush m W L O V) as HV.
  pose proof (stepf2_hdr_za flush m W L) as HH.
  pose proof (stepf2_ret_swfW flush lenfix_list distfix_list m) as HR.
  destruct (stepf2 flush lenfix_list distfix_list m) as [m'|r m'].
  - destruct HV as (O' & _ & V'). destruct HH as ((E & _) & _).
    split; [exact HW|]. split; [exact O'|]. split; [exact V'|]. congruence.
  - destruct HV as (_ & V'). destruct HH as ((E & _) & _).
    split; [exact HW|]. split; [exact V'|]. split; [congruence|]. exact (HR r m' eq_refl).
Qed.

Lemma uw_loop: forall flush m o, loop2 flush lenfix_list distfix_list m o ->
  uw_linv m -> m_leave m = 0 ->
  match o with
  | IBrk m' => uw_linv m'
  | IRet _ m' => uw_rinv m'
  end.
Proof.
  induction 1 as [m r m' E | m m' E L1 | m m' o E L1 Hl IH]; intros HI L0;
    pose proof (uw_pass flush m HI L0) as P; rewrite E in P.
  - exact P.
  - exact P.
  - apply IH; [exact P|]. destruct P as (W & _).
    pose proof (mw_leave_za _ (mwf3_mwf_za _ W)). lia.
Qed.

(* outside the modes HEAD..BAD (MEM, SYNC) inflate() returns at once, the machine unchanged *)
Lemma stepf2_novmode: forall flush m, ~ vmode (i_mode (m_s m)) ->
  exists r, stepf2 flush lenfix_list distfix_list m = IRet r m.
Proof.
  intros flush m NV. unfold stepf2, step2. cbv zeta.
  repeat match goal with
  | |- exists r, (if ?c then _ else _) = _ =>
      let EC := fresh "EC" in
      destruct c eqn:EC; [apply Z.eqb_eq in EC; first [eexists; reflexivity | exfalso; apply NV; unfold vmode, m_mode in *; mode_consts; lia] |]
  end.
  eexists; reflexivity.
Qed.

Lemma loop2_ret_now: forall flush m o r, loop2 flush lenfix_list distfix_list m o ->
  stepf2 flush lenfix_list distfix_list m = IRet r m -> o = IRet r m.
Proof.
  intros flush m o r LP E. destruct LP as [m1 r1 m1' E1 | m1 m1' E1 _ | m1 m1' o1 E1 _ _];
    rewrite E in E1; congruence.
Qed.

(* the live part after the call *)
Lemma uw_live_fin: forall (L: live) m, live_ok L -> fin_ok5_za m -> i_head (m_s m) = false ->
  live_ok (Live (l_sp L) (l_winp L) (m_s m) (m_h m) (l_headp L) (l_hsh L) (l_xb L) (l_nb L) (l_cb L)).
Proof.
  intros L m (LP & _ & _ & _ & _ & LW & _) (A & B & C & D & [W1 W2] & _) H.
  unfold live_ok; simpl. rewrite H.
  refine (conj LP (conj A (conj B (conj C (conj D (conj LW (conj W1 (conj _ W2)))))))). discriminate.
Qed.

Lemma uw_live : forall flush m inp aout res,
  uw_mlive m -> Zlength inp <= Int.max_unsigned -> bytes_ok inp -> 0 <= aout <= Int.max_unsigned ->
  run2 flush lenfix_list distfix_list (m_next m inp aout) res -> r_ret res <> Z_MEM_ERROR ->
  uw_mlive (r_m res) /\ Zlength (m_ow (r_m res)) <= aout.
Proof.
  intros flush m inp aout res ((L & LOK & ES & EH) & SW & HD & T1 & T2 & T3) IL BI AO RUN NM.
  set (z := ZF nullval (Zlength inp) (m_tin m) nullval aout (m_tout m) (m_msg m) 0 (m_adler m) nullval).
  assert (EN: m_next m inp aout = m_init z L inp).
  { unfold m_next, m_init, z. cbn [zf_ao zf_adler zf_msg zf_tin zf_tout]. rewrite ES, EH. reflexivity. }
  assert (ZOK: zf_ok z).
  { unfold zf_ok, z, lrange in *; cbn [zf_ai zf_ao zf_tin zf_tout zf_dt zf_adler].
    pose proof (Zlength_nonneg inp). rep_lia. }
  rewrite EN in RUN. set (m0 := m_init z L inp) in RUN.
  assert (MW: mwf3_za m0) by (apply m_init_mwf3_za; auto; rewrite ES; exact SW).
  assert (OI: out_inv m0) by (apply m_init_out_inv; unfold z; cbn [zf_ao]; lia).
  assert (WI0: win_inv5 (m_s m0)) by (unfold m0; rewrite m_init_s; apply s_typedo_win_inv5, live_win_inv5, LOK).
  assert (HD0: i_head (m_s m0) = false).
  { unfold m0. rewrite m_init_s. unfold s_typedo. rewrite ES.
    destruct (i_mode (m_s m) =? Zlib.proof.inflate.Model.TYPE); exact HD. }
  pose proof RUN as (out & LP & HO).
  pose proof (uw_loop flush m0 out LP (conj MW (conj OI (conj WI0 HD0))) eq_refl) as HL.
  assert (FIN: swfW (m_s (r_m res)) /\ fin_ok5_za (r_m res) /\ i_head (m_s (r_m res)) = false).
  { destruct out as [m1 | r1 m1].
    - destruct HL as (W & O & V & H).
      destruct (leave_fin5_za flush m1 res W O V HO) as (S & F & _ & _ & EHd & _).
      split; [exact S|]. split; [exact F|]. congruence.
    - destruct HL as (W & V & H & S). subst res. cbn [r_m].
      split; [exact S|]. split; [apply mwf3_fin_ok5_za; assumption | exact H]. }
  destruct FIN as (SWr & FO & HDr).
  pose proof FO as (_ & _ & _ & _ & _ & _ & _ & SOW & _ & LT1 & LT2 & LT3).
  split.
  - split; [|split; [exact SWr | split; [exact HDr | auto]]].
    eexists; split; [apply uw_live_fin; eassumption | split; reflexivity].
  - assert (AO0: m_aout m0 = aout) by reflexivity.
    destruct (Z_le_gt_dec HEAD (i_mode (m_s m0))) as [V1|V1];
      [destruct (Z_le_gt_dec (i_mode (m_s m0)) BAD) as [V2|V2]|].
    + destruct (run2_frame flush _ _ m0 res (conj V1 V2) RUN) as (_ & FA & FS & _). lia.
    + destruct (stepf2_novmode flush m0 ltac:(unfold vmode; lia)) as (r & E).
      rewrite (loop2_ret_now flush m0 out r LP E) in HO. rewrite HO.
      cbn [r_m]. unfold m0, m_init. cbn [m_ow]. rewrite Zlength_nil. lia.
    + destruct (stepf2_novmode flush m0 ltac:(unfold vmode; lia)) as (r & E).
      rewrite (loop2_ret_now flush m0 out r LP E) in HO. rewrite HO.
      cbn [r_m]. unfold m0, m_init. cbn [m_ow]. rewrite Zlength_nil. lia.
Qed.
