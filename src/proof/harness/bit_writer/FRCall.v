(* The fixed-block run theory (FRDefs.v): one call, from the passes and the exit: the loop head invariant fr_K at
   Spec5.m_init, the switch by mode, the loop (Model2.loop2) to the exit fr_E. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.bit_writer.FRDefs.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* The modes of fr_at                                                                             *)

(* fr_at only knows ten modes *)
Lemma fr_at_mode (C: frc) (s: istate) (c hold bits: Z) (out: list Z) :
  fr_at C s c hold bits out ->
  i_mode s = BAD \/ i_mode s = HEAD \/ i_mode s = TYPEDO \/ i_mode s = LEN_ \/ i_mode s = LEN \/
  i_mode s = LIT \/ i_mode s = LENEXT \/ i_mode s = DIST \/ i_mode s = DISTEXT \/ i_mode s = MATCH.
Proof.
  unfold fr_at. cbv zeta.
  intros [[A _]|[_ [A|[A|[_ [A|[A|[A|[A|[A|A]]]]]]]]]]; tauto.
Qed.

(* entering LEN from LEN_ keeps the place in the input *)
Lemma fr_at_len_ (C: frc) (s: istate) (c hold bits: Z) (out: list Z) :
  i_mode s = LEN_ -> fr_at C s c hold bits out -> fr_at C (set_i_mode s LEN) c hold bits out.
Proof.
  intros E. unfold fr_at, fr_fixed. cbv zeta. cbn [i_mode set_i_mode i_lencode i_lenbits i_distcode i_distbits].
  rewrite E.
  intros [[A _]|[H [A|[A|[F [A|[A|[A|[A|[A|A]]]]]]]]]];
    try (exfalso; lazymatch type of A with _ /\ _ => destruct A as [A _] | _ => idtac end; unfold LEN_, BAD, HEAD, TYPEDO, LIT, LENEXT, DIST, DISTEXT, MATCH in *;
         lia).
  - right. split; [exact H|]. right; right. split; [exact F|]. left.
    destruct A as (_ & B & R). split; [right; reflexivity|]. split; [exact B | exact R].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The loop head at the start of the call                                                         *)

Lemma fr_init_K (C: frc) (pos: Z) (ob: list Z) (L: live) (z: zfields) (inp: list Z) :
  fr_inv C pos ob (l_s L) -> zf_ok z -> fr_K C pos inp ob L z (m_init z L inp).
Proof.
  intros [A W] Z.
  assert (T: (i_mode (l_s L) =? Zlib.proof.inflate.Model.TYPE) = false).
  { apply Z.eqb_neq. pose proof (fr_at_mode _ _ _ _ _ _ A) as M.
    unfold Zlib.proof.inflate.Model.TYPE, LEN_, BAD, HEAD, TYPEDO, LEN, LIT, LENEXT, DIST, DISTEXT, MATCH in *.
    lia. }
  unfold m_init. cbv zeta. rewrite T.
  destruct Z as (_ & Zo & _).
  constructor; [constructor|..]; cbn [m_s m_inp m_in m_aout m_out m_nx m_ow m_hold m_bits m_leave m_ret];
    auto.
  - pose proof (Zlength_nonneg inp). lia.
  - rewrite Zlength_nil. lia.
  - repeat split.
  - rewrite Z.add_0_r, app_nil_r. exact A.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The switch                                                                                     *)

Section Switch.
Variables (flush: Z) (m: mst).
Let fx := lenfix_list.
Let dx := distfix_list.

Lemma fr_sw_head : m_mode m = HEAD -> stepf2 flush fx dx m = c_HEAD2 m.
Proof. intros E. unfold stepf2, step2. rewrite E. reflexivity. Qed.
Lemma fr_sw_typedo : m_mode m = TYPEDO -> stepf2 flush fx dx m = c_TYPEDO flush m.
Proof. intros E. unfold stepf2, step2. rewrite E. reflexivity. Qed.
Lemma fr_sw_len_ : m_mode m = LEN_ -> stepf2 flush fx dx m = c_LEN fx dx (fast fx dx) (set_mode m LEN).
Proof. intros E. unfold stepf2, step2. rewrite E. reflexivity. Qed.
Lemma fr_sw_len : m_mode m = LEN -> stepf2 flush fx dx m = c_LEN fx dx (fast fx dx) m.
Proof. intros E. unfold stepf2, step2. rewrite E. reflexivity. Qed.
Lemma fr_sw_lit : m_mode m = LIT -> stepf2 flush fx dx m = c_LIT m.
Proof. intros E. unfold stepf2, step2. rewrite E. reflexivity. Qed.
Lemma fr_sw_lenext : m_mode m = LENEXT -> stepf2 flush fx dx m = c_LENEXT fx dx m.
Proof. intros E. unfold stepf2, step2. rewrite E. reflexivity. Qed.
Lemma fr_sw_dist : m_mode m = DIST -> stepf2 flush fx dx m = c_DIST fx dx m.
Proof. intros E. unfold stepf2, step2. rewrite E. reflexivity. Qed.
Lemma fr_sw_distext : m_mode m = DISTEXT -> stepf2 flush fx dx m = c_DISTEXT m.
Proof. intros E. unfold stepf2, step2. rewrite E. reflexivity. Qed.
Lemma fr_sw_match : m_mode m = MATCH -> stepf2 flush fx dx m = c_MATCH m.
Proof. intros E. unfold stepf2, step2. rewrite E. reflexivity. Qed.
Lemma fr_sw_bad : m_mode m = BAD -> stepf2 flush fx dx m = c_BAD m.
Proof. intros E. unfold stepf2, step2. rewrite E. reflexivity. Qed.

End Switch.

(* LEN_ only sets the mode to LEN: the loop head invariant holds there *)
Lemma fr_K_len_ (C: frc) (pos: Z) (inp ob: list Z) (L: live) (z: zfields) (m: mst) :
  m_mode m = LEN_ -> fr_K C pos inp ob L z m -> fr_K C pos inp ob L z (set_mode m LEN).
Proof.
  intros E [[I1 I2 I3 I4 I5 I6 I7 I8 I9] K1 K2].
  unfold set_mode, upd_s.
  constructor; [constructor|..];
    cbn [m_s m_inp m_in m_aout m_out m_nx m_ow m_hold m_bits m_leave m_ret set_m_s]; auto.
  all: first [ apply fr_at_len_; auto
             | unfold fr_wsame in *; cbn [i_wsize i_whave i_wnext i_win i_wdata i_wbits i_sane set_i_mode]; exact I7 ].
Qed.

(* one pass of the switch from a loop head *)
Lemma fr_step : fr_passes ->
  forall C pos inp ob L z flush m,
    fr_ctx C pos inp L z -> fr_K C pos inp ob L z m ->
    fr_res C pos inp ob L z flush (stepf2 flush lenfix_list distfix_list m).
Proof.
  intros [[HE TD] [[LN LT] [LX [DS [DX [MA BA]]]]]] C pos inp ob L z flush m X K.
  pose proof (fr_at_mode _ _ _ _ _ _ (frm_at _ _ _ _ _ _ _ (frk_m _ _ _ _ _ _ _ K))) as M.
  fold (m_mode m) in M.
  destruct M as [M|[M|[M|[M|[M|[M|[M|[M|[M|M]]]]]]]]].
  - rewrite fr_sw_bad by exact M. exact (BA C pos inp ob L z flush m X K M).
  - rewrite fr_sw_head by exact M. exact (HE C pos inp ob L z flush m X K M).
  - rewrite fr_sw_typedo by exact M. exact (TD C pos inp ob L z flush m X K M).
  - rewrite fr_sw_len_ by exact M. apply (LN C pos inp ob L z flush (set_mode m LEN) X).
    + exact (fr_K_len_ _ _ _ _ _ _ _ M K).
    + reflexivity.
  - rewrite fr_sw_len by exact M. exact (LN C pos inp ob L z flush m X K M).
  - rewrite fr_sw_lit by exact M. exact (LT C pos inp ob L z flush m X K M).
  - rewrite fr_sw_lenext by exact M. exact (LX C pos inp ob L z flush m X K M).
  - rewrite fr_sw_dist by exact M. exact (DS C pos inp ob L z flush m X K M).
  - rewrite fr_sw_distext by exact M. exact (DX C pos inp ob L z flush m X K M).
  - rewrite fr_sw_match by exact M. exact (MA C pos inp ob L z flush m X K M).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The loop                                                                                       *)

(* from a loop head, the loop is left (never a return) at fr_E *)
Lemma fr_loop : fr_passes ->
  forall C pos inp ob L z flush m o,
    fr_ctx C pos inp L z -> loop2 flush lenfix_list distfix_list m o -> fr_K C pos inp ob L z m ->
    exists m', o = IBrk m' /\ fr_E C pos inp ob L z flush m'.
Proof.
  intros P C pos inp ob L z flush m o X LP.
  induction LP as [m r m' E | m m' E L1 | m m' o E L1 LP IH]; intros K;
    pose proof (fr_step P C pos inp ob L z flush m X K) as R; rewrite E in R; cbn [fr_res] in R.
  - contradiction.
  - destruct R as [K'|E']; [|eauto].
    exfalso. pose proof (frk_leave _ _ _ _ _ _ _ K'). lia.
  - destruct R as [K'|E']; [auto|].
    exfalso. pose proof (fre_leave _ _ _ _ _ _ _ _ E'). lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* One call                                                                                       *)

Lemma fr_call_ok : fr_passes -> fr_leave_stmt -> fr_call_stmt.
Proof.
  intros P LV C pos ob L z inp flush res Ok I Lv Zo P0 P1 P2 P3 _ [o [LP R]].
  assert (X: fr_ctx C pos inp L z) by (unfold fr_ctx; tauto).
  destruct (fr_loop P C pos inp ob L z flush _ o X LP (fr_init_K C pos ob L z inp I Zo)) as [m' [-> E]].
  exact (LV C pos inp ob L z flush m' res X E R).
Qed.
