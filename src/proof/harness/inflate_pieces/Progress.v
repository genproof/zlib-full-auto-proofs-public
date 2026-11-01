(* The laws rj_any_input and api_untouched_output (round 4): zlib.h, inflate() "returns Z_OK if some progress has
   been made (more input processed or more output produced)".  A call offered neither input nor output space
   therefore does not return Z_OK (it moves nothing: Facts.pf_inflate).

   In the model, inflate() returns Z_OK only through inf_leave (leave_fin): there the code Z_OK becomes Z_BUF_ERROR
   when the call consumed no byte (in - have = 0) and `out - left` is 0.  `out` is avail_out at the start of the
   call, or `left` after CHECK, so left <= out <= avail_out: out - left > 0 means bytes were written.  The other
   exits (DICT's Z_NEED_DICT, a failed window allocation's Z_MEM_ERROR) are not Z_OK.

   pieces_progress P states it for the stream invariant P of Facts.v; it holds of Theory.pinv
   (pinv_progress). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Export Zlib.proof.harness.inflate_pieces.Facts.
Require Import Zlib.proof.harness.inflate_pieces.Theory.
Require Import Zlib.proof.harness.inflate_buffers.IBStepKit.
Require Zlib.proof.harness.inflate_buffers.IBRun.
Require Zlib.proof.harness.inflate_codes.TheoryRun.
Require Import Zlib.proof.inflate_api.StepInv5Kit.
Import ListNotations.
Local Open Scope Z_scope.

(* inflate(strm, flush) offered the bytes inp and aout bytes of output space returned Z_OK: it consumed input
   (avail_in' < |inp|) or wrote output (avail_out' < aout) *)
Definition pieces_progress (P: zfields -> live -> Prop) : Prop :=
  forall z L strmp flush ib inp o aout r z' st' ow,
    P z L -> live_ok L -> zf_ok z -> strmp <> nullval -> Int.min_signed <= flush <= Int.max_signed ->
    ib <> InNull -> in_ok ib inp -> out_ok o aout ->
    Zlength inp <= Int.max_unsigned -> aout <= Int.max_unsigned ->
    inflate_rel flush strmp (offer_z z (in_ptr ib 0) (Zlength inp) (out_ptr o 0) aout) (Some L) ib inp (Some o)
      r z' st' ow ->
    r = Z_OK ->
    zf_ai z' < Zlength inp \/ zf_ao z' < aout.

(* the pass of HEAD changes neither `out` nor the size of the output space *)
Lemma pp_head_out m :
  match c_HEAD2 m with IBrk m' => m_out m' = m_out m /\ m_aout m' = m_aout m | IRet _ _ => True end.
Proof.
  unfold c_HEAD2. hsplit; hcbn; autorewrite with wi; auto.
Qed.

Section Run.
Variables (flush: Z) (z: zfields) (L: live) (inp: list Z).
Context (SW : stepf2_mwf3W_stmt).

(* one pass keeps out <= avail_out: `out` is set only by CHECK, to `left` (StepInv5Kit.stepf2_wgood) *)
Lemma pp_step_out m m' : pJ z L inp m -> m_out m <= m_aout m ->
  stepf2 flush lenfix_list distfix_list m = IBrk m' -> m_out m' <= m_aout m'.
Proof.
  intros J O E.
  destruct (Z.eq_dec (m_mode m) HEAD) as [Hh|Hh].
  - pose proof (pp_head_out m) as K.
    replace (stepf2 flush lenfix_list distfix_list m) with (c_HEAD2 m) in E
      by (unfold stepf2, step2; rewrite Hh; reflexivity).
    rewrite E in K. lia.
  - pose proof (stepf2_wgood flush lenfix_list distfix_list m Hh) as W. rewrite E in W.
    destruct W as (_ & _ & A & _ & B & _). lia.
Qed.

(* the switch loop of one call: a return from inside the loop is DICT's Z_NEED_DICT; at the exit
   left <= out <= avail_out, with the input and the output space of the call *)
Lemma pp_loop m o : loop2 flush lenfix_list distfix_list m o -> pJ z L inp m -> m_out m <= m_aout m ->
  match o with
  | IRet r _ => r <> Z_OK
  | IBrk m' => m_left m' <= m_out m' <= m_aout m' /\ mwfW m' /\ m_inp m' = inp /\ m_aout m' = zf_ao z
  end.
Proof.
  intros HL. induction HL as [m r m' E | m m' E Hlv | m m' o E Hlv HL IH]; intros J O.
  - pose proof J as (W & Lv & J1 & J2 & J3 & J4 & J5 & J6 & J7 & J8 & Hr & Rt).
    destruct (pc_step_pre z L inp m J) as [P1 P2].
    pose proof (stepf2_tgood flush lenfix_list distfix_list m Hr P1 P2) as G. rewrite E in G.
    destruct G as [-> _]. intro F. inversion F.
  - destruct (pc_brk flush z L inp SW m m' J E) as (T & W' & _).
    pose proof J as (W & Lv & J1 & J2 & J3 & J4 & J5 & J6 & J7 & J8 & Hr & Rt).
    pose proof (pp_step_out m m' J O E) as O'.
    destruct T as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
    split; [split; [apply T7; exact J5 | exact O'] |].
    split; [exact (proj1 W') |]. split; congruence.
  - pose proof (pp_step_out m m' J O E) as O'.
    destruct (pc_brk flush z L inp SW m m' J E) as (T & W' & Hh & Hw & Rk).
    pose proof J as (W & Lv & J1 & J2 & J3 & J4 & J5 & J6 & J7 & J8 & Hr & Rt).
    destruct T as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
    pose proof (mwW_leave _ (proj1 W')) as Lv'.
    apply IH; [ | exact O'].
    unfold pJ.
    split; [exact W'|]. split; [lia|]. split; [congruence|]. split; [congruence|]. split; [congruence|].
    split; [congruence|]. split; [auto|].
    split; [intros Hd; destruct (T8 Hd) as (K1 & K2 & K3 & K4); destruct (J6 K1) as (L1 & L2 & L3);
            split; [congruence|]; split; congruence|].
    split; [congruence|]. split; [congruence|]. split; [exact T9|]. apply Rk.
Qed.

End Run.

Lemma pinv_progress : stepf2_mwf3W_stmt -> pieces_progress pinv.
Proof.
  intros SW z L strmp flush ib inp o aout r z' st' ow PI HL Hz Hs Hf Hib Hin Hout Hlen Haout Hrel Hr.
  destruct Hrel as [(Bad & _) | (NB & L0 & o0 & res & winp & Est & Eob & Run & Snx & Er & Eow & Ez & _ & Est')].
  - exfalso. unfold inflate_bad, is_live in Bad.
    destruct (eq_dec strmp nullval); [contradiction|].
    destruct Bad as [Bad | [Bad | (Bad & _)]]; discriminate || contradiction.
  - inversion Est; subst L0. inversion Eob; subst o0.
    assert (Ha0: 0 <= aout) by (destruct o; unfold out_ok in Hout; tauto).
    assert (Hb: bytes_ok inp) by (destruct ib; [contradiction | unfold in_ok in Hin; tauto]).
    set (z0 := offer_z z (in_ptr ib 0) (Zlength inp) (out_ptr o 0) aout) in *.
    assert (Hz0: zf_ok z0).
    { destruct Hz as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6). pose proof (Zlength_nonneg inp).
      unfold zf_ok, z0, offer_z; cbn. repeat split; rep_lia. }
    destruct Run as (ol & Hlo & Hres).
    assert (O0: m_out (m_init z0 L inp) <= m_aout (m_init z0 L inp)) by (unfold m_init; cbn; lia).
    pose proof (pp_loop flush z0 L inp SW _ _ Hlo (pc_J_init z0 L inp HL Hz0 Hb Hlen PI) O0) as H.
    subst r z'. unfold z_after; cbn [zf_ai zf_ao].
    destruct ol as [m'|r' m'].
    + destruct H as ((O1 & O2) & W' & I' & A').
      assert (A'': m_aout m' = aout) by (rewrite A'; reflexivity).
      inversion Hres as [_ _ | ]; subst res; cbn [r_ret r_m] in *.
      { exfalso. inversion Hr. }
      destruct (IBRun.ib_leave_fin flush m') as (F1 & F2 & F3 & F4 & F5 & _).
      destruct (Zlib.proof.harness.inflate_codes.TheoryRun.rn_leave_fin flush m') as (R1 & _).
      rewrite F1, F2, F4, F5. rewrite R1 in Hr. unfold Zlib.proof.harness.inflate_codes.TheoryRun.rn_bufret in Hr.
      pose proof (mwW_nx _ W') as Nx. pose proof (mwW_in _ W') as In. pose proof (mwW_ow _ W') as [Ow _].
      pose proof (mwW_aout _ W') as Ao.
      unfold m_have, m_left in *. rewrite In, I' in Hr. rewrite I' in Nx.
      replace (Zlength inp - (Zlength inp - m_nx m')) with (m_nx m') in Hr by lia.
      unfold u32 in Hr. rewrite (Z.mod_small (m_nx m')) in Hr by rep_lia.
      rewrite (Z.mod_small (m_out m' - (m_aout m' - Zlength (m_ow m')))) in Hr by rep_lia.
      rewrite I'.
      destruct (Z.eq_dec (m_nx m') 0) as [N0|N0]; [|left; lia].
      right. destruct (Z.eq_dec (m_out m' - (m_aout m' - Zlength (m_ow m'))) 0) as [E0|E0]; [|lia].
      exfalso. rewrite N0, E0 in Hr. cbn [Z.eqb andb orb] in Hr.
      destruct (m_ret m' =? Z_OK) eqn:ER; cbn in Hr; [inversion Hr | apply Z.eqb_neq in ER; contradiction].
    + subst res. cbn [r_ret] in Hr. contradiction.
Qed.

(* the invariant of the three laws with both kinds of facts *)
Lemma pieces_theory4 : stepf2_mwf3W_stmt -> exists P, pieces_facts P /\ pieces_progress P.
Proof. intros SW. exists pinv. split; [exact (pinv_facts SW) | exact (pinv_progress SW)]. Qed.
