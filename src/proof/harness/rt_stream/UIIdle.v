(* inflate() offered neither input nor output space (avail_in = 0, avail_out = 0): the call does not return
   Z_OK, produces nothing, and (unless it fails with Z_MEM_ERROR) consumes nothing and keeps total_in and
   total_out.

   The harnesses of round 4 assert this after every call made with zero-length buffers (rt_stream,
   rt_stream_trailing, rt_session, rj_any_input, api_inflate_any).  The statement is the model's: a call
   Model2.run2 from Spec5.m_init, from a state between calls of the decoder proper (inflate_pieces' pinv: no
   gz_header, a mode HEAD .. BAD, swfW), for any flush.

   Why: zlib's inflate() returns Z_BUF_ERROR when it consumed and produced nothing and would return Z_OK
   (inflate.c: `if (((in == 0 && out == 0) || flush == Z_FINISH) && ret == Z_OK) ret = Z_BUF_ERROR;`,
   Model.leave_fin); its other returns are not Z_OK.  The count `out` it tests is `out - left` of the last
   CHECK (which sets `out = left`) or of the call's start (`out = avail_out`): the loop keeps
   out <= avail_out (ui_idle_loop), so with no output space out = left = 0. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.inflate_pieces.Theory.
Require Import Zlib.proof.inflate.StepW.
Require Zlib.proof.inflate_api.StepInv5Kit.
Require Zlib.proof.harness.inflate_codes.TheoryRun.
Require Zlib.proof.harness.res_inflate.Model.
Import ListNotations.
Local Open Scope Z_scope.

(* one pass of the switch keeps avail_out at the call's start and sets `out` only to a value <= it *)
Lemma ui_idle_step flush m :
  match stepf2 flush lenfix_list distfix_list m with
  | IBrk m' => m_aout m' = m_aout m /\ (m_out m' = m_out m \/ m_out m' <= m_aout m')
  | IRet _ m' => m_aout m' = m_aout m /\ (m_out m' = m_out m \/ m_out m' <= m_aout m')
  end.
Proof.
  destruct (Z.eq_dec (m_mode m) HEAD) as [Hh|Hh].
  - replace (stepf2 flush lenfix_list distfix_list m) with (c_HEAD2 m)
      by (unfold stepf2, step2; rewrite Hh; reflexivity).
    unfold c_HEAD2.
    destruct (i_wrap (m_s m) =? 0); [auto|].
    rewrite <- (StepInv5Kit.needbits_aout 16 m), <- (StepInv5Kit.needbits_out 16 m).
    generalize (needbits 16 m); intros m1.
    repeat match goal with |- context [if ?c then _ else _] => destruct c end; auto.
  - pose proof (StepInv5Kit.stepf2_wgood flush lenfix_list distfix_list m Hh) as G.
    destruct (stepf2 flush lenfix_list distfix_list m);
      destruct G as (_ & _ & A & _ & [O|[O _]] & _); auto.
Qed.

(* the loop keeps mwf3W and out <= avail_out *)
Lemma ui_idle_loop flush m o : loop2 flush lenfix_list distfix_list m o ->
  mwf3W m -> m_leave m = 0 -> m_out m <= m_aout m ->
  match o with
  | IBrk m' => mwf3W m' /\ m_out m' <= m_aout m'
  | IRet _ m' => mwf3W m' /\ m_out m' <= m_aout m'
  end.
Proof.
  intros HL. induction HL as [m r m' E | m m' E Hlv | m m' o E Hlv HL IH]; intros W L0 O0;
    pose proof (stepf2_mwf3W flush m W L0) as W'; pose proof (ui_idle_step flush m) as S;
    rewrite E in W', S; destruct S as [A [S|S]].
  all: try (split; [exact W' | lia]).
  all: apply IH; [exact W' | pose proof (mwW_leave _ (proj1 W')); lia | lia].
Qed.

(* any call from such a state: inflate_pieces' ppost (the counters, the mode HEAD .. BAD, swfW, the output
   within the space offered) *)
Lemma ui_call_ppost flush z L inp res :
  pinv z L -> live_ok L -> zf_ok z -> Zlength inp < 2 ^ 32 -> bytes_ok inp ->
  run2 flush lenfix_list distfix_list (m_init z L inp) res -> ppost z L inp res.
Proof.
  intros PI HL Hz Hn Hb (o & Hlo & Hres).
  assert (Hmx: Zlength inp <= Int.max_unsigned) by rep_lia.
  pose proof (pc_loop flush z L inp stepf2_mwf3W Hz Hmx _ _ Hlo (pc_J_init z L inp HL Hz Hb Hmx PI)) as PP.
  destruct o as [m'|r' m']; [exact (PP res Hres) | subst res; exact PP].
Qed.

(* the call offered no input and no output space *)
Theorem ui_idle_call flush z L inp res :
  pinv z L -> live_ok L -> zf_ok z -> Zlength inp = 0 -> zf_ao z = 0 ->
  run2 flush lenfix_list distfix_list (m_init z L inp) res ->
  r_ret res <> Z_OK /\ m_ow (r_m res) = [] /\
  (r_ret res <> Z_MEM_ERROR -> m_tin (r_m res) = zf_tin z /\ m_tout (r_m res) = zf_tout z).
Proof.
  intros PI HL Hz Hn Ha Run.
  assert (Ei: inp = []) by (apply Zlength_nil_inv; exact Hn). subst inp.
  assert (Hb: bytes_ok (@nil Z)) by constructor.
  assert (Hmx: Zlength (@nil Z) <= Int.max_unsigned) by (rewrite Zlength_nil; rep_lia).
  pose proof (pc_J_init z L [] HL Hz Hb Hmx PI) as J.
  destruct Run as (o & Hlo & Hres).
  pose proof (pc_loop flush z L [] stepf2_mwf3W Hz Hmx _ _ Hlo J) as PP.
  pose proof (Zlib.proof.harness.res_inflate.Model.loop_ret flush z L [] stepf2_mwf3W _ _ Hlo J) as RT.
  assert (I0: mwf3W (m_init z L []) /\ m_out (m_init z L []) <= m_aout (m_init z L [])).
  { split; [exact (proj1 J) | cbn; lia]. }
  pose proof (ui_idle_loop flush _ _ Hlo (proj1 I0) eq_refl (proj2 I0)) as LP.
  assert (Pp: ppost z L [] res).
  { destruct o as [m'|r' m']; [exact (PP res Hres) | subst res; exact PP]. }
  destruct Pp as (Q1 & Q2 & Q3 & Q4 & _ & _ & Q7).
  rewrite Ha in Q2, Q4.
  assert (Ow: m_ow (r_m res) = []) by (apply Zlength_nil_inv; pose proof (Zlength_nonneg (m_ow (r_m res))); lia).
  destruct Hz as (Z1 & Z2 & Z3 & Z4 & _).
  (* nothing consumed: the final machine's next-input index is 0 *)
  assert (Ret: r_ret res <> Z_OK /\ (r_ret res <> Z_MEM_ERROR -> m_snx (r_m res) = 0)).
  { destruct o as [m'|r' m'].
    - destruct LP as (W' & O').
      inversion Hres; subst.
      + split; [cbn; discriminate | intros N; exfalso; apply N; reflexivity].
      + destruct (Zlib.proof.harness.inflate_codes.TheoryRun.rn_leave_fin flush m')
          as (R1 & R2 & R3 & R4 & R5 & _ & R7 & _).
        rewrite R4 in Q1. rewrite R5 in Q2. rewrite R7 in Ow.
        pose proof (mwW_nx _ (proj1 W')) as Nx. pose proof (mwW_in _ (proj1 W')) as In.
        pose proof (mwW_out _ (proj1 W')) as Ou. unfold urange in Ou.
        rewrite Q1, Zlength_nil in Nx, In.
        rewrite R1, R2. split; [|intros _; lia].
        unfold Zlib.proof.harness.inflate_codes.TheoryRun.rn_bufret, m_have, m_left.
        rewrite In, Q1, Ow, Q2, Zlength_nil.
        replace (0 - (0 - m_nx m')) with 0 by lia. replace (m_out m' - (0 - 0)) with 0 by lia.
        cbn [u32 Z.modulo Z.eqb andb orb].
        destruct (Z.eqb_spec (m_ret m') Z_OK) as [E|E]; cbn; [discriminate | exact E].
    - subst res. cbn [r_ret r_m] in *. subst r'. split; [discriminate|].
      intros _. destruct LP as (W' & _). pose proof (mwW_snx _ (proj1 W')) as S.
      rewrite Q1, Zlength_nil in S. lia. }
  destruct Ret as [Rn Sn].
  split; [exact Rn|]. split; [exact Ow|].
  intros M. destruct (Q7 M) as (T1 & T2 & _). rewrite (Sn M) in T1. rewrite Q3, Ow in T2.
  rewrite Zlength_nil in T2. rewrite Z.add_0_r in T1, T2. rewrite T1, T2.
  unfold u64; split; apply Z.mod_small; unfold Int64.max_unsigned in *; rep_lia.
Qed.
