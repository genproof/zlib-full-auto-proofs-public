(* Law rt_session, sessions with a gzip header: an inflate() call after the gzip header offered neither input nor
   output space (SGzDefs.sgz_idle_d_stmt): not Z_OK, nothing written, the counters kept (as rt_stream's
   UIIdle.ui_idle_call, with a gz_header attached).

   The run is moved to the machine with the small gz_header (G2IDefs.g2_mc, RTH8SimKit.hs_run: the passes after
   the header do not read it, the result differs only in the header).  There, from a mode after the header
   (TYPE .. BAD), each pass of the switch keeps the mode after the header and never returns
   (inflate_buffers' IBStepKit.stepf2_tgood: the only return is DICT's Z_NEED_DICT, from a header mode), keeps
   total_in, total_out + out (mod 2^64) and out <= avail_out (UIIdle.ui_idle_step).  With avail_out = 0 and no
   input, the exit then sees in = out = 0 and returns Z_BUF_ERROR or the error it had, and adds nothing to the
   counters. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.rt_session.SGzDefs.
Require Import Zlib.proof.harness.rt_session.SGzTail.
Require Import Zlib.proof.inflate.StepW.
Require Zlib.proof.harness.rt_stream.UIIdle.
Require Zlib.proof.harness.inflate_buffers.IBStepKit.
Require Zlib.proof.harness.inflate_buffers.IBRun.
Require Zlib.proof.harness.inflate_codes.TheoryRun.
Import ListNotations.
Local Open Scope Z_scope.

Module IBK := Zlib.proof.harness.inflate_buffers.IBStepKit.

Section Idle.
Variables (flush ti to: Z).

(* a loop head of a call offered no input and no output space, in a mode after the header, with total_in ti and
   total_out + out = to (mod 2^64) *)
Definition sgi_J (m: mst) : Prop :=
  mwf3W m /\ m_inp m = [] /\ m_aout m = 0 /\ m_tin m = ti /\
  (m_tout m + m_out m) mod 2 ^ 64 = to mod 2 ^ 64 /\ m_out m <= m_aout m /\
  DICT < m_mode m <= BAD.

Lemma sgi_step m : sgi_J m -> m_leave m = 0 ->
  match stepf2 flush lenfix_list distfix_list m with IRet _ _ => False | IBrk m' => sgi_J m' end.
Proof.
  intros (W & I & A & T & O & OA & M1 & M2) Lv.
  pose proof (mwW_ow _ (proj1 W)) as [Ow _]. pose proof (mwW_out _ (proj1 W)) as Ou. unfold urange in Ou.
  assert (Hr: IBK.md_rng m) by (unfold IBK.md_rng, HEAD, DICT, BAD in *; lia).
  assert (P1: 0 <= m_left m <= m_out m) by (unfold m_left; pose proof (Zlength_nonneg (m_ow m)); lia).
  assert (P2: m_out m < 2 ^ 32) by rep_lia.
  pose proof (IBK.stepf2_tgood flush lenfix_list distfix_list m Hr P1 P2) as Gd.
  pose proof (stepf2_mwf3W flush m W Lv) as W'.
  pose proof (Zlib.proof.harness.rt_stream.UIIdle.ui_idle_step flush m) as S.
  destruct (stepf2 flush lenfix_list distfix_list m) as [m'|r m'].
  - destruct Gd as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9). destruct S as [SA SO].
    split; [exact W'|]. split; [congruence|]. split; [congruence|]. split; [congruence|].
    split; [congruence|]. split; [destruct SO; lia|].
    split; [|lia].
    destruct (Z_lt_le_dec DICT (m_mode m')) as [D|D]; [exact D|].
    exfalso. destruct T8 as [T8 _]; [unfold IBK.hdr_md; lia|]. unfold IBK.hdr_md, DICT in *; lia.
  - destruct Gd as (_ & Th & _). unfold IBK.hdr_md, DICT in *; lia.
Qed.

(* the loop never returns and keeps sgi_J *)
Lemma sgi_loop m o : loop2 flush lenfix_list distfix_list m o -> sgi_J m -> m_leave m = 0 ->
  match o with IRet _ _ => False | IBrk m' => sgi_J m' end.
Proof.
  intros HL. induction HL as [m r m' E | m m' E Hlv | m m' o E Hlv HL IH]; intros J Lv;
    pose proof (sgi_step m J Lv) as S; rewrite E in S.
  - exact S.
  - exact S.
  - apply IH; [exact S|]. pose proof (mwW_leave _ (proj1 (proj1 S))). lia.
Qed.

Lemma sgi_run m res : sgi_J m -> m_leave m = 0 -> 0 <= ti <= Int64.max_unsigned -> 0 <= to <= Int64.max_unsigned ->
  run2 flush lenfix_list distfix_list m res ->
  r_ret res <> Z_OK /\ m_ow (r_m res) = [] /\
  (r_ret res <> Z_MEM_ERROR -> m_tin (r_m res) = ti /\ m_tout (r_m res) = to).
Proof.
  intros J Lv Bi Bo (o & LP & RO). pose proof (sgi_loop m o LP J Lv) as J'.
  destruct o as [m'|r m']; [|contradiction].
  destruct J' as (W & I & A & T & O & OA & _).
  pose proof (mwW_ow _ (proj1 W)) as [Ow _]. rewrite A in Ow.
  assert (E: m_ow m' = []) by (apply Zlength_nil_inv; pose proof (Zlength_nonneg (m_ow m')); lia).
  pose proof (mwW_out _ (proj1 W)) as Ou. unfold urange in Ou.
  assert (O0: m_out m' = 0) by lia.
  pose proof (mwW_nx _ (proj1 W)) as Nx. rewrite I, Zlength_nil in Nx.
  assert (N0: m_nx m' = 0) by lia.
  pose proof (mwW_in _ (proj1 W)) as In. rewrite I, Zlength_nil in In.
  assert (Hv: m_have m' = 0) by (unfold m_have; rewrite I, Zlength_nil; lia).
  assert (Hl: m_left m' = 0) by (unfold m_left; rewrite A, E, Zlength_nil; lia).
  inversion RO; subst.
  - split; [cbn; discriminate|]. split; [exact E|]. intros N; exfalso; apply N; reflexivity.
  - pose proof (Zlib.proof.harness.inflate_codes.TheoryRun.rn_leave_fin flush m') as R. cbv zeta in R.
    destruct R as (R1 & _).
    pose proof (Zlib.proof.harness.inflate_buffers.IBRun.ib_leave_fin flush m') as F. cbv zeta in F.
    destruct F as (_ & _ & F3 & _ & _ & _ & F7 & F8).
    split; [|split; [rewrite F3; exact E|]].
    + rewrite R1. unfold Zlib.proof.harness.inflate_codes.TheoryRun.rn_bufret.
      rewrite In, Hv, O0, Hl. cbn [Z.sub u32 Z.modulo Z.eqb andb orb].
      destruct (Z.eqb_spec (m_ret m') Z_OK) as [Q|Q]; cbn; [discriminate | exact Q].
    + intros _. rewrite F7, F8, T, In, Hv, Hl, O0.
      rewrite O0, Z.add_0_r in O. unfold u64, u32. cbn [Z.sub Z.modulo].
      rewrite !Z.add_0_r, O. split; apply Z.mod_small; unfold Int64.max_unsigned in *; rep_lia.
Qed.

End Idle.

Lemma sgz_idle_d : sgz_idle_d_stmt.
Proof.
  intros G pos out L z flush res OK DV LV ZF AO P0 PL HP PF RUN.
  destruct (sgz_canon_init G pos out L z [] OK DV LV ZF ltac:(lia) ltac:(rewrite Zlength_nil; rep_lia)
              ltac:(constructor)) as (_ & MW).
  set (m0 := m_init z L []) in *.
  pose proof (g2_dinv_mode _ _ _ _ _ DV) as MD.
  assert (MD0: Zlib.proof.inflate.Model.TYPE <= i_mode (m_s m0) <= DONE).
  { unfold m0, m_init. cbv zeta. destruct (i_mode (l_s L) =? Zlib.proof.inflate.Model.TYPE); cbn [m_s];
      [cbn; unfold TYPEDO, DONE, Zlib.proof.inflate.Model.TYPE; lia | exact MD]. }
  assert (HK: SK.hk m0) by (right; apply g2_hdr_mode_after; unfold m_mode; lia).
  destruct (SK.hs_run flush lenfix_list distfix_list m0 g2_hc res HK RUN) as [RUN' _].
  destruct ZF as (Z1 & Z2 & Z3 & Z4 & _).
  assert (J0: sgi_J (zf_tin z) (zf_tout z) (g2_mc m0)).
  { assert (MD1: Zlib.proof.inflate.Model.TYPE <= m_mode (g2_mc m0) <= DONE) by exact MD0.
    assert (MR: DICT < m_mode (g2_mc m0) <= BAD).
    { revert MD1. generalize (m_mode (g2_mc m0)). intros x Hx.
      unfold Zlib.proof.inflate.Model.TYPE, DICT, DONE, BAD in *; lia. }
    refine (conj MW (conj _ (conj _ (conj _ (conj _ (conj _ MR)))))).
    all: unfold g2_mc, m0, m_init; cbv zeta; cbn [m_inp m_aout m_tin m_tout m_out m_s set_m_h].
    all: rewrite ?AO, ?Z.add_0_r; first [reflexivity | lia]. }
  destruct (sgi_run flush (zf_tin z) (zf_tout z) (g2_mc m0) (SK.rh g2_hc res) J0 eq_refl Z3 Z4 RUN')
    as (R1 & R2 & R3).
  unfold SK.rh, SK.mh in R1, R2, R3. cbn [r_ret r_m m_ow m_tin m_tout set_m_h] in R1, R2, R3.
  exact (conj R1 (conj R2 R3)).
Qed.
