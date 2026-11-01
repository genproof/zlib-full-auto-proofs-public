(* An inflate() call of uncompress2_z's loop (flush Z_NO_FLUSH) on a well-formed zlib stream that returns
   Z_BUF_ERROR has made no progress: it consumed no input and wrote no output.

   inflate() returns Z_BUF_ERROR when it neither consumed nor produced anything (inflate.c: `if (((in == 0 &&
   out == 0) || flush == Z_FINISH) && ret == Z_OK) ret = Z_BUF_ERROR`; Model.leave_fin).  The decode theory
   (rfc1951/Decode7.v, decode_call7_stmt) does not state it; uncompress2's model needs it to tell a call that
   stopped with the output space full (Z_BUF_ERROR from uncompress2) from one that was offered nothing.
   The hypotheses are decode_call7_stmt's, for a stream that is not gzip and the flush Z_NO_FLUSH. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.rfc1951.Decode7.
Require Zlib.proof.wide.Decode7.
Require Zlib.proof.inflate.StepW.
Require Import Zlib.proof.wide.rfc1951.Decode Zlib.proof.wide.rfc1951.DecKit Zlib.proof.rfc1951.TabDec.
Require Import Zlib.proof.wide.rfc1951.DecHdr Zlib.proof.wide.rfc1951.DecType Zlib.proof.wide.rfc1951.DecTab.
Require Import Zlib.proof.wide.rfc1951.DecDec Zlib.proof.wide.rfc1951.DecFast Zlib.proof.wide.rfc1951.DecTrl.
Require Import Zlib.proof.wide.rfc1951.DecCall.
Import ListNotations.
Local Open Scope Z_scope.

Lemma uw_buf : forall G pos out L z inp res,
  dctx_ok7 G -> dinv G pos out (l_s L) (zf_tout z) -> live_ok L -> zf_ok z ->
  Zlength inp <= 2 ^ 32 - 1 -> 0 <= pos -> pos + Zlength inp <= Zlength (dc_src G) ->
  inp = sublist pos (pos + Zlength inp) (dc_src G) -> (forall h, dc_w G <> WGzip h) ->
  run2 0 lenfix_list distfix_list (m_init z L inp) res -> r_ret res = Z_BUF_ERROR ->
  m_snx (r_m res) = 0 /\ m_ow (r_m res) = [].
Proof.
  intros G pos out L z inp res D DI LV ZF LIN P0 PL IE NG RUN RB.
  (* the call's loop, as in the wide port's DecCall.dec_call_fx_wide: it leaves at mE, a decoder state *)
  pose proof dkit_wide as K.
  pose proof (Zlib.proof.wide.Decode7.stepf2_kd_of_mwf3W Zlib.proof.inflate.StepW.stepf2_mwf3W) as SM.
  pose proof (group_dec_wide K (dfast_wide K)) as H4.
  pose proof (dc_step_wide (proj2 dec_hdr_part_wide K) (group_type_wide K tabdec) (group_tab_wide K tabdec SM H4)
    H4 (group_trl_wide K)) as ST.
  pose proof (Zlib.proof.wide.Decode7.dctx_ok7_wide G D) as C.
  pose proof C as (_ & _ & _ & _ & _ & _ & CB & _).
  assert (BI: bytes_ok (sublist pos (pos + Zlength inp) (dc_src G))) by (apply Forall_sublist; exact CB).
  rewrite <- IE in BI.
  pose proof ZF as (_ & AO & _).
  destruct (dc_init_wide G pos out L z inp DI LV ZF ltac:(lia) ltac:(dc_rep) BI) as (K0 & W0).
  destruct RUN as (o & LP & RO).
  destruct (dc_loop_wide SM ST G pos inp out 0 C P0 PL IE _ _ LP K0 W0 eq_refl)
    as (mE & -> & KE & WE & LE & _ & _ & _).
  inversion RO; subst; [discriminate RB|].
  (* inf_leave: Z_BUF_ERROR only when no input was consumed and no output written *)
  destruct (dc_lf 0 mE) as (_ & _ & _ & F4 & F5 & _ & _ & _ & _ & _ & F11 & _).
  rewrite F4, F5. rewrite F11 in RB.
  pose proof (mwf3_mwf_wide _ WE) as MW.
  pose proof (kd_inp _ _ _ _ _ KE) as KI. pose proof (mw_nx_wide _ MW) as NX. pose proof (mw_in_wide _ MW) as IN.
  destruct (mw_ow_wide _ MW) as [OWL _]. pose proof (mw_aout_wide _ MW) as AOE.
  pose proof (Zlength_nonneg (m_ow mE)) as OW0.
  pose proof (kd_ret _ _ _ _ _ KE) as KR. rewrite LE in KR. change (1 =? 1) with true in KR. rewrite andb_true_r in KR.
  pose proof (kd_out _ _ _ _ _ KE) as KO.
  change (0 =? Z_FINISH) with false in RB. rewrite orb_false_r in RB.
  destruct ((u32 (m_in mE - m_have mE) =? 0) && (dc_oc mE =? 0) && (m_ret mE =? Z_OK)) eqn:X;
    [|rewrite KR in RB; destruct (m_mode mE =? DONE); discriminate RB].
  apply andb_true_iff in X. destruct X as [X MR]. apply andb_true_iff in X. destruct X as [X1 X2].
  apply Z.eqb_eq in X1, X2, MR.
  (* after CHECK the output count is not avail_out's: LENGTH is gzip's, DONE returns Z_STREAM_END *)
  assert (AC: after_check G (m_mode mE) = false).
  { destruct (after_check G (m_mode mE)) eqn:A; [|reflexivity]. exfalso.
    unfold after_check in A. apply andb_true_iff in A. destruct A as [_ LD]. apply orb_true_iff in LD.
    destruct LD as [LL|DD]; apply Z.eqb_eq in LL || apply Z.eqb_eq in DD.
    - destruct (dc_at_length _ _ _ _ _ _ (kd_at _ _ _ _ _ KE) LL) as (hh & Hh). exact (NG hh Hh).
    - rewrite KR in MR. rewrite DD in MR. discriminate MR. }
  rewrite AC in KO.
  unfold m_have in X1. rewrite KI in IN, NX, X1. rewrite IN in X1.
  replace (Zlength inp - (Zlength inp - m_nx mE)) with (m_nx mE) in X1 by lia.
  rewrite dc_u32_id in X1 by lia.
  unfold dc_oc, m_left in X2. rewrite KO in X2.
  replace (m_aout mE - (m_aout mE - Zlength (m_ow mE))) with (Zlength (m_ow mE)) in X2 by lia.
  rewrite dc_u32_id in X2 by dc_rep.
  split; [exact X1 | apply Zlength_nil_inv; exact X2].
Qed.
