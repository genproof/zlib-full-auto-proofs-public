(* RT-H: mechanical port of inflate/HdrCrc5.v to the header-external loop state (RTHLoop.v); identifiers whose meaning changes carry the suffix H. *)
(* CRC2 / CRC4 of inflate.c (the gzip header cases): do { hbuf[0..] = hold bytes; check = crc32(check, hbuf, n); }
   while (0), in a minimal context (the temps state and hold, the local hbuf, the check field, the crc table),
   to be framed into a case with semax_frame_PQR.  One lemma per site (the temps differ). *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.roundtrip.RTHHdrKit5.
Require Import Zlib.proof.roundtrip.RTHCaseHyps5.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.inflate.MwfLemmas.
Require Export Zlib.proof.inflate.HdrCrc5.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.











(* the crc32 spec's buffer is stated in the crc32 unit's compspecs *)








(* if ((state->flags & 0x0200) && (state->wrap & 4)) CRCn(state->check, hold); (temps ta, tb, tf) *)
(* frame the crc lemma LEM (its arguments given) into the current goal *)
Ltac crcblock_tacH tf LEM :=
  match goal with W: mwf _ |- _ =>
  pose proof (sw_flags _ (mw_s _ W)) as RF; pose proof (sw_wrap_range _ (mw_s _ W)) as RW end;
  unfold crcblock, crc_if; cbv zeta;
  destruct (negb (Z.land (i_flags (m_s _)) 512 =? 0) && negb (Z.land (i_wrap (m_s _)) 4 =? 0))%bool eqn:Ec;
  [ apply andb_prop in Ec; destruct Ec as [Ec1 Ec2]; apply negb_true_iff in Ec1; apply negb_true_iff in Ec2;
    rewrite !loop_state_hsplitH; unfold loop_state_hH;
    rewrite mem_rep_h_check, head_part_checkH, strm_part_check; cbn [upd_s set_m_s m_s set_i_check i_check i_mode i_wrap i_flags i_head];
    abbreviate_semax;
    forward;
    forward_if (temp tf (Vint (Int.repr 1)));
    [ forward; forward; entailer!;
      rewrite hk_tbool by (apply hk_land_small; rep_lia); rewrite Ec2; reflexivity
    | match goal with H: Int.and _ _ = Int.zero |- _ =>
        rewrite (hk_flagbit0 _ _ H) in Ec1 by rep_lia; discriminate end
    | forward_if; [ apply semax_dowhile0; frame_crc LEM | if_absurd ] ]
  | rewrite !loop_state_hsplitH; unfold loop_state_hH;
    abbreviate_semax;
    forward;
    forward_if (temp tf (Vint (Int.repr 0)));
    [ forward; forward; entailer!;
      match goal with H: Int.and _ _ <> Int.zero |- _ => rewrite (hk_flagbit _ _ H) in Ec end;
      cbn [negb andb] in Ec;
      rewrite hk_tbool by (apply hk_land_small; rep_lia);
      destruct (Z.land (i_wrap (m_s _)) 4 =? 0); [reflexivity | discriminate]
    | forward; entailer!
    | forward_if; [ if_absurd | forward; entailer! ] ] ].

Lemma semax_crcblock_TIMEH {Espec: OracleKind} (F: frame) (m: mst):
  frame_ok F -> mwf m ->
  semax Delta_cases5 (loop_stateH F m) (crcblock _t'420 _t'421 _t'18 (crc4_stmt _t'419 _t'17))
    (normal_ret_assert (loop_stateH F (crc_if m (hbytes4 (m_hold m))))).
Proof.
  intros FOK W. pose proof FOK as (_ & _ & _ & HRT).
  pose proof (sw_check _ (mw_s _ W)) as RC. pose proof (mw_hold _ W) as RH.
  crcblock_tacH _t'18 (semax_crc4_TIME (f_sp F) (f_vhbuf F) (f_gv F) (f_tsh F) (m_hold m) (i_check (m_s m)) HRT RH RC).
Qed.

Lemma semax_crcblock_FLAGSH {Espec: OracleKind} (F: frame) (m: mst):
  frame_ok F -> mwf m ->
  semax Delta_cases5 (loop_stateH F m) (crcblock _t'426 _t'427 _t'15 (crc2_stmt _t'425 _t'14))
    (normal_ret_assert (loop_stateH F (crc_if m (hbytes2 (m_hold m))))).
Proof.
  intros FOK W. pose proof FOK as (_ & _ & _ & HRT).
  pose proof (sw_check _ (mw_s _ W)) as RC. pose proof (mw_hold _ W) as RH.
  crcblock_tacH _t'15 (semax_crc2_FLAGS (f_sp F) (f_vhbuf F) (f_gv F) (f_tsh F) (m_hold m) (i_check (m_s m)) HRT RH RC).
Qed.

Lemma semax_crcblock_OSH {Espec: OracleKind} (F: frame) (m: mst):
  frame_ok F -> mwf m ->
  semax Delta_cases5 (loop_stateH F m) (crcblock _t'413 _t'414 _t'21 (crc2_stmt _t'412 _t'20))
    (normal_ret_assert (loop_stateH F (crc_if m (hbytes2 (m_hold m))))).
Proof.
  intros FOK W. pose proof FOK as (_ & _ & _ & HRT).
  pose proof (sw_check _ (mw_s _ W)) as RC. pose proof (mw_hold _ W) as RH.
  crcblock_tacH _t'21 (semax_crc2_OS (f_sp F) (f_vhbuf F) (f_gv F) (f_tsh F) (m_hold m) (i_check (m_s m)) HRT RH RC).
Qed.
