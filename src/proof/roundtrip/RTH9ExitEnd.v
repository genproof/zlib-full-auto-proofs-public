(* inflate()'s exit inf_leave, the end of the tail for calls of any uInt size: the return code and return
   (after the store of data_type, RTH9ExitDt.v), from the proof script of src/proof/hl/inflate_api/
   HlBody5ExitTail.v's et_end_ok_hl (copied by hand) with the counts of the call (in, out) up to
   Int.max_unsigned. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.hl.inflate_api.HlBody5Parts.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.hl.inflate_api.HlBody5ExitKit.
Require Import Zlib.proof.hl.inflate_api.HlBody5ExitTail.
Require Import Zlib.proof.inflate_api.Body5ExitWin.
Require Import Zlib.proof.inflate_api.Body5Exit.
Require Import Zlib.proof.roundtrip.RTH9ExitDt.

#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Lemma et_rc_ok9 {Espec: OracleKind} (F: frame) (X: mpred) (m0 m2: mst) (inn o: Z) (R: ret_assert):
  frame_ok5 F -> -5 <= m_ret m2 <= 2 -> 0 <= inn <= Int.max_unsigned -> 0 <= o <= Int.max_unsigned ->
  ENTAIL Delta_inflate5_hl,
    PROPx [] (LOCALx (ret_locals F)
      (SEPx [mem_rep_hl F m2; locals_rep F; hdr_tok F m0; mem_mgr (f_gv F); zfuncs (f_gv F); X]))
    |-- RA_return R (Some (zv (lt_r (f_flush F) inn o (m_ret m2)))) ->
  semax Delta_inflate5_hl (tst_hl F X m0 m2 inn o) et_rc R.
Proof.
  intros FOK RR RI RO HRET.
  destruct R as [Rn Rb Rc Rr]. cbn [RA_return] in HRET.
  pose proof FOK as ((HWS & HWH & HRG & HRT) & HFL).
  cbv beta iota zeta delta [et_rc et_end ex_tail inflate_exit f_inflate fn_body].
  unfold tst_hl, strm_e, strm_rep.
  abbreviate_semax. Intros.
  remember (f_gv F _zcalloc) as zca eqn:Hzca. remember (f_gv F _zcfree) as zcf eqn:Hzcf.
  forward_if (temp _t'108 (Vint (Int.repr (if ((inn =? 0) && (o =? 0))%bool then 1 else 0)))).
  { forward. entailer!. zeqfix. }
  { forward. entailer!. zfix. }
  forward_if (temp _t'109 (Vint (Int.repr (if (((inn =? 0) && (o =? 0)) || (f_flush F =? Z_FINISH))%bool then 1 else 0)))).
  { forward. entailer!. bsplit ((inn =? 0) && (o =? 0))%bool; [reflexivity | bctr]. }
  { forward. entailer!. bsplit ((inn =? 0) && (o =? 0))%bool; [bctr | zeqfix]. }
  forward_if (temp _t'110 (Vint (Int.repr (if ((((inn =? 0) && (o =? 0)) || (f_flush F =? Z_FINISH)) && (m_ret m2 =? Z_OK))%bool then 1 else 0)))).
  { forward. entailer!. bsplit (((inn =? 0) && (o =? 0)) || (f_flush F =? Z_FINISH))%bool; [zeqfix | bctr]. }
  { forward. entailer!. bsplit (((inn =? 0) && (o =? 0)) || (f_flush F =? Z_FINISH))%bool; [bctr | reflexivity]. }
  forward_if (temp _ret (Vint (Int.repr (lt_r (f_flush F) inn o (m_ret m2))))).
  { forward. entailer!. unfold lt_r.
    bsplit ((((inn =? 0) && (o =? 0)) || (f_flush F =? Z_FINISH)) && (m_ret m2 =? Z_OK))%bool; [reflexivity | bctr]. }
  { forward. entailer!. unfold lt_r.
    bsplit ((((inn =? 0) && (o =? 0)) || (f_flush F =? Z_FINISH)) && (m_ret m2 =? Z_OK))%bool; [bctr | reflexivity]. }
  apply semax_ret_tmp_hl with (r := lt_r (f_flush F) inn o (m_ret m2)).
  { entailer!. }
  { apply andp_left2. unfold PROPx, LOCALx. apply andp_left2. apply andp_left1.
    intro rho. unfold local, lift1. apply prop_derives. intros HL. exact (proj1 HL). }
  cbn [RA_return].
  eapply derives_trans; [ | exact HRET].
  apply andp_right; [apply andp_left1, derives_refl | ].
  unfold ret_locals. rewrite mem_rep_esplit_hl.
  unfold strm_e, strm_rep, state_f9.
  rewrite <- Hzca, <- Hzcf.
  entailer!.
Qed.

Lemma et_end_ok9 {Espec: OracleKind} (F: frame) (X: mpred) (m0 m2: mst) (inn o: Z) (R: ret_assert):
  frame_ok5 F -> i_bits (m_s m2) = m_bits m2 -> 0 <= m_bits m2 <= 39 -> 0 <= i_last (m_s m2) <= 1 ->
  HEAD <= i_mode (m_s m2) <= SYNC -> -5 <= m_ret m2 <= 2 -> 0 <= inn <= Int.max_unsigned -> 0 <= o <= Int.max_unsigned ->
  ENTAIL Delta_inflate5_hl,
    PROPx [] (LOCALx (ret_locals F)
      (SEPx [mem_rep_hl (set_f_winp_dt F (f_winp F) (lt_dt m2)) m2;
             locals_rep F; hdr_tok F m0; mem_mgr (f_gv F); zfuncs (f_gv F); X]))
    |-- RA_return R (Some (zv (lt_r (f_flush F) inn o (m_ret m2)))) ->
  semax Delta_inflate5_hl (tst_hl F X m0 m2 inn o) et_end R.
Proof.
  intros FOK HB RB RL RM RR RI RO HRET.
  rewrite et_end_eq9.
  eapply semax_seq'; [apply et_dt_ok9; assumption | ].
  apply et_rc_ok9; auto.
Qed.
