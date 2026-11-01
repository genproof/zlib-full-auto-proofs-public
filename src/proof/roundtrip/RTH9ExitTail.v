(* inflate()'s exit inf_leave, the tail (Body5ExitKit.v ex_tail), for calls of any uInt size: in -= avail_in;
   out -= avail_out; the counters; UPDATE_CHECK; data_type; the return code.  This file: the bounds (tail_facts9) and the counters
   (et_cnt_ok9); RTH9ExitChk.v: UPDATE_CHECK; RTH9ExitEnd.v: data_type and the return; RTH9Exit.v: the tail
   from them.  The proof scripts are those of the
   headless port src/proof/hl/inflate_api/HlBody5ExitTail.v (copied by hand); only the bounds change: the input
   of the call and its output space are up to Int.max_unsigned (tail_facts9, et_end_ok9), as in the wide port
   src/proof/za/inflate_api/Body5ExitTail.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.hl.inflate_api.HlBody5Parts.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.hl.inflate_api.HlBody5ExitKit.
Require Import Zlib.proof.hl.inflate_api.HlBody5ExitTail.

#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* Body5ExitKit.tail_facts with the input and the output space up to Int.max_unsigned *)
Definition tail_facts9 (m: mst) : Prop :=
  m_snx m = m_nx m /\ m_sow m = Zlength (m_ow m) /\ i_bits (m_s m) = m_bits m /\
  m_in m = Zlength (m_inp m) /\ 0 <= m_nx m <= Zlength (m_inp m) /\ Zlength (m_inp m) <= Int.max_unsigned /\
  m_left m <= m_out m <= m_aout m /\ Zlength (m_ow m) <= m_aout m <= Int.max_unsigned /\ bytes_ok (m_ow m) /\
  lrange (m_tin m) /\ lrange (m_tout m) /\ lrange (i_check (m_s m)) /\ lrange (i_total (m_s m)) /\
  0 <= i_wrap (m_s m) <= 15 /\ srange (i_flags (m_s m)) /\ 0 <= m_bits m <= 39 /\ 0 <= i_last (m_s m) <= 1 /\
  HEAD <= i_mode (m_s m) <= SYNC /\ -5 <= m_ret m <= 2.

(* HlBody5ExitKit.ex_tail_stmt_hl with tail_facts9 *)
Definition ex_tail_stmt9 : Prop :=
  forall {Espec: OracleKind} (F: frame) (X: mpred) (m: mst) (R: ret_assert),
  frame_ok5 F -> tail_facts9 m ->
  ENTAIL Delta_inflate5_hl,
    PROPx [] (LOCALx (ret_locals F)
      (SEPx [mem_rep_hl (set_f_winp_dt F (f_winp F) (res_dt F (leave_tail (f_flush F) m))) (r_m (leave_tail (f_flush F) m));
             locals_rep F; hdr_tok F m; mem_mgr (f_gv F); zfuncs (f_gv F); X]))
    |-- RA_return R (Some (zv (r_ret (leave_tail (f_flush F) m)))) ->
  semax Delta_inflate5_hl (lstate_hl F X m) ex_tail R.

Lemma lt_inn_eq9: forall m, tail_facts9 m -> lt_inn m = m_nx m.
Proof.
  intros m TF. destruct TF as (T1 & T2 & T3 & T4 & T5 & T6 & _). unfold lt_inn, m_have, u32.
  rewrite T4. replace (Zlength (m_inp m) - (Zlength (m_inp m) - m_nx m)) with (m_nx m) by lia.
  apply Z.mod_small. rep_lia.
Qed.

Lemma lt_out_eq9: forall m, tail_facts9 m -> lt_out m = m_out m - m_left m /\ 0 <= lt_out m <= Zlength (m_ow m).
Proof.
  intros m TF. destruct TF as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & _). unfold lt_out, m_left, u32 in *.
  rewrite Z.mod_small by rep_lia. split; [reflexivity | lia].
Qed.

Lemma et_cnt_ok9 {Espec: OracleKind} (F: frame) (X: mpred) (m: mst):
  frame_ok5 F -> tail_facts9 m ->
  semax Delta_inflate5_hl (lstate_hl F X m) et_cnt
    (normal_ret_assert (tst_hl F X m (lt_m1 m) (lt_inn m) (lt_out m))).
Proof.
  intros FOK TF.
  pose proof (lt_inn_eq9 m TF) as EI. pose proof (lt_out_eq9 m TF) as [EO RO].
  pose proof TF as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & T10 & T11 & T12 & T13 & _).
  pose proof FOK as ((HWS & HWH & HRG & HRT) & HFL).
  cbv beta iota zeta delta [et_cnt ex_tail inflate_exit f_inflate fn_body].
  rewrite lstate_esplit_hl. unfold lstate_e_hl, strm_e, strm_rep.
  abbreviate_semax.
  remember (f_gv F _zcalloc) as zca eqn:Hzca. remember (f_gv F _zcfree) as zcf eqn:Hzcf.
  forward. forward. forward. forward. forward. forward. forward. forward. forward. forward.
  assert (SI: Int.sub (Int.repr (m_in m)) (Int.repr (Zlength (m_inp m) - m_snx m)) = Int.repr (lt_inn m))
    by (rewrite sub_repr, EI; f_equal; lia).
  assert (SO: Int.sub (Int.repr (m_out m)) (Int.repr (m_aout m - m_sow m)) = Int.repr (lt_out m))
    by (rewrite sub_repr, EO; f_equal; unfold m_left; lia).
  assert (UI: Int.unsigned (Int.repr (lt_inn m)) = lt_inn m) by (rewrite Int.unsigned_repr; rep_lia).
  assert (UO: Int.unsigned (Int.repr (lt_out m)) = lt_out m) by (rewrite Int.unsigned_repr; rep_lia).
  rewrite SI, SO, UI, UO, !ck_add_u64.
  unfold tst_hl, strm_e, strm_rep.
  change (mem_rep_e_hl F (lt_m1 m)) with (mem_rep_e_hl F m).
  unfold lt_m1, upd_s.
  cbn [m_s set_m_s set_m_tout set_m_tin set_i_total i_mode i_last i_wrap i_flags i_check i_total i_wsize i_hold
       i_bits m_tin m_tout m_snx m_sow m_inp m_aout m_msg m_adler m_ret m_ow].
  rewrite <- Hzca, <- Hzcf.
  entailer!.
Qed.
