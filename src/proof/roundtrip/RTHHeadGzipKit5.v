(* RT-H: mechanical port of inflate/HeadGzipKit5.v to the header-external loop state (RTHLoop.v); identifiers whose meaning changes carry the suffix H. *)
(* The kit of the gzip branch of case HEAD (HeadGzipW5.v), in Delta_cases5: a view of loop_stateH with the
   state fields mode, check and wbits, the crc table and the stack variables apart (the rest of the memory
   one opaque item mem_rep_gH), and CRC2 (do { hbuf[0..1] = hold bytes; check = crc32(check, hbuf, 2); }
   while (0)) in a minimal context (ported from HdrCrc5.v, temps _t'439/_t'6). *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.roundtrip.RTHCaseHyps5.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.inflate.MwfLemmas.
Require Export Zlib.proof.inflate.HeadGzipKit5.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* the conjuncts 2, 8, 11 of 35 to the front (on variables: a cheap proof term) *)




(* the memory but the three fields and the crc table *)
Definition mem_rep_gH (F: frame) (m: mst) : mpred :=
  state_rep_g (f_gv F) (f_sp F) (f_strmp F) (f_headp F) (f_winp F) (m_s m) *
  win_rep (f_winp F) (m_s m) *
  head_partH F m *
  strm_rep (f_gv F) (f_shs F) (f_strmp F)
    (in_ptr (f_ib F) (m_snx m)) (zv (Zlength (m_inp m) - m_snx m)) (m_tin m)
    (out_ptr (f_ob F) (m_sow m)) (zv (m_aout m - m_sow m)) (m_tout m)
    (msg_val (f_gv F) (m_msg m)) (f_sp F) (f_dt F) (m_adler m) (f_vres F) *
  in_rep (f_ib F) *
  out_rep (f_ob F) (m_ow m) *
  tables_rep (f_gsh F) (f_gv F).

Lemma mem_rep_gsplitH: forall F m,
  mem_repH F m =
  field_at Ews t_state (DOT _mode) (zv (i_mode (m_s m))) (f_sp F) *
  field_at Ews t_state (DOT _check) (lv (i_check (m_s m))) (f_sp F) *
  field_at Ews t_state (DOT _wbits) (zv (i_wbits (m_s m))) (f_sp F) *
  crc_table_at (f_tsh F) (f_gv F) * mem_rep_gH F m.
Proof.
  intros. unfold mem_repH, mem_rep_gH. rewrite state_rep_gsplit.
  apply pred_ext; cancel.
Qed.

(* loop_stateH with these parts apart: the fields' values md, ck, wb given *)
Definition loop_state_gH (F: frame) (m: mst) (md ck wb: val) : environ -> mpred :=
  PROP (in_ok (f_ib F) (m_inp m); out_ok (f_ob F) (m_aout m))
  LOCAL (temp _strm (f_strmp F); temp _flush (zv (f_flush F)); temp _state (f_sp F);
         temp _next (in_ptr (f_ib F) (m_nx m)); temp _put (out_ptr (f_ob F) (Zlength (m_ow m)));
         temp _have (zv (m_have m)); temp _left (zv (m_left m)); temp _hold (lv (m_hold m));
         temp _bits (zv (m_bits m)); temp _in (zv (m_in m)); temp _out (zv (m_out m));
         temp _ret (zv (m_ret m)); temp _leave (zv (m_leave m));
         lvar _here t_code (f_vhere F); lvar _last t_code (f_vlast F);
         lvar _hbuf (tarray tuchar 4) (f_vhbuf F); gvars (f_gv F))
  SEP (field_at Ews t_state (DOT _mode) md (f_sp F);
       field_at Ews t_state (DOT _check) ck (f_sp F);
       field_at Ews t_state (DOT _wbits) wb (f_sp F);
       crc_table_at (f_tsh F) (f_gv F);
       data_at_ Tsh (tarray tuchar 4) (f_vhbuf F);
       data_at_ Tsh t_code (f_vhere F); data_at_ Tsh t_code (f_vlast F); mem_rep_gH F m).

Lemma loop_state_gsplitH: forall F m,
  loop_stateH F m = loop_state_gH F m (zv (i_mode (m_s m))) (lv (i_check (m_s m))) (zv (i_wbits (m_s m))).
Proof.
  intros. unfold loop_stateH, loop_state_gH, locals_rep. rewrite mem_rep_gsplitH.
  f_equal. unfold SEPx. simpl. f_equal. extensionality rho. apply pred_ext; cancel.
Qed.

(* the gzip branch's machine, in this view *)


Lemma loop_state_head_gzipH: forall F m (w c: Z),
  (i_wbits (m_s m) = 0 -> i_win (m_s m) = false) ->
  w = (if i_wbits (m_s m) =? 0 then 15 else i_wbits (m_s m)) ->
  loop_stateH F (set_mode (initbits (upd_s m (fun s => set_i_check (set_i_wbits s w) c)))
                  Zlib.proof.inflate.Model.FLAGS) =
  loop_state_gH F (initbits m) (zv Zlib.proof.inflate.Model.FLAGS) (lv c) (zv w).
Proof.
  intros F m w c H E. rewrite loop_state_gsplitH.
  assert (M: mem_rep_gH F (set_mode (initbits (upd_s m (fun s => set_i_check (set_i_wbits s w) c)))
                  Zlib.proof.inflate.Model.FLAGS) = mem_rep_gH F (initbits m)).
  { unfold mem_rep_gH.
    cbn [set_mode initbits upd_s set_m_s set_m_hold set_m_bits m_s set_i_mode set_i_check].
    rewrite <- (win_rep_wbits (f_winp F) (m_s m) w H E). reflexivity. }
  unfold loop_state_gH. rewrite M. reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* CRC2 in a minimal context                                                                      *)













(* the crc32 spec's buffer is stated in the crc32 unit's compspecs *)




(* do { body } while (0) *)

