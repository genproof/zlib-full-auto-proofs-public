(* RT-H: mechanical port of inflate/ModeKit.v to the header-external loop state (RTHLoop.v); identifiers whose meaning changes carry the suffix H. *)
(* The mode field of inflate()'s state alone: state_rep = field_at mode * state_rep_nm (the 33 other
   fields), so that `state->mode = X;` changes one field_at and the rest of the memory stays one opaque
   SEP item (mem_rep_nmH, unchanged by set_mode).  semax_store_modeH: the store, for any mode value. *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Export Zlib.proof.roundtrip.RTHCaseCommon.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.inflate.MwfLemmas.
Require Export Zlib.proof.inflate.ModeKit.

#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* the second of 35 separating conjuncts to the front (on variables: a cheap proof term) *)




Definition mem_rep_nmH (F: frame) (m: mst) : mpred :=
  state_rep_nm (f_gv F) (f_sp F) (f_strmp F) (f_headp F) (f_winp F) (m_s m) *
  win_rep (f_winp F) (m_s m) *
  head_partH F m *
  strm_rep (f_gv F) (f_shs F) (f_strmp F)
    (in_ptr (f_ib F) (m_snx m)) (zv (Zlength (m_inp m) - m_snx m)) (m_tin m)
    (out_ptr (f_ob F) (m_sow m)) (zv (m_aout m - m_sow m)) (m_tout m)
    (msg_val (f_gv F) (m_msg m)) (f_sp F) (f_dt F) (m_adler m) (f_vres F) *
  in_rep (f_ib F) *
  out_rep (f_ob F) (m_ow m) *
  tables_rep (f_gsh F) (f_gv F) *
  crc_table_at (f_tsh F) (f_gv F).

Lemma mem_rep_splitH: forall F m,
  mem_repH F m = field_at Ews t_state (DOT _mode) (zv (m_mode m)) (f_sp F) * mem_rep_nmH F m.
Proof.
  intros. unfold mem_repH, mem_rep_nmH. rewrite state_rep_split. unfold m_mode.
  apply pred_ext; cancel.
Qed.

Lemma mem_rep_nm_set_modeH: forall F m md, mem_rep_nmH F (set_mode m md) = mem_rep_nmH F m.
Proof. reflexivity. Qed.

(* loop_stateH with the mode field (value v) apart *)
Definition loop_state_mH (F: frame) (m: mst) (v: val) : environ -> mpred :=
  PROP (in_ok (f_ib F) (m_inp m); out_ok (f_ob F) (m_aout m))
  LOCAL (temp _strm (f_strmp F); temp _flush (zv (f_flush F)); temp _state (f_sp F);
         temp _next (in_ptr (f_ib F) (m_nx m)); temp _put (out_ptr (f_ob F) (Zlength (m_ow m)));
         temp _have (zv (m_have m)); temp _left (zv (m_left m)); temp _hold (lv (m_hold m));
         temp _bits (zv (m_bits m)); temp _in (zv (m_in m)); temp _out (zv (m_out m));
         temp _ret (zv (m_ret m)); temp _leave (zv (m_leave m));
         lvar _here t_code (f_vhere F); lvar _last t_code (f_vlast F);
         lvar _hbuf (tarray tuchar 4) (f_vhbuf F); gvars (f_gv F))
  SEP (field_at Ews t_state (DOT _mode) v (f_sp F); mem_rep_nmH F m; locals_rep F).

Lemma loop_state_splitH: forall F m, loop_stateH F m = loop_state_mH F m (zv (m_mode m)).
Proof.
  intros. unfold loop_stateH, loop_state_mH. rewrite mem_rep_splitH.
  f_equal. unfold SEPx. simpl. rewrite !sepcon_assoc. reflexivity.
Qed.

Lemma loop_state_set_modeH: forall F m md, loop_stateH F (set_mode m md) = loop_state_mH F m (zv md).
Proof. intros. rewrite loop_state_splitH. reflexivity. Qed.

(* state->mode = md; *)
Lemma semax_store_modeH {Espec: OracleKind} (F: frame) (m: mst) (md: Z):
  semax Delta_inflate (loop_stateH F m)
    (Sassign (Efield (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                       (Tstruct _inflate_state noattr)) _mode tint)
       (Econst_int (Int.repr md) tint))
    (normal_ret_assert (loop_stateH F (set_mode m md))).
Proof.
  rewrite loop_state_set_modeH, loop_state_splitH. unfold loop_state_mH.
  abbreviate_semax.
  forward.
  entailer!.
Qed.

(* mwf after a change between the modes that need only the decoding tables (LEN_, LEN, LIT), from a
   decoding mode.  Do not prove such side goals with `apply mwf_set_mode; auto`: it took > 5 min. *)

