(* RT-H: mechanical port of inflate/ExHdrKit5.v to the header-external loop state (RTHLoop.v); identifiers whose meaning changes carry the suffix H. *)
(* Copy of HdrKit5.v for the cases EXLEN/EXTRA.  A view of loop_stateH for the gzip header cases (FLAGS, TIME, OS, ...) in Delta_cases5: the state fields
   mode, wrap, flags, check, head apart (state_rep_h: the 30 others), the head part, the stream, the crc
   table and the stack variables as separate SEP items, the rest of the memory one opaque item (mem_rep_h,
   unchanged by the updates of these cases).  And INITBITS(). *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Export Zlib.proof.roundtrip.RTHModeKit5.
Require Import Zlib.proof.crc32.Spec.
Require Export Zlib.proof.inflate.ExHdrKit5.

#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* the conjuncts 2, 4, 6, 8, 10 of 35 to the front (on variables: a cheap proof term) *)




(* the memory but the five fields, the head part, the stream and the crc table *)
Lemma mem_rep_hsplitH: forall F m,
  mem_repH F m =
  field_at Ews t_state (DOT _mode) (zv (i_mode (m_s m))) (f_sp F) *
  field_at Ews t_state (DOT _wrap) (zv (i_wrap (m_s m))) (f_sp F) *
  field_at Ews t_state (DOT _flags) (zv (i_flags (m_s m))) (f_sp F) *
  field_at Ews t_state (DOT _check) (lv (i_check (m_s m))) (f_sp F) *
  field_at Ews t_state (DOT _head) (if i_head (m_s m) then f_headp F else nullval) (f_sp F) *
  head_partH F m * strm_part F m * crc_table_at (f_tsh F) (f_gv F) * mem_rep_h F m.
Proof.
  intros. unfold mem_repH, mem_rep_h, strm_part. rewrite state_rep_hsplit.
  apply pred_ext; cancel.
Qed.

(* loop_stateH with these parts apart *)
Definition loop_state_hH (F: frame) (m: mst) : environ -> mpred :=
  PROP (in_ok (f_ib F) (m_inp m); out_ok (f_ob F) (m_aout m))
  LOCAL (temp _strm (f_strmp F); temp _flush (zv (f_flush F)); temp _state (f_sp F);
         temp _next (in_ptr (f_ib F) (m_nx m)); temp _put (out_ptr (f_ob F) (Zlength (m_ow m)));
         temp _have (zv (m_have m)); temp _left (zv (m_left m)); temp _hold (lv (m_hold m));
         temp _bits (zv (m_bits m)); temp _in (zv (m_in m)); temp _out (zv (m_out m));
         temp _ret (zv (m_ret m)); temp _leave (zv (m_leave m));
         lvar _here t_code (f_vhere F); lvar _last t_code (f_vlast F);
         lvar _hbuf (tarray tuchar 4) (f_vhbuf F); gvars (f_gv F))
  SEP (field_at Ews t_state (DOT _mode) (zv (i_mode (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _wrap) (zv (i_wrap (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _flags) (zv (i_flags (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _check) (lv (i_check (m_s m))) (f_sp F);
       field_at Ews t_state (DOT _head) (if i_head (m_s m) then f_headp F else nullval) (f_sp F);
       head_partH F m; strm_part F m; crc_table_at (f_tsh F) (f_gv F);
       data_at_ Tsh (tarray tuchar 4) (f_vhbuf F);
       data_at_ Tsh t_code (f_vhere F); data_at_ Tsh t_code (f_vlast F); mem_rep_h F m).

Lemma loop_state_hsplitH: forall F m, loop_stateH F m = loop_state_hH F m.
Proof.
  intros. unfold loop_stateH, loop_state_hH, locals_rep. rewrite mem_rep_hsplitH.
  f_equal. unfold SEPx. simpl. f_equal. extensionality rho. apply pred_ext; cancel.
Qed.

(* INITBITS(): do { hold = 0; bits = 0; } while (0) *)
Lemma semax_initbits5H {Espec: OracleKind} (F: frame) (m: mst):
  semax Delta_cases5 (loop_stateH F m)
    (Sloop (Ssequence (Sset _hold (Ecast (Econst_int (Int.repr 0) tint) tulong))
                      (Sset _bits (Econst_int (Int.repr 0) tint))) Sbreak)
    (normal_ret_assert (loop_stateH F (initbits m))).
Proof.
  apply semax_loop with (Q' := loop_stateH F (initbits m)).
  - unfold loop_stateH. abbreviate_semax. forward. forward.
    unfold loop1_ret_assert. simpl RA_normal. entailer!. apply derives_refl.
  - eapply semax_pre; [ | apply semax_break]. simpl RA_break. unfold loop2_ret_assert. simpl RA_break.
    apply andp_left2. apply derives_refl.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* pure facts of the header cases                                                                 *)

Require Import Zlib.proof.crc32.Combine.
Require Import Zlib.proof.inflate.MwfLemmas.













(* crc_if keeps mwf *)








(* the mode change at the end of a header case: to a mode of FLAGS .. TYPEDO, from a header mode *)


(* do { body } while (0) *)


(* the bit tests of int fields *)










(* what the header updates keep *)









Lemma head_part_checkH: forall F m d,
  head_partH F (upd_s m (fun s => set_i_check s (ref_crc32 (i_check s) d))) = head_partH F m.
Proof. reflexivity. Qed.

