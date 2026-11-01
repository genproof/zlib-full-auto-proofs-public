(* RT-H: a mechanical port of inflate/ExKit5.v to RTHLoop without its two lemmas that unfold the defined head_rep, so that it compiles. *)
(* Kit of the switch cases EXLEN and EXTRA (Cases5_EX.v; ported from the v3 kit to Model2/stepf2): the fields of struct inflate_state these
   cases touch (mode, wrap, flags, check, head, length), the gz_header, the input and the crc table apart
   from the rest of the memory (mem_x, one opaque SEP item, unchanged by the cases' updates), and the
   model facts (mwf3 of the fallthrough machines). *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Export Zlib.proof.roundtrip.RTHExHdrKit5.
Require Export Zlib.proof.inflate.ExHdrSame5.
Require Import Zlib.proof.inflate.Steps2.
Require Import Zlib.proof.inflate.MwfLemmas.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.crc32.Combine.
Require Export Zlib.proof.inflate.ExKit5.

#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* conjuncts 2, 4, 6, 8, 10, 18 of 35 to the front (on variables: a cheap proof term) *)




(* the rest of the memory *)


Lemma mem_rep_split_xH: forall F m,
  mem_repH F m =
  field_at Ews t_state (DOT _mode) (zv (i_mode (m_s m))) (f_sp F) *
  field_at Ews t_state (DOT _wrap) (zv (i_wrap (m_s m))) (f_sp F) *
  field_at Ews t_state (DOT _flags) (zv (i_flags (m_s m))) (f_sp F) *
  field_at Ews t_state (DOT _check) (lv (i_check (m_s m))) (f_sp F) *
  field_at Ews t_state (DOT _head) (if i_head (m_s m) then f_headp F else nullval) (f_sp F) *
  field_at Ews t_state (DOT _length) (zv (i_length (m_s m))) (f_sp F) *
  head_partH F m * in_rep (f_ib F) * crc_table_at (f_tsh F) (f_gv F) * mem_x F m.
Proof.
  intros. unfold mem_repH, mem_x. rewrite state_rep_split_x. apply sepcon_pick_mem.
Qed.

(* loop_stateH with the fields of the cases apart *)
Definition ex_stateH (F: frame) (m: mst) : environ -> mpred :=
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
       field_at Ews t_state (DOT _length) (zv (i_length (m_s m))) (f_sp F);
       head_partH F m; in_rep (f_ib F); crc_table_at (f_tsh F) (f_gv F); mem_x F m; locals_rep F).

Lemma loop_state_exH: forall F m, loop_stateH F m = ex_stateH F m.
Proof.
  intros. unfold loop_stateH, ex_stateH. rewrite mem_rep_split_xH.
  f_equal. unfold SEPx. simpl. rewrite !sepcon_assoc. reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The model                                                                                      *)

(* EXLEN with FEXTRA, after NEEDBITS(16) *)
(* EXLEN without FEXTRA *)
(* EXTRA with FEXTRA: the copy of min(length, have) bytes *)




(* the step of EXLEN *)




(* the step of EXTRA *)


(* ---------------------------------------------------------------------------------------------- *)
(* mwf3 of the fallthrough machines                                                               *)































(* ---------------------------------------------------------------------------------------------- *)
(* mem_x and head_partH under the updates of the cases                                             *)











Lemma head_part_lengthH: forall F m v, head_partH F (upd_s m (fun s => set_i_length s v)) = head_partH F m.
Proof. reflexivity. Qed.
Lemma head_part_chkH: forall F m v, head_partH F (set_m_s m (set_i_check (m_s m) v)) = head_partH F m.
Proof. reflexivity. Qed.
Lemma head_part_initbitsH: forall F m, head_partH F (initbits m) = head_partH F m.
Proof. reflexivity. Qed.
Lemma head_part_nxH: forall F m v, head_partH F (set_m_nx m v) = head_partH F m.
Proof. reflexivity. Qed.
Lemma head_part_leaveH: forall F m, head_partH F (set_leave m) = head_partH F m.
Proof. reflexivity. Qed.
Lemma head_part_modeH: forall F m md, head_partH F (set_mode m md) = head_partH F m.
Proof. reflexivity. Qed.
Lemma head_part_offH: forall F m, i_head (m_s m) = false -> head_partH F m = emp.
Proof. intros F m E. unfold head_partH. rewrite E. reflexivity. Qed.

Ltac x_simplH :=
  rewrite ?mem_x_upd_h, ?mem_x_length, ?mem_x_check, ?mem_x_initbits, ?mem_x_nx, ?mem_x_leave, ?mem_x_mode,
          ?head_part_lengthH, ?head_part_chkH, ?head_part_initbitsH, ?head_part_nxH, ?head_part_leaveH,
          ?head_part_modeH.



(* do { c } while (0) *)


(* ex_stateH with the temporary _t'24 (the condition of CRC2) *)
Definition ex_state_t24H (F: frame) (m: mst) (v: val) : environ -> mpred :=
  PROP (in_ok (f_ib F) (m_inp m); out_ok (f_ob F) (m_aout m))
  LOCAL (temp _t'24 v; temp _strm (f_strmp F); temp _flush (zv (f_flush F)); temp _state (f_sp F);
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
       field_at Ews t_state (DOT _length) (zv (i_length (m_s m))) (f_sp F);
       head_partH F m; in_rep (f_ib F); crc_table_at (f_tsh F) (f_gv F); mem_x F m; locals_rep F).

(* whether crc_if updates the check *)




(* projections of the machine under upd_s / upd_h / set_m_s *)




























































(* ---------------------------------------------------------------------------------------------- *)
(* the extra-field buffer of the gz_header (EXTRA's zmemcpy)                                      *)





(* ex_stateH with the temporary _copy *)
Definition ex_state_copyH (F: frame) (m: mst) (v: val) : environ -> mpred :=
  PROP (in_ok (f_ib F) (m_inp m); out_ok (f_ob F) (m_aout m))
  LOCAL (temp _copy v; temp _strm (f_strmp F); temp _flush (zv (f_flush F)); temp _state (f_sp F);
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
       field_at Ews t_state (DOT _length) (zv (i_length (m_s m))) (f_sp F);
       head_partH F m; in_rep (f_ib F); crc_table_at (f_tsh F) (f_gv F); mem_x F m; locals_rep F).
