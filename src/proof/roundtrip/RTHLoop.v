(* RT-H: Loop.v's loop state WITHOUT the application's gz_header.  In the header modes the header
   (RTHSpec.head_rep6, possibly undefined fields) is held as a separate frame by the header cases; the loop
   state's head part is only the atom `hnoneH` (= emp), so that the case kit ports unchanged (RTH*.v: mechanical
   ports of the inflate area's kit, identifiers whose meaning changes carry the suffix H). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Export Zlib.proof.inflate.Loop.
Require Import Zlib.proof.crc32.Spec.

#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* the place of the header in the loop state: nothing *)
Definition hnoneH (hsh: share) (headp xb nb cb: val) (h: hstate) : mpred := emp.

Definition head_partH (F: frame) (m: mst) : mpred :=
  if i_head (m_s m) then hnoneH (f_hsh F) (f_headp F) (f_xb F) (f_nb F) (f_cb F) (m_h m) else emp.

Definition mem_repH (F: frame) (m: mst) : mpred :=
  state_rep (f_gv F) (f_sp F) (f_strmp F) (f_headp F) (f_winp F) (m_s m) *
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

Definition loop_stateH (F: frame) (m: mst) : environ -> mpred :=
  PROP (in_ok (f_ib F) (m_inp m); out_ok (f_ob F) (m_aout m))
  LOCAL (temp _strm (f_strmp F); temp _flush (zv (f_flush F)); temp _state (f_sp F);
         temp _next (in_ptr (f_ib F) (m_nx m)); temp _put (out_ptr (f_ob F) (Zlength (m_ow m)));
         temp _have (zv (m_have m)); temp _left (zv (m_left m)); temp _hold (lv (m_hold m));
         temp _bits (zv (m_bits m)); temp _in (zv (m_in m)); temp _out (zv (m_out m));
         temp _ret (zv (m_ret m)); temp _leave (zv (m_leave m));
         lvar _here t_code (f_vhere F); lvar _last t_code (f_vlast F);
         lvar _hbuf (tarray tuchar 4) (f_vhbuf F); gvars (f_gv F))
  SEP (mem_repH F m; locals_rep F).

Definition case_postH (F: frame) (m: mst) : ret_assert :=
  {| RA_normal := EX m': mst,
       !! (stepf (f_flush F) lenfix_list distfix_list m = IBrk m') && loop_stateH F m';
     RA_break := FF;
     RA_continue := FF;
     RA_return := fun vl _ => EX r: Z, EX m': mst,
       !! (stepf (f_flush F) lenfix_list distfix_list m = IRet r m' /\ vl = Some (zv r)) &&
       (mem_repH F m' * locals_rep F) |}.

(* the loop state with the head is the headless one and Loop.head_part *)
Lemma mem_rep_headH: forall F m, mem_rep F m = mem_repH F m * head_part F m.
Proof.
  intros. unfold mem_rep, mem_repH, head_partH, hnoneH.
  destruct (i_head (m_s m)); apply pred_ext; cancel.
Qed.
