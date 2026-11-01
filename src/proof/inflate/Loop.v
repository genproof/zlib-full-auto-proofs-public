(* The state of inflate()'s main loop (at the head of `for (;;)`, and after the switch), for the
   per-case lemmas: the frame of the call (pointers, shares, buffers: frame) and the machine (mst).

   The input of the call is m_inp at next_in on entry: an object (InBuf) holding them at [lo, lo + |inp|),
   or next_in = NULL (InNull, with no input).  The output space is an object (OutBuf) of which
   [lo, lo + aout) is offered; the machine's m_ow are the bytes written there so far. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Export Zlib.proof.inflate.Rep.
Require Import Zlib.proof.crc32.Spec.

#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Inductive inbuf := InNull | InBuf (sh: share) (p: val) (lo n: Z) (cont: list val).
Inductive outbuf := OutBuf (sh: share) (p: val) (lo n: Z) (cont: list val).

Definition in_ptr (ib: inbuf) (k: Z) : val :=
  match ib with InNull => nullval | InBuf _ p lo _ _ => offset_val (lo + k) p end.
Definition out_ptr (ob: outbuf) (k: Z) : val :=
  match ob with OutBuf _ p lo _ _ => offset_val (lo + k) p end.

Definition in_rep (ib: inbuf) : mpred :=
  match ib with InNull => emp | InBuf sh p _ n c => data_at sh (tarray tuchar n) c p end.
Definition out_rep (ob: outbuf) (ow: list Z) : mpred :=
  match ob with OutBuf sh p lo n c =>
    data_at sh (tarray tuchar n) (sublist 0 lo c ++ byte_vals ow ++ sublist (lo + Zlength ow) n c) p
  end.

(* the input object holds the bytes inp *)
Definition in_ok (ib: inbuf) (inp: list Z) : Prop :=
  match ib with
  | InNull => inp = []
  | InBuf sh p lo n c => readable_share sh /\ isptr p /\ 0 <= lo /\ lo + Zlength inp <= n /\
      Zlength c = n /\ n <= Ptrofs.max_unsigned /\ sublist lo (lo + Zlength inp) c = byte_vals inp /\
      bytes_ok inp
  end.
(* the output object offers aout bytes *)
Definition out_ok (ob: outbuf) (aout: Z) : Prop :=
  match ob with OutBuf sh p lo n c => writable_share sh /\ isptr p /\ 0 <= lo /\ 0 <= aout /\
      lo + aout <= n /\ Zlength c = n /\ n <= Ptrofs.max_unsigned
  end.

(* the frame of one inflate() call *)
Record frame := Fr {
  f_gv : globals; f_shs : share; f_strmp : val; f_sp : val; f_headp : val; f_winp : val;
  f_hsh : share; f_xb : val; f_nb : val; f_cb : val;
  f_ib : inbuf; f_ob : outbuf; f_gsh : share; f_tsh : share; f_dt : Z; f_vres : val;
  f_vhere : val; f_vlast : val; f_vhbuf : val; f_flush : Z }.

(* the head part: the gz_header when state->head is set *)
Definition head_part (F: frame) (m: mst) : mpred :=
  if i_head (m_s m) then head_rep (f_hsh F) (f_headp F) (f_xb F) (f_nb F) (f_cb F) (m_h m) else emp.

(* the memory at the loop head and after the switch, without the stack variables here/last/hbuf *)
Definition mem_rep (F: frame) (m: mst) : mpred :=
  state_rep (f_gv F) (f_sp F) (f_strmp F) (f_headp F) (f_winp F) (m_s m) *
  win_rep (f_winp F) (m_s m) *
  head_part F m *
  strm_rep (f_gv F) (f_shs F) (f_strmp F)
    (in_ptr (f_ib F) (m_snx m)) (zv (Zlength (m_inp m) - m_snx m)) (m_tin m)
    (out_ptr (f_ob F) (m_sow m)) (zv (m_aout m - m_sow m)) (m_tout m)
    (msg_val (f_gv F) (m_msg m)) (f_sp F) (f_dt F) (m_adler m) (f_vres F) *
  in_rep (f_ib F) *
  out_rep (f_ob F) (m_ow m) *
  tables_rep (f_gsh F) (f_gv F) *
  crc_table_at (f_tsh F) (f_gv F).

(* the stack variables of inflate() (any contents) *)
Definition locals_rep (F: frame) : mpred :=
  data_at_ Tsh t_code (f_vhere F) * data_at_ Tsh t_code (f_vlast F) *
  data_at_ Tsh (tarray tuchar 4) (f_vhbuf F).

(* the loop head (leave = 0) and after the switch (leave = m_leave m) *)
Definition loop_state (F: frame) (m: mst) : environ -> mpred :=
  PROP (in_ok (f_ib F) (m_inp m); out_ok (f_ob F) (m_aout m))
  LOCAL (temp _strm (f_strmp F); temp _flush (zv (f_flush F)); temp _state (f_sp F);
         temp _next (in_ptr (f_ib F) (m_nx m)); temp _put (out_ptr (f_ob F) (Zlength (m_ow m)));
         temp _have (zv (m_have m)); temp _left (zv (m_left m)); temp _hold (lv (m_hold m));
         temp _bits (zv (m_bits m)); temp _in (zv (m_in m)); temp _out (zv (m_out m));
         temp _ret (zv (m_ret m)); temp _leave (zv (m_leave m));
         lvar _here t_code (f_vhere F); lvar _last t_code (f_vlast F);
         lvar _hbuf (tarray tuchar 4) (f_vhbuf F); gvars (f_gv F))
  SEP (mem_rep F m; locals_rep F).

(* the postcondition of one pass of the switch (stated through switch_ret_assert):
   a break leaves the switch with the machine stepf gives; a return returns its value *)
Definition case_post (F: frame) (m: mst) : ret_assert :=
  {| RA_normal := EX m': mst,
       !! (stepf (f_flush F) lenfix_list distfix_list m = IBrk m') && loop_state F m';
     RA_break := FF;
     RA_continue := FF;
     RA_return := fun vl _ => EX r: Z, EX m': mst,
       !! (stepf (f_flush F) lenfix_list distfix_list m = IRet r m' /\ vl = Some (zv r)) &&
       (mem_rep F m' * locals_rep F) |}.
