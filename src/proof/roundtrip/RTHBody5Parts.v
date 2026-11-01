(* RT-H: mechanical port of inflate_api/Body5Parts.v to the header-external loop state (RTHLoop.v); identifiers whose meaning changes carry the suffix H. *)
(* The parts of inflate()'s body (Body5_inflate.v, v5 specs: Spec5.v, Callees5.v, Model2.v): the
   statements (the prologue, the main loop `for (;;) { switch ...; if (leave) break; }`, the exit
   inf_leave), the loop state with the frame items the body keeps around the loop, the pure invariants
   along the loop (out_inv, win_inv5, hdr_same), and the statements of the parts:
   - pro_part5_stmtH: the prologue, from inflate_spec's precondition to the loop head (or the return of
     Z_STREAM_ERROR);
   - loop_part5_stmtH: the loop, for any pure invariant P preserved by one pass;
   - exit_part5_stmtH: the exit inf_leave;
   - stepf_inv5_stmt, stepf2_hdr_stmt, leave_fin5_stmt: the pure facts (one pass keeps out_inv / the
     window facts / the header's presence and buffer sizes; the machine after inf_leave is a live
     stream's).

   The loop and exit lemmas take the function's return postcondition R abstractly: a return must imply
   RA_return R from the memory after it and the stack variables (ret_ok5H, exit_ok5H, discharged by the body
   assembly), and X is whatever else the body keeps (malloc tokens, padding). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Export Zlib.proof.inflate_api.Bodies5.
Require Export Zlib.proof.roundtrip.RTHCaseHyps5.
Require Import Zlib.proof.crc32.Spec.
Require Export Zlib.proof.inflate_api.Body5Parts.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* ---------------------------------------------------------------------------------------------- *)
(* The statements                                                                                 *)

(* fn_body f_inflate =
     leave = 0; CHK; ST; TY; LD; IN; OUT; RET; inflate_mainloop; inflate_exit
   (CHK: the inflateStateCheck / next_out / next_in test with its return; ST: state = strm->state;
    TY: TYPE -> TYPEDO; LD: LOAD(); IN, OUT, RET: in = have; out = left; ret = Z_OK) *)
(* CHK; ST; TY; LD; IN; OUT; RET *)
(* leave = 0 *)


(* ---------------------------------------------------------------------------------------------- *)
(* The loop state with the frame items                                                            *)

(* loop_stateH (Loop.v) with the header buffers' tokens (CaseHyps5.v hdr_tok), the allocator and the
   stream's zalloc/zfree (updatewindow at the exit) and X: what else the body holds (the state's
   malloc token and padding, the buffers' tokens) *)
Definition lstateH (F: frame) (X: mpred) (m: mst) : environ -> mpred :=
  PROP (in_ok (f_ib F) (m_inp m); out_ok (f_ob F) (m_aout m))
  LOCAL (temp _strm (f_strmp F); temp _flush (zv (f_flush F)); temp _state (f_sp F);
         temp _next (in_ptr (f_ib F) (m_nx m)); temp _put (out_ptr (f_ob F) (Zlength (m_ow m)));
         temp _have (zv (m_have m)); temp _left (zv (m_left m)); temp _hold (lv (m_hold m));
         temp _bits (zv (m_bits m)); temp _in (zv (m_in m)); temp _out (zv (m_out m));
         temp _ret (zv (m_ret m)); temp _leave (zv (m_leave m));
         lvar _here t_code (f_vhere F); lvar _last t_code (f_vlast F);
         lvar _hbuf (tarray tuchar 4) (f_vhbuf F); gvars (f_gv F))
  SEP (mem_repH F m; locals_rep F; hdr_tok F m; mem_mgr (f_gv F); zfuncs (f_gv F); X).

(* the local facts that hold at every return: the stack variables and the globals *)
(* ---------------------------------------------------------------------------------------------- *)
(* The pure invariants along the loop                                                             *)

(* `out` (avail_out at the start, or `left` after CHECK) bounds the bytes counted at the exit:
   left <= out <= the output space, so out - left <= the bytes written; in mode HEAD nothing was
   written yet *)
(* the window facts of a live stream (Spec5.v live_ok): wbits 0 only on a wrapped stream without a
   window, which has not read its header (HEAD, flags -1) or has failed (BAD, SYNC, MEM) *)
(* the header's presence and its buffers' sizes are unchanged (hdr_tok F m' = hdr_tok F m) *)


(* one pass keeps out_inv, the window flag (only the exit allocates the window) and win_inv5
   (pure, Model2.v) *)
(* one pass keeps the header's presence and its buffers' sizes, and the input (pure, Model2.v) *)
(* what the postcondition (istream of a live stream, the stream fields) needs of a final machine *)
(* the machine after inf_leave (Model.v) is a live stream's, with the same header and input;
   data_type is an int *)
(* ---------------------------------------------------------------------------------------------- *)
(* The loop                                                                                       *)

(* a return inside the switch gives the function's return (Q: what holds of the returning machine) *)
Definition ret_ok5H (F: frame) (X: mpred) (m0: mst) (Q: mst -> Prop) (R: ret_assert) : Prop :=
  forall r m', loop2 (f_flush F) lenfix_list distfix_list m0 (IRet r m') -> mwf3 m' -> hd_ok F m' -> Q m' ->
    ENTAIL Delta_inflate5,
      PROPx [] (LOCALx (ret_locals F)
        (SEPx [mem_repH F m'; locals_rep F; hdr_tok F m'; mem_mgr (f_gv F); zfuncs (f_gv F); X]))
      |-- RA_return R (Some (zv r)).

(* the state after the loop: the machine m reached from m0 with leave = 1 *)
Definition loop_exitH (F: frame) (X: mpred) (m0: mst) (P: mst -> Prop) : environ -> mpred :=
  EX m: mst,
    !! (loop2 (f_flush F) lenfix_list distfix_list m0 (IBrk m) /\ mwf3 m /\ hd_ok F m /\ m_leave m = 1 /\
        P m) &&
    lstateH F X m.

(* P: a pure invariant of the loop head, kept by one pass (Q for a returning pass) *)
Definition loop_part5_stmtH : Prop :=
  forall {Espec: OracleKind} (F: frame) (X: mpred) (m0: mst) (P Q: mst -> Prop) (R: ret_assert),
  cases_all5H -> stepf2_mwf3_stmt -> stepf2_hd_stmt -> stepf2_hdr_stmt -> frame_ok5 F ->
  (forall m, mwf3 m -> m_leave m = 0 -> hd_ok F m -> P m ->
     match stepf2 (f_flush F) lenfix_list distfix_list m with IBrk m' => P m' | IRet _ m' => Q m' end) ->
  mwf3 m0 -> m_leave m0 = 0 -> hd_ok F m0 -> P m0 -> ret_ok5H F X m0 Q R ->
  semax Delta_inflate5 (lstateH F X m0) inflate_mainloop (overridePost (loop_exitH F X m0 P) R).

(* ---------------------------------------------------------------------------------------------- *)
(* The exit                                                                                       *)

(* the frame after the exit: the window pointer (updatewindow may allocate it) and strm->data_type *)
(* each outcome of inf_leave (Model.v) gives the function's return; winp is the window pointer after
   the exit (the old one when the window existed) *)
Definition exit_ok5H (F: frame) (X: mpred) (m: mst) (R: ret_assert) : Prop :=
  forall res winp, inf_leave (f_flush F) m res -> (i_win (m_s m) = true -> winp = f_winp F) ->
    ENTAIL Delta_inflate5,
      PROPx [] (LOCALx (ret_locals F)
        (SEPx [mem_repH (set_f_winp_dt F winp (res_dt F res)) (r_m res); locals_rep F; hdr_tok F m;
               mem_mgr (f_gv F); zfuncs (f_gv F); X]))
      |-- RA_return R (Some (zv (r_ret res))).

Definition exit_part5_stmtH : Prop :=
  forall {Espec: OracleKind} (F: frame) (X: mpred) (m: mst) (R: ret_assert),
  frame_ok5 F -> mwf3 m -> m_leave m = 1 -> out_inv m -> win_inv5 (m_s m) -> exit_ok5H F X m R ->
  semax Delta_inflate5 (lstateH F X m) inflate_exit R.

(* ---------------------------------------------------------------------------------------------- *)
(* The prologue                                                                                   *)

(* the frame of the call on a live stream L with the output object o *)
(* what the body keeps besides lstate's items: the state's malloc token and padding, the tokens of the
   input and output objects *)
(* inflate_spec's precondition after start_function *)
(* the loop head after the prologue on a valid call *)
Definition pro_postH (gv: globals) (shs: share) (strmp: val) (z: zfields) (st: option live) (ib: inbuf)
    (inp: list Z) (ob: option outbuf) (flush: Z) (gsh tsh: share) (itok otok: bool) (vh vl vb: val)
    : environ -> mpred :=
  EX L: live, EX o: outbuf,
    !! (st = Some L /\ ob = Some o /\ ~ inflate_bad strmp z st ib ob /\ live_ok L /\ zf_ok z /\
        writable_share shs /\ strmp <> nullval) &&
    lstateH (mkF gv shs strmp L ib o gsh tsh z vh vl vb flush) (xfr L itok otok ib o) (m_init z L inp).

(* leave = 0; the stream checks (return Z_STREAM_ERROR on inflate_bad); state = strm->state;
   TYPE -> TYPEDO; LOAD(); in = have; out = left; ret = Z_OK *)
Definition pro_part5_stmtH : Prop :=
  forall {Espec: OracleKind} (gv: globals) (shs: share) (strmp: val) (z: zfields) (st: option live)
    (ib: inbuf) (inp: list Z) (ob: option outbuf) (flush: Z) (gsh tsh: share) (itok otok: bool)
    (vh vl vb: val) (R: ret_assert),
  Int.min_signed <= flush <= Int.max_signed -> readable_share gsh -> readable_share tsh ->
  in_tok_ok itok ib -> out_tok_ok otok ob -> zf_ni z = in_ptr ib 0 ->
  match ib with InNull => inp = [] | InBuf _ _ _ _ _ => in_ok ib inp /\ zf_ai z = Zlength inp end ->
  match ob with None => zf_no z = nullval | Some o => zf_no z = out_ptr o 0 /\ out_ok o (zf_ao z) end ->
  zf_ai z <= Int.max_signed -> zf_ao z <= Int.max_signed ->
  (inflate_bad strmp z st ib ob ->
   ENTAIL Delta_inflate5,
     PROPx [] (LOCALx [lvar _hbuf (tarray tuchar 4) vb; lvar _last t_code vl; lvar _here t_code vh; gvars gv]
       (SEPx [data_at_ Tsh (tarray tuchar 4) vb; data_at_ Tsh t_code vl; data_at_ Tsh t_code vh;
              istream_opt gv shs strmp z st; head_opt (is_live strmp st);
              bufs_opt (is_live strmp st) ib ob [] itok otok;
              tables_rep gsh gv; crc_table_at tsh gv; mem_mgr gv; zfuncs gv]))
     |-- RA_return R (Some (zv Z_STREAM_ERROR))) ->
  semax Delta_inflate5 (pro_pre gv shs strmp z st ib ob flush gsh tsh itok otok vh vl vb)
    (Ssequence inflate_leave0 inflate_pre)
    (overridePost (pro_postH gv shs strmp z st ib inp ob flush gsh tsh itok otok vh vl vb) R).
