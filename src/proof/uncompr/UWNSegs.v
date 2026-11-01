(* uncompress2_z with a Z_NULL source of length 0 (USpecW.v, snull = true), cut into the segments of UWSegs.v.

   The statements, the cuts and the destination (uw_dq, uw_ob) are UWSegs.v's; only the source differs: the
   code's source is Z_NULL and *sourceLen = 0, there is no source object, len stays 0, next_in stays Z_NULL and
   avail_in 0, and every inflate() call is offered SpecWSelf's InNull input with no bytes.  The assertions are
   UWSegs.v's with src = [], used = 0 and ai = 0 (the source counters of the model's loop UModelW.uncw_loop):
   nothing can be consumed from an empty input.  After avail_in's refill (it writes avail_in = 0 and len = 0)
   the state is the one after avail_out's refill, so un_M1 is the assertion before and after it. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Uncompr.
Require Zlib.units.Inflate.
Require Import Zlib.uncompr.code.
Require Export Zlib.proof.uncompr.UWSegs.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Uncompr.CS.
Local Open Scope logic.

(* the WITH of uncompress2_z_spec_w for snull = true, without the fields that a Z_NULL source fixes *)
Record unargs := UNA {
  n_gv: globals; n_dnull: bool; n_dsh: share; n_dp: val; n_dn: Z; n_dc: list val; n_cap: Z; n_dlp: val;
  n_dtok: bool; n_slp: val; n_gsh: share; n_tsh: share }.

(* its PROP *)
Definition un_facts (A: unargs) : Prop :=
  match A with UNA gv dnull dsh dp dn dc cap dlp dtok slp gsh tsh =>
    dest_ok_w dnull dsh dp dn dc cap dtok /\ readable_share gsh /\ readable_share tsh
  end.

(* the postcondition of the body after start_function *)
Definition POST_un (A: unargs) : ret_assert :=
  match A with UNA gv dnull dsh dp dn dc cap dlp dtok slp gsh tsh =>
  frame_ret_assert
    (function_body_ret_assert tint
       (EX r: Z, EX slen: Z, EX dlen: Z, EX out: list Z,
        PROP (uncompressw_rel [] cap r slen dlen out)
        RETURN (Vint (Int.repr r))
        SEP (dest_rep dnull dsh dp dn (dest_after dc dn out) dtok;
             data_at Tsh tulong (Vlong (Int64.repr dlen)) dlp;
             data_at Tsh tulong (Vlong (Int64.repr slen)) slp;
             uversion_lit gv; inflate_globals gsh tsh gv; mem_mgr gv))%argsassert)
    (stackframe_of f_uncompress2_z)
  end.

(* the precondition of the body after start_function (v: the address of the local stream) *)
Definition PRE_un (A: unargs) (v: val) : environ -> mpred :=
  match A with UNA gv dnull dsh dp dn dc cap dlp dtok slp gsh tsh =>
  PROP ()
  LOCAL (lvar _stream (Tstruct _z_stream_s noattr) v; gvars gv; temp _dest dp; temp _destLen dlp;
         temp _source nullval; temp _sourceLen slp)
  SEP (data_at_ Tsh (Tstruct _z_stream_s noattr) v; dest_rep dnull dsh dp dn dc dtok;
       data_at Tsh tulong (Vlong (Int64.repr cap)) dlp;
       data_at Tsh tulong (Vlong (Int64.repr 0)) slp;
       uversion_lit gv; inflate_globals gsh tsh gv; mem_mgr gv)
  end.

(* the locals that do not change after statement 4 *)
Definition un_lcl (A: unargs) (v: val) : list localdef :=
  match A with UNA gv dnull dsh dp dn dc cap dlp dtok slp gsh tsh =>
  [temp _max (Vint (Int.neg (Int.repr 1))); lvar _stream (Tstruct _z_stream_s noattr) v; gvars gv;
   temp _dest (uw_dq dnull dp v); temp _destLen dlp; temp _source nullval; temp _sourceLen slp]
  end.

(* the resources that the loop does not touch *)
Definition un_fr (A: unargs) : list mpred :=
  match A with UNA gv dnull dsh dp dn dc cap dlp dtok slp gsh tsh =>
  [uw_lit gv; version_lit gv; mem_mgr gv; zfuncs gv;
   data_at Tsh tulong (Vlong (Int64.repr cap)) dlp;
   data_at Tsh tulong (Vlong (Int64.repr 0)) slp;
   tables_rep gsh gv; crc_table_at tsh gv]
  end.

(* before statement 5: len and left read, dest fixed *)
Definition un_A5 (A: unargs) (v: val) : environ -> mpred :=
  match A with UNA gv dnull dsh dp dn dc cap dlp dtok slp gsh tsh =>
  PROPx []
  (LOCALx (temp _len (Vlong (Int64.repr 0)) :: temp _left (Vlong (Int64.repr cap)) :: un_lcl A v)
  (SEPx [data_at_ Tsh (Tstruct _z_stream_s noattr) v; dest_rep dnull dsh dp dn dc dtok;
         data_at Tsh tulong (Vlong (Int64.repr cap)) dlp;
         data_at Tsh tulong (Vlong (Int64.repr 0)) slp;
         uversion_lit gv; inflate_globals gsh tsh gv; mem_mgr gv]))
  end.

(* before statement 10 (inflateInit): next_in = Z_NULL, avail_in = 0, zalloc = zfree = opaque = 0 *)
Definition un_A10 (A: unargs) (v: val) : environ -> mpred :=
  match A with UNA gv dnull dsh dp dn dc cap dlp dtok slp gsh tsh =>
  PROPx []
  (LOCALx (temp _len (Vlong (Int64.repr 0)) :: temp _left (Vlong (Int64.repr cap)) :: un_lcl A v)
  (SEPx [raw_strm gv Tsh v (RF nullval (Vint (Int.repr 0)) Vundef Vundef Vundef Vundef Vundef Vundef Vundef)
           Vundef Vundef nullval nullval nullval;
         dest_rep dnull dsh dp dn dc dtok;
         data_at Tsh tulong (Vlong (Int64.repr cap)) dlp;
         data_at Tsh tulong (Vlong (Int64.repr 0)) slp;
         uversion_lit gv; inflate_globals gsh tsh gv; mem_mgr gv]))
  end.

(* the facts of the loop's stream (m, out) in z and L (next_in Z_NULL), ao the avail_out of the last call *)
Definition un_sfacts (A: unargs) (v: val) (m: mst) (out: list Z) (z: zfields) (L: live) (ao: Z) : Prop :=
  match A with UNA gv dnull dsh dp dn dc cap dlp dtok slp gsh tsh =>
  i_head (m_s m) = false /\ l_s L = m_s m /\ l_h L = m_h m /\ zf_adler z = m_adler m /\ zf_msg z = m_msg m /\
  zf_tin z = m_tin m /\ zf_tout z = m_tout m /\
  zf_ni z = nullval /\ zf_no z = offset_val (Zlength out) (uw_dq dnull dp v) /\
  0 <= ao <= uw_max /\ Zlength out + ao <= cap /\
  raw_live (Some L) = false /\ swfW (l_s L)
  end.

(* the stream and the destination with out written *)
Definition un_sep (A: unargs) (v: val) (out: list Z) (z: zfields) (L: live) : list mpred :=
  match A with UNA gv dnull dsh dp dn dc cap dlp dtok slp gsh tsh =>
  istream gv Tsh v z (Some L) :: dest_rep dnull dsh dp dn (dest_after dc dn out) dtok :: un_fr A
  end.

(* the loop invariant (before avail_out's refill) *)
Definition un_inv (A: unargs) (v: val) : environ -> mpred :=
  match A with UNA gv dnull dsh dp dn dc cap dlp dtok slp gsh tsh =>
  EX m: mst, EX out: list Z, EX z: zfields, EX L: live, EX ao: Z,
  PROPx [reach_w [] cap m 0 out 0 ao; vmode (i_mode (m_s m)); un_sfacts A v m out z L ao;
         zf_ai z = 0; zf_ao z = ao]
  (LOCALx (temp _len (Vlong (Int64.repr 0)) ::
           temp _left (Vlong (Int64.repr (cap - Zlength out - ao))) :: un_lcl A v)
  (SEPx (un_sep A v out z L)))
  end.

(* after avail_out's refill (and after avail_in's, which changes nothing): avail_out is the next call's offer *)
Definition un_M1 (A: unargs) (v: val) : environ -> mpred :=
  match A with UNA gv dnull dsh dp dn dc cap dlp dtok slp gsh tsh =>
  EX m: mst, EX out: list Z, EX z: zfields, EX L: live, EX ao: Z,
  PROPx [reach_w [] cap m 0 out 0 ao; vmode (i_mode (m_s m)); un_sfacts A v m out z L ao;
         zf_ai z = 0; zf_ao z = uw_aout cap out ao]
  (LOCALx (temp _len (Vlong (Int64.repr 0)) ::
           temp _left (Vlong (Int64.repr (cap - Zlength out - uw_aout cap out ao))) :: un_lcl A v)
  (SEPx (un_sep A v out z L)))
  end.

(* after the call err = inflate(&stream, Z_NO_FLUSH) *)
Definition un_LC (A: unargs) (v: val) : environ -> mpred :=
  match A with UNA gv dnull dsh dp dn dc cap dlp dtok slp gsh tsh =>
  EX err: Z, EX m: mst, EX out: list Z, EX z: zfields, EX L: live, EX ao: Z,
  PROPx [-5 <= err <= 2;
         err = Z_OK -> reach_w [] cap m 0 out 0 ao /\ vmode (i_mode (m_s m));
         err <> Z_OK -> uncw_loop [] cap m_first 0 [] 0 0 err 0 out;
         un_sfacts A v m out z L ao; zf_ai z = 0; zf_ao z = ao]
  (LOCALx (temp _err (Vint (Int.repr err)) ::
           temp _len (Vlong (Int64.repr 0)) ::
           temp _left (Vlong (Int64.repr (cap - Zlength out - ao))) :: un_lcl A v)
  (SEPx (un_sep A v out z L)))
  end.

(* after the loop: the loop of the model from the start has ended with err *)
Definition un_brk (A: unargs) (v: val) : environ -> mpred :=
  match A with UNA gv dnull dsh dp dn dc cap dlp dtok slp gsh tsh =>
  EX err: Z, EX m: mst, EX out: list Z, EX z: zfields, EX L: live, EX ao: Z,
  PROPx [err <> Z_OK; -5 <= err <= 2; uncw_loop [] cap m_first 0 [] 0 0 err 0 out;
         un_sfacts A v m out z L ao; zf_ai z = 0; zf_ao z = ao]
  (LOCALx (temp _err (Vint (Int.repr err)) ::
           temp _len (Vlong (Int64.repr 0)) ::
           temp _left (Vlong (Int64.repr (cap - Zlength out - ao))) :: un_lcl A v)
  (SEPx (un_sep A v out z L)))
  end.

(* ---------------------------------------------------------------------------------------------- *)
(* The segment statements                                                                        *)

(* statements 0-4: the checks (they pass since *sourceLen = 0), len, left, dest *)
Definition un_p1_stmt : Prop :=
  forall {Espec: OracleKind} (A: unargs) (v: val), un_facts A ->
  semax Delta_uw (un_A5 A v) uw_seg5 (POST_un A) ->
  semax Delta_uw (PRE_un A v) uw_seg0 (POST_un A).

(* statements 5-9: the stores into the stream *)
Definition un_p2_stmt : Prop :=
  forall {Espec: OracleKind} (A: unargs) (v: val), un_facts A ->
  semax Delta_uw (un_A10 A v) uw_seg10 (POST_un A) ->
  semax Delta_uw (un_A5 A v) uw_seg5 (POST_un A).

(* statements 10-13: inflateInit (Z_MEM_ERROR returns), next_out, avail_out; the loop's entry *)
Definition un_p3_stmt : Prop :=
  forall {Espec: OracleKind} (A: unargs) (v: val), un_facts A -> isptr v ->
  semax Delta_uw (un_inv A v) uw_seg14 (POST_un A) ->
  semax Delta_uw (un_A10 A v) uw_seg10 (POST_un A).

(* the loop *)
Definition un_loop_stmt : Prop :=
  forall {Espec: OracleKind} (A: unargs) (v: val), un_facts A -> isptr v ->
  semax Delta_uw (un_brk A v) uw_seg15 (POST_un A) ->
  semax Delta_uw (un_inv A v) uw_seg14 (POST_un A).

(* the loop's body *)
Definition un_rout_stmt : Prop :=
  forall {Espec: OracleKind} (A: unargs) (v: val), un_facts A -> isptr v ->
  semax Delta_uw (un_inv A v) uw_rout (normal_ret_assert (un_M1 A v)).
Definition un_rin_stmt : Prop :=
  forall {Espec: OracleKind} (A: unargs) (v: val), un_facts A -> isptr v ->
  semax Delta_uw (un_M1 A v) uw_rin (normal_ret_assert (un_M1 A v)).
Definition un_call_stmt : Prop :=
  forall {Espec: OracleKind} (A: unargs) (v: val), un_facts A -> isptr v ->
  semax Delta_uw (un_M1 A v) uw_call_st (normal_ret_assert (un_LC A v)).

(* statements 15-: after the loop *)
Definition un_exit_stmt : Prop :=
  forall {Espec: OracleKind} (A: unargs) (v: val), un_facts A -> isptr v ->
  semax Delta_uw (un_brk A v) uw_seg15 (POST_un A).
