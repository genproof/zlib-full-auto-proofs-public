(* The prologue and the exit of inflate()'s body for calls of any uInt size (avail_in, avail_out up to 2^32 - 1),
   in the headless world of the port src/proof/hl (the gz_header is a frame the caller holds).

   [exit_part9_stmt]: the exit inf_leave from a machine with the WIDE invariant InvW.mwf3W (the port's
   HlBody5Parts.exit_part5_stmt_hl has the narrow Inv3.mwf3).  [pro_part9_stmt]: the prologue with any header
   part Hd (RTHCase.pro_part6_stmt without its bounds avail_in, avail_out <= 2^31 - 1).  Both are stated in the
   contexts of the narrow proofs (Delta_inflate5_hl, Delta_inflate5), which are sub-contexts of
   RTH9Defs.Delta_inflate9 fast for the inflate_fast specification of RTH9Defs.fast9_stmt. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.roundtrip.RTHSpec.
Require Export Zlib.proof.roundtrip.RTH8Defs.
Require Export Zlib.proof.roundtrip.RTH9Defs.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* the exit inf_leave from a wide machine *)
Definition exit_part9_stmt : Prop :=
  forall {Espec: OracleKind} (F: frame) (X: mpred) (m: mst) (R: ret_assert),
  frame_ok5 F -> mwf3W m -> m_leave m = 1 -> out_inv m -> win_inv5 (m_s m) -> exit_ok5_hl F X m R ->
  semax Delta_inflate5_hl (lstate_hl F X m) inflate_exit R.

(* the prologue, for a call of any uInt size *)
Definition pro_part9_stmt : Prop :=
  forall {Espec: OracleKind} (gv: globals) (shs: share) (strmp: val) (z: zfields) (st: option live)
    (ib: inbuf) (inp: list Z) (ob: option outbuf) (flush: Z) (gsh tsh: share) (itok otok: bool)
    (vh vl vb: val) (Hd: mpred) (R: ret_assert),
  Int.min_signed <= flush <= Int.max_signed -> readable_share gsh -> readable_share tsh ->
  in_tok_ok itok ib -> out_tok_ok otok ob -> zf_ni z = in_ptr ib 0 ->
  match ib with InNull => inp = [] | InBuf _ _ _ _ _ => in_ok ib inp /\ zf_ai z = Zlength inp end ->
  match ob with None => zf_no z = nullval | Some o => zf_no z = out_ptr o 0 /\ out_ok o (zf_ao z) end ->
  (inflate_bad strmp z st ib ob ->
   ENTAIL Delta_inflate5,
     PROPx [] (LOCALx [lvar _hbuf (tarray tuchar 4) vb; lvar _last t_code vl; lvar _here t_code vh; gvars gv]
       (SEPx [data_at_ Tsh (tarray tuchar 4) vb; data_at_ Tsh t_code vl; data_at_ Tsh t_code vh;
              istream_opt gv shs strmp z st; Hd; htok6 (is_live strmp st);
              bufs_opt (is_live strmp st) ib ob [] itok otok;
              tables_rep gsh gv; crc_table_at tsh gv; mem_mgr gv; zfuncs gv]))
     |-- RA_return R (Some (zv Z_STREAM_ERROR))) ->
  semax Delta_inflate5 (pro_pre6 gv shs strmp z st ib ob flush gsh tsh itok otok vh vl vb Hd)
    (Ssequence inflate_leave0 inflate_pre)
    (overridePost (pro_post6 gv shs strmp z st ib inp ob flush gsh tsh itok otok vh vl vb Hd) R).
