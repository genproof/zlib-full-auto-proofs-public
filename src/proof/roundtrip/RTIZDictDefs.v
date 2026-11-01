(* RT-I, part rti_zdict: definitions shared by RTIZDict*.v.  The zlib FDICT stream
   O = [zcmf wb; flg] ++ be_bytes (adler dict) 4 ++ ... (RTFinal.dfinal, ANY valid FLG):
   - the first inflate() call (inflateInit2 windowBits 0) stops at DICT with Z_NEED_DICT, its state `zd_nd`;
   - inflateSetDictionary sets the window; the state's TYPE version `d1_ty` (template
     harness/inflate_dict/ITTheoryDefs.v) satisfies the decode invariant `dinv` at pos 6 for the context
     `zd_ctx` (Format's header bytes with FLEVEL 0 in place of O[0..2), never read again). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTIKit.
Require Export Zlib.proof.rfc1951.Decode.
Import ListNotations.
Local Open Scope Z_scope.

(* the state after Z_NEED_DICT: DICT, havedict 0, check = the dictionary id, no window, empty bit buffer; wrap 13 is
   the zlib wrapper 5 with bit 3 that inflateInit2(windowBits 0) stores (patch F8, ApiModel.reset2_wrap 5 0) *)
Definition zd_nd (wb id: Z) (s: istate) : Prop :=
  i_mode s = DICT /\ i_wrap s = 13 /\ i_head s = false /\ i_last s = 0 /\ i_havedict s = 0 /\
  i_total s = 0 /\ i_wsize s = 0 /\ i_whave s = 0 /\ i_wnext s = 0 /\ i_win s = false /\ i_wdata s = [] /\
  i_wbits s = wb /\ i_flags s = 0 /\ i_hold s = 0 /\ i_bits s = 0 /\ i_check s = id.

(* the decode context of the stream after the dictionary: Format's zlib stream (FLEVEL 0) *)
Definition zd_w (dict: list Z) (wb: Z) : wrapper :=
  WZlib wb 0 (Some (Zlib.proof.adler32.Model.ref_adler32 1 dict)).
Definition zd_ctx (wb: Z) (dict: list Z) (bs: list block) : dctx :=
  DCtx (zd_w dict wb) wb dict bs 0 (stream_bytes (zd_w dict wb) dict bs).

(* zlib right after the right dictionary: DICT with havedict 1; its TYPE version *)
Definition d1_ty (s: istate) : istate := set_i_mode (set_i_check s 1) Zlib.proof.inflate.Model.TYPE.

(* the stream fields with adler := a *)
Definition z_adl (z: zfields) (a: Z) : zfields :=
  ZF (zf_ni z) (zf_ai z) (zf_tin z) (zf_no z) (zf_ao z) (zf_tout z) (zf_msg z) (zf_dt z) a (zf_res z).
