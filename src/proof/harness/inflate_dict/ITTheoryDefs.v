(* Law inflate_dict, the theory: THE definitions shared by ITTheory*.v.

   The invariant `it_I` of ITFacts.v's it_inv, by phase:
   - zlib, before the dictionary: `pre_st` (HEAD with p <= 1 header bytes in the bit buffer, or DICTID with the
     2 header bytes and p - 2 bytes of the dictionary id read), no output, total_out 0, no window;
   - zlib, after Z_NEED_DICT (nd): `nd_st` (DICT, havedict 0, check = the dictionary id, 6 bytes consumed);
   - dictionary set: `post_st` = the decode invariant `dinv` (rfc1951/DecodeDefs.v) for the context
     `itd G` (wrapper, wb, history = the dictionary, blocks, iw, input = it_src G) with the output
     dict ++ data[0..opos), plus the window `win_st` (wbits = wb, wsize = 2^wb, window = last bytes of the output);
     or `d1_st`: zlib right after the dictionary (DICT with havedict 1): its TYPE version `d1_ty` (check 1)
     satisfies post_st at pos 6 (the first inflate() call from there behaves as the call from the TYPE version). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Export Zlib.proof.harness.inflate_dict.ITFacts.
Require Export Zlib.proof.rfc1951.Decode.
Import ListNotations.
Local Open Scope Z_scope.

(* the decode context of the stream (history = the dictionary; the input is exactly the stream) *)
Definition itd (G: it_ghost) : dctx :=
  DCtx (it_wrapper G) (g_wb G) (g_dict G) (g_bs G) (g_iw G) (it_src G).

(* the output after opos data bytes, the history included *)
Definition it_out (G: it_ghost) (opos: Z) : list Z := g_dict G ++ sublist 0 opos (it_data G).

(* inflateInit2_'s wrap and wbits for the harness's windowBits (wrap with bit 3 set when the window size comes from
   the header, wb = 0: inflateReset2 of patch F8) *)
Definition it_wrap (G: it_ghost) : Z :=
  match reset2_wb (g_iw G) with Some (w, b) => reset2_wrap w b | None => 0 end.
Definition it_wb0 (G: it_ghost) : Z := match reset2_wb (g_iw G) with Some (_, b) => b | None => 0 end.

(* little-endian value of bytes (the bit buffer after pulling them from bits = 0) *)
Fixpoint it_le (l: list Z) : Z :=
  match l with [] => 0 | b :: l' => b + 256 * it_le l' end.

(* ---------------------------------------------------------------------------------------------- *)
(* zlib before the dictionary                                                                     *)

Definition pre_common (G: it_ghost) (s: istate) : Prop :=
  i_wrap s = it_wrap G /\ i_head s = false /\ i_last s = 0 /\ i_havedict s = 0 /\ i_total s = 0 /\
  i_wsize s = 0 /\ i_whave s = 0 /\ i_wnext s = 0 /\ i_win s = false /\ i_wdata s = [].

(* pos bytes of the stream consumed *)
Definition pre_st (G: it_ghost) (pos: Z) (s: istate) : Prop :=
  pre_common G s /\
  ((i_mode s = HEAD /\ i_wbits s = it_wb0 G /\ 0 <= pos <= 1 /\ i_bits s = 8 * pos /\
    i_hold s = it_le (sublist 0 pos (it_src G))) \/
   (i_mode s = DICTID /\ i_wbits s = g_wb G /\ i_flags s = 0 /\ 2 <= pos <= 5 /\ i_bits s = 8 * (pos - 2) /\
    i_hold s = it_le (sublist 2 pos (it_src G)))).

(* after Z_NEED_DICT (6 bytes consumed) *)
Definition nd_st (G: it_ghost) (s: istate) : Prop :=
  pre_common G s /\ i_mode s = DICT /\ i_wbits s = g_wb G /\ i_flags s = 0 /\ i_hold s = 0 /\ i_bits s = 0 /\
  i_check s = it_dictid G.

(* ---------------------------------------------------------------------------------------------- *)
(* the dictionary set                                                                             *)

(* the window's shape (Inv.swf's window facts) *)
Definition wstruct (s: istate) : Prop :=
  0 <= i_whave s <= i_wsize s /\ 0 <= i_wnext s < i_wsize s /\
  (i_whave s < i_wsize s -> i_wnext s = i_whave s) /\ Zlength (i_wdata s) = i_whave s.

(* the window holds the last min(|out|, 2^wb) bytes of out *)
Definition win_st (G: it_ghost) (s: istate) (out: list Z) : Prop :=
  i_wbits s = g_wb G /\ i_wsize s = 2 ^ g_wb G /\ i_win s = true /\ wstruct s /\ win_ok (itd G) s out.

(* between calls: pos bytes consumed, opos data bytes produced, total_out tout *)
Definition post_st (G: it_ghost) (pos opos tout: Z) (s: istate) : Prop :=
  0 <= opos <= Zlength (it_data G) /\ dinv (itd G) pos (it_out G opos) s tout /\ win_st G s (it_out G opos).

(* zlib right after the right dictionary: DICT, havedict 1; its TYPE version *)
Definition d1_ty (s: istate) : istate := set_i_mode (set_i_check s 1) Zlib.proof.inflate.Model.TYPE.
Definition d1_st (G: it_ghost) (tout: Z) (s: istate) : Prop :=
  g_zlib G = true /\ i_mode s = DICT /\ i_havedict s = 1 /\ post_st G 6 0 tout (d1_ty s).

(* the stream fields with adler := a *)
Definition z_adl (z: zfields) (a: Z) : zfields :=
  ZF (zf_ni z) (zf_ai z) (zf_tin z) (zf_no z) (zf_ao z) (zf_tout z) (zf_msg z) (zf_dt z) a (zf_res z).

(* ---------------------------------------------------------------------------------------------- *)
(* The invariant                                                                                  *)

Definition it_I : it_inv := fun G pos opos dset nd z L =>
  let s := l_s L in
  it_ok G /\ wbits_ok (g_iw G) = true /\ 0 <= pos <= Zlength (it_src G) /\ 0 <= opos <= Zlength (it_data G) /\
  match dset, nd with
  | false, false => g_zlib G = true /\ opos = 0 /\ zf_tout z = 0 /\ pre_st G pos s
  | false, true => g_zlib G = true /\ opos = 0 /\ pos = 6 /\ zf_tout z = 0 /\ nd_st G s
  | true, false => post_st G pos opos (zf_tout z) s \/ (pos = 6 /\ opos = 0 /\ d1_st G (zf_tout z) s)
  | true, true => False
  end.

(* ---------------------------------------------------------------------------------------------- *)
(* The frame of one inflate() call (run2 from Spec5.m_init): the input and avail_out on entry are kept,
   wbits is kept (outside a wrapped HEAD), the state stays well-formed (Inv.swf), the output written fits *)
Definition frame_stmt : Prop :=
  forall flush z L inp res,
    live_ok L -> zf_ok z -> zf_ao z <= Int.max_signed -> Zlength inp <= Int.max_signed -> bytes_ok inp ->
    run2 flush lenfix_list distfix_list (m_init z L inp) res ->
    m_inp (r_m res) = inp /\ m_aout (r_m res) = zf_ao z /\
    (i_mode (l_s L) <> HEAD \/ i_wrap (l_s L) = 0 -> i_wbits (m_s (r_m res)) = i_wbits (l_s L)) /\
    (r_ret res <> Z_MEM_ERROR -> swf (m_s (r_m res)) /\ 0 <= m_sow (r_m res) <= m_aout (r_m res)).
