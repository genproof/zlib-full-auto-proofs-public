(* Law rj_bad_checksum (BadTheory.v): the shared definitions of its parts.

   G is the decode context of the true stream O (dc_src G = O, IDecode.dctx_stmt), a zlib or gzip stream; src is
   O with its trailer changed ([bad_src]).  The trailer starts at byte [tpos G] = |O| - trl_len; the header is the
   first [hlen G] bytes.  inflate() on src goes through three phases:
   - the header: the passes read only header bytes, which src shares with O, so the decode theory on G applies
     to the machine with O's bytes in place of src's (BadHdr.v);
   - the blocks: inflate_fast may read bytes of the (changed) trailer ahead and give them back, so the run is
     compared with the run of the RAW deflate stream of the same blocks on the bytes of src after the header
     ([rawctx]: a raw stream may be followed by anything).  The zlib machine and the raw one differ only in
     the fields the block modes never read ([bview]: the wrapper, the check value, the total, the flags, the
     saved bit buffer, strm->next_in) and in the input, which the raw machine sees from the end of the header
     on (shift d) (BadView.v);
   - the trailer: CHECK compares the changed Adler-32 / CRC-32 with the check value of the data and LENGTH the
     changed ISIZE with the total (BadTrl.v): Z_DATA_ERROR, or the call ends with part of the trailer read
     ([chead] at a loop head, [pc_state] between calls). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.rfc1951.Decode7Step.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* The stream and the changed input                                                               *)

(* the length of the header, the position of the trailer *)
Definition hlen (G: dctx) : Z := Zlength (hdr_bytes (dc_w G)).
Definition tpos (G: dctx) : Z := slen G - trl_len (dc_w G).

(* the context of the true stream as the clip laws have it: deflate's zlib or gzip stream, no history, no
   preset dictionary, the input exactly the stream *)
Definition bad_ctx (G: dctx) : Prop :=
  dctx_ok7 G /\ dc_hist G = [] /\ wrapped G = true /\
  (forall wb fl did, dc_w G = WZlib wb fl did -> did = None) /\
  dc_src G = stream_bytes (dc_w G) (dc_hist G) (dc_bs G).

(* src is the stream with its trailer changed *)
Definition bad_src (G: dctx) (src: list Z) : Prop :=
  Zlength src = slen G /\ bytes_ok src /\
  sublist 0 (tpos G) src = sublist 0 (tpos G) (dc_src G) /\
  sublist (tpos G) (slen G) src <> sublist (tpos G) (slen G) (dc_src G).

(* the raw deflate stream of the same blocks on the bytes of src after the header *)
Definition rawctx (G: dctx) (src: list Z) : dctx :=
  DCtx WRaw (dc_wb G) [] (dc_bs G) (- dc_wb G) (sublist (hlen G) (Zlength src) src).

(* ---------------------------------------------------------------------------------------------- *)
(* The raw view of the machine                                                                    *)

(* the modes of the blocks *)
Definition blk_mode (md: Z) : Prop := md_type md \/ md_tab md \/ md_dec md.

(* the machine with: the input from byte d on (next, avail and strm->next_in moved accordingly), the saved
   bit buffer (state->hold, state->bits: hh, bb), wrap, check, total and flags replaced; x is strm->next_in *)
Definition bview (d x hh bb w c t f: Z) (m: mst) : mst :=
  MS (set_i_flags (set_i_total (set_i_check (set_i_wrap (set_i_bits (set_i_hold (m_s m) hh) bb) w) c) t) f)
     (m_h m) (sublist d (Zlength (m_inp m)) (m_inp m)) (m_aout m) (m_nx m - d) (m_ow m) (m_hold m) (m_bits m)
     (m_in m - d) (m_out m) (m_ret m) (m_leave m) (m_adler m) (m_msg m) (m_tin m) (m_tout m) x (m_sow m).

Definition iomap (g: mst -> mst) (o: iout) : iout :=
  match o with IBrk m => IBrk (g m) | IRet r m => IRet r (g m) end.

(* ---------------------------------------------------------------------------------------------- *)
(* The trailer                                                                                    *)

(* the value of bytes read into the bit buffer, the first one least significant *)
Definition le_val (l: list Z) : Z := fold_right (fun b a => b + 256 * a) 0 l.

(* the zlib machine at a loop head in CHECK or LENGTH, in a call that started at byte pos of src with the
   input inp, ob written before the call.  CHECK: the check value and total of the data before the call
   (the call's output, the rest of the data, is not counted yet), k bytes of the trailer in the bit buffer.
   LENGTH (gzip, at the start of a call only): the CRC-32 matched, k bytes of ISIZE in the bit buffer. *)
Definition chead (G: dctx) (src: list Z) (pos: Z) (inp ob: list Z) (m: mst) : Prop :=
  m_inp m = inp /\ 0 <= pos /\ pos + Zlength inp <= Zlength src /\ inp = sublist pos (pos + Zlength inp) src /\
  Zlength inp <= 2 ^ 32 - 1 /\ 0 <= m_nx m <= Zlength inp /\ m_in m = Zlength inp /\
  m_leave m = 0 /\ m_ret m = Z_OK /\ glob_ok G (m_s m) /\ ob ++ m_ow m = full G /\
  Zlength (m_ow m) <= m_aout m <= 2 ^ 32 - 1 /\ m_out m = m_aout m /\
  ((m_mode m = CHECK /\
    i_check (m_s m) = chkv G (produced G ob) /\ i_total (m_s m) = Zlength (produced G ob) mod 2 ^ 64 /\
    exists k, 0 <= k < 4 /\ pos + m_nx m = tpos G + k /\ m_bits m = 8 * k /\
      m_hold m = le_val (sublist (tpos G) (tpos G + k) src)) \/
   (m_mode m = LENGTH /\ (exists h, dc_w G = WGzip h) /\ m_ow m = [] /\
    i_total (m_s m) = Zlength (produced G ob) mod 2 ^ 64 /\
    sublist (tpos G) (tpos G + 4) src = sublist (tpos G) (tpos G + 4) (dc_src G) /\
    exists k, 0 <= k < 4 /\ pos + m_nx m = tpos G + 4 + k /\ m_bits m = 8 * k /\
      m_hold m = le_val (sublist (tpos G + 4) (tpos G + 4 + k) src))).

(* the state between calls after part of the trailer was read: pos bytes of src consumed, out written *)
Definition pc_state (G: dctx) (src: list Z) (pos: Z) (out: list Z) (s: istate) : Prop :=
  out = full G /\ glob_ok G s /\
  ((i_mode s = CHECK /\
    i_check s = chkv G (produced G out) /\ i_total s = Zlength (produced G out) mod 2 ^ 64 /\
    exists k, 0 <= k < 4 /\ pos = tpos G + k /\ i_bits s = 8 * k /\
      i_hold s = le_val (sublist (tpos G) (tpos G + k) src)) \/
   (i_mode s = LENGTH /\ (exists h, dc_w G = WGzip h) /\
    i_total s = Zlength (produced G out) mod 2 ^ 64 /\
    sublist (tpos G) (tpos G + 4) src = sublist (tpos G) (tpos G + 4) (dc_src G) /\
    exists k, 0 <= k < 4 /\ pos = tpos G + 4 + k /\ i_bits s = 8 * k /\
      i_hold s = le_val (sublist (tpos G + 4) (tpos G + 4 + k) src))).
