(** * The deflateBound accounting for the short laws: the invariants

    The accounting of LTBDefs.v (the classes [bcls_of], [body], [tlen], [xb], [acct], the bits produced [Gb],
    the phases [bphase], the call frame [cframe]) for the streams of the short laws: data of up to 2^63-1 bytes
    (harness/res_bound.c, LawFactsW.bw_once: below 2^32, in one deflate(Z_FINISH) call; the clip() loops,
    LawFactsW2.bw_clip: calls of up to 2^32-1 bytes), calls with up to 2^32-1 bytes of output space, a dictionary
    of up to 2^32-1 bytes, the gzip headers [hdr_ok_w] (at most 2^34 bytes).  [BpreW] / [BrunW] /
    [MidW] are LTBDefs' [Bpre] / [Brun] / [Mid] with these limits; the phases and the frame are LTBDefs' own. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTWIface Zlib.proof.deflate.LTBDefs.
Import ListNotations.
Local Open Scope Z_scope.

(** The gzip header given to deflateSetHeader, if any, is one of the short laws'. *)
Definition gzh_ok_w (s : dstate) : Prop := forall h, d_gzhead s = Some h -> hdr_ok_w h.

(** A margin of one bit that the last block leaves when [2^25 <= n] (LTWBArith, LTWBEvent.chain_acct_w state
    the cost of the last block with it; the invariants below do not need it). *)
Definition slk (n : Z) : Z := if n <? 33554432 then 0 else 1.

(** ** After deflateInit2 (and deflateSetDictionary, deflateSetHeader) *)
Definition BpreW (W : dstate -> Prop) (level wbits mem strategy : Z) (ds : bool) (s : dstate) (tin tout adler : Z)
    : Prop :=
  W s /\ outok s /\ params_ok level 8 wbits mem strategy = true /\
  d_status s = (if wrap_of wbits =? 2 then GZIP_STATE else INIT_STATE) /\ d_wrap s = wrap_of wbits /\
  d_pending s = 0 /\ d_po s = 0 /\ d_bi_valid s = 0 /\ d_sym_next s = 0 /\ d_lookahead s = 0 /\
  d_strstart s = d_block_start s /\ (ds = false -> d_strstart s = 0 /\ tin = 0) /\
  d_level s = (if level =? -1 then 6 else level) /\ d_strategy s = strategy /\
  d_w_bits s = Z.max 9 (wb_of wbits) /\ d_hash_bits s = mem + 7 /\
  gzh_ok_w s /\ -2 <= d_last_flush s <= 5 /\
  tout = 0 /\ 0 <= tin <= 4294967295 /\ adler_ok (d_wrap s) adler.

(** ** Between the deflate() calls, after [b = deflateBound(strm, n)] *)
Definition BrunW (W : dstate -> Prop) (HI : hdr_inv) (n b pos : Z) (fin : bool) (s : dstate) (tin tout adler : Z)
    : Prop :=
  exists H w0,
    W s /\ outok s /\ 0 <= w0 <= 2 /\ b = Zlength H + body (bcls_of s) n + tlen w0 /\ Zlength H <= 17179869184 /\
    0 <= n <= 9223372036854775807 /\ 0 <= pos <= n /\ 0 <= tin <= 4294967295 + pos /\ 0 <= tout /\
    gzh_ok_w s /\ -2 <= d_last_flush s <= 5 /\
    bphase HI n pos fin s tout adler H w0.

(** ** Inside one deflate() call offered the whole object [inb] and [aout] bytes of output space
    ([tin0] / [tout0] / [pos0]: total_in, total_out and the data position at the call; [gz0] the gzip header) *)
Definition MidW (W : dstate -> Prop) (HI : hdr_inv) (n b pos0 : Z) (inb : list Z) (aout tin0 tout0 flush : Z)
    (gz0 : option gzh) (s : dstate) (z : strm) : Prop :=
  cframe inb aout tin0 tout0 z /\ bytes inb /\ 0 <= pos0 /\ pos0 + Zlength inb <= n /\
  (flush = Z_NO_FLUSH \/ flush = Z_FINISH) /\ (flush = Z_FINISH -> pos0 + Zlength inb = n) /\
  0 <= aout <= 4294967295 /\ 0 <= tin0 /\ 0 <= tout0 /\ d_gzhead s = gz0 /\
  BrunW W HI n b (pos0 + z_next_in z) (flush =? Z_FINISH) s (z_total_in z) (z_total_out z) (z_adler z).
