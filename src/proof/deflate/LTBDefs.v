(** * The deflate_bound / deflate_bound_split part of the deflate laws theory: definitions

  The invariants [Bpre] / [Brun] of [bound_facts] (LawFacts.v), the
    three bound classes of deflateBound, the accounting of all bits produced ([Gb]) against the bound, and the
    invariant [Mid] of the state inside one deflate() call.

    The accounting: [b = |H| + body c n + tlen w0] ([H] the header bytes, [c] the class, [w0] the wrap).  After the
    header, [Gb s tout <= xb c |H| E k] where [E] is the number of bytes of the [k] blocks emitted so far (none of
    them last, each at least [minblk c] bytes); after the last block, [Gb <= 8 (|H| + body c n)], then the trailer
    adds [8 * tlen w0]. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTIface.
Import ListNotations.
Local Open Scope Z_scope.

(** ** The three bounds of deflateBound *)
Inductive bcls := BTight | BFixed | BStore.

(** deflateBound's test for the tight bound: [w_bits == 15 && hash_bits == 8 + 7] and not Z_FIXED at levels 1..3. *)
Definition tight_b (s : dstate) : bool :=
  (d_w_bits s =? 15) && (d_hash_bits s =? 8 + 7) &&
  negb ((d_strategy s =? Z_FIXED) && (d_level s >=? 1) && (d_level s <=? 3)).

Definition bcls_of (s : dstate) : bcls :=
  if tight_b s then BTight
  else if (d_w_bits s <=? d_hash_bits s) && negb (d_level s =? 0) then BFixed else BStore.

(** The bound without the wrapper (deflateBound minus wraplen). *)
Definition body (c : bcls) (n : Z) : Z :=
  match c with
  | BTight => n + Z.shiftr n 12 + Z.shiftr n 14 + Z.shiftr n 25 + 7
  | BFixed => n + Z.shiftr n 3 + Z.shiftr n 8 + Z.shiftr n 9 + 4
  | BStore => n + Z.shiftr n 5 + Z.shiftr n 7 + Z.shiftr n 11 + 7
  end.

(** The size of the trailer: 4 (zlib), 8 (gzip), 0 (raw). *)
Definition tlen (w : Z) : Z := if w =? 1 then 4 else if w =? 2 then 8 else 0.

(** The least size of a block that is not the last one (Z_NO_FLUSH / Z_FINISH): L - 1 symbols of at least one
    byte each (L = 16384 tight, >= 256 fixed (hash_bits >= w_bits >= 9), >= 128 store), stored blocks of at least
    min(pending_buf_size - 6, w_size) bytes. *)
Definition minblk (c : bcls) : Z := match c with BTight => 16383 | BFixed => 255 | BStore => 127 end.

(** The bit budget of [h] header bytes and [k] non-last blocks of [e] bytes in all: [e + 5k] bytes (tight /
    store: stored blocks or blocks no larger than a stored one), [9 e + 10 k] bits (fixed: static codes, at most 9
    bits per byte, 3 header bits and END_BLOCK's 7). *)
Definition xb (c : bcls) (h e k : Z) : Z :=
  match c with
  | BFixed => 8 * h + 9 * e + 10 * k
  | _ => 8 * (h + e + 5 * k)
  end.

Definition acct (c : bcls) (h e k g : Z) : Prop := 0 <= k /\ minblk c * k <= e /\ g <= xb c h e k.

(** strm->adler is a valid running check value of the wrapper. *)
Definition adler_ok (w a : Z) : Prop :=
  (w = 1 -> Zlib.proof.adler32.Model.adler_valid a) /\ (w = 2 -> 0 <= a < 4294967296).

(** The gzip header given to deflateSetHeader, if any, is one of the harnesses'. *)
Definition gzh_ok (s : dstate) : Prop := forall h, d_gzhead s = Some h -> hdr_ok h.

(** A DFlush event comes from a Huffman compressor (level > 0).  ([ev_ok] does not say it; [cpost_extra]
    below does, proved in LTBound.cpost_extra_ok.) *)
Definition ev_lvl (s0 : dstate) (e : dev) : Prop :=
  match e with DFlush _ _ _ _ _ _ => 0 < d_level s0 | DStored _ _ _ => True end.

(** ** [Bpre]: after deflateInit2 (and deflateSetDictionary, deflateSetHeader) *)
Definition Bpre (W : dstate -> Prop) (level wbits mem strategy : Z) (ds : bool) (s : dstate) (tin tout adler : Z)
    : Prop :=
  W s /\ outok s /\ params_ok level 8 wbits mem strategy = true /\
  d_status s = (if wrap_of wbits =? 2 then GZIP_STATE else INIT_STATE) /\ d_wrap s = wrap_of wbits /\
  d_pending s = 0 /\ d_po s = 0 /\ d_bi_valid s = 0 /\ d_sym_next s = 0 /\ d_lookahead s = 0 /\
  d_strstart s = d_block_start s /\ (ds = false -> d_strstart s = 0 /\ tin = 0) /\
  d_level s = (if level =? -1 then 6 else level) /\ d_strategy s = strategy /\
  d_w_bits s = Z.max 9 (wb_of wbits) /\ d_hash_bits s = mem + 7 /\
  gzh_ok s /\ -2 <= d_last_flush s <= 5 /\
  tout = 0 /\ 0 <= tin <= 32768 /\ adler_ok (d_wrap s) adler.

(** ** [Brun]: between the deflate() calls of deflate_bound(_split), after [b = deflateBound(strm, n)] *)

(** The phase of the stream ([H] the header bytes, [w0] the wrap). *)
Definition bphase (HI : hdr_inv) (n pos : Z) (fin : bool) (s : dstate) (tout adler : Z) (H : list Z) (w0 : Z)
    : Prop :=
  (* P0: nothing done yet *)
  (d_status s = (if w0 =? 2 then GZIP_STATE else INIT_STATE) /\ d_wrap s = w0 /\ H = hdr_bytes s adler /\
   pos = 0 /\ tout = 0 /\ d_pending s = 0 /\ d_bi_valid s = 0 /\ d_sym_next s = 0 /\ ub s = 0 /\
   adler_ok w0 adler) \/
  (* P1: in the middle of the gzip header, its first k bytes handed out or pending (strm->adler: the header
     CRC so far) *)
  (w0 = 2 /\ d_wrap s = 2 /\ (exists k, HI s adler H k /\ tout + d_pending s = k) /\
   pos = 0 /\ d_bi_valid s = 0 /\ d_sym_next s = 0 /\ ub s = 0) \/
  (* P2: compressing; [E] bytes in [k] blocks, none of them last *)
  (d_status s = BUSY_STATE /\ d_wrap s = w0 /\ d_bi_valid s <= 7 /\ adler_ok w0 adler /\
   exists E k, E + ub s = pos /\ acct (bcls_of s) (Zlength H) E k (Gb s tout)) \/
  (* P3: the last block emitted; the trailer not yet put ([d_wrap = w0]) or put ([d_wrap = - w0]) *)
  (d_status s = FINISH_STATE /\ fin = true /\ pos = n /\ ub s = 0 /\ d_sym_next s = 0 /\ d_bi_valid s = 0 /\
   adler_ok w0 adler /\
   ((d_wrap s = w0 /\ Gb s tout <= 8 * (Zlength H + body (bcls_of s) n)) \/
    (0 < w0 /\ d_wrap s = - w0 /\ Gb s tout <= 8 * (Zlength H + body (bcls_of s) n + tlen w0)))).

Definition Brun (W : dstate -> Prop) (HI : hdr_inv) (n b pos : Z) (fin : bool) (s : dstate) (tin tout adler : Z)
    : Prop :=
  exists H w0,
    W s /\ outok s /\ 0 <= w0 <= 2 /\ b = Zlength H + body (bcls_of s) n + tlen w0 /\ Zlength H <= 16384 /\
    0 <= n <= 1048576 /\ 0 <= pos <= n /\ 0 <= tin <= 32768 + pos /\ 0 <= tout /\
    gzh_ok s /\ -2 <= d_last_flush s <= 5 /\
    bphase HI n pos fin s tout adler H w0.

(** ** Inside one deflate() call offered the whole object [inb] and [aout] bytes of output space
    ([tin0] / [tout0] / [pos0]: total_in, total_out and the data position at the call; [gz0] the gzip header) *)
Definition cframe (inb : list Z) (aout tin0 tout0 : Z) (z : strm) : Prop :=
  z_in z = inb /\ 0 <= z_next_in z /\ z_next_in z + z_avail_in z = Zlength inb /\
  z_total_in z = tin0 + z_next_in z /\
  0 <= z_avail_out z /\ Zlength (z_out z) + z_avail_out z = aout /\
  z_total_out z = tout0 + Zlength (z_out z) /\ bytes (z_out z).

Definition Mid (W : dstate -> Prop) (HI : hdr_inv) (n b pos0 : Z) (inb : list Z) (aout tin0 tout0 flush : Z)
    (gz0 : option gzh) (s : dstate) (z : strm) : Prop :=
  cframe inb aout tin0 tout0 z /\ bytes inb /\ 0 <= pos0 /\ pos0 + Zlength inb <= n /\
  (flush = Z_NO_FLUSH \/ flush = Z_FINISH) /\ (flush = Z_FINISH -> pos0 + Zlength inb = n) /\
  0 <= aout <= 1073741824 /\ 0 <= tin0 /\ 0 <= tout0 /\ d_gzhead s = gz0 /\
  Brun W HI n b (pos0 + z_next_in z) (flush =? Z_FINISH) s (z_total_in z) (z_total_out z) (z_adler z).

(** Three facts of the compression call (proved in LTBound.cpost_extra_ok): every
    DFlush event is at level > 0, need_more leaves at most 7 bits in the bit buffer, the output space is not
    overrun. *)
Definition cpost_extra (W : dstate -> Prop) : Prop :=
  forall s z flush s' z' bs evs, cpost W s z flush s' z' bs evs ->
    Forall (ev_lvl s) evs /\ (bs = need_more -> d_bi_valid s' <= 7) /\ 0 <= z_avail_out z'.
