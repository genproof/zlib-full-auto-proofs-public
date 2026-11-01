(** * The model theory of the deflate laws: shared definitions

    The theory of LawTheory.v is split into four parts, each an existential package like LawFacts.v:
    - LTCore.v  [core_facts W]: the compressors and everything that touches the window, the hash chains and the
      trees.c state (deflateInit2_'s reset, deflateTune, deflateSetDictionary, deflateParams' level change, the
      Z_FULL_FLUSH reset), over an invariant [W] of the state that the core part chooses;
    - LTHdr.v   [hdr_facts HI]: the zlib / gzip header stages of deflate(), over an invariant [HI] of a stream in
      the middle of a gzip header that the header part chooses;
    - LTApi.v   [api_facts] from [core_facts] and [hdr_facts];
    - LTBound.v [bound_facts] from [core_facts], [hdr_facts] and lemma (ii).
    This file: the concrete notions all four share. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LawFacts.
Require Export Zlib.proof.huffman.Bits Zlib.proof.huffman.Overlay Zlib.proof.huffman.BlockBound.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** Parts of the state *)

(** lit_bufsize, and the bytes pending_buf[pending_out .. pending_out + pending) waiting for next_out *)
Definition d_L (s : dstate) : Z := tr_lit_bufsize (d_tr s).
Definition d_bi_valid (s : dstate) : Z := o_bi_valid (tr_out (d_tr s)).
Definition pend (s : dstate) : list Z :=
  sublist (d_po s) (d_po s + d_pending s) (o_buf (tr_out (d_tr s))).

(** The static parameters of a live stream (deflateInit2_ with accepted parameters). *)
Definition prm (s : dstate) : Prop :=
  9 <= d_w_bits s <= 15 /\ d_w_size s = 2 ^ d_w_bits s /\ d_w_mask s = d_w_size s - 1 /\
  8 <= d_hash_bits s <= 16 /\ d_hash_size s = 2 ^ d_hash_bits s /\ d_hash_mask s = d_hash_size s - 1 /\
  d_hash_shift s = (d_hash_bits s + 2) / 3 /\
  d_L s = 2 ^ (d_hash_bits s - 1) /\ d_pending_buf_size s = 4 * d_L s /\
  Zlength (o_buf (tr_out (d_tr s))) = 4 * d_L s /\ Zlength (d_pbm s) = 4 * d_L s /\
  tr_sym_end (d_tr s) = 3 * (d_L s - 1) /\
  0 <= d_level s <= 9 /\ 0 <= d_strategy s <= 4 /\ d_method s = 8.

(** The pending output: pending_buf's defined bytes are bytes, the bit buffer is sane, the pending bytes are
    defined and inside the buffer, and pending_out is at the start when nothing is pending. *)
Definition outok (s : dstate) : Prop :=
  mb_ok (d_pb s) /\ bits_ok (tr_out (d_tr s)) /\
  0 <= d_po s /\ d_po s + d_pending s <= d_pending_buf_size s /\
  mb_defined (d_pb s) (d_po s) (d_po s + d_pending s) /\
  (d_pending s = 0 -> d_po s = 0).

(** Nothing pending, whole bytes flushed: the state in which deflate() enters the compression stage. *)
Definition quiet (s : dstate) : Prop := d_pending s = 0 /\ d_po s = 0 /\ d_bi_valid s <= 7.

(** The bytes read into the window that no block covers yet. *)
Definition ub (s : dstate) : Z := d_strstart s - d_block_start s + d_lookahead s.

(** All bits produced so far: [tout] bytes handed out (total_out), the pending bytes, the bit buffer. *)
Definition Gb (s : dstate) (tout : Z) : Z := 8 * (tout + d_pending s) + d_bi_valid s.

(** ** Relations between two states *)

(** The fields deflate()'s own stages change (status, pending_out, wrap, gzhead, gzindex, last_flush and the
    output part of trees.c's state: pending_buf outside the symbols, pending, the bit buffer, the mask) blanked;
    everything else (window, hash chains, positions, configuration, trees, symbol count, ...) kept. *)
Definition strip (s : dstate) : dstate :=
  mkDS 0 0 0 None 0 (d_method s) 0 (d_w_size s) (d_w_bits s) (d_w_mask s) (d_window s) (d_window_size s)
       (d_prev s) (d_head s) (d_ins_h s) (d_hash_size s) (d_hash_bits s) (d_hash_mask s) (d_hash_shift s)
       (d_block_start s) (d_match_length s) (d_prev_match s) (d_match_available s) (d_strstart s)
       (d_match_start s) (d_lookahead s) (d_prev_length s) (d_max_chain_length s) (d_max_lazy_match s)
       (d_good_match s) (d_nice_match s) (d_insert s) (d_high_water s) (d_slid s) (d_pending_buf_size s)
       (set_out (d_tr s) (mkOut [] 0 0 0 0)) [].

(** The symbols tallied so far: sym_buf = pending_buf + lit_bufsize, [sym_next] bytes, with their mask. *)
Definition sym_region (s : dstate) : list Z * list bool :=
  (sublist (d_L s) (d_L s + d_sym_next s) (o_buf (tr_out (d_tr s))),
   sublist (d_L s) (d_L s + d_sym_next s) (d_pbm s)).

(** [s'] differs from [s] only in what deflate()'s stages (headers, trailer, flush_pending, _tr_align, the
    empty stored block) change; the tallied symbols are kept. *)
Definition core_eq (s s' : dstate) : Prop :=
  strip s' = strip s /\ sym_region s' = sym_region s /\
  Zlength (o_buf (tr_out (d_tr s'))) = Zlength (o_buf (tr_out (d_tr s))) /\ Zlength (d_pbm s') = Zlength (d_pbm s).

(** The API part unchanged. *)
Definition api_eq (s s' : dstate) : Prop :=
  d_status s' = d_status s /\ d_wrap s' = d_wrap s /\ d_gzhead s' = d_gzhead s /\
  d_gzindex s' = d_gzindex s /\ d_last_flush s' = d_last_flush s /\ d_method s' = d_method s.

(** The output part unchanged. *)
Definition out_eq (s s' : dstate) : Prop :=
  tr_out (d_tr s') = tr_out (d_tr s) /\ d_pbm s' = d_pbm s /\ d_po s' = d_po s.

(** The parameters that deflateBound and the costs depend on, unchanged. *)
Definition same_prm (s s' : dstate) : Prop :=
  d_w_bits s' = d_w_bits s /\ d_w_size s' = d_w_size s /\ d_hash_bits s' = d_hash_bits s /\
  d_L s' = d_L s /\ d_pending_buf_size s' = d_pending_buf_size s /\
  d_level s' = d_level s /\ d_strategy s' = d_strategy s.

(** ** The stream during a call *)

(** The input of a call: bytes, next_in / avail_in inside the object, sizes far from any wrap-around. *)
Definition zin_ok (z : strm) : Prop :=
  bytes (z_in z) /\ 0 <= z_next_in z /\ 0 <= z_avail_in z <= 1073741824 /\
  z_next_in z + z_avail_in z <= Zlength (z_in z) /\ 0 <= z_avail_out z <= 1073741824 /\
  0 <= z_total_in z <= 1099511627776 /\ 0 <= z_total_out z <= 1099511627776.

(** strm->adler after read_buf consumed [data] ([wrap]: 1 Adler-32, 2 CRC-32, else unchanged). *)
Definition adler_upd (wrap a : Z) (data : list Z) : Z :=
  if wrap =? 1 then Zlib.proof.adler32.Model.ref_adler32 a data
  else if wrap =? 2 then Zlib.proof.crc32.Model.ref_crc32 a data else a.

Definition adler_pre (wrap a : Z) : Prop :=
  (wrap = 1 -> Zlib.proof.adler32.Model.adler_valid a) /\ (wrap = 2 -> 0 <= a < 2 ^ 32).

(** [z'] is [z] after consuming [k] input bytes (with the checksum of [wrap]) and writing [x] to next_out. *)
Definition zstep (wrap : Z) (z z' : strm) (k : Z) (x : list Z) : Prop :=
  z_in z' = z_in z /\ 0 <= k <= z_avail_in z /\
  z_next_in z' = z_next_in z + k /\ z_avail_in z' = z_avail_in z - k /\
  z_total_in z' = u64 (z_total_in z + k) /\
  z_adler z' = adler_upd wrap (z_adler z) (sublist (z_next_in z) (z_next_in z + k) (z_in z)) /\
  z_out z' = z_out z ++ x /\ Zlength x <= z_avail_out z /\ z_avail_out z' = z_avail_out z - Zlength x /\
  z_total_out z' = u64 (z_total_out z + Zlength x) /\ z_msg z' = z_msg z.

(** [z'] is [z] after writing [x] to next_out and setting adler to [a'] (the header stages). *)
Definition zout_step (z z' : strm) (x : list Z) (a' : Z) : Prop :=
  z_in z' = z_in z /\ z_next_in z' = z_next_in z /\ z_avail_in z' = z_avail_in z /\
  z_total_in z' = z_total_in z /\
  z_out z' = z_out z ++ x /\ z_avail_out z' = z_avail_out z - Zlength x /\
  z_total_out z' = u64 (z_total_out z + Zlength x) /\ z_adler z' = a' /\ z_msg z' = z_msg z.

(** ** The blocks a call of a compression function emits

    [DFlush g t syms buf stored_len last]: a _tr_flush_block call (FLUSH_BLOCK_ONLY) on the trees state [t] (with
    its symbols [syms], the window bytes [buf] or [None] for block_start < 0, [stored_len], [last]), when the
    count of all bits produced ([Gb]) is [g].  [DStored g len last]: a stored block of deflate_stored ([len]
    bytes, from the window and / or directly from next_in).  Between the events [Gb] does not change
    (flush_pending moves bytes, the tallies write only sym_buf). *)
Inductive dev :=
| DFlush (g : Z) (t : tstate) (syms : list (Z * Z)) (buf : option (list Z)) (stored_len last : Z)
| DStored (g len last : Z).

Definition ev_g (e : dev) : Z := match e with DFlush g _ _ _ _ _ => g | DStored g _ _ => g end.
Definition ev_len (e : dev) : Z := match e with DFlush _ _ _ _ sl _ => sl | DStored _ len _ => len end.
Definition ev_last (e : dev) : Z := match e with DFlush _ _ _ _ _ l => l | DStored _ _ l => l end.

(** [Gb] after the event: the bits _tr_flush_block adds, or a stored block's 3 header bits, the padding to a
    byte, LEN / NLEN and the [len] bytes. *)
Definition ev_after (e : dev) : Z :=
  match e with
  | DFlush g t _ buf sl last =>
      g - bitpos (tr_out t) + bitpos (tr_out (fst (tr_flush_block t buf sl last)))
  | DStored g len _ => 8 * ((g + 10) / 8) + 32 + 8 * len
  end.

Fixpoint ev_chain (g : Z) (evs : list dev) (g' : Z) : Prop :=
  match evs with
  | [] => g' = g
  | e :: r => ev_g e = g /\ ev_chain (ev_after e) r g'
  end.

Definition sum_len (evs : list dev) : Z := fold_right (fun e a => ev_len e + a) 0 evs.

(** The last block of the stream is the last event; no other is marked last. *)
Definition last_ev (evs : list dev) : Prop :=
  exists evs0 e, evs = evs0 ++ [e] /\ ev_last e = 1 /\ Forall (fun e => ev_last e = 0) evs0.

(** What is known of each block ([s0]: the state at the start of the call, [flush] the call's flush). *)
Definition ev_ok (s0 : dstate) (flush : Z) (e : dev) : Prop :=
  match e with
  | DFlush g t syms buf sl last =>
      0 < d_level s0 /\ flush_pre t syms /\
      (exists T, 0 <= T /\ g = 8 * T + bitpos (tr_out t)) /\
      tr_lit_bufsize t = d_L s0 /\ tr_level t = d_level s0 /\ tr_strategy t = d_strategy s0 /\
      0 <= last <= 1 /\ (last = 1 -> flush = Z_FINISH) /\
      (last = 0 -> Zlength syms = d_L s0 - 1 \/ (flush <> Z_NO_FLUSH /\ flush <> Z_FINISH)) /\
      sl = blk_len syms /\
      match buf with
      | Some b => Zlength b = sl /\ bytes b /\ sl <= 65535
      | None => d_w_size s0 - MIN_LOOKAHEAD < sl
      end /\
      (* every match is at a distance of at most MAX_DIST *)
      (forall x, In x syms -> fst x <> 0 -> fst x <= d_w_size s0 - MIN_LOOKAHEAD) /\
      (* deflate_slow (levels 4..9) drops matches of length 3 farther than TOO_FAR unless Z_FILTERED *)
      (4 <= d_level s0 -> d_strategy s0 <> Z_FILTERED ->
       forall x, In x syms -> fst x <> 0 -> snd x = 0 -> fst x <= TOO_FAR)
  | DStored g len last =>
      d_level s0 = 0 /\ 0 <= len <= MAX_STORED /\ 0 <= last <= 1 /\ (last = 1 -> flush = Z_FINISH) /\
      (last = 0 -> (flush <> Z_NO_FLUSH /\ flush <> Z_FINISH) \/
                   Z.min (d_pending_buf_size s0 - 6) (d_w_size s0) <= len)
  end.

(** What a call of a compression function ([c_compress_func s z flush = Some (s', z', bs)], blocks [evs])
    guarantees. *)
Definition cpost (W : dstate -> Prop) (s : dstate) (z : strm) (flush : Z)
    (s' : dstate) (z' : strm) (bs : bstate) (evs : list dev) : Prop :=
  W s' /\ outok s' /\ same_prm s s' /\ api_eq s s' /\
  (exists k x, zstep (d_wrap s) z z' k x /\ bytes x /\ k + ub s = sum_len evs + ub s') /\
  ev_chain (Gb s (z_total_out z)) evs (Gb s' (z_total_out z')) /\
  Forall (ev_ok s flush) evs /\
  match bs with
  | need_more =>
      Forall (fun e => ev_last e = 0) evs /\ d_bi_valid s' <= 7 /\
      (flush = Z_NO_FLUSH \/ z_avail_out z' = 0 \/ d_level s = 0)
  | block_done =>
      Forall (fun e => ev_last e = 0) evs /\ flush <> Z_NO_FLUSH /\ flush <> Z_FINISH /\
      z_avail_in z' = 0 /\ ub s' = 0 /\ quiet s' /\ d_sym_next s' = 0
  | finish_started =>
      last_ev evs /\ flush = Z_FINISH /\ z_avail_in z' = 0 /\ ub s' = 0 /\ d_sym_next s' = 0 /\
      d_bi_valid s' = 0 /\ z_avail_out z' = 0 /\ (d_level s <> 0 -> d_pending s' <> 0 \/ d_wrap s <> 0)
  | finish_done =>
      last_ev evs /\ flush = Z_FINISH /\ z_avail_in z' = 0 /\ ub s' = 0 /\ d_sym_next s' = 0 /\
      quiet s' /\ d_bi_valid s' = 0
  end.

(** ** deflateParams after its optional deflate(strm, Z_BLOCK): the level / strategy change (the [None] branch
    of [c_deflateParams], verbatim). *)
Definition params_tail (s : dstate) (level strategy : Z) : option dstate :=
  let* s :=
    (if negb (d_level s =? level) then
       let* s := (if (d_level s =? 0) && negb (d_matches s =? 0) then
                    let* s := (if d_matches s =? 1 then c_slide_hash s else c_clear_hash s) in
                    Some (set_d_matches s 0)
                  else Some s) in
       let s := set_d_level s level in
       let '(good, lazy, nice, chain, _) := Znth level config_table in
       let s := set_d_max_lazy_match s lazy in
       let s := set_d_good_match s good in
       let s := set_d_nice_match s nice in
       Some (set_d_max_chain_length s chain)
     else Some s) in
  Some (set_d_strategy s strategy).

(** deflateTune's assignments. *)
Definition tune_set (s : dstate) (good lazy nice chain : Z) : dstate :=
  set_d_max_chain_length (set_d_nice_match (set_d_max_lazy_match (set_d_good_match s (u32 good)) (u32 lazy)) nice)
    (u32 chain).

(** The Z_FULL_FLUSH reset of deflate() after CLEAR_HASH (lookahead = 0). *)
Definition full_reset (s : dstate) : dstate := set_d_insert (set_d_block_start (set_d_strstart s 0) 0) 0.

(** ** The header bytes *)

(** putShortMSB(s, b): the two bytes put_byte stores. *)
Definition msb2 (b : Z) : list Z := [u8 (Z.shiftr b 8); u8 (Z.land b 255)].

(** The zlib header (RFC 1950) with the dictionary id [a] when a dictionary was set (strstart != 0). *)
Definition zlib_hdr_bytes (s : dstate) (a : Z) : list Z :=
  msb2 (zlib_header s) ++
  (if d_strstart s =? 0 then [] else msb2 (u32 (Z.shiftr a 16)) ++ msb2 (u32 (Z.land a 65535))).

(** The gzip header (RFC 1952) of deflateSetHeader's [h], with the XFL byte [xfl]. *)
Definition gz_pre (h : gzh) (xfl : Z) : list Z :=
  map u8 [31; 139; 8; gz_flags h; Z.land (gz_time h) 255; Z.land (Z.shiftr (gz_time h) 8) 255;
          Z.land (Z.shiftr (gz_time h) 16) 255; Z.land (Z.shiftr (gz_time h) 24) 255; xfl; Z.land (gz_os h) 255].
Definition gz_extra_bytes (h : gzh) : list Z :=
  match gz_extra h with
  | Some x => map u8 [Z.land (gz_extra_len h) 255; Z.land (Z.shiftr (gz_extra_len h) 8) 255] ++
              sublist 0 (Z.land (gz_extra_len h) 65535) x
  | None => []
  end.
Definition cstr_bytes (o : option (list Z)) : list Z := match o with Some l => l | None => [] end.
Definition gz_body (h : gzh) (xfl : Z) : list Z :=
  gz_pre h xfl ++ gz_extra_bytes h ++ cstr_bytes (gz_name h) ++ cstr_bytes (gz_comment h).
Definition gz_hdr_bytes (o : option gzh) (xfl : Z) : list Z :=
  match o with
  | None => [31; 139; 8; 0; 0; 0; 0; 0; xfl; OS_CODE]
  | Some h =>
      gz_body h xfl ++
      (if gz_hcrc h =? 0 then []
       else let c := Zlib.proof.crc32.Model.ref_crc32 0 (gz_body h xfl) in
            [Z.land c 255; Z.land (Z.shiftr c 8) 255])
  end.

(** The header deflate() writes for the state [s] (wrap 1: zlib, 2: gzip, 0: none) with strm->adler [a]. *)
Definition hdr_bytes (s : dstate) (a : Z) : list Z :=
  if d_wrap s =? 1 then zlib_hdr_bytes s a
  else if d_wrap s =? 2 then gz_hdr_bytes (d_gzhead s) (xfl_byte s)
  else [].

(** strm->adler when the header is complete: 1 (zlib), 0 (gzip), unchanged (raw). *)
Definition hdr_adler (wrap a : Z) : Z := if wrap =? 1 then 1 else if wrap =? 2 then 0 else a.

(** Stages 2 to 7 of deflate(): the zlib header, GZIP, EXTRA, NAME, COMMENT, HCRC. *)
Definition hdr_stages (s : dstate) (z : strm) : option dres :=
  then_stage (c_deflate_zlib_header s z) (fun s z =>
  then_stage (c_deflate_gzip_header s z) (fun s z =>
  then_stage (c_deflate_extra s z) (fun s z =>
  then_stage (c_deflate_name s z) (fun s z =>
  then_stage (c_deflate_comment s z) (fun s z =>
  c_deflate_hcrc s z))))).

(** ** Small facts *)

Lemma then_stage_assoc : forall r f g,
  then_stage (then_stage r f) g = then_stage r (fun s z => then_stage (f s z) g).
Proof.
  intros r f g. unfold then_stage. destruct r as [[[s z] [c|]]|]; reflexivity.
Qed.

Lemma then_stage_none : forall r, then_stage r (fun s z => Some (s, z, None)) = r.
Proof. intros r. unfold then_stage. destruct r as [[[s z] [c|]]|]; reflexivity. Qed.

(** deflate() as entry stage, header stages, compression stage, trailer. *)
Lemma c_deflate_stages : forall s z flush,
  c_deflate s z flush =
  if bad_state s || (flush >? Z_BLOCK) || (flush <? 0) then Some (s, z, Z_STREAM_ERROR) else
  let* (s, z, o) :=
    then_stage (then_stage (c_deflate_entry s z flush) hdr_stages) (fun s z => c_deflate_compress s z flush) in
  match o with
  | Some r => Some (s, z, r)
  | None => c_deflate_trailer s z flush
  end.
Proof.
  intros s z flush. unfold c_deflate.
  destruct (bad_state s || (flush >? Z_BLOCK) || (flush <? 0)); [reflexivity|].
  unfold hdr_stages, then_stage, bind.
  destruct (c_deflate_entry s z flush) as [[[s1 z1] [c1|]]|]; try reflexivity.
  destruct (c_deflate_zlib_header s1 z1) as [[[s2 z2] [c2|]]|]; try reflexivity.
  destruct (c_deflate_gzip_header s2 z2) as [[[s3 z3] [c3|]]|]; try reflexivity.
  destruct (c_deflate_extra s3 z3) as [[[s4 z4] [c4|]]|]; try reflexivity.
  destruct (c_deflate_name s4 z4) as [[[s5 z5] [c5|]]|]; try reflexivity.
  destruct (c_deflate_comment s5 z5) as [[[s6 z6] [c6|]]|]; try reflexivity.
Qed.

(** The header stages do nothing once the header is done. *)
Lemma hdr_stages_busy : forall s z,
  d_status s = BUSY_STATE \/ d_status s = FINISH_STATE -> hdr_stages s z = Some (s, z, None).
Proof.
  intros s z H. unfold hdr_stages, c_deflate_zlib_header, c_deflate_gzip_header, c_deflate_extra,
    c_deflate_name, c_deflate_comment, c_deflate_hcrc, then_stage.
  destruct s; simpl in H; destruct H as [H|H]; subst; reflexivity.
Qed.
