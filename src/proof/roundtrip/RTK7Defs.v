(* The deflate side of the round trips without deflate_roundtrip's size limits: the invariant [K7] of
   RTK7.kfacts7 and the statements of its parts.

   RTDTheory.rt_kfacts proves kfacts for [Krt3] = [Iapi W3 hinv] (safety, the deflate laws' theory) /\ [KF3]
   (functional, RTDV3.v).  Both halves are stated for calls of at most 2^30 bytes (LTDefs.zin_ok,
   LTCSpecs.zall: total_out + avail_out <= 2^41), a dictionary of at most 32768 bytes and gzip header fields of at
   most 4096 bytes.  Here:

   - [zin_ok7] / [zall7]: the stream of a call as the C types allow it: avail_in and avail_out any uInt, total_in
     any uLong, total_out + avail_out at most 2^64 - 1 (total_out is the output produced so far, so it does not
     wrap inside a call);
   - [cpost7]: what a compression call guarantees on such a stream.  It is LTDefs.cpost except in ONE case, a
     zlib defect: deflate_stored compares [len] with [left + strm->avail_in] in 32-bit unsigned arithmetic
     (deflate.c, "len != left + s->strm->avail_in" and "last = flush == Z_FINISH && len == left + ..."; the
     model's ds_body has the same u32).  When left + avail_in >= 2^32 and len equals the wrapped sum, a final
     stored block of only [len] bytes is written and finish_done is returned with input left (e.g. 100 bytes
     in the window, avail_in = 2^32 - 50, avail_out = 55, Z_FINISH: a final block of 50 bytes).  Then deflate()
     returns Z_STREAM_END with avail_in <> 0 (raw), or Z_OK in FINISH_STATE with input left, after which no call
     returns Z_STREAM_END (any further input after Z_FINISH in FINISH_STATE is Z_BUF_ERROR);
   - [core_facts7 W] / [hdr_facts7 HI]: the parts of LTIface.core_facts / hdr_facts the round trips use, for
     these streams, the dictionary of up to 2^32 - 1 bytes and the headers of RTK7.rhdr_ok7;
   - [hinv7]: the header invariant of the deflate laws (LTHdrKit.hinv) for the headers rhdr_ok7;
   - [comp_fspec7]: RTDV3.comp_fspec3 for these streams, with the same exception;
   - [Iapi7]: LTApiDefs.Iapi for these limits (total_in modulo 2^64; with a dictionary it also counted the bytes
     of the dictionary read into the window);
   - [Stuck7]: FINISH_STATE with input left after Z_FINISH (the defect above);
   - [K7] = (Iapi7 W3 hinv7 /\ KF3) \/ Stuck7, and one statement per field of kfacts7. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTK7.
Require Export Zlib.proof.roundtrip.RTDV3.
Require Export Zlib.proof.roundtrip.RTDLTApiDefs Zlib.proof.roundtrip.RTDLTHdrKit.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** The stream of a call, any sizes *)

(* LTDefs.zin_ok for the C types *)
Definition zin_ok7 (z : strm) : Prop :=
  bytes (z_in z) /\ 0 <= z_next_in z /\ 0 <= z_avail_in z <= 4294967295 /\
  z_next_in z + z_avail_in z <= Zlength (z_in z) /\ 0 <= z_avail_out z <= 4294967295 /\
  0 <= z_total_in z <= 18446744073709551615 /\
  0 <= z_total_out z /\ z_total_out z + z_avail_out z <= 18446744073709551615.

(* LTCSpecs.zin_in / zout_ok / zall for the C types *)
Definition zin_in7 (z : strm) : Prop :=
  bytes (z_in z) /\ 0 <= z_next_in z /\ 0 <= z_avail_in z <= 4294967295 /\
  z_next_in z + z_avail_in z <= Zlength (z_in z) /\ 0 <= z_total_in z < 18446744073709551616.
Definition zout_ok7 (z : strm) : Prop :=
  0 <= z_avail_out z <= 4294967295 /\ 0 <= z_total_out z /\
  z_total_out z + z_avail_out z <= 18446744073709551615.
Definition zall7 (z : strm) : Prop := zin_in7 z /\ zout_ok7 z.

(* the defect of deflate_stored (see the head of this file): a final block with input left *)
Definition stored_cut (s : dstate) (z' : strm) (flush : Z) (bs : bstate) : Prop :=
  d_level s = 0 /\ flush = Z_FINISH /\ bs = finish_done /\ 0 < z_avail_in z'.

Definition cpost7 (W : dstate -> Prop) (s : dstate) (z : strm) (flush : Z)
    (s' : dstate) (z' : strm) (bs : bstate) (evs : list dev) : Prop :=
  cpost W s z flush s' z' bs evs \/ stored_cut s z' flush bs.

(** ** The core facts the round trips use, for these streams *)
Record core_facts7 (W : dstate -> Prop) : Prop := {
  cf7_prm : forall s, W s -> prm s;
  cf7_pos : forall s, W s ->
    0 <= d_lookahead s /\ 0 <= d_strstart s /\ - 1099511627776 <= d_block_start s <= d_strstart s /\
    d_strstart s + d_lookahead s <= 2 * d_w_size s;
  cf7_frame : forall s s', W s -> core_eq s s' -> W s';
  (** deflateSetDictionary: a dictionary of up to 2^32 - 1 bytes (the last w_size bytes go to the window when it
      is longer; the Adler-32 is of the whole dictionary); total_in moves modulo 2^64 *)
  cf7_dict : forall s z d,
    W s -> 0 <= d_wrap s <= 1 -> bad_state s = false -> (d_wrap s = 1 -> d_status s = INIT_STATE) ->
    d_strstart s = 0 -> d_lookahead s = 0 -> d_block_start s = 0 ->
    bytes d -> Zlength d <= 4294967295 -> 0 <= z_total_in z <= 18446744073709551615 ->
    adler_pre (d_wrap s) (z_adler z) ->
    exists s' z' k,
      c_deflateSetDictionary s z (Some d) = Some (s', z', Z_OK) /\ W s' /\
      api_eq s s' /\ out_eq s s' /\ same_prm s s' /\
      d_lookahead s' = 0 /\ d_strstart s' = d_block_start s' /\
      (d_strstart s' = 0 <-> d = []) /\
      d_sym_next s' = d_sym_next s /\ 0 <= k <= Zlength d /\
      z' = mkST (z_in z) (z_next_in z) (z_avail_in z) (u64 (z_total_in z + k)) (z_out z) (z_avail_out z)
                (z_total_out z)
                (if d_wrap s =? 1 then Zlib.proof.adler32.Model.ref_adler32 (z_adler z) d else z_adler z)
                (z_msg z);
  (** the compression stage (with deflate_stored's defect) *)
  cf7_compress : forall s z flush,
    W s -> outok s -> quiet s -> 0 <= flush <= 5 -> zin_ok7 z ->
    0 <= d_wrap s <= 2 -> adler_pre (d_wrap s) (z_adler z) ->
    exists s' z' bs evs, c_compress_func s z flush = Some (s', z', bs) /\ cpost7 W s z flush s' z' bs evs;
  cf7_still : forall s z flush s' z' bs,
    W s -> outok s -> quiet s -> 0 <= flush <= 5 -> zin_ok7 z ->
    0 <= d_wrap s <= 2 -> adler_pre (d_wrap s) (z_adler z) ->
    c_compress_func s z flush = Some (s', z', bs) ->
    ub s = 0 -> d_strstart s = 0 -> z_next_in z' = z_next_in z -> d_strstart s' = 0;
  cf7_full : forall s,
    W s -> d_lookahead s = 0 -> d_strstart s = d_block_start s ->
    exists s1, c_clear_hash s = Some s1 /\ W (full_reset s1) /\
      api_eq s s1 /\ out_eq s s1 /\ same_prm s s1 /\ d_sym_next s1 = d_sym_next s
}.

(** ** The gzip header *)

(* LTHdrKit.hinv for the headers of the short laws *)
Definition hinv7 : hdr_inv := fun s a H k =>
  d_wrap s = 2 /\
  exists h xfl, d_gzhead s = Some h /\ rhdr_ok7 h /\ H = gz_hdr_bytes (Some h) xfl /\
  ((d_status s = EXTRA_STATE /\ gz_extra h <> None /\ d_gzindex s < gz_extra_len h) \/
   (d_status s = NAME_STATE /\ gz_name h <> None) \/
   (d_status s = COMMENT_STATE /\ gz_comment h <> None) \/
   (d_status s = HCRC_STATE /\ gz_hcrc h <> 0)) /\
  gidx_ok h (d_status s) (d_gzindex s) /\ k = gpos h (d_status s) (d_gzindex s) /\ a = hadler h H k.

(* LTIface.hdr_pre for these headers and any output space *)
Definition hdr_pre7 (HI : hdr_inv) (s : dstate) (z : strm) (H : list Z) (k : Z) : Prop :=
  prm s /\ outok s /\ d_pending s = 0 /\ d_sym_next s = 0 /\ d_bi_valid s = 0 /\
  0 <= z_avail_out z <= 4294967295 /\ 0 <= z_total_out z /\
  z_total_out z + z_avail_out z <= 18446744073709551615 /\
  (forall h, d_gzhead s = Some h -> rhdr_ok7 h) /\
  ((d_status s = INIT_STATE /\ 0 <= d_wrap s <= 1 /\ H = hdr_bytes s (z_adler z) /\ k = 0) \/
   (d_status s = GZIP_STATE /\ d_wrap s = 2 /\ H = hdr_bytes s (z_adler z) /\ k = 0) \/
   HI s (z_adler z) H k).

Record hdr_facts7 (HI : hdr_inv) : Prop := {
  hf7_frame : forall s s' a H k, HI s a H k ->
    d_status s' = d_status s -> d_gzindex s' = d_gzindex s -> d_gzhead s' = d_gzhead s ->
    d_wrap s' = d_wrap s -> d_pending_buf_size s' = d_pending_buf_size s -> HI s' a H k;
  hf7_status : forall s a H k, HI s a H k ->
    d_wrap s = 2 /\ (exists h, d_gzhead s = Some h) /\
    (d_status s = EXTRA_STATE \/ d_status s = NAME_STATE \/ d_status s = COMMENT_STATE \/
     d_status s = HCRC_STATE) /\
    (exists xfl, H = gz_hdr_bytes (d_gzhead s) xfl) /\ 10 <= k < Zlength H;
  hf7_run : forall s z H k, hdr_pre7 HI s z H k ->
    exists s' z' r, hdr_stages s z = Some (s', z', r) /\ hdr_post HI s z H k s' z' r
}.

(** ** The functional specifications of the parts that touch the stream, for these streams *)

(* RTDFix.fpend_fspec2 with any output space *)
Definition fpend_fspec7 : Prop :=
  forall s z s' z',
    outok s -> zout_ok7 z -> (d_bi_valid s < 8 \/ d_po s = 0) -> c_flush_pending s z = Some (s', z') ->
    exists x, zout_only z z' x /\ F.bytes_bits (x ++ pend s') ++ bibits s' = F.bytes_bits (pend s) ++ bibits s.

(* RTDV3.comp_fspec3 for these streams; deflate_stored may end in its defect instead *)
Definition comp_fspec7 (f : Z) (c : dstate -> strm -> Z -> option (dstate * strm * bstate)) : Prop :=
  forall s z flush s' z' bs dict D BS syms p,
    W3 s -> outok s -> quiet s -> 0 <= flush <= 5 -> zin_ok7 z -> 0 <= d_wrap s <= 2 ->
    adler_pre (d_wrap s) (z_adler z) -> fn_of s = f ->
    Forall F.byte_ok dict -> bytes D -> kcore3 dict D BS syms s ->
    0 <= p -> (p - d_bi_valid s) mod 8 = 0 ->
    c s z flush = Some (s', z', bs) ->
    (exists k x BS' syms',
      zstep (d_wrap s) z z' k x /\
      kcore3 dict (D ++ sublist (z_next_in z) (z_next_in z + k) (z_in z)) (BS ++ BS') syms' s' /\
      F.bytes_bits (x ++ pend s') ++ bibits s' = bibits s ++ enc_out p BS' (fin_bs bs) /\
      (fin_bs bs = true -> BS' <> [])) \/
    stored_cut s z' flush bs.

(** ** The invariant between the calls *)
Section Inv7.
Variable W : dstate -> Prop.
Variable HI : hdr_inv.

(* LTApiDefs.Iapi: a dictionary of up to 2^32 - 1 bytes, the headers rhdr_ok7, total_in = the data consumed
   plus the bytes of the dictionary deflateSetDictionary counted, modulo 2^64 *)
Definition Iapi7 : rinv := fun dict wrap D O fin s tin tout adler =>
  W s /\ outok s /\ 0 <= wrap <= 2 /\ (wrap = 2 -> dict = []) /\ bytes dict /\ Zlength dict <= 4294967295 /\
  -2 <= d_last_flush s <= 5 /\ (forall h, d_gzhead s = Some h -> rhdr_ok7 h) /\
  tout = Zlength O /\ bytes O /\ bytes D /\ Zlength D <= 18446744073709551615 /\
  (exists k, 0 <= k <= Zlength dict /\ tin = u64 (Zlength D + k)) /\
  (d_status s = FINISH_STATE -> fin = Some []) /\
  (D = [] -> d_lookahead s = 0 /\ d_strstart s = d_block_start s /\ (dict = [] -> d_strstart s = 0)) /\
  (ph0 dict wrap D O s tin adler \/
   (d_last_flush s <> -2 /\
    (ph1 HI dict wrap D O s tin adler \/ ph2 dict wrap D O s tin adler \/ ph3 dict wrap D O s tin adler))).

End Inv7.

(* FINISH_STATE with input left after Z_FINISH: no call ends the stream any more *)
Definition Stuck7 : rinv := fun dict wrap D O fin s tin tout adler =>
  d_status s = FINISH_STATE /\ exists R, fin = Some R /\ R <> [].

Definition K7 : rinv := fun dict wrap D O fin s tin tout adler =>
  (Iapi7 W3 hinv7 dict wrap D O fin s tin tout adler /\ KF3 dict wrap D O fin s tin tout adler) \/
  Stuck7 dict wrap D O fin s tin tout adler.

(** ** The fields of kfacts7 for a given K (verbatim from RTK7.kfacts7) *)
Definition kf7_init_stmt (K : rinv) : Prop :=
  forall level method wbits mem strategy a1 a2 a3 a4 a5 z s z',
    rs32 level -> rs32 method -> rs32 wbits -> rs32 mem -> rs32 strategy ->
    c_deflateInit2_ true true false level method wbits mem strategy a1 a2 a3 a4 a5 z = Some (Some s, z', Z_OK) ->
    d_w_bits s = rwbe wbits /\ d_gzhead s = None /\
    K [] (rwrap_of wbits) [] [] None s (z_total_in z') (z_total_out z') (z_adler z').

Definition kf7_dict_stmt (K : rinv) : Prop :=
  forall wrap s tin tout adler d ain aout msg s' z' code,
    K [] wrap [] [] None s tin tout adler -> rbytes d -> Zlength d <= 4294967295 ->
    0 <= ain <= 4294967295 -> 0 <= aout <= 4294967295 ->
    c_deflateSetDictionary s (rzcall [] 0 ain tin aout tout adler msg) (Some d) = Some (s', z', code) ->
    (code = Z_OK \/ code = Z_STREAM_ERROR) -> (code = Z_STREAM_ERROR <-> wrap = 2) ->
    d_w_bits s' = d_w_bits s /\ d_gzhead s' = d_gzhead s /\
    K (if wrap =? 2 then [] else d) wrap [] [] None s' (z_total_in z') (z_total_out z') (z_adler z').

Definition kf7_head_stmt (K : rinv) : Prop :=
  forall dict s tin tout adler h,
    K dict 2 [] [] None s tin tout adler -> rhdr_ok7 h ->
    K dict 2 [] [] None (set_d_gzhead s (Some h)) tin tout adler.

Definition kf7_deflate_stmt (K : rinv) : Prop :=
  forall dict wrap D O fin s tin tout adler inb aout flush msg s' z' code,
    K dict wrap D O fin s tin tout adler ->
    0 <= flush <= 5 -> rbytes inb -> Zlength inb <= 4294967295 -> Zlength D + Zlength inb <= 2 ^ 64 - 1 ->
    0 <= aout <= 4294967295 -> Zlength O + aout <= 2 ^ 64 - 1 ->
    (forall R, fin = Some R -> flush = Z_FINISH /\ inb = R) ->
    c_deflate s (rzcall inb 0 (Zlength inb) tin aout tout adler msg) flush = Some (s', z', code) ->
    d_gzhead s' = d_gzhead s -> rcall_ok inb aout tin tout z' ->
    (code = Z_OK \/ code = Z_STREAM_END \/ code = Z_BUF_ERROR) ->
    (code = Z_STREAM_END -> flush = Z_FINISH /\ z_avail_in z' = 0) ->
    (code = Z_BUF_ERROR -> z_avail_in z' = Zlength inb /\ z_avail_out z' = aout) ->
    d_w_bits s' = d_w_bits s /\
    (let used := Zlength inb - z_avail_in z' in
     let D' := D ++ sublist 0 used inb in
     let O' := O ++ z_out z' in
     if code =? Z_STREAM_END then dfinal dict wrap (d_w_bits s) (d_gzhead s) D' O'
     else K dict wrap D' O' (if flush =? Z_FINISH then Some (sublist used (Zlength inb) inb) else None)
            s' (z_total_in z') (z_total_out z') (z_adler z')).

Lemma kfacts7_of : forall K,
  kf7_init_stmt K -> kf7_dict_stmt K -> kf7_head_stmt K -> kf7_deflate_stmt K -> kfacts7 K.
Proof. intros K A B C D. constructor; assumption. Qed.

(** ** The statements of the parts *)

(* the wide core of the deflate laws' theory for its invariant W3 (from the wide port of LTCore) *)
Definition core7_stmt : Prop := Zlib.proof.huffman.Overlay.overlay_statement -> core_facts7 W3.

(* the wide header theory for hinv7 (from the wide port of LTHdr) *)
Definition hdr7_stmt : Prop := hdr_facts7 hinv7.

(* the functional compression functions on these streams *)
Definition comp7_stmt : Prop :=
  Zlib.proof.huffman.Overlay.overlay_statement ->
  comp_fspec7 0 c_deflate_stored /\ comp_fspec7 1 c_deflate_fast /\ comp_fspec7 2 c_deflate_slow /\
  comp_fspec7 3 c_deflate_huff /\ comp_fspec7 4 c_deflate_rle.
