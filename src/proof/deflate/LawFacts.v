(** * The interface between the model theory and the harness mains of the three deflate laws

    The mains of harness/deflate_api.c (with deflate_common.h's deflate_run), harness/deflate_bound.c and
    harness/deflate_bound_split.c call the API through the shared specifications of DSpec.v, whose
    preconditions are checked model runs [c_f args = Some r].  This file states, in pure Coq over the checked
    model (DModel3.v, DModel4.v), exactly what the mains need about these runs, for EVERY call they make:

    - [api_facts I Iend] for deflate_api: an invariant [I dict wrap D O fin s tin tout adler] of a live stream
      between calls ([dict] the dictionary set ([] if none), [wrap] 0 raw / 1 zlib / 2 gzip, [D] the data
      consumed so far, [O] the output produced so far, [fin = Some R] once Z_FINISH was given, [R] the input
      not yet consumed since; [s] the state; [tin], [tout], [adler] the z_stream fields total_in, total_out,
      adler) and an invariant [Iend s] of a stream after Z_STREAM_END, with one fact per call of the harness;
    - [bound_facts Bpre Brun] for deflate_bound and deflate_bound_split: [Bpre level wbits mem strategy ds s
      tin tout adler] after deflateInit2 / deflateSetDictionary / deflateSetHeader ([ds]: a dictionary was
      set), [Brun n b pos fin s tin tout adler] after [b = deflateBound(strm, n)] ([pos] bytes of the data
      consumed so far, [fin]: Z_FINISH given).

    The invariants are abstract: the theory (LawTheory.v) chooses them ([exists I Iend, api_facts I Iend]),
    the mains only use the facts.  The model's stream of a call is [zmk inb nin ain tin aout tout adler msg]
    (DSpec.zmk): the input object [inb] with next_in at [nin], [ain] bytes offered, [aout] bytes of output
    space; the harnesses always offer a whole new input object ([nin = 0], [ain = Zlength inb]). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.DModel4.
Require Zlib.proof.adler32.Model Zlib.proof.crc32.Model.
Import ListNotations.
Local Open Scope Z_scope.

(** ** Ranges and the harness's own computations *)
Definition s32 (x : Z) : Prop := -2147483648 <= x <= 2147483647.
Definition u32r (x : Z) : Prop := 0 <= x <= 4294967295.
Definition u64r (x : Z) : Prop := 0 <= x <= 18446744073709551615.
Definition bytes (l : list Z) : Prop := Forall (fun b => 0 <= b < 256) l.

(** The model's stream of an API call (= DSpec.zmk). *)
Definition zcall (inb : list Z) (nin ain tin aout tout adler : Z) (msg : option Z) : strm :=
  mkST inb nin ain tin [] aout tout adler msg.

(** deflate_common.h: [R->wrap] and [R->wb] of windowBits, and deflate_params_ok. *)
Definition wrap_of (wbits : Z) : Z := if wbits <? 0 then 0 else if wbits >? 15 then 2 else 1.
Definition wb_of (wbits : Z) : Z := if wbits <? 0 then - wbits else if wbits >? 15 then wbits - 16 else wbits.

Definition params_ok (level method wbits mem strategy : Z) : bool :=
  let lv := if level =? -1 then 6 else level in
  negb (wbits <? -15) && (1 <=? mem) && (mem <=? 9) && (method =? 8) &&
  (8 <=? wb_of wbits) && (wb_of wbits <=? 15) && (0 <=? lv) && (lv <=? 9) &&
  (0 <=? strategy) && (strategy <=? 4) && (negb (wb_of wbits =? 8) || (wrap_of wbits =? 1)).

(** zlib_common.h's be32 / le32 of 4 bytes. *)
Definition be32 (l : list Z) : Z := Znth 0 l * 16777216 + Znth 1 l * 65536 + Znth 2 l * 256 + Znth 3 l.
Definition le32 (l : list Z) : Z := Znth 3 l * 16777216 + Znth 2 l * 65536 + Znth 1 l * 256 + Znth 0 l.

(** The gzip headers the harnesses give to deflateSetHeader (text, hcrc 0/1, os a byte, time 32 bits, the
    extra field the whole object (xlen <= 2^12 bytes; extra_len = xlen also when extra is Z_NULL), the name
    and the comment whole objects of at most 2^12 non-zero bytes and their zero byte). *)
Definition cstr_ok (o : option (list Z)) : Prop :=
  forall l, o = Some l -> exists l0, l = l0 ++ [0] /\ Zlength l0 <= 4096 /\ Forall (fun b => 0 < b < 256) l0.

Definition hdr_ok (h : gzh) : Prop :=
  (gz_text h = 0 \/ gz_text h = 1) /\ (gz_hcrc h = 0 \/ gz_hcrc h = 1) /\
  0 <= gz_os h < 256 /\ u32r (gz_time h) /\ 0 <= gz_extra_len h <= 4096 /\
  (forall x, gz_extra h = Some x -> Zlength x = gz_extra_len h /\ bytes x) /\
  cstr_ok (gz_name h) /\ cstr_ok (gz_comment h).

(** ** The facts of one deflate() / deflateParams() call on the caller's fields *)

(** The stream after a call offered the whole object [inb] ([nin = 0]) and [aout] bytes of output space:
    next_in advanced by the bytes consumed, the counters, the bytes written. *)
Definition call_ok (inb : list Z) (aout tin tout : Z) (z' : strm) : Prop :=
  z_in z' = inb /\
  0 <= z_avail_in z' <= Zlength inb /\ z_next_in z' = Zlength inb - z_avail_in z' /\
  z_total_in z' = tin + (Zlength inb - z_avail_in z') /\
  0 <= z_avail_out z' <= aout /\ Zlength (z_out z') = aout - z_avail_out z' /\
  z_total_out z' = tout + (aout - z_avail_out z') /\ bytes (z_out z').

(** What deflate_api checks after the run (the stream ended with Z_STREAM_END): [D] all the data, [O] all the
    output, [adler] strm->adler. *)
Definition final_ok (dict : list Z) (wrap : Z) (D O : list Z) (adler : Z) : Prop :=
  bytes O /\
  (wrap = 1 ->
     adler = Zlib.proof.adler32.Model.ref_adler32 1 D /\
     (match dict with [] => 6 | _ => 10 end) <= Zlength O /\
     Z.land (Znth 0 O) 15 = 8 /\ Z.shiftr (Znth 0 O) 4 <= 7 /\ (Znth 0 O * 256 + Znth 1 O) mod 31 = 0 /\
     (Z.land (Znth 1 O) 32 <> 0 <-> dict <> []) /\
     (dict <> [] -> be32 (sublist 2 6 O) = Zlib.proof.adler32.Model.ref_adler32 1 dict) /\
     be32 (sublist (Zlength O - 4) (Zlength O) O) = adler) /\
  (wrap = 2 ->
     adler = Zlib.proof.crc32.Model.ref_crc32 0 D /\ 18 <= Zlength O /\ sublist 0 3 O = [31; 139; 8] /\
     le32 (sublist (Zlength O - 8) (Zlength O - 4) O) = adler /\
     le32 (sublist (Zlength O - 4) (Zlength O) O) = Zlength D mod 4294967296).

(** ** deflate_api *)
Definition api_inv : Type :=
  list Z -> Z -> list Z -> list Z -> option (list Z) -> dstate -> Z -> Z -> Z -> Prop.

Record api_facts (I : api_inv) (Iend : dstate -> Prop) : Prop := {
  (** deflateInit2(strm, level, method, windowBits, memLevel, strategy) (deflateInit2_ with the right version
      and stream size), for every outcome of the five allocations *)
  af_init : forall level method wbits mem strategy a1 a2 a3 a4 a5 z,
    s32 level -> s32 method -> s32 wbits -> s32 mem -> s32 strategy ->
    (exists r, c_deflateInit2_ true true false level method wbits mem strategy a1 a2 a3 a4 a5 z = Some r) /\
    forall os z' code,
      c_deflateInit2_ true true false level method wbits mem strategy a1 a2 a3 a4 a5 z = Some (os, z', code) ->
      (code = Z_OK \/ code = Z_STREAM_ERROR \/ code = Z_MEM_ERROR) /\
      (code = Z_STREAM_ERROR <-> params_ok level method wbits mem strategy = false) /\
      (code = Z_OK -> exists s, os = Some s /\ d_gzhead s = None /\
                       I [] (wrap_of wbits) [] [] None s (z_total_in z') (z_total_out z') (z_adler z'));
  (** deflateTune, right after deflateInit2 *)
  af_tune : forall wrap s tin tout adler good lazy nice chain z,
    I [] wrap [] [] None s tin tout adler -> s32 good -> s32 lazy -> s32 nice -> s32 chain ->
    exists s', c_deflateTune s z good lazy nice chain = Some (s', z, Z_OK) /\ d_gzhead s' = d_gzhead s /\
               I [] wrap [] [] None s' tin tout adler;
  (** deflateSetDictionary, after deflateInit2 (and deflateTune) *)
  af_dict : forall wrap s tin tout adler d ain aout msg,
    I [] wrap [] [] None s tin tout adler -> bytes d -> Zlength d <= 32768 -> u32r ain -> u32r aout ->
    exists s' z' code,
      c_deflateSetDictionary s (zcall [] 0 ain tin aout tout adler msg) (Some d) = Some (s', z', code) /\
      d_gzhead s' = d_gzhead s /\ (code = Z_OK \/ code = Z_STREAM_ERROR) /\ (code = Z_STREAM_ERROR <-> wrap = 2) /\
      I (if wrap =? 2 then [] else d) wrap [] [] None s' (z_total_in z') (z_total_out z') (z_adler z');
  (** deflateSetHeader, before any deflate() call *)
  af_head : forall dict wrap s tin tout adler h z,
    I dict wrap [] [] None s tin tout adler -> hdr_ok h ->
    (wrap = 2 -> c_deflateSetHeader s z (Some h) = Some (set_d_gzhead s (Some h), z, Z_OK) /\
                 I dict wrap [] [] None (set_d_gzhead s (Some h)) tin tout adler) /\
    (wrap <> 2 -> c_deflateSetHeader s z (Some h) = Some (s, z, Z_STREAM_ERROR));
  (** deflate(strm, flush) with any flush of zlib.h, any input object and output space; once Z_FINISH was
      given, only Z_FINISH with the rest of the input *)
  af_deflate : forall dict wrap D O fin s tin tout adler inb aout flush msg,
    I dict wrap D O fin s tin tout adler ->
    0 <= flush <= 5 -> bytes inb -> Zlength D + Zlength inb <= 1048576 ->
    0 <= aout <= 1048576 -> Zlength O + aout <= 4194304 ->
    (forall R, fin = Some R -> flush = Z_FINISH /\ inb = R) ->
    exists s' z' code,
      c_deflate s (zcall inb 0 (Zlength inb) tin aout tout adler msg) flush = Some (s', z', code) /\
      d_gzhead s' = d_gzhead s /\ call_ok inb aout tin tout z' /\
      (code = Z_OK \/ code = Z_STREAM_END \/ code = Z_BUF_ERROR) /\
      (code = Z_STREAM_END -> flush = Z_FINISH /\ z_avail_in z' = 0) /\
      (code = Z_BUF_ERROR -> z_avail_in z' = Zlength inb /\ z_avail_out z' = aout) /\
      (let used := Zlength inb - z_avail_in z' in
       let D' := D ++ sublist 0 used inb in
       let O' := O ++ z_out z' in
       if code =? Z_STREAM_END then Iend s' /\ final_ok dict wrap D' O' (z_adler z')
       else I dict wrap D' O'
              (if flush =? Z_FINISH then Some (sublist used (Zlength inb) inb) else None)
              s' (z_total_in z') (z_total_out z') (z_adler z'));
  (** deflateParams(strm, level, strategy) with any ints, before Z_FINISH *)
  af_params : forall dict wrap D O s tin tout adler inb aout level strategy msg,
    I dict wrap D O None s tin tout adler -> s32 level -> s32 strategy ->
    bytes inb -> Zlength D + Zlength inb <= 1048576 -> 0 <= aout <= 1048576 -> Zlength O + aout <= 4194304 ->
    exists s' z' code,
      c_deflateParams s (zcall inb 0 (Zlength inb) tin aout tout adler msg) level strategy = Some (s', z', code) /\
      d_gzhead s' = d_gzhead s /\ call_ok inb aout tin tout z' /\
      (code = Z_OK \/ code = Z_BUF_ERROR \/ code = Z_STREAM_ERROR) /\
      (code = Z_STREAM_ERROR <-> ~ (-1 <= level <= 9 /\ 0 <= strategy <= 4)) /\
      I dict wrap (D ++ sublist 0 (Zlength inb - z_avail_in z') inb) (O ++ z_out z') None
        s' (z_total_in z') (z_total_out z') (z_adler z');
  (** after Z_STREAM_END: deflate(Z_FINISH) with no input and 1 byte of output space *)
  af_end_finish : forall s inb nin tin tout adler msg,
    Iend s -> 0 <= nin <= Zlength inb ->
    exists s' z',
      c_deflate s (zcall inb nin 0 tin 1 tout adler msg) Z_FINISH = Some (s', z', Z_STREAM_END) /\
      z_out z' = [] /\ z_avail_out z' = 1 /\ z_avail_in z' = 0 /\ z_next_in z' = nin /\
      d_gzhead s' = d_gzhead s /\ Iend s';
  (** after Z_STREAM_END: any other valid flush *)
  af_end_other : forall s z flush,
    Iend s -> 0 <= flush <= 5 -> flush <> Z_FINISH ->
    exists z', c_deflate s z flush = Some (s, z', Z_STREAM_ERROR);
  (** an invalid flush *)
  af_end_bad : forall s z flush,
    Iend s -> (flush < 0 \/ 5 < flush) -> c_deflate s z flush = Some (s, z, Z_STREAM_ERROR);
  (** deflateEnd after Z_STREAM_END *)
  af_end_end : forall s z, Iend s -> c_deflateEnd s z = Some (None, z, Z_OK)
}.

(** ** deflate_bound and deflate_bound_split *)
Definition bpre_inv : Type := Z -> Z -> Z -> Z -> bool -> dstate -> Z -> Z -> Z -> Prop.
Definition brun_inv : Type := Z -> Z -> Z -> bool -> dstate -> Z -> Z -> Z -> Prop.

Record bound_facts (Bpre : bpre_inv) (Brun : brun_inv) : Prop := {
  (** deflateInit2 with parameters it accepts (method Z_DEFLATED) *)
  bf_init : forall level wbits mem strategy a1 a2 a3 a4 a5 z,
    params_ok level 8 wbits mem strategy = true ->
    (exists r, c_deflateInit2_ true true false level 8 wbits mem strategy a1 a2 a3 a4 a5 z = Some r) /\
    forall os z' code,
      c_deflateInit2_ true true false level 8 wbits mem strategy a1 a2 a3 a4 a5 z = Some (os, z', code) ->
      code = Z_OK ->
      exists s, os = Some s /\ d_gzhead s = None /\
                Bpre level wbits mem strategy false s (z_total_in z') (z_total_out z') (z_adler z');
  (** deflateSetDictionary right after deflateInit2, for raw and zlib streams *)
  bf_dict : forall level wbits mem strategy s tin tout adler d ain aout msg,
    Bpre level wbits mem strategy false s tin tout adler -> wbits <= 15 ->
    bytes d -> Zlength d <= 32768 -> u32r ain -> u32r aout ->
    exists s' z',
      c_deflateSetDictionary s (zcall [] 0 ain tin aout tout adler msg) (Some d) = Some (s', z', Z_OK) /\
      d_gzhead s' = d_gzhead s /\
      Bpre level wbits mem strategy true s' (z_total_in z') (z_total_out z') (z_adler z');
  (** deflateSetHeader for gzip streams *)
  bf_head : forall level wbits mem strategy ds s tin tout adler h z,
    Bpre level wbits mem strategy ds s tin tout adler -> 15 < wbits -> hdr_ok h ->
    c_deflateSetHeader s z (Some h) = Some (set_d_gzhead s (Some h), z, Z_OK) /\
    Bpre level wbits mem strategy ds (set_d_gzhead s (Some h)) tin tout adler;
  (** b = deflateBound(strm, n); the default parameters without dictionary: b <= compressBound(n) *)
  bf_bound : forall level wbits mem strategy ds s tin tout adler n,
    Bpre level wbits mem strategy ds s tin tout adler -> 0 <= n <= 1048576 ->
    exists b, c_deflateBound (Some s) n = Some b /\ 0 <= b <= 4294967295 /\
      (ds = false -> (level = 6 \/ level = -1) -> wbits = 15 -> mem = 8 -> b <= c_compressBound n) /\
      Brun n b 0 false s tin tout adler;
  bf_cbound : forall n, 0 <= n <= 1048576 -> n <= c_compressBound n;
  (** deflate_bound: one deflate(Z_FINISH) offered all n bytes and b bytes of output space *)
  bf_once : forall n b s tin tout adler data msg,
    Brun n b 0 false s tin tout adler -> bytes data -> Zlength data = n ->
    exists s' z',
      c_deflate s (zcall data 0 n tin b tout adler msg) Z_FINISH = Some (s', z', Z_STREAM_END) /\
      z_avail_in z' = 0 /\ z_total_out z' <= b /\ d_gzhead s' = d_gzhead s;
  (** deflate_bound_split: Z_NO_FLUSH calls on any split of the data, then Z_FINISH calls offered the rest,
      any output space of at most 2^20 bytes per call *)
  bf_split : forall n b pos fin s tin tout adler inb aout flush msg,
    Brun n b pos fin s tin tout adler ->
    (flush = Z_NO_FLUSH \/ flush = Z_FINISH) -> (fin = true -> flush = Z_FINISH) ->
    bytes inb -> pos + Zlength inb <= n -> (flush = Z_FINISH -> pos + Zlength inb = n) ->
    0 <= aout <= 1048576 ->
    exists s' z' code,
      c_deflate s (zcall inb 0 (Zlength inb) tin aout tout adler msg) flush = Some (s', z', code) /\
      d_gzhead s' = d_gzhead s /\ (code = Z_OK \/ code = Z_BUF_ERROR \/ code = Z_STREAM_END) /\
      0 <= z_avail_in z' <= Zlength inb /\ z_total_out z' <= b /\
      (code <> Z_STREAM_END ->
       Brun n b (pos + Zlength inb - z_avail_in z') (flush =? Z_FINISH) s'
            (z_total_in z') (z_total_out z') (z_adler z'))
}.
