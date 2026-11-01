(* The laws rt_dictionary and api_dict_id: THE interface between the deflate part of their mains (VST) and the
   model theory of deflate.

   The two harnesses compress the same way:
     deflateInit2(&c, level, Z_DEFLATED, wbits, mem, strategy)      wbits 8..15, the other ints any; not Z_OK ends
     deflateSetDictionary(&c, dict, dict_len)                         dict_len 1..2^32 - 1; not Z_OK ends the run
     capacity = deflateBound_z(&c, n)                                 n = data_len <= PTRDIFF_MAX = 2^63 - 1
     do { rest = n - consumed; flush = rest <= UINT_MAX ? Z_FINISH : Z_NO_FLUSH;
          avail_in = clip(rest); avail_out = clip(capacity - produced); code = deflate(&c, flush); }
     while (code == Z_OK);                                            not Z_STREAM_END ends the run
   as the clip()-stream laws (clip_streams/DFacts.v), with deflateSetDictionary between deflateInit2 and
   deflateBound_z.  The theory chooses three invariants (existential, so that the mains and the theory are
   independent): [J0 wbits s tin tout adler] after deflateInit2, [J1 wbits dict s tin tout adler] after
   deflateSetDictionary and [J wbits dict data b pos O s tin tout adler] at the head of the loop (data: the n
   bytes, b: the capacity, pos: the bytes consumed, O: the bytes produced; s and tin, tout, adler: the state and
   the z_stream's fields).  At Z_STREAM_END the output is the zlib stream of the data with the dictionary
   ([dfinal_dict]: FDICT set, DICTID the Adler-32 of the whole dictionary, distances into its last bytes). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.harness.clip_streams.DFacts.
Import ListNotations.
Local Open Scope Z_scope.

(* the longest dictionary the harnesses give (dict_len = 1 + upto(UINT_MAX - 1)) *)
Definition dict_max : Z := 4294967295.

(* the zlib stream O of the data with the dictionary dict, written by a run started with windowBits wbits *)
Definition dfinal_dict (wbits : Z) (dict data O : list Z) : Prop :=
  8 <= wbits <= 15 /\ dfinal dict 1 (rwbe wbits) None data O.

(* what an invariant of the stream before the loop says of its fields *)
Definition dfields_ok (s : dstate) (tin tout adler : Z) : Prop :=
  d_gzhead s = None /\ 0 <= tin <= max_u64 /\ 0 <= tout <= max_u64 /\ 0 <= adler <= max_u64.

Record dict_dfacts (J0 : Z -> dstate -> Z -> Z -> Z -> Prop)
                   (J1 : Z -> list Z -> dstate -> Z -> Z -> Z -> Prop)
                   (J : Z -> list Z -> list Z -> Z -> Z -> list Z -> dstate -> Z -> Z -> Z -> Prop) : Prop := {
  (** deflateInit2 (right version and stream size) with windowBits 8..15, any other ints, method Z_DEFLATED: the
      model run is defined for every outcome of the five allocations; on Z_OK the stream is live and J0 holds *)
  dw_init : forall level wbits mem strategy a1 a2 a3 a4 a5,
    rs32 level -> rs32 mem -> rs32 strategy -> 8 <= wbits <= 15 ->
    (exists r, c_deflateInit2_ true true false level 8 wbits mem strategy a1 a2 a3 a4 a5 dz0 = Some r) /\
    forall os z' code,
      c_deflateInit2_ true true false level 8 wbits mem strategy a1 a2 a3 a4 a5 dz0 = Some (os, z', code) ->
      code = Z_OK ->
      exists s, os = Some s /\ J0 wbits s (z_total_in z') (z_total_out z') (z_adler z');
  dw_range0 : forall wbits s tin tout adler, J0 wbits s tin tout adler -> dfields_ok s tin tout adler;
  (** deflateSetDictionary(strm, dict, |dict|) right after it, no input object (next_in as deflateInit2 left
      it), any avail_in / avail_out and msg: Z_OK *)
  dw_dict : forall wbits s tin tout adler dict ain aout msg,
    J0 wbits s tin tout adler -> rbytes dict -> 1 <= Zlength dict <= dict_max ->
    0 <= ain <= umax -> 0 <= aout <= umax ->
    exists s' z',
      c_deflateSetDictionary s (rzcall [] 0 ain tin aout tout adler msg) (Some dict) = Some (s', z', Z_OK) /\
      J1 wbits dict s' (z_total_in z') (z_total_out z') (z_adler z');
  dw_range1 : forall wbits dict s tin tout adler, J1 wbits dict s tin tout adler -> dfields_ok s tin tout adler;
  (** capacity = deflateBound_z(strm, n) right after deflateSetDictionary, for any n <= PTRDIFF_MAX; the loop then
      starts from J for any n bytes of data *)
  dw_bound : forall wbits dict s tin tout adler n,
    J1 wbits dict s tin tout adler -> 0 <= n <= max_size ->
    exists b, c_deflateBound_z (Some s) n = Some b /\ 0 <= b <= max_u64 /\
      forall data, Zlength data = n -> rbytes data -> J wbits dict data b 0 [] s tin tout adler;
  (** what J says of the quantities at the head of the loop *)
  dw_range : forall wbits dict data b pos O s tin tout adler,
    J wbits dict data b pos O s tin tout adler ->
    0 <= pos <= Zlength data /\ Zlength data <= max_size /\ 0 <= Zlength O <= b /\ b <= max_u64 /\
    rbytes data /\ rbytes O /\ d_gzhead s = None /\
    0 <= tin <= max_u64 /\ 0 <= tout <= max_u64 /\ 0 <= adler <= max_u64;
  (** one iteration of the loop: deflate(strm, dflush rest) offered the object [dpiece data pos] and
      clip(b - |O|) bytes of output space, any msg; the run is defined; the stream moves on as rcall_ok says;
      Z_OK keeps J, Z_STREAM_END comes with all the data consumed and the zlib stream of the data with the
      dictionary *)
  dw_call : forall wbits dict data b pos O s tin tout adler msg,
    J wbits dict data b pos O s tin tout adler ->
    let inb := dpiece data pos in
    let aout := clipz (b - Zlength O) in
    exists s' z' code,
      c_deflate s (rzcall inb 0 (Zlength inb) tin aout tout adler msg) (dflush (Zlength data - pos)) =
        Some (s', z', code) /\
      rcall_ok inb aout tin tout z' /\ d_gzhead s' = None /\
      (code = Z_OK \/ code = Z_STREAM_END \/ code = Z_BUF_ERROR) /\
      (code = Z_OK ->
         J wbits dict data b (pos + (Zlength inb - z_avail_in z')) (O ++ z_out z') s'
           (z_total_in z') (z_total_out z') (z_adler z')) /\
      (code = Z_STREAM_END ->
         z_avail_in z' = 0 /\ pos + Zlength inb = Zlength data /\ dfinal_dict wbits dict data (O ++ z_out z'))
}.

Definition dict_dfacts_stmt : Prop := exists J0 J1 J, dict_dfacts J0 J1 J.
