(* The round-trip laws: THE interface of the deflate side, pure Coq over the checked model of
   deflate.c (DModel4.v: c_deflateInit2_, c_deflateTune, c_deflateSetDictionary, c_deflateSetHeader,
   c_deflate, c_deflateParams; with patch D2 the C's deflateParams is c_deflateParams, and every law takes
   ef = id, i.e. DModel5.c_deflate_g id = c_deflate).

   - [kfacts K]: an invariant [K dict wrap D O fin s tin tout adler] of a live stream between the calls the
     harnesses make ([dict] the dictionary set, [wrap] 0/1/2, [D] the data consumed, [O] the output produced,
     [fin = Some R] once Z_FINISH was given with R not yet consumed, [s] the state, [tin], [tout], [adler] the
     z_stream fields), preserved by every call, and giving [RTFinal.dfinal] at Z_STREAM_END.  The facts only
     speak of model runs that SUCCEED (the call's result is a hypothesis): safety (that the runs are [Some]) and
     the return codes come from the deflate laws' theory (LawFacts.api_facts / bound_facts), whose
     invariant is conjoined with K.  The hypotheses of each fact are what api_facts gives for that call.
     Shape: the same arguments as LawFacts.api_inv, so that the combined invariant fits deflate_run's kit.
   - [rt_init_facts], [rt_bound_once]: what compress2 needs from the deflate laws' theory (deflateInit2's
     return codes; one deflate(Z_FINISH) with compressBound(n) bytes of output space ends the stream).
   - [c2_rel]: compress.c's compress2_z (compress2, compress) over the model, and [c2_fact], what
     compress_roundtrip needs about it. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.DModel4.
Require Export Zlib.proof.roundtrip.RTFinal.
Import ListNotations.
Local Open Scope Z_scope.

(** ** The harnesses' quantities (as in LawFacts.v of the deflate laws) *)
Definition rs32 (x : Z) : Prop := -2147483648 <= x <= 2147483647.
Definition rbytes (l : list Z) : Prop := Forall (fun b => 0 <= b < 256) l.
(* the model's stream of a call offered the whole object inb and aout bytes of output space (= DSpec.zmk) *)
Definition rzcall (inb : list Z) (nin ain tin aout tout adler : Z) (msg : option Z) : strm :=
  mkST inb nin ain tin [] aout tout adler msg.
Definition rwrap_of (wbits : Z) : Z := if wbits <? 0 then 0 else if wbits >? 15 then 2 else 1.
Definition rwb_of (wbits : Z) : Z := if wbits <? 0 then - wbits else if wbits >? 15 then wbits - 16 else wbits.
(* deflate's w_bits for windowBits wbits (deflateInit2_: windowBits 8 is changed to 9) *)
Definition rwbe (wbits : Z) : Z := if rwb_of wbits =? 8 then 9 else rwb_of wbits.
Definition rparams_ok (level method wbits mem strategy : Z) : bool :=
  let lv := if level =? -1 then 6 else level in
  negb (wbits <? -15) && (1 <=? mem) && (mem <=? 9) && (method =? 8) &&
  (8 <=? rwb_of wbits) && (rwb_of wbits <=? 15) && (0 <=? lv) && (lv <=? 9) &&
  (0 <=? strategy) && (strategy <=? 4) && (negb (rwb_of wbits =? 8) || (rwrap_of wbits =? 1)).
(* the stream after a call offered the whole object inb (nin = 0) and aout bytes (= LawFacts.call_ok) *)
Definition rcall_ok (inb : list Z) (aout tin tout : Z) (z' : strm) : Prop :=
  z_in z' = inb /\
  0 <= z_avail_in z' <= Zlength inb /\ z_next_in z' = Zlength inb - z_avail_in z' /\
  z_total_in z' = tin + (Zlength inb - z_avail_in z') /\
  0 <= z_avail_out z' <= aout /\ Zlength (z_out z') = aout - z_avail_out z' /\
  z_total_out z' = tout + (aout - z_avail_out z') /\ rbytes (z_out z').

(** ** The invariant of the round trip *)
Definition rinv : Type :=
  list Z -> Z -> list Z -> list Z -> option (list Z) -> dstate -> Z -> Z -> Z -> Prop.

Record kfacts (K : rinv) : Prop := {
  (** deflateInit2 (right version and stream size) accepted the parameters *)
  kf_init : forall level method wbits mem strategy a1 a2 a3 a4 a5 z s z',
    rs32 level -> rs32 method -> rs32 wbits -> rs32 mem -> rs32 strategy ->
    c_deflateInit2_ true true false level method wbits mem strategy a1 a2 a3 a4 a5 z = Some (Some s, z', Z_OK) ->
    d_w_bits s = rwbe wbits /\ d_gzhead s = None /\
    K [] (rwrap_of wbits) [] [] None s (z_total_in z') (z_total_out z') (z_adler z');
  (** deflateTune right after deflateInit2 *)
  kf_tune : forall wrap s tin tout adler good lazy nice chain z s' z' code,
    K [] wrap [] [] None s tin tout adler -> rs32 good -> rs32 lazy -> rs32 nice -> rs32 chain ->
    c_deflateTune s z good lazy nice chain = Some (s', z', code) ->
    d_w_bits s' = d_w_bits s /\ d_gzhead s' = d_gzhead s /\ K [] wrap [] [] None s' tin tout adler;
  (** deflateSetDictionary after deflateInit2 (and deflateTune); Z_STREAM_ERROR exactly for gzip *)
  kf_dict : forall wrap s tin tout adler d ain aout msg s' z' code,
    K [] wrap [] [] None s tin tout adler -> rbytes d -> Zlength d <= 32768 ->
    0 <= ain <= 4294967295 -> 0 <= aout <= 4294967295 ->
    c_deflateSetDictionary s (rzcall [] 0 ain tin aout tout adler msg) (Some d) = Some (s', z', code) ->
    (code = Z_OK \/ code = Z_STREAM_ERROR) -> (code = Z_STREAM_ERROR <-> wrap = 2) ->
    d_w_bits s' = d_w_bits s /\ d_gzhead s' = d_gzhead s /\
    K (if wrap =? 2 then [] else d) wrap [] [] None s' (z_total_in z') (z_total_out z') (z_adler z');
  (** deflateSetHeader on a gzip stream, before any deflate() call (on another stream it changes nothing) *)
  kf_head : forall dict s tin tout adler h,
    K dict 2 [] [] None s tin tout adler -> rhdr_ok h -> K dict 2 [] [] None (set_d_gzhead s (Some h)) tin tout adler;
  (** deflate(strm, flush): any flush of zlib.h, any input object and output space; once Z_FINISH was given,
      only Z_FINISH with the rest of the input *)
  kf_deflate : forall dict wrap D O fin s tin tout adler inb aout flush msg s' z' code,
    K dict wrap D O fin s tin tout adler ->
    0 <= flush <= 5 -> rbytes inb -> Zlength D + Zlength inb <= 1048576 ->
    0 <= aout <= 2097152 -> Zlength O + aout <= 4194304 ->
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
            s' (z_total_in z') (z_total_out z') (z_adler z'));
  (** deflateParams(strm, level, strategy) with any ints, before Z_FINISH *)
  kf_params : forall dict wrap D O s tin tout adler inb aout level strategy msg s' z' code,
    K dict wrap D O None s tin tout adler -> rs32 level -> rs32 strategy ->
    rbytes inb -> Zlength D + Zlength inb <= 1048576 -> 0 <= aout <= 2097152 -> Zlength O + aout <= 4194304 ->
    c_deflateParams s (rzcall inb 0 (Zlength inb) tin aout tout adler msg) level strategy = Some (s', z', code) ->
    d_gzhead s' = d_gzhead s -> rcall_ok inb aout tin tout z' ->
    (code = Z_OK \/ code = Z_BUF_ERROR \/ code = Z_STREAM_ERROR) ->
    (code = Z_STREAM_ERROR <-> ~ (-1 <= level <= 9 /\ 0 <= strategy <= 4)) ->
    d_w_bits s' = d_w_bits s /\
    K dict wrap (D ++ sublist 0 (Zlength inb - z_avail_in z') inb) (O ++ z_out z') None
      s' (z_total_in z') (z_total_out z') (z_adler z')
}.

(** ** What compress2 needs from the deflate laws' theory *)

(* deflateInit2's outcomes (= LawFacts.af_init without the invariant) *)
Definition rt_init_facts : Prop :=
  forall level method wbits mem strategy a1 a2 a3 a4 a5 z,
    rs32 level -> rs32 method -> rs32 wbits -> rs32 mem -> rs32 strategy ->
    (exists r, c_deflateInit2_ true true false level method wbits mem strategy a1 a2 a3 a4 a5 z = Some r) /\
    forall os z' code,
      c_deflateInit2_ true true false level method wbits mem strategy a1 a2 a3 a4 a5 z = Some (os, z', code) ->
      (code = Z_OK \/ code = Z_STREAM_ERROR \/ code = Z_MEM_ERROR) /\
      (code = Z_STREAM_ERROR <-> rparams_ok level method wbits mem strategy = false) /\
      (code = Z_OK -> exists s, os = Some s /\ d_gzhead s = None).

(* deflateInit(strm, level) (default parameters), then one deflate(Z_FINISH) offered all n <= 2^20 bytes and
   compressBound(n) bytes of output space returns Z_STREAM_END (zlib.h; from the deflate laws' bound theory:
   deflateBound of the default parameters is compressBound for every level) *)
Definition rt_bound_once : Prop :=
  forall level a1 a2 a3 a4 a5 z s z1 src msg,
    -1 <= level <= 9 -> rbytes src -> Zlength src <= 1048576 ->
    c_deflateInit2_ true true false level 8 15 8 0 a1 a2 a3 a4 a5 z = Some (Some s, z1, Z_OK) ->
    exists s' z',
      c_deflate s (rzcall src 0 (Zlength src) (z_total_in z1) (c_compressBound (Zlength src)) (z_total_out z1)
                     (z_adler z1) msg) Z_FINISH = Some (s', z', Z_STREAM_END) /\
      d_gzhead s' = d_gzhead s /\ z_avail_in z' = 0 /\
      rcall_ok src (c_compressBound (Zlength src)) (z_total_in z1) (z_total_out z1) z'.

(** ** compress.c: compress2_z(dest, &destLen, source, sourceLen, level) over the model
    (destLen = cap and sourceLen at most (uInt)-1: the loop gives each in one piece) *)
Definition umax : Z := 4294967295.

(* the stream offered by one iteration of compress2_z's loop, from the stream z after the previous call (or
   after the setup): the output space and the input are refilled when exhausted; the flush; the destination
   and source bytes not given yet *)
Definition c2_give (src : list Z) (z : strm) (left srcleft : Z) : strm * Z * Z * Z :=
  let '(ao, left') :=
    if z_avail_out z =? 0 then (Z.min left umax, left - Z.min left umax) else (z_avail_out z, left) in
  let '(ai, srcleft') :=
    if z_avail_in z =? 0 then (Z.min srcleft umax, srcleft - Z.min srcleft umax) else (z_avail_in z, srcleft) in
  (mkST src (z_next_in z) ai (z_total_in z) [] ao (z_total_out z) (z_adler z) (z_msg z), left', srcleft',
   if srcleft' =? 0 then Z_FINISH else Z_NO_FLUSH).

(* the loop: [do { ... err = deflate(&stream, ...); } while (err == Z_OK);] from the state s and stream z with
   the output out so far; ends with err, the output, the state and stream for deflateEnd *)
Inductive c2_loop (src : list Z) : dstate -> strm -> Z -> Z -> list Z -> Z -> list Z -> dstate -> strm -> Prop :=
| c2_more : forall s z left srcleft out z1 left' srcleft' flush s' z' err out' sf zf,
    c2_give src z left srcleft = (z1, left', srcleft', flush) ->
    c_deflate s z1 flush = Some (s', z', Z_OK) ->
    c2_loop src s' z' left' srcleft' (out ++ z_out z') err out' sf zf ->
    c2_loop src s z left srcleft out err out' sf zf
| c2_last : forall s z left srcleft out z1 left' srcleft' flush s' z' err,
    c2_give src z left srcleft = (z1, left', srcleft', flush) ->
    c_deflate s z1 flush = Some (s', z', err) -> err <> Z_OK ->
    c2_loop src s z left srcleft out err (out ++ z_out z') s' z'.

(* compress2_z with destLen = cap, the allocation outcomes a1..a5 of deflateInit2_ and the stream z0 deflateInit
   sees: return value r and the bytes out written at dest ( *destLen = |out| ) *)
Definition c2_rel (src : list Z) (cap level : Z) (a1 a2 a3 a4 a5 : bool) (z0 : strm) (r : Z) (out : list Z) : Prop :=
  exists os z1 code,
    c_deflateInit2_ true true false level 8 15 8 0 a1 a2 a3 a4 a5 z0 = Some (os, z1, code) /\
    ((code <> Z_OK /\ r = code /\ out = []) \/
     (code = Z_OK /\ exists s err sf zf,
        os = Some s /\
        c2_loop src s (mkST src 0 0 (z_total_in z1) [] 0 (z_total_out z1) (z_adler z1) (z_msg z1)) cap
          (Zlength src) [] err out sf zf /\
        r = (if err =? Z_STREAM_END then Z_OK else err))).

(* what compress_roundtrip needs: for n <= 2^20 bytes and destLen = compressBound(n), compress2_z succeeds
   (the model runs are defined) and returns Z_STREAM_ERROR exactly for a level not in -1..9, else Z_OK or
   Z_MEM_ERROR; the output fits and, on Z_OK, is the zlib stream of the data *)
Definition c2_fact : Prop :=
  forall src level a1 a2 a3 a4 a5 z0,
    rbytes src -> Zlength src <= 1048576 -> rs32 level ->
    (exists r out, c2_rel src (c_compressBound (Zlength src)) level a1 a2 a3 a4 a5 z0 r out) /\
    forall r out, c2_rel src (c_compressBound (Zlength src)) level a1 a2 a3 a4 a5 z0 r out ->
      (r = Z_OK \/ r = Z_STREAM_ERROR \/ r = Z_MEM_ERROR) /\
      (r = Z_STREAM_ERROR <-> ~ (-1 <= level <= 9)) /\
      Zlength out <= c_compressBound (Zlength src) /\
      (r = Z_OK -> dfinal [] 1 15 None src out).
