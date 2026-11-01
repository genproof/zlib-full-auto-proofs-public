(* The round-trip laws: what deflate_roundtrip's deflate_run needs besides LawFacts.api_facts.

   deflate_roundtrip's deflate_run is deflate_api's (harness/deflate_common.h, api = 0); its end state must give
   RTFinal.dfinal (the output is the well-formed stream of the data) instead of only LawFacts.final_ok, with the
   window bits deflate used.  [rt_extra I]: for an invariant I of LawFacts.api_facts' shape,
   - deflateInit2's w_bits is rwbe wbits (and, for raw, the harness's R->wb = wb_of wbits);
   - every call keeps w_bits;
   - the deflate() call that returns Z_STREAM_END ends a dfinal stream (dict, wrap, w_bits and gzhead of the state
     before the call; the data consumed and the output produced).
   [ik I K]: the conjunction of the deflate laws' invariant (LawTheory) and the round trip's (RTDIface.kfacts);
   [rt_ik_facts] (RTXTheory.v) proves that it satisfies both records. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LawFacts.
Require Export Zlib.proof.roundtrip.RTDIface.
Import ListNotations.
Local Open Scope Z_scope.

Record rt_extra (I : api_inv) : Prop := {
  rx_init : forall level method wbits mem strategy a1 a2 a3 a4 a5 z s z',
    s32 level -> s32 method -> s32 wbits -> s32 mem -> s32 strategy ->
    c_deflateInit2_ true true false level method wbits mem strategy a1 a2 a3 a4 a5 z = Some (Some s, z', Z_OK) ->
    d_w_bits s = rwbe wbits /\ (wrap_of wbits = 0 -> rwbe wbits = wb_of wbits);
  rx_tune : forall wrap s tin tout adler good lazy nice chain z s' z' code,
    I [] wrap [] [] None s tin tout adler -> s32 good -> s32 lazy -> s32 nice -> s32 chain ->
    c_deflateTune s z good lazy nice chain = Some (s', z', code) -> d_w_bits s' = d_w_bits s;
  rx_dict : forall wrap s tin tout adler d ain aout msg s' z' code,
    I [] wrap [] [] None s tin tout adler -> bytes d -> Zlength d <= 32768 -> u32r ain -> u32r aout ->
    c_deflateSetDictionary s (zcall [] 0 ain tin aout tout adler msg) (Some d) = Some (s', z', code) ->
    d_w_bits s' = d_w_bits s;
  rx_deflate : forall dict wrap D O fin s tin tout adler inb aout flush msg s' z' code,
    I dict wrap D O fin s tin tout adler ->
    0 <= flush <= 5 -> bytes inb -> Zlength D + Zlength inb <= 1048576 ->
    0 <= aout <= 1048576 -> Zlength O + aout <= 4194304 ->
    (forall R, fin = Some R -> flush = Z_FINISH /\ inb = R) ->
    c_deflate s (zcall inb 0 (Zlength inb) tin aout tout adler msg) flush = Some (s', z', code) ->
    d_w_bits s' = d_w_bits s /\
    (code = Z_STREAM_END ->
     dfinal dict wrap (d_w_bits s) (d_gzhead s) (D ++ sublist 0 (Zlength inb - z_avail_in z') inb) (O ++ z_out z'));
  rx_params : forall dict wrap D O s tin tout adler inb aout level strategy msg s' z' code,
    I dict wrap D O None s tin tout adler -> s32 level -> s32 strategy ->
    bytes inb -> Zlength D + Zlength inb <= 1048576 -> 0 <= aout <= 1048576 -> Zlength O + aout <= 4194304 ->
    c_deflateParams s (zcall inb 0 (Zlength inb) tin aout tout adler msg) level strategy = Some (s', z', code) ->
    d_w_bits s' = d_w_bits s
}.

Definition ik (I : api_inv) (K : rinv) : api_inv :=
  fun dict wrap D O fin s tin tout adler => I dict wrap D O fin s tin tout adler /\ K dict wrap D O fin s tin tout adler.

(* what RTXTheory.v proves *)
Definition rt_ik_stmt : Prop :=
  forall I Iend K, api_facts I Iend -> kfacts K -> api_facts (ik I K) Iend /\ rt_extra (ik I K).
