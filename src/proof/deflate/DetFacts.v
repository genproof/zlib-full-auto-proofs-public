(** * The interface between the model theory and the main of law api_deterministic

    harness/api_deterministic.c drives two streams by the same calls: deflateInit2 with any parameters, then a
    loop of calls, each offering the next piece of the data (at most 2^20 bytes in all) and up to 2^32 - 1 bytes
    of output space, maybe deflateParams with any level and strategy, then deflate with a flush Z_NO_FLUSH ..
    Z_BLOCK (Z_FINISH, once given, repeated with the rest of the data) until Z_STREAM_END.  The shared
    specifications (DSpec.v, DSpec9.v) are functional: a call's result is the checked model run
    [c_f s z args = Some r].  So the two streams stay equal as long as every call of main is defined; main's
    loop invariant is [J fin s tin adler] of the common state [s] ([fin = Some R] once Z_FINISH was given, [R]
    the data not consumed since; [tin], [adler] the fields total_in, strm->adler; total_out is any 64-bit
    value: the model only counts it), with the facts below.  [J] is abstract: DetTheory.v chooses it
    ([det_theory_stmt]). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.DetWide.
Import ListNotations.
Local Open Scope Z_scope.

Definition det_inv : Type := option (list Z) -> dstate -> Z -> Z -> Prop.

Record det_facts (J : det_inv) : Prop := {
  (** deflateInit2(strm, level, Z_DEFLATED, windowBits, memLevel, strategy) for every outcome of the five
      allocations; on Z_OK the state and the stream do not depend on the outcomes *)
  df_init : forall level wbits mem strategy a1 a2 a3 a4 a5 z,
    s32 level -> s32 wbits -> s32 mem -> s32 strategy ->
    (exists r, c_deflateInit2_ true true false level 8 wbits mem strategy a1 a2 a3 a4 a5 z = Some r) /\
    forall os z' code,
      c_deflateInit2_ true true false level 8 wbits mem strategy a1 a2 a3 a4 a5 z = Some (os, z', code) ->
      (code = Z_OK \/ code = Z_STREAM_ERROR \/ code = Z_MEM_ERROR) /\
      (code = Z_STREAM_ERROR <-> params_ok level 8 wbits mem strategy = false) /\
      (code = Z_OK ->
         (exists s, os = Some s /\ z_total_in z' = 0 /\ z_total_out z' = 0 /\
                    J None s (z_total_in z') (z_adler z')) /\
         forall b1 b2 b3 b4 b5 os2 z2 code2,
           c_deflateInit2_ true true false level 8 wbits mem strategy b1 b2 b3 b4 b5 z = Some (os2, z2, code2) ->
           code2 = Z_OK -> os2 = os /\ z2 = z');
  (** strm->adler stays a 32-bit value *)
  df_adler : forall fin s tin adler, J fin s tin adler -> 0 <= adler < 4294967296;
  (** deflate(strm, flush), the input object [inb] with next_in at [nin], [aout] bytes of output space, any
      total_out; once Z_FINISH was given, only Z_FINISH with the rest of the data *)
  df_deflate : forall fin s tin adler inb nin aout tout flush msg,
    J fin s tin adler -> 0 <= flush <= 5 -> bytes inb -> 0 <= nin <= Zlength inb ->
    tin + (Zlength inb - nin) <= 1048576 -> 0 <= aout <= 4294967295 -> u64r tout ->
    (forall R, fin = Some R -> flush = Z_FINISH /\ R = sublist nin (Zlength inb) inb) ->
    exists s' z' code,
      c_deflate s (zcall inb nin (Zlength inb - nin) tin aout tout adler msg) flush = Some (s', z', code) /\
      call_okw inb nin aout tin tout z' /\
      (code <> Z_STREAM_END ->
       J (if flush =? Z_FINISH then Some (sublist (z_next_in z') (Zlength inb) inb) else None)
         s' (z_total_in z') (z_adler z'));
  (** deflateParams(strm, level, strategy) with any ints, also after Z_FINISH *)
  df_params : forall fin s tin adler inb nin aout tout level strategy msg,
    J fin s tin adler -> s32 level -> s32 strategy -> bytes inb -> 0 <= nin <= Zlength inb ->
    tin + (Zlength inb - nin) <= 1048576 -> 0 <= aout <= 4294967295 -> u64r tout ->
    (forall R, fin = Some R -> R = sublist nin (Zlength inb) inb) ->
    exists s' z' code,
      c_deflateParams s (zcall inb nin (Zlength inb - nin) tin aout tout adler msg) level strategy =
        Some (s', z', code) /\
      call_okw inb nin aout tin tout z' /\
      J (match fin with None => None | Some _ => Some (sublist (z_next_in z') (Zlength inb) inb) end)
        s' (z_total_in z') (z_adler z')
}.

Definition det_theory_stmt : Prop := exists J, det_facts J.
