(* Law inflate_reset: THE interface between the main of harness/inflate_reset.c (IRMain*.v, VST) and the pure
   theory over the model (IRTheory*.v, IRSim*.v).  Pure Coq over Spec5's relations (inflate_rel over
   Model2.run2, reset_f / reset2_f, init_live).

   The harness's loop has two phases.  Phase 1: only stream a, initialised by inflateInit2_(&a, w), is fed by
   inflate() calls; pos = the input bytes consumed so far.  The reset: inflateReset(&a) (w2 = w) or
   inflateReset2(&a, w2); then stream b is initialised by inflateInit2_(&b, w2) (for w2 < 0 the harness copies
   a.adler into b.adler), pos = 0.  Phase 2: every inflate() call on a is followed by the same call on b (the
   same bytes src[pos .. pos + ain), the same flush and amount of output space), and the harness checks that
   both calls agree.  The theory chooses the invariants I1 (phase 1) and I2 (phase 2) (existential:
   `ir_theory_stmt`) and proves the facts below; IRMain.v proves main for ANY I1, I2 with reset_facts I1 I2. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Export Zlib.proof.inflate_api.Spec5.
Require Export Zlib.proof.harness.inflate_common.HDefs.
Import ListNotations.
Local Open Scope Z_scope.

(* the stream fields the harness sets before an inflate() call: next_in, avail_in, next_out, avail_out *)
Definition ir_call (z: zfields) (ni: val) (ai: Z) (no: val) (ao: Z) : zfields :=
  ZF ni ai (zf_tin z) no ao (zf_tout z) (zf_msg z) (zf_dt z) (zf_adler z) (zf_res z).

(* the harness's reset of stream a: `how & 1` (rst1 = true): inflateReset; else inflateReset2(&a, w2) *)
Definition reset_out (rst1: bool) (w2: Z) (z: zfields) (L: live) : Z * zfields * live :=
  if rst1 then reset_f z L else reset2_f w2 z L.

Record reset_facts (I1: Z -> list Z -> Z -> zfields -> live -> Prop)
                   (I2: Z -> list Z -> Z -> zfields -> live -> zfields -> live -> Prop) : Prop := {
  (* after inflateInit2_(&a, w) returned Z_OK (z: the stream fields then; msg NULL) *)
  rf_init : forall w src z sp,
    wbits_ok w = true -> isptr sp -> zf_ok z -> zf_msg z = None -> live_ok (init_live sp w) ->
    Int.min_signed <= w <= Int.max_signed -> Zlength src <= 2 ^ 24 -> bytes_ok src ->
    I1 w src 0 z (init_live sp w);
  (* inflate() sees no gz_header *)
  rf_head1 : forall w src pos z L, I1 w src pos z L -> i_head (l_s L) = false;
  rf_head2 : forall w2 src pos za La zb Lb, I2 w2 src pos za La zb Lb ->
    i_head (l_s La) = false /\ i_head (l_s Lb) = false;
  (* phase 1: inflate(&a, flush) offered src[pos .. pos + ain) and aout bytes of space; unless it returns
     Z_MEM_ERROR (the harness then returns) *)
  rf_inflate1 : forall w src pos z L strmp flush ib inp o ain aout r z' st' ow,
    I1 w src pos z L -> live_ok L -> zf_ok z -> strmp <> nullval ->
    0 <= pos -> 0 <= ain -> pos + ain <= Zlength src -> Zlength src <= 2 ^ 24 -> bytes_ok src ->
    0 <= aout <= 2 ^ 20 -> Int.min_signed <= flush <= Int.max_signed ->
    ib <> InNull -> inp = sublist pos (pos + ain) src ->
    inflate_rel flush strmp (ir_call z (in_ptr ib 0) ain (out_ptr o 0) aout) (Some L) ib inp (Some o) r z' st' ow ->
    r <> Z_MEM_ERROR ->
    exists L', st' = Some L' /\ 0 <= zf_ai z' <= ain /\ 0 <= zf_ao z' <= aout /\
      I1 w src (pos + (ain - zf_ai z')) z' L';
  (* the reset of a (an accepted w2; for inflateReset w2 = w): it returns Z_OK, the reset stream is live, and
     with b just made by inflateInit2_(&b, w2) (b's fields: totals 0, msg NULL, data_type 0, adler as the
     harness leaves it) the phase-2 invariant holds at pos = 0 *)
  rf_reset : forall w src pos za La rst1 w2,
    I1 w src pos za La -> live_ok La -> zf_ok za ->
    (rst1 = true -> w2 = w) -> wbits_ok w2 = true -> Int.min_signed <= w2 <= Int.max_signed ->
    fst3 (reset_out rst1 w2 za La) = Z_OK /\ live_ok (thd3 (reset_out rst1 w2 za La)) /\
    forall zb sp,
      isptr sp -> live_ok (init_live sp w2) -> zf_ok zb -> zf_tin zb = 0 -> zf_tout zb = 0 ->
      zf_msg zb = None -> zf_dt zb = 0 ->
      (w2 < 0 -> zf_adler zb = zf_adler (snd3 (reset_out rst1 w2 za La))) ->
      (0 <= w2 -> zf_adler zb = Z.land (i_wrap (l_s (init_live sp w2))) 1) ->
      I2 w2 src 0 (snd3 (reset_out rst1 w2 za La)) (thd3 (reset_out rst1 w2 za La)) zb (init_live sp w2);
  (* phase 2: inflate(&a, flush) then inflate(&b, flush), both offered src[pos .. pos + ain) (each in its own
     object) and aout bytes of space; unless one returns Z_MEM_ERROR: the same code, the same bytes consumed
     and produced (the first aout - avail_out bytes of the output space), the same counters, data_type, msg,
     and with a wrapper adler *)
  rf_inflate2 : forall w2 src pos za La zb Lb strma strmb flush iba ibb inp oa ob ain aout
                       ra za' sta' owa rb zb' stb' owb,
    I2 w2 src pos za La zb Lb -> live_ok La -> live_ok Lb -> zf_ok za -> zf_ok zb ->
    strma <> nullval -> strmb <> nullval ->
    0 <= pos -> 0 <= ain -> pos + ain <= Zlength src -> Zlength src <= 2 ^ 24 -> bytes_ok src ->
    0 <= aout <= 2 ^ 20 -> Int.min_signed <= flush <= Int.max_signed ->
    iba <> InNull -> ibb <> InNull -> inp = sublist pos (pos + ain) src ->
    inflate_rel flush strma (ir_call za (in_ptr iba 0) ain (out_ptr oa 0) aout) (Some La) iba inp (Some oa)
      ra za' sta' owa ->
    ra <> Z_MEM_ERROR ->
    inflate_rel flush strmb (ir_call zb (in_ptr ibb 0) ain (out_ptr ob 0) aout) (Some Lb) ibb inp (Some ob)
      rb zb' stb' owb ->
    rb <> Z_MEM_ERROR ->
    exists La' Lb', sta' = Some La' /\ stb' = Some Lb' /\
      ra = rb /\ zf_ai za' = zf_ai zb' /\ zf_ao za' = zf_ao zb' /\ owa = owb /\
      Zlength owa = aout - zf_ao za' /\
      zf_tin za' = zf_tin zb' /\ zf_tout za' = zf_tout zb' /\ zf_dt za' = zf_dt zb' /\
      zf_msg za' = zf_msg zb' /\ (0 <= w2 -> zf_adler za' = zf_adler zb') /\
      0 <= zf_ai za' <= ain /\ 0 <= zf_ao za' <= aout /\
      I2 w2 src (pos + (ain - zf_ai za')) za' La' zb' Lb'
}.

(* The theory (IRTheory.v).  The model facts of the inflate area (InvQ5.v: stepf2_mwf3_proof, cover3_proof,
   fixed_ok5_proof) are hypotheses here, discharged at the assembly. *)
Definition ir_theory_stmt : Prop :=
  stepf2_mwf3_stmt -> Zlib.proof.inflate.Cover3.cover3_stmt -> fixed_ok5 ->
  exists I1 I2, reset_facts I1 I2.
