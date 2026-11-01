(* Law api_reset, the theory: the invariants of the harness's two phases.  W0 and wrap are the window size and
   the wrapper inflateInit2_(strm, w) stores (with fix F8 wrap has bit 3 set when the window size is to come
   from the header, W0 = 0); inflate() never writes wrap and writes wbits only in HEAD when it is 0
   (x_inflate_reset's `wcl`).  J0: stream used in phase 0 (IRinv of the stream with itself), J1: used and fresh
   in phase 1, related by x_inflate_reset's relation (IRRunCall.IRinv). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Export Zlib.proof.harness.api_reset.ARFacts.
Require Export Zlib.proof.harness.api_reset.ARSimDefs.
Import ListNotations.
Local Open Scope Z_scope.

Definition ar_wrap (w: Z) : Z := i_wrap (l_s (init_live nullval w)).
Definition ar_wb0 (w: Z) : Z := i_wbits (l_s (init_live nullval w)).

Definition J0 (w: Z) (src: list Z) (pos: Z) (z: zfields) (L: live) : Prop :=
  wbits_ok w = true /\ IRinv (ar_wb0 w) (ar_wrap w) src pos z L z L.

Definition J1 (w: Z) (src: list Z) (pos: Z) (za: zfields) (La: live) (zb: zfields) (Lb: live) : Prop :=
  wbits_ok w = true /\ IRinv (ar_wb0 w) (ar_wrap w) src pos za La zb Lb.

(* the reset (fix F8: ARReset.v) *)
Definition ar_reset_stmt : Prop :=
  forall w src pos za La,
    J0 w src pos za La -> live_ok La -> zf_ok za ->
    fst3 (reset_f za La) = Z_OK /\ live_ok (thd3 (reset_f za La)) /\ swfW (l_s (thd3 (reset_f za La))) /\
    forall src' zb sp,
      isptr sp -> live_ok (init_live sp w) -> zf_ok zb -> zf_tin zb = 0 -> zf_tout zb = 0 ->
      zf_msg zb = None -> zf_dt zb = 0 ->
      (w < 0 -> zf_adler zb = zf_adler (snd3 (reset_f za La))) ->
      (0 <= w -> zf_adler zb = Z.land (i_wrap (l_s (init_live sp w))) 1) ->
      bytes_ok src' ->
      J1 w src' 0 (snd3 (reset_f za La)) (thd3 (reset_f za La)) zb (init_live sp w).
