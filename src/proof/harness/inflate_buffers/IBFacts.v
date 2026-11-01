(* Law inflate_buffers: THE interface between the main of harness/inflate_buffers.c (IBMain*.v, VST) and the pure
   theory over the model (IBTheory*.v).  Pure Coq over Spec5's relations (inflate_rel over Model2.run2, the API
   model functions of ApiModel.v).

   The harness keeps one live stream (z, L) through any sequence of API calls.  Its invariant, besides what istream
   carries (zf_ok z, live_ok L), is `ib_inv L`: no gz_header (the harness never calls inflateGetHeader, so inflate()
   takes no head_mem) and windowBits <= 15 (so inflateGetDictionary reports at most 2^15 bytes: the window has
   2^wbits bytes; contract fix F7 makes HEAD store wbits only after checking it).

   Main proves the harness for ANY proofs of the statements below (record ib_facts); the theory proves them. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Export Zlib.proof.inflate_api.Spec5.
Import ListNotations.
Local Open Scope Z_scope.

Definition ib_inv_s (s: istate) : Prop := i_head s = false /\ i_wbits s <= 15.
Definition ib_inv (L: live) : Prop := ib_inv_s (l_s L).

(* ---------------------------------------------------------------------------------------------- *)
(* inflate(): the model                                                                           *)

(* run2 keeps windowBits <= 15: Model2's c_HEAD2 stores wbits only after checking it (contract fix F7).  Proved in
   IBWbits.v (ib_wbits). *)
Definition ib_wbits_stmt : Prop :=
  forall flush z L inp res,
    live_ok L -> zf_ok z -> i_wbits (l_s L) <= 15 ->
    Zlib.proof.inflate.Model2.run2 flush lenfix_list distfix_list (m_init z L inp) res ->
    i_wbits (m_s (r_m res)) <= 15.

(* the counters of one call of run2 from the loop head after the prologue: the input and the output space do not
   change, next_out is advanced by exactly the bytes written, the written bytes fit the space, the gz_header flag is
   kept, and (unless the call fails with Z_MEM_ERROR) total_in / total_out grow by the bytes consumed / produced *)
Definition ib_run_stmt : Prop :=
  forall flush z L inp res,
    live_ok L -> zf_ok z -> bytes_ok inp -> Zlength inp <= 2 ^ 24 -> 0 <= zf_ao z <= 2 ^ 20 ->
    Zlib.proof.inflate.Model2.run2 flush lenfix_list distfix_list (m_init z L inp) res ->
    let m := r_m res in
    m_inp m = inp /\ m_aout m = zf_ao z /\
    m_sow m = Zlength (m_ow m) /\ Zlength (m_ow m) <= zf_ao z /\
    i_head (m_s m) = i_head (l_s L) /\
    (r_ret res <> Z_MEM_ERROR ->
       m_tin m = u64 (zf_tin z + m_snx m) /\ m_tout m = u64 (zf_tout z + m_sow m)).

(* ---------------------------------------------------------------------------------------------- *)
(* What main needs, per call                                                                      *)

(* inflate(strm, flush) on the live stream: z has the call's next_in/avail_in/next_out/avail_out; ib = InNull for
   next_in Z_NULL (then any avail_in), ob = None for next_out Z_NULL *)
Definition ib_inflate_stmt : Prop :=
  forall flush strmp z L ib inp ob r z' st' ow,
    live_ok L -> zf_ok z -> ib_inv L -> strmp <> nullval ->
    bytes_ok inp -> Zlength inp <= 2 ^ 24 -> 0 <= zf_ao z <= 2 ^ 20 ->
    zf_ni z = in_ptr ib 0 ->
    match ib with InNull => inp = [] | InBuf _ _ _ _ _ => zf_ai z = Zlength inp end ->
    match ob with None => zf_no z = nullval | Some o => zf_no z = out_ptr o 0 end ->
    inflate_rel flush strmp z (Some L) ib inp ob r z' st' ow ->
    exists L', st' = Some L' /\ ib_inv L' /\
      0 <= zf_ai z' <= zf_ai z /\ 0 <= zf_ao z' <= zf_ao z /\
      zf_ni z' = in_ptr ib (zf_ai z - zf_ai z') /\ (ib = InNull -> zf_ai z' = zf_ai z) /\
      zf_no z' = match ob with None => nullval | Some o => out_ptr o (zf_ao z - zf_ao z') end /\
      (ob = None -> zf_ao z' = zf_ao z) /\
      Zlength ow = zf_ao z - zf_ao z' /\
      (r <> Z_MEM_ERROR ->
         zf_tin z' = u64 (zf_tin z + (zf_ai z - zf_ai z')) /\ zf_tout z' = u64 (zf_tout z + (zf_ao z - zf_ao z'))).

Record ib_facts : Prop := {
  (* inflateInit2_ accepted w *)
  fi_init : forall w sp, wbits_ok w = true -> ib_inv (init_live sp w);
  fi_inflate : ib_inflate_stmt;
  (* inflateSync: the bytes looked at are offered bytes; the invariant is kept *)
  fi_sync : forall s inp s' len, swf s -> ib_inv_s s ->
    (sync_s s inp = SyncData s' len \/ sync_s s inp = SyncOk s' len) ->
    0 <= len <= Zlength inp /\ ib_inv_s s';
  (* inflateGetDictionary: at most 2^15 bytes, exactly whave of them *)
  fi_getdict : forall L, live_ok L -> ib_inv L ->
    0 <= i_whave (l_s L) <= 32768 /\ Zlength (dict_bytes (l_s L)) = i_whave (l_s L) /\ bytes_ok (dict_bytes (l_s L));
  (* inflateSetDictionary, inflatePrime, inflateValidate keep the invariant *)
  fi_setdict : forall s dict, ib_inv_s s -> ib_inv_s (setdict_s s dict) /\ ib_inv_s (set_i_mode s MEM);
  fi_prime : forall bits value s s', ib_inv_s s -> prime_s bits value s = Some s' -> ib_inv_s s';
  fi_validate : forall check s, ib_inv_s s -> ib_inv_s (validate_s check s);
  (* inflateReset / inflateReset2: the reset state is live (the specs' reset_pre) and keeps the invariant *)
  fi_reset : forall L, live_ok L -> ib_inv L ->
    live_ok (set_l_s L (reset_s (l_s L))) /\ ib_inv (set_l_s L (reset_s (l_s L)));
  fi_reset2 : forall L w wrap wb, live_ok L -> ib_inv L -> reset2_wb w = Some (wrap, wb) ->
    live_ok (set_l_s L (reset2_s wrap wb (l_s L))) /\ ib_inv (set_l_s L (reset2_s wrap wb (l_s L)))
}.
