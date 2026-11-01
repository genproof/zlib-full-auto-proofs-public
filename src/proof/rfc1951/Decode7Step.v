(* The decode theory for calls of any size (Decode7.v), (1) with inflateInit2's windowBits larger than a zlib
   header's window and (2) at the loop heads of a call, not only between calls.

   (1) DecodeDefs.accepts asks inflateInit2's windowBits of a zlib stream to be the header's window (CINFO + 8),
   0 or 32 + it.  inflate() accepts any larger window: HEAD rejects a header only when CINFO + 8 > state->wbits,
   and keeps state->wbits (glob_ok already allows dc_wb <= wbits <= 15).  [accepts7] adds dc_wb <= dc_iw <= 15
   for zlib; [dctx_ok7a] is Decode7.dctx_ok7 with it.  Law rfc_stored writes CINFO = upto(window - 8) and calls
   inflateInit2(window).

   (2) Decode.v / Decode7.v state one call ([decode_call7_stmt]); their proof goes through the invariant Kd
   at the loop heads of the call (DecodeDefs.v: at_mode, glob_ok, ..., dstep_post).  Law rfc_stored relates
   inflate() on its stream (stored blocks whose first byte has ANY padding bits) to inflate() on Format's
   canonical stream (zero padding) pass by pass, so it needs that invariant: [kd_init7a_stmt] (Kd and the wide
   machine invariant mwf3W at the start of a call, from dinv: DecCall.dc_init) and [dc_step7a_stmt] (one pass
   of the switch from a loop head with Kd: DecCall.dc_all), for calls of up to 2^32 - 1 bytes of input and of
   output space on streams of any length. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.rfc1951.Decode7.
Require Export Zlib.proof.inflate.InvW.
Import ListNotations.
Local Open Scope Z_scope.

(* inflateInit2's windowBits accepts the stream; zlib: also any window from the header's to 15 *)
Definition accepts7 (G: dctx) : Prop :=
  accepts G \/ (exists wb fl did, dc_w G = WZlib wb fl did /\ dc_wb G <= dc_iw G <= 15).

Definition dctx_ok7a (G: dctx) : Prop :=
  stream_ok (dc_w G) (dc_wb G) (dc_hist G) (dc_bs G) /\ accepts7 G /\
  (forall h, dc_w G = WGzip h -> gz_simple h) /\
  (forall wb fl did, dc_w G = WZlib wb fl did ->
     did = None \/ did = Some (Zlib.proof.adler32.Model.ref_adler32 1 (dc_hist G))) /\
  slen G <= Zlength (dc_src G) /\ Zlength (dc_src G) <= 2 ^ 64 - 1 /\ bytes_ok (dc_src G) /\
  sublist 0 (slen G) (dc_src G) = stream_bytes (dc_w G) (dc_hist G) (dc_bs G).

Lemma dctx_ok7_7a G : dctx_ok7 G -> dctx_ok7a G.
Proof.
  intros (A & B & C). split; [exact A|]. split; [left; exact B | exact C].
Qed.

(* Decode7's statements over dctx_ok7a *)
Definition decode_init7a_stmt : Prop :=
  forall G sp, dctx_ok7a G -> dc_hist G = [] -> (forall wb fl did, dc_w G = WZlib wb fl did -> did = None) ->
    dinv G 0 [] (l_s (init_live sp (dc_iw G))) 0.

Definition decode_call7a_stmt : Prop :=
  forall G pos out L z inp flush res,
    dctx_ok7a G -> dinv G pos out (l_s L) (zf_tout z) -> live_ok L -> zf_ok z ->
    zf_ao z <= 2 ^ 32 - 1 -> Zlength inp <= 2 ^ 32 - 1 ->
    0 <= pos -> pos + Zlength inp <= Zlength (dc_src G) -> inp = sublist pos (pos + Zlength inp) (dc_src G) ->
    run2 flush lenfix_list distfix_list (m_init z L inp) res ->
    let m := r_m res in
    r_ret res = Z_MEM_ERROR \/
    ((r_ret res = Z_OK \/ r_ret res = Z_BUF_ERROR \/ r_ret res = Z_STREAM_END) /\
     0 <= m_snx m <= Zlength inp /\ m_sow m = Zlength (m_ow m) /\ m_aout m = zf_ao z /\
     (exists rest, full G = out ++ m_ow m ++ rest) /\
     dinv G (pos + m_snx m) (out ++ m_ow m) (m_s m) (m_tout m) /\
     ((forall h, dc_w G <> WGzip h) -> i_wsize (l_s L) <> 0 -> win_ok G (l_s L) out ->
      (r_ret res <> Z_STREAM_END \/ wrapped G = false) ->
      i_wsize (m_s m) <> 0 /\ win_ok G (m_s m) (out ++ m_ow m)) /\
     (r_ret res = Z_STREAM_END -> out ++ m_ow m = full G /\ pos + m_snx m = slen G) /\
     (r_ret res <> Z_STREAM_END ->
        (m_snx m = Zlength inp /\ pos + Zlength inp < slen G) \/
        (Zlength (m_ow m) = zf_ao z /\ Zlength (out ++ m_ow m) < Zlength (full G)) \/
        flush = Z_BLOCK \/ flush = Z_TREES) /\
     exists dt, r_dtype res = Some dt /\ dtype_ok G (out ++ m_ow m) dt).

(* the start of a call (DecCall.dc_init) *)
Definition kd_init7a_stmt : Prop :=
  forall G pos out L z inp,
    dctx_ok7a G -> dinv G pos out (l_s L) (zf_tout z) -> live_ok L -> zf_ok z ->
    zf_ao z <= 2 ^ 32 - 1 -> Zlength inp <= 2 ^ 32 - 1 -> bytes_ok inp ->
    Kd G pos inp out (m_init z L inp) /\ mwf3W (m_init z L inp).

(* one pass of the switch from a loop head (DecCall.dc_all) *)
Definition dc_step7a_stmt : Prop :=
  forall G pos inp ob flush m,
    dctx_ok7a G -> 0 <= pos -> pos + Zlength inp <= Zlength (dc_src G) ->
    inp = sublist pos (pos + Zlength inp) (dc_src G) ->
    Kd G pos inp ob m -> mwf3W m -> m_leave m = 0 ->
    dstep_post G pos inp ob flush m (stepf2 flush lenfix_list distfix_list m).

Definition decode7a_stmt : Prop :=
  decode_init7a_stmt /\ decode_call7a_stmt /\ kd_init7a_stmt /\ dc_step7a_stmt /\ stepf2_mwf3W_stmt.
