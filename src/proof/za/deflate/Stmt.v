(* What the laws with a caller-supplied allocator need of deflate.c, as statements:
   - [za_deflate_bodies_stmt]: the bodies of the generated allocator-generic port (the functions deflate()
     reaches, deflateStateCheck, deflateResetKeep, deflateReset) against their specifications, for every
     allocator, and the conversion of a live stream into what deflateEnd needs;
   - [za_deflate_api_stmt] (ZSpec.v): the bodies of deflateInit2_ and deflateEnd against their
     allocator-generic specifications;
   - [za_dstream_end_stmt]: a live stream with positive buffer sizes (as after deflateInit2_) gives
     deflateEnd its four buffers, none of them Z_NULL;
   - [za_deflate_model_stmt]: the model of one deflate() call right after a successful deflateInit2_ is
     defined (memory safety of the call) for any flush, any input of up to 2^32-1 bytes and any output space of
     up to 2^32-1 bytes. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Export Zlib.proof.za.deflate.ZSpec.
Require Export Zlib.proof.za.deflate.Obligations9.
#[export] Existing Instance DCS.CS.

Definition za_deflate_bodies_stmt : Prop :=
  forall ZA : zallocator,
  @ob_read_buf_za ZA /\ @ob_flush_pending_za ZA /\ @ob_fill_window_za ZA /\
  @ob_deflate_stored_za ZA /\ @ob_deflate_fast_za ZA /\ @ob_deflate_slow_za ZA /\ @ob_deflate_rle_za ZA /\
  @ob_deflate_huff_za ZA /\ @ob_deflateStateCheck_za ZA /\ @ob_deflateResetKeep9_za ZA /\
  @ob_deflateReset9_za ZA /\ @ob_deflate_za ZA /\ @ob_dstream_to_end_za ZA.

Definition za_dstream_end_stmt : Prop :=
  forall (ZA : zallocator) (s : dstate) (strmp ghp : val) (gv : globals),
    0 < d_w_size s -> 0 < d_hash_size s -> 0 < tr_lit_bufsize (d_tr s) ->
    dstream_za 2 (Some s) strmp ghp gv |--
    EX p : dptrs, !! (p_strm p = strmp /\ p_pbuf p <> nullval /\ p_head p <> nullval /\ p_prev p <> nullval /\
                      p_window p <> nullval) && dend_stream (Some s) p strmp gv.

Definition za_deflate_model_stmt : Prop :=
  forall level method wbits mem strategy s z1 inb aout flush,
    s32_ok level -> s32_ok method -> s32_ok wbits -> s32_ok mem -> s32_ok strategy ->
    c_deflateInit2_ true true false level method wbits mem strategy true true true true true zrst0
      = Some (Some s, z1, Z_OK) ->
    Forall (fun b => 0 <= b < 256) inb -> Zlength inb <= Int.max_unsigned ->
    0 <= aout <= Int.max_unsigned -> s32_ok flush ->
    exists r, c_deflate s (zmk inb 0 (Zlength inb) (z_total_in z1) aout (z_total_out z1) (z_adler z1) (z_msg z1))
                flush = Some r.
