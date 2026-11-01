(* Law res_free_deflate: main after deflate(): the stream given to deflateEnd and what is left of it.

   - [end_pre]: the live stream after deflate() (deflate.c's dstream_sp_za) gives deflateEnd its four buffers,
     none of them Z_NULL (Stmt.za_dstream_end_stmt), when the buffer sizes are positive (as deflateInit2_
     made them);
   - [closed_back]: after deflateEnd freed the state, the members of the z_stream are again data_at_;
   - [free_count]: count.now is 0 after deflateInit2_'s allocations and deflateEnd's releases of the same
     sizes. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.DeflateKit.
Require Import Zlib.proof.za.deflate.Stmt.
Require Import Zlib.proof.harness.counted.Spec.
Require Import Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.res_alloc_deflate.StrmKit.
Require Import Zlib.proof.harness.res_free_deflate.Facts.
Require Import Zlib.deflate.code.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.

Lemma end_pre {ZA : zallocator} (s : dstate) (sp spp : val) (gv : globals) :
  za_dstream_end_stmt -> 0 < d_w_size s -> 0 < d_hash_size s -> 0 < tr_lit_bufsize (d_tr s) ->
  dstream_sp_za 2 (Some s) sp nullval spp gv |--
  EX p : dptrs, !! (p_strm p = sp /\ p_pbuf p <> nullval /\ p_head p <> nullval /\ p_prev p <> nullval /\
                    p_window p <> nullval) && dend_stream (Some s) p sp gv.
Proof.
  intros HE Hw Hh Hl.
  eapply derives_trans; [ | apply (HE ZA s sp nullval gv Hw Hh Hl)].
  rewrite dstream_sp_eq_za. Exists spp. apply derives_refl.
Qed.

(* the application's members but next_in, as main holds them around deflateEnd *)
Definition api_rest (sp : val) (ain tin : Z) (nout : val) (aout tout : Z) (msgv : val) (adler : Z) : mpred :=
  field_at Ews t_strm (DOT _avail_in) (vi ain) sp * field_at Ews t_strm (DOT _total_in) (vl tin) sp *
  field_at Ews t_strm (DOT _next_out) nout sp * field_at Ews t_strm (DOT _avail_out) (vi aout) sp *
  field_at Ews t_strm (DOT _total_out) (vl tout) sp * field_at Ews t_strm (DOT _msg) msgv sp *
  field_at Ews t_strm (DOT _adler) (vl adler) sp.

Lemma api_fields_split sp nin ain tin nout aout tout msgv adler :
  api_fields sp nin ain tin nout aout tout msgv adler |--
  field_at Ews t_strm (DOT _next_in) nin sp * api_rest sp ain tin nout aout tout msgv adler.
Proof. unfold api_fields, api_rest. Intros. cancel. Qed.

Lemma closed_back {ZA : zallocator} (sp ni : val) (gv : globals) ain tin nout aout tout msgv adler :
  field_at Ews t_strm (DOT _next_in) ni sp * api_rest sp ain tin nout aout tout msgv adler *
  dclosed sp gv * strm_pad sp |-- data_at_ Ews t_strm sp * TT.
Proof.
  unfold dclosed, api_rest. Intros dt.
  eapply derives_trans with
    (strm_members sp ni (vi ain) (vl tin) nout (vi aout) (vl tout) msgv nullval za_alloc za_free za_opaque dt
       (vl adler) Vundef * strm_pad sp * TT).
  { unfold strm_members. cancel. }
  sep_apply strm_members_data_at_. cancel.
Qed.

Lemma free_count {ZA : zallocator} (s s' : dstate) (p : dptrs) :
  dkeep s s' -> p_pbuf p <> nullval -> p_head p <> nullval -> p_prev p <> nullval -> p_window p <> nullval ->
  fst (cnt (([] ++ dinit_events s) ++ dend_events s' p)) = 0.
Proof.
  intros K N1 N2 N3 N4. rewrite cnt_now_mod, <- app_assoc.
  rewrite (free_events_now s s' p K N1 N2 N3 N4). reflexivity.
Qed.
