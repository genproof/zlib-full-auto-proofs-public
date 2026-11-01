(** * The deflateBound accounting without the size limits of the deflate_bound laws

    LawFacts.bound_facts serves harness/x_deflate_bound.c and x_deflate_bound_split.c: data of at most 2^20 bytes,
    at most 2^20 bytes of output space per call, a dictionary of at most 32768 bytes, gzip header fields of at most
    4096 bytes with text / hcrc 0 or 1 and os a byte.  The short laws need the same accounting for any size the
    allocator provides:

    - harness/res_bound.c: any accepted parameters, a dictionary of up to 2^32-1 bytes or a gzip header with any
      int text / hcrc / os, an extra field of up to 65535 bytes, a name and a comment of up to 2^32-2 bytes
      each; data and deflateBound below 2^32: ONE deflate(Z_FINISH) returns Z_STREAM_END ([bw_once]).

    (harness/res_compress_bound.c, compress2_z's loop of (uInt)-1-byte pieces into compressBound_z(n) bytes, is
    not covered: it is false at level 0 for some n of about 5.6e13 bytes, see CONTRACT.md.)

    [bound_facts_w Bpre Brun] states this over the checked model, with invariants [Bpre] (after deflateInit2,
    deflateSetDictionary, deflateSetHeader) and [Brun] (after deflateBound) of the same shapes as in LawFacts.v,
    chosen by the theory (LTWBound.v: [bound_theory_w]). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LawFacts.
Import ListNotations.
Local Open Scope Z_scope.

(** ** The gzip headers of the short laws *)

(** A name or a comment: at most 2^32-2 non-zero bytes and their zero byte (the header then has fewer than 2^34
    bytes, and deflateBound's count of it in 64 bits does not wrap). *)
Definition cstr_ok_w (o : option (list Z)) : Prop :=
  forall l, o = Some l -> exists l0, l = l0 ++ [0] /\ Zlength l0 <= 4294967294 /\ Forall (fun b => 0 < b < 256) l0.

(** text, hcrc and os any ints (deflate.c tests text and hcrc against 0 and writes os & 0xff), time 32 bits,
    extra_len at most 65535 (also when extra is Z_NULL: it is then not read), the extra field [extra_len] bytes. *)
Definition hdr_ok_w (h : gzh) : Prop :=
  s32 (gz_text h) /\ s32 (gz_hcrc h) /\ s32 (gz_os h) /\ u32r (gz_time h) /\ 0 <= gz_extra_len h <= 65535 /\
  (forall x, gz_extra h = Some x -> Zlength x = gz_extra_len h /\ bytes x) /\
  cstr_ok_w (gz_name h) /\ cstr_ok_w (gz_comment h).

(** ** The facts *)
Record bound_facts_w (Bpre : bpre_inv) (Brun : brun_inv) : Prop := {
  (** deflateInit2 with parameters it accepts (method Z_DEFLATED) *)
  bw_init : forall level wbits mem strategy a1 a2 a3 a4 a5 z,
    params_ok level 8 wbits mem strategy = true ->
    (exists r, c_deflateInit2_ true true false level 8 wbits mem strategy a1 a2 a3 a4 a5 z = Some r) /\
    forall os z' code,
      c_deflateInit2_ true true false level 8 wbits mem strategy a1 a2 a3 a4 a5 z = Some (os, z', code) ->
      code = Z_OK ->
      exists s, os = Some s /\ d_gzhead s = None /\
                Bpre level wbits mem strategy false s (z_total_in z') (z_total_out z') (z_adler z');
  (** deflateSetDictionary right after deflateInit2, raw and zlib streams, a dictionary of up to 2^32-1 bytes *)
  bw_dict : forall level wbits mem strategy s tin tout adler d ain aout msg,
    Bpre level wbits mem strategy false s tin tout adler -> wbits <= 15 ->
    bytes d -> Zlength d <= 4294967295 -> u32r ain -> u32r aout ->
    exists s' z',
      c_deflateSetDictionary s (zcall [] 0 ain tin aout tout adler msg) (Some d) = Some (s', z', Z_OK) /\
      d_gzhead s' = d_gzhead s /\
      Bpre level wbits mem strategy true s' (z_total_in z') (z_total_out z') (z_adler z');
  (** deflateSetHeader for gzip streams *)
  bw_head : forall level wbits mem strategy ds s tin tout adler h z,
    Bpre level wbits mem strategy ds s tin tout adler -> 15 < wbits -> hdr_ok_w h ->
    c_deflateSetHeader s z (Some h) = Some (set_d_gzhead s (Some h), z, Z_OK) /\
    Bpre level wbits mem strategy ds (set_d_gzhead s (Some h)) tin tout adler;
  (** b = deflateBound(strm, n) for n < 2^32 *)
  bw_bound : forall level wbits mem strategy ds s tin tout adler n,
    Bpre level wbits mem strategy ds s tin tout adler -> 0 <= n <= 4294967295 ->
    exists b, c_deflateBound (Some s) n = Some b /\ 0 <= b <= 18446744073709551615 /\
      Brun n b 0 false s tin tout adler;
  (** res_bound: one deflate(Z_FINISH) offered all n bytes and b < 2^32 bytes of output space *)
  bw_once : forall n b s tin tout adler data msg,
    Brun n b 0 false s tin tout adler -> b <= 4294967295 -> bytes data -> Zlength data = n ->
    exists s' z',
      c_deflate s (zcall data 0 n tin b tout adler msg) Z_FINISH = Some (s', z', Z_STREAM_END) /\
      d_gzhead s' = d_gzhead s
}.

Definition bound_w_stmt : Prop := exists Bpre Brun, bound_facts_w Bpre Brun.
