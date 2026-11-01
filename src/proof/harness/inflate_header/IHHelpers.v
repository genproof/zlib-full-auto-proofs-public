(* Law inflate_header: THE specifications of the harness's own (static) functions draw_nonzero, head_buf and
   field_ok (harness/inflate_header.c), at the law's compspecs, and the statement of their bodies
   (`ih_helpers_stmt`, proved in IHHelpersBody.v).  The helpers of zlib_common.h are specified elsewhere:
   bytes_copy, bytes_same (adler32/HarnessBytes.v), ref_crc32 (crc32/HarnessRef.v), exact_copy, exact_space,
   stream_defaults (inflate_common/HarnessLib.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes.
Require Import Zlib.proof.harness.inflate_common.HarnessLib.
Require Import Zlib.proof.harness.inflate_header.IHLawCS.
Require Zlib.harness.x_inflate_header.code.
Module HH := Zlib.harness.x_inflate_header.code.

(* what field_ok checks: the buffer cb (max = |cb| bytes) holds the first k = min(|f|, max) bytes of f and,
   after them, the snapshot cs *)
Definition field_okb (cb cs f: list Z) : bool :=
  let k := Z.min (Zlength f) (Zlength cb) in
  (if list_eq_dec Z.eq_dec (sublist 0 k cb) (sublist 0 k f) then true else false) &&
  (if list_eq_dec Z.eq_dec (sublist k (Zlength cb) cb) (sublist k (Zlength cb) cs) then true else false).

(* draw_nonzero(buf, n): buf[0..n) := any non-zero bytes *)
Definition draw_nonzero_spec :=
  DECLARE HH._draw_nonzero
  WITH buf: val, n: Z, sh: share
  PRE [ tptr tuchar, tuint ]
    PROP (writable_share sh; 0 <= n <= Int.max_unsigned)
    PARAMS (buf; Vint (Int.repr n))
    SEP (data_at_ sh (tarray tuchar n) buf)
  POST [ tvoid ]
    EX bs: list Z,
    PROP (Zlength bs = n; Forall (fun b => 0 < b <= Byte.max_unsigned) bs)
    RETURN ()
    SEP (data_at sh (tarray tuchar n) (bytes_rep bs) buf).

(* head_buf(max, nul, snap): Z_NULL (and *snap = Z_NULL) when nul = 0, else exact_space(max, snap) *)
Definition head_buf_spec :=
  DECLARE HH._head_buf
  WITH max: Z, nul: Z, snapp: val, ssh: share, gv: globals
  PRE [ tuint, tuchar, tptr (tptr tuchar) ]
    PROP (0 <= max <= Int.max_unsigned; 0 <= nul <= Byte.max_unsigned; writable_share ssh)
    PARAMS (Vint (Int.repr max); Vint (Int.repr nul); snapp) GLOBALS (gv)
    SEP (mem_mgr gv; data_at_ ssh (tptr tuchar) snapp)
  POST [ tptr tuchar ]
    EX r: val, EX q: val, EX bs: list Z,
    PROP (Zlength bs = max; is_bytes bs; r = nullval -> q = nullval; nul = 0 -> r = nullval)
    RETURN (r)
    SEP (mem_mgr gv; data_at ssh (tptr tuchar) q snapp;
         if eq_dec r nullval then emp
         else (malloc_token Ews (tarray tuchar max) r * data_at Ews (tarray tuchar max) (bytes_rep bs) r *
               malloc_token Ews (tarray tuchar max) q * data_at Ews (tarray tuchar max) (bytes_rep bs) q)).

(* field_ok(buf, snap, max, f, len): the buffer holds the first min(len, max) bytes of f, then the snapshot *)
Definition field_ok_spec :=
  DECLARE HH._field_ok
  WITH buf: val, shb: share, cb: list Z, snap: val, shs: share, cs: list Z, f: val, shf: share, cf: list Z
  PRE [ tptr tuchar, tptr tuchar, tuint, tptr tuchar, tuint ]
    PROP (readable_share shb; readable_share shs; readable_share shf;
          Zlength cb <= Int.max_unsigned; Zlength cs = Zlength cb; Zlength cf <= Int.max_unsigned;
          is_bytes cb; is_bytes cs; is_bytes cf)
    PARAMS (buf; snap; Vint (Int.repr (Zlength cb)); f; Vint (Int.repr (Zlength cf)))
    SEP (data_at shb (tarray tuchar (Zlength cb)) (bytes_rep cb) buf;
         data_at shs (tarray tuchar (Zlength cb)) (bytes_rep cs) snap;
         data_at shf (tarray tuchar (Zlength cf)) (bytes_rep cf) f)
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr (if field_okb cb cs cf then 1 else 0)))
    SEP (data_at shb (tarray tuchar (Zlength cb)) (bytes_rep cb) buf;
         data_at shs (tarray tuchar (Zlength cb)) (bytes_rep cs) snap;
         data_at shf (tarray tuchar (Zlength cf)) (bytes_rep cf) f).

Definition Vprog_ih : varspecs := [].
Definition Gprog_draw_nonzero : funspecs := [nondet_bytes_spec; gp_assume_spec].
Definition Gprog_head_buf : funspecs := [exact_space_spec].
Definition Gprog_field_ok : funspecs := [bytes_same_spec].

(* the bodies (IHHelpersBody.v) *)
Definition ih_helpers_stmt : Prop :=
  semax_body Vprog_ih Gprog_draw_nonzero HH.f_draw_nonzero draw_nonzero_spec /\
  semax_body Vprog_ih Gprog_head_buf HH.f_head_buf head_buf_spec /\
  semax_body Vprog_ih Gprog_field_ok HH.f_field_ok field_ok_spec.
