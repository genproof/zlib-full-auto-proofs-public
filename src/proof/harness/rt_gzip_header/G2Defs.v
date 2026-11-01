(* Law rt_gzip_header on the round-2 harness: the definitions shared by its deflate and inflate interfaces.

   harness/rt_gzip_header.c draws a gzip header for deflateSetHeader: text, hcrc and os any ints, time below
   2^32, extra_len = upto(65535) with an extra field of extra_len bytes (or Z_NULL), a name and a comment of
   upto(UINT_MAX - 1) nonzero bytes each followed by their zero byte (or Z_NULL).  [g2_hdr_ok] says this of a
   model header: it is RTK7.rhdr_ok7 with the strings' length bound 2^32 - 2 in place of 2^20.  [clipz] is
   laws_common.h's clip(n) = min(n, UINT_MAX), the size of each piece the harness offers. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.roundtrip.RTK7.
Import ListNotations.
Local Open Scope Z_scope.

Definition umax : Z := 4294967295.
Definition max_u64 : Z := 18446744073709551615.

(* laws_common.h's clip(n): the most one call takes *)
Definition clipz (n : Z) : Z := Z.min n umax.

(* a name or a comment: absent, or at most 2^32 - 2 nonzero bytes followed by a zero byte *)
Definition g2_cstr_ok (o : option (list Z)) : Prop :=
  forall l, o = Some l -> exists l0, l = l0 ++ [0] /\ Zlength l0 <= 4294967294 /\ Forall (fun b => 0 < b < 256) l0.

(* the headers the harness gives to deflateSetHeader *)
Definition g2_hdr_ok (h : DS7.gzh) : Prop :=
  rs32 (DS7.gz_text h) /\ rs32 (DS7.gz_hcrc h) /\ rs32 (DS7.gz_os h) /\
  0 <= DS7.gz_time h <= 4294967295 /\ 0 <= DS7.gz_extra_len h <= 65535 /\
  (forall x, DS7.gz_extra h = Some x -> Zlength x = DS7.gz_extra_len h /\ Forall (fun b => 0 <= b < 256) x) /\
  g2_cstr_ok (DS7.gz_name h) /\ g2_cstr_ok (DS7.gz_comment h).
