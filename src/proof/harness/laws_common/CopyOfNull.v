(* copy_of(source, len) (harness/laws_common.h) when source may be Z_NULL with len = 0.

   copy_of reads nothing when len = 0, so a Z_NULL source is fine there (rj_uncompress_any copies an output space of
   size 0, which alloc_any_bytes may return as Z_NULL).  Spec.copy_of_spec takes the source as a cbuf_ok slice.
   [copy_of_spec_n] adds the flag isnull: isnull = false is Spec.copy_of_spec exactly; isnull = true is
   source = Z_NULL, len = 0, no object (the result is a new object of 0 bytes, or NULL).  [copy_of_n_stmt]: its body,
   from Spec's (the body obligation in laws_common_ok) and the empty case. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.units.Adler32.

Section CopyOfNull.
#[local] Existing Instance Zlib.units.Adler32.CS.

Definition copy_of_spec_n :=
  DECLARE HL._copy_of
  WITH isnull : bool, buf : val, sh : share, p : val, lo : Z, n : Z, contents : list val, len : Z,
       data : list Z, gv : globals
  PRE [ tptr tuchar, tulong ]
    PROP (0 <= len <= Ptrofs.max_unsigned;
          if isnull then buf = nullval /\ len = 0 /\ data = [] else cbuf_ok false buf sh p lo n len contents data)
    PARAMS (buf; Vlong (Int64.repr len)) GLOBALS (gv)
    SEP (mem_mgr gv; if isnull then emp else data_at sh (tarray tuchar n) contents p)
  POST [ tptr tuchar ]
    EX q : val,
    PROP ()
    RETURN (q)
    SEP (mem_mgr gv; if isnull then emp else data_at sh (tarray tuchar n) contents p;
         if eq_dec q nullval then emp
         else (malloc_token Ews (tarray tuchar len) q * data_at Ews (tarray tuchar len) (bytes_rep data) q)).

Definition copy_of_n_stmt : Prop :=
  laws_common_ok -> @semax_body Vprog_lc Gprog_copy_of Zlib.units.Adler32.CS HL.f_copy_of copy_of_spec_n.

End CopyOfNull.
