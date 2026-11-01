(* Law res_bound: the specification of the harness's own function any_string and the statement of its body.

   any_string(len) gives NULL (malloc failed) or a new object of len + 1 bytes: len non-zero bytes, then a zero
   byte.  Specified at the compspecs of the adler32 unit (no struct), as laws_common.h's byte helpers
   (laws_common/Spec.v); its callees are any_bytes and gp_assume. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.units.Adler32.
Require Import Zlib.harness.res_bound.code.

Section AnyString.
#[local] Existing Instance Zlib.units.Adler32.CS.

Definition any_string_spec :=
  DECLARE _any_string
  WITH len : Z, gv : globals
  PRE [ tulong ]
    PROP (0 <= len < Ptrofs.max_unsigned)
    PARAMS (Vlong (Int64.repr len)) GLOBALS (gv)
    SEP (mem_mgr gv)
  POST [ tptr tuchar ]
    EX q : val, EX bs : list Z,
    PROP (Zlength bs = len; Forall (fun b => 0 < b <= Byte.max_unsigned) bs)
    RETURN (q)
    SEP (mem_mgr gv;
         if eq_dec q nullval then emp
         else (malloc_token Ews (tarray tuchar (len + 1)) q *
               data_at Ews (tarray tuchar (len + 1)) (bytes_rep (bs ++ [0])) q)).

Definition Gprog_any_string : funspecs := [any_bytes_spec; gp_assume_spec].

End AnyString.

(* the body of any_string against its specification *)
Definition any_string_body_stmt : Prop :=
  @semax_body Vprog_lc Gprog_any_string Zlib.units.Adler32.CS f_any_string any_string_spec.
