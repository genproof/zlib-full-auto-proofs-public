(* THE specifications of crc32.c's combination functions (crc32_combine, crc32_combine64,
   crc32_combine_gen, crc32_combine_gen64, crc32_combine_op) and of their static helpers (multmodp,
   x2nmodp), shared by every law.  Stated in the compspecs of the crc32 unit.

   crc32_combine(crc1, crc2, len2) (and crc32_combine64): crc32_combine_val (X2n.v): for len2 >= 0 the
   register of crc1 advanced over len2 zero bytes, xor crc2 (X2n.crc32_combine_val_shift), hence the
   CRC-32 of a concatenation (Combine.v); for len2 < 0: 0.  crc32_combine_gen(len2) (and _gen64):
   crc32_combine_gen_val (x^(8 len2) mod P; 0 for len2 < 0); crc32_combine_op(crc1, crc2, op):
   crc32_combine_op_val.  They read the constant x2n_table (x2n_table_at, any readable share).
   The static helpers: multmodp(a, b) = gf_mul a b (GF2.v) for a 32-bit b, x2nmodp(n, k) = x2n_val n k. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Crc32.
Require Import Zlib.crc32.code.
Require Export Zlib.proof.crc32.Spec.
Require Export Zlib.proof.crc32.X2n.

#[local] Existing Instance Zlib.units.Crc32.CS.

Definition x2n_table_rep : list val := map (fun x => Vint (Int.repr x)) x2n_table_vals.

Definition x2n_table_at (sh: share) (gv: globals) : mpred :=
  data_at sh (tarray tuint 32) x2n_table_rep (gv _x2n_table).

Definition multmodp_spec :=
  DECLARE _multmodp
  WITH a: Z, b: Z
  PRE [ tulong, tulong ]
    PROP (0 <= a <= Int64.max_unsigned; 0 <= b < 2 ^ 32)
    PARAMS (Vlong (Int64.repr a); Vlong (Int64.repr b))
    SEP ()
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr (gf_mul a b))) SEP ().

Definition x2nmodp_spec :=
  DECLARE _x2nmodp
  WITH n: Z, k: Z, gv: globals, tsh: share
  PRE [ tlong, tuint ]
    PROP (0 <= n <= Int64.max_signed; 0 <= k <= Int.max_unsigned; readable_share tsh)
    PARAMS (Vlong (Int64.repr n); Vint (Int.repr k))
    GLOBALS (gv)
    SEP (x2n_table_at tsh gv)
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr (x2n_val n k))) SEP (x2n_table_at tsh gv).

Definition crc32_combine_gen64_spec :=
  DECLARE _crc32_combine_gen64
  WITH len2: Z, gv: globals, tsh: share
  PRE [ tlong ]
    PROP (Int64.min_signed <= len2 <= Int64.max_signed; readable_share tsh)
    PARAMS (Vlong (Int64.repr len2))
    GLOBALS (gv)
    SEP (x2n_table_at tsh gv)
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr (crc32_combine_gen_val len2))) SEP (x2n_table_at tsh gv).

Definition crc32_combine_gen_spec :=
  DECLARE _crc32_combine_gen
  WITH len2: Z, gv: globals, tsh: share
  PRE [ tlong ]
    PROP (Int64.min_signed <= len2 <= Int64.max_signed; readable_share tsh)
    PARAMS (Vlong (Int64.repr len2))
    GLOBALS (gv)
    SEP (x2n_table_at tsh gv)
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr (crc32_combine_gen_val len2))) SEP (x2n_table_at tsh gv).

Definition crc32_combine_op_spec :=
  DECLARE _crc32_combine_op
  WITH crc1: Z, crc2: Z, op: Z
  PRE [ tulong, tulong, tulong ]
    PROP (0 <= crc1 <= Int64.max_unsigned; 0 <= crc2 <= Int64.max_unsigned; 0 <= op <= Int64.max_unsigned)
    PARAMS (Vlong (Int64.repr crc1); Vlong (Int64.repr crc2); Vlong (Int64.repr op))
    SEP ()
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr (crc32_combine_op_val crc1 crc2 op))) SEP ().

Definition crc32_combine64_spec :=
  DECLARE _crc32_combine64
  WITH crc1: Z, crc2: Z, len2: Z, gv: globals, tsh: share
  PRE [ tulong, tulong, tlong ]
    PROP (0 <= crc1 <= Int64.max_unsigned; 0 <= crc2 <= Int64.max_unsigned;
          Int64.min_signed <= len2 <= Int64.max_signed; readable_share tsh)
    PARAMS (Vlong (Int64.repr crc1); Vlong (Int64.repr crc2); Vlong (Int64.repr len2))
    GLOBALS (gv)
    SEP (x2n_table_at tsh gv)
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr (crc32_combine_val crc1 crc2 len2))) SEP (x2n_table_at tsh gv).

Definition crc32_combine_spec :=
  DECLARE _crc32_combine
  WITH crc1: Z, crc2: Z, len2: Z, gv: globals, tsh: share
  PRE [ tulong, tulong, tlong ]
    PROP (0 <= crc1 <= Int64.max_unsigned; 0 <= crc2 <= Int64.max_unsigned;
          Int64.min_signed <= len2 <= Int64.max_signed; readable_share tsh)
    PARAMS (Vlong (Int64.repr crc1); Vlong (Int64.repr crc2); Vlong (Int64.repr len2))
    GLOBALS (gv)
    SEP (x2n_table_at tsh gv)
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr (crc32_combine_val crc1 crc2 len2))) SEP (x2n_table_at tsh gv).

Definition Gprog_multmodp : funspecs := [].
Definition Gprog_x2nmodp : funspecs := [multmodp_spec].
Definition Gprog_crc32_combine_gen64 : funspecs := [x2nmodp_spec].
Definition Gprog_crc32_combine_gen : funspecs := [crc32_combine_gen64_spec].
Definition Gprog_crc32_combine_op : funspecs := [multmodp_spec].
Definition Gprog_crc32_combine64 : funspecs := [crc32_combine_gen64_spec; crc32_combine_op_spec].
Definition Gprog_crc32_combine : funspecs := [crc32_combine64_spec].
