(** * THE specifications of compress.c's compressBound_z and compressBound (compress unit's compspecs).
    compress2 / compress (used by compress_roundtrip only) are not specified here yet. *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Compress.
Require Import Zlib.compress.code.
Require Import Zlib.proof.deflate.DModel3.

#[local] Existing Instance Zlib.units.Compress.CS.

Definition Vprog : varspecs. mk_varspecs Zlib.compress.code.prog. Defined.

Definition compressBound_z_spec :=
 DECLARE _compressBound_z
 WITH n : Z
 PRE [ tulong ] PROP (0 <= n <= Int64.max_unsigned) PARAMS (Vlong (Int64.repr n)) SEP ()
 POST [ tulong ] PROP () RETURN (Vlong (Int64.repr (compressBound_z n))) SEP ().

Definition compressBound_spec :=
 DECLARE _compressBound
 WITH n : Z
 PRE [ tulong ] PROP (0 <= n <= Int64.max_unsigned) PARAMS (Vlong (Int64.repr n)) SEP ()
 POST [ tulong ] PROP () RETURN (Vlong (Int64.repr (c_compressBound n))) SEP ().

Definition Gprog_compressBound_z : funspecs := [].
Definition Gprog_compressBound : funspecs := [compressBound_z_spec].
