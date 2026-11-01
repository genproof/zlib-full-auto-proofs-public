(* The variable and function specifications for the body of inflate_fast (inffast.c), at the compspecs of
   the inflate unit (inffast.c's composites are inflate.c's).  The body is proved (Qed) in BodyF5.v
   (body_inflate_fast5, against Callees3.v's inflate_fast_spec3, the specification the proof uses). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inffast.code.
Require Import Zlib.proof.inflate.Callees.
#[local] Existing Instance Zlib.units.Inflate.CS.

Definition Vprog_fast : varspecs. mk_varspecs Zlib.inffast.code.prog. Defined.
Definition Gprog_fast : funspecs := [].
