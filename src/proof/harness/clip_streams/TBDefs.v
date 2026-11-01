(* Law rfc_trailing_bytes: main's context.  Since round 4 the harness draws deflateInit2's parameters in zlib.h's
   ranges (gp_assume of laws_session.h's deflate_params_ok), so its main calls deflate_params_ok and gp_assume:
   Gmain_tb4 is MainDefs.Gmain_tb (the same specifications of deflate.c, inflate.c, the laws_common.h helpers and
   the environment) with gp_assume_spec and laws_session/Spec.v's deflate_params_ok_spec. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.proof.harness.laws_session.Spec.
Require Import Zlib.proof.harness.clip_streams.CS Zlib.proof.harness.clip_streams.Globals.
Require Import Zlib.proof.harness.clip_streams.MainDefs.
Require Zlib.harness.rfc_trailing_bytes.code.

Definition Gmain_tb4 : funspecs :=
  Gmain_tb ++ [gp_assume_spec; Zlib.proof.harness.laws_session.Spec.deflate_params_ok_spec].
