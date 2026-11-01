(* Version 5: the library bodies against Spec5/Callees5. *)
(* The body obligations of the inflate area's library functions that are proved in separate files
   (the laws are assembled from them: law_<name> : inflate_lib_stmt -> harness_safe ...). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Export Zlib.proof.inflate_api.Bodies5.
Require Export Zlib.proof.inffast.Body.
Require Export Zlib.proof.inflate.BodyUpdatewindow.
Require Export Zlib.proof.uncompr.UBodies5.
Require Zlib.proof.inftrees.spec.
#[local] Existing Instance Zlib.units.Inflate.CS.

Definition inflate_lib5_stmt : Prop :=
  api_init_stmt /\ api_reset_stmt /\ api_dict_stmt /\ api_misc_stmt /\ api_sync_stmt /\ body_inflate_stmt /\
  (forall {Espec: OracleKind}, semax_body Vprog_fast Gprog_fast Zlib.inffast.code.f_inflate_fast inflate_fast_spec3) /\
  (forall {Espec: OracleKind}, semax_body Vprog_inflate Gprog_updatewindow f_updatewindow updatewindow_spec3) /\
  (forall {Espec: OracleKind},
     semax_body Zlib.proof.inftrees.spec.Vprog [] Zlib.inftrees.code.f_inflate_fixed inflate_fixed_spec) /\
  (forall {Espec: OracleKind}, semax_body Vprog_inflate [] f_inflateStateCheck inflateStateCheck_spec).
