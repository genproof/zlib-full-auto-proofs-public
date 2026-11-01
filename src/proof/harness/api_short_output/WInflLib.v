(* Law api_short_output (data of any length): the bodies of inflate.c against Spec5 that the program reaches,
   the parts of LibStmt5.inflate_lib5_stmt it needs: inflateInit_ / inflateInit2_, the resets and inflateEnd,
   and inflate_fixed (inftrees.c's fixed tables).  inflate() itself is SpecWSelf's, inflate_fast, updatewindow
   and inflateStateCheck the allocator-generic port's (SpecWLib.specw_lib_stmt); inflateSync and the other API
   functions are not reached. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate_api.LibStmt5.
Require Zlib.proof.inftrees.spec.
#[local] Existing Instance Zlib.units.Inflate.CS.

Definition inflate_lib_w : Prop :=
  api_init_stmt /\ api_reset_stmt /\
  (forall {Espec: OracleKind},
     semax_body Zlib.proof.inftrees.spec.Vprog [] Zlib.inftrees.code.f_inflate_fixed inflate_fixed_spec).

(* inflate_lib5_stmt has these parts *)
Lemma inflate_lib_w_of_lib5 : inflate_lib5_stmt -> inflate_lib_w.
Proof.
  intros (Hinit & Hreset & _ & _ & _ & _ & _ & _ & Hfixed & _).
  exact (conj Hinit (conj Hreset Hfixed)).
Qed.
