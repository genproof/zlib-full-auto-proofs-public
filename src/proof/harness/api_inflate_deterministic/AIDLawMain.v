(* Law api_inflate_deterministic: the entry of main in the assembly's context (AIDLawG.v): any proof of
   AIDMainDefs.aid_main_stmt for the invariant of AIDTheory.aid_theory, moved to the program by
   QuickProof.Assembly.entry_moved. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.EnvBodies.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.SpecWLib.
Require Import Zlib.proof.harness.api_inflate_deterministic.AIDMainDefs.
Require Import Zlib.proof.harness.api_inflate_deterministic.AIDLawG.
Require Import Zlib.proof.harness.api_inflate_deterministic.AIDGlobals.
Require Import Zlib.proof.harness.api_inflate_deterministic.AIDTheory.
Require Zlib.proof.harness.api_reset.ARLawMain.
Require Zlib.harness.api_inflate_deterministic.code.

Lemma aid_main_entry : aid_main_stmt -> specw_bridge_stmt ->
  entry_of_prog (@HonestEspec CS) CS p (G ++ vacuous_internals p G)
    (Zlib.harness.api_inflate_deterministic.code._main, QPmain_spec_ext' p tt main_post_TT).
Proof.
  intros M BR.
  destruct aid_theory as (J & AF).
  pose proof (M J AF) as B_main.
  pose proof (semax_body_main_core _ _ p _ _ R_aid aid_globals B_main eq_refl) as B.
  eapply (entry_moved _ _ CS _ _ _ _ _ _ _ B);
    [ reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
    | apply Zlib.proof.harness.api_reset.ARLawMain.ar_vars_found; vm_compute; reflexivity
    | vm_compute; reflexivity | vm_compute; reflexivity | aid_ctx_sub BR ].
Qed.
