(* Law api_reset: the entry of main in the assembly's context (ARLawG.v): ARMain.ar_main for the invariants of
   ARTheory.ar_theory, moved to the program by QuickProof.Assembly.entry_moved. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.SpecWLib.
Require Import Zlib.proof.harness.api_reset.ARMainDefs.
Require Import Zlib.proof.harness.api_reset.ARLawG.
Require Import Zlib.proof.harness.api_reset.ARMain.
Require Import Zlib.proof.harness.api_reset.ARGlobals.
Require Import Zlib.proof.harness.api_reset.ARTheory.
Require Zlib.harness.api_reset.code.

(* every variable of a list without repeated names is found in it (instead of find_ids_V, which recomputes
   the program's variables for each of them) *)
Lemma ar_vars_found (V: varspecs) : compute_list_norepet (map fst V) = true ->
  Forall (fun x => initial_world.find_id (fst x) V = Some (snd x)) V.
Proof.
  intros N. apply Forall_forall. intros [i phi] H. simpl.
  apply initial_world.find_id_i; [exact H | apply compute_list_norepet_e; exact N].
Qed.

Lemma ar_main_entry : specw_bridge_stmt -> ar_bridge_stmt ->
  entry_of_prog (@HonestEspec CS) CS p (G ++ vacuous_internals p G)
    (Zlib.harness.api_reset.code._main, QPmain_spec_ext' p tt main_post_TT).
Proof.
  intros BR AB.
  destruct ar_theory as (J0 & J1 & AF).
  pose proof (ar_main J0 J1 AF) as B_main.
  pose proof (semax_body_main_core _ _ p _ _ R_ar ar_globals B_main eq_refl) as B.
  eapply (entry_moved _ _ CS _ _ _ _ _ _ _ B);
    [ reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
    | apply ar_vars_found; vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | ar_ctx_sub BR AB ].
Qed.
