(* Law api_short_output (data of any length): the resources of the program's global variables that main needs
   (WMainDefs.R), out of globvars2pred; the rest goes to TT.  The program links the same units as
   compress_roundtrip's, so its global variables are the same list, and R is the same predicate as
   roundtrip/RTCLGlobals.R: the lemma is RTCLGlobals.globals_ok moved to this program. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Assembly.
Require Zlib.proof.roundtrip.RTCLCS Zlib.proof.roundtrip.RTCLGlobals.
Require Import Zlib.proof.harness.api_short_output.WLawCS Zlib.proof.harness.api_short_output.WMainDefs.

(* the global variables of this program are those of compress_roundtrip's *)
Lemma vars_eq : QPprog_vars p = QPprog_vars Zlib.proof.roundtrip.RTCLCS.p.
Proof. vm_compute; reflexivity. Qed.

Lemma globals_ok gv : (forall i b o, gv i = Vptr b o -> o = Ptrofs.zero) ->
  (forall f, In f Zlib.proof.roundtrip.RTCLGlobals.cfg_funs -> gv f = Vundef \/ isptr (gv f)) ->
  globvars2pred gv (QPprog_vars p) |-- R gv * TT.
Proof.
  intros HP HU. rewrite vars_eq. exact (Zlib.proof.roundtrip.RTCLGlobals.globals_ok gv HP HU).
Qed.
