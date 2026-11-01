(* Law rt_roundtrip (data of any length): the resources of the program's global variables that main needs.
   The harness defines no global variable and links the same units as compress_roundtrip, so its program has
   the same global variables: main's resources are compress_roundtrip's R (src/proof/roundtrip/RTCLGlobals.v:
   deflate's globals, compress.c's ZLIB_VERSION literal, inflate's read-only tables, inflate.c's and uncompr.c's
   ZLIB_VERSION literals). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Assembly.
Require Zlib.proof.roundtrip.RTCLCS Zlib.proof.roundtrip.RTCLGlobals.
Require Import Zlib.proof.harness.rt_roundtrip.WCS.

Definition R := Zlib.proof.roundtrip.RTCLGlobals.R.
Definition cfg_funs := Zlib.proof.roundtrip.RTCLGlobals.cfg_funs.

Lemma vars_same : QPprog_vars p = QPprog_vars Zlib.proof.roundtrip.RTCLCS.p.
Proof. vm_compute; reflexivity. Qed.

Lemma globals_ok gv : (forall i b o, gv i = Vptr b o -> o = Ptrofs.zero) ->
  (forall f, In f cfg_funs -> gv f = Vundef \/ isptr (gv f)) ->
  globvars2pred gv (QPprog_vars p) |-- R gv * TT.
Proof. rewrite vars_same. apply Zlib.proof.roundtrip.RTCLGlobals.globals_ok. Qed.
