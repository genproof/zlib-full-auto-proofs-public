(* Law rj_uncompress_any: the resources of the program's global variables that main needs.  The harness defines
   no global variable and links the same units as x_uncompress_any, so its program has the same global variables:
   main's resources are x_uncompress_any's R (uncompress_any/UAGlobals.v: inflate's read-only tables, crc32's
   table, inflate.c's and uncompr.c's ZLIB_VERSION literals). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Assembly.
Require Zlib.proof.harness.uncompress_any.UALawCS.
Require Zlib.proof.harness.uncompress_any.UAGlobals.
Require Import Zlib.proof.harness.rj_uncompress_any.RUCS.

Definition R := Zlib.proof.harness.uncompress_any.UAGlobals.R.

Lemma vars_same : QPprog_vars p = QPprog_vars Zlib.proof.harness.uncompress_any.UALawCS.p.
Proof. vm_compute; reflexivity. Qed.

Lemma globals_ok gv : (forall i b o, gv i = Vptr b o -> o = Ptrofs.zero) ->
  globvars2pred gv (QPprog_vars p) |-- R gv * TT.
Proof. rewrite vars_same. apply Zlib.proof.harness.uncompress_any.UAGlobals.globals_ok. Qed.
