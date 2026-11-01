(** * Level 0 over several deflate() calls: the facts of Level0Calls.v from the model of deflate *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.Level0Calls.
Require Import Zlib.proof.deflate.Level0CallsJ.
Require Import Zlib.proof.deflate.Level0CallsCallA.
Require Import Zlib.proof.deflate.Level0CallsCallB.
Import ListNotations.
Local Open Scope Z_scope.

(** The invariant is [Level0CallsJ.l0_J]; the first call and the calls after Z_NO_FLUSH calls are
    [Level0CallsCallA.l0_callA] and [Level0CallsCallB.l0_callB]. *)
Theorem l0_facts_thm : l0_facts_stmt.
Proof.
  exists l0_J. apply l0_facts_J.
  - intros wbits data room pos O s tin tout adler msg k Hc HA Hk.
    eexists. exact (l0_callA wbits data room pos O s tin tout adler msg k Hc HA Hk).
  - intros wbits data room pos O s tin tout adler msg k Hc HB Hk.
    eexists. exact (l0_callB wbits data room pos O s tin tout adler msg k Hc HB Hk).
Qed.
