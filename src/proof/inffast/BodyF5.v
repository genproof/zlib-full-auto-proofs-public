(* The body of inflate_fast (inffast.c) against Callees3.v's inflate_fast_spec3 (the spec of the v5 layer:
   LibStmt5.inflate_lib5_stmt), at the compspecs of the inflate unit. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inffast.code.
Require Import Zlib.proof.inflate.Callees3.
Require Import Zlib.proof.inffast.Body.
Require Import Zlib.proof.inffast.F5Kit Zlib.proof.inffast.F5Main.
Require Import Zlib.proof.inffast.F5Tab Zlib.proof.inffast.F5WalkFacts Zlib.proof.inffast.F5Walk
  Zlib.proof.inffast.F5WLoop Zlib.proof.inffast.F5Tail Zlib.proof.inffast.F5Copy Zlib.proof.inffast.F5Len
  Zlib.proof.inffast.F5Iter Zlib.proof.inffast.F5Facts.
#[local] Existing Instance Zlib.units.Inflate.CS.

Lemma body_inflate_fast5 {Espec: OracleKind} :
  semax_body Vprog_fast Gprog_fast Zlib.inffast.code.f_inflate_fast inflate_fast_spec3.
Proof.
  destruct f5_walk_facts as [LW DW].
  destruct (f5_walks f5_tab_focus LW DW) as [WL WD].
  destruct f5_wloops as (W1 & W2 & W3 & W4).
  destruct f5_tail_direct as [TL DR].
  pose proof (f5_copy_ok W1 W2 W3 W4 TL DR) as CP.
  pose proof (f5_lenbr_ok f5_tab_focus DW WD CP) as LB.
  apply fast_main.
  - exact (f5_iter_ok f5_tab_focus LW WL LB).
  - exact (f5_iter_facts LW DW).
Qed.
