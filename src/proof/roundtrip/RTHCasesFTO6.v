(* RT-H: cases FLAGS, TIME, OS (indices 1-3) with a partial gz_header attached (RTHCase.case_ok6). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.roundtrip.RTHSpec.
Require Import Zlib.proof.roundtrip.RTHCase.
Require Import Zlib.proof.roundtrip.RTHFTO6.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Lemma rth_fto : rth_fto_stmt.
Proof.
  exact rth_fto_proof.
Qed.
