(* The header case HEAD of inflate() for calls of any uInt size, every branch (RTH9WKit.rth_head_stmt9v). *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.roundtrip.RTH9WKit.
Require Import Zlib.proof.hl9h.roundtrip.H9HRTHCaseHEAD6.

Lemma rth9_head : rth_head_stmt9v.
Proof.
  exact rth_head_h9h.
Qed.
