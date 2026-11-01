(* The header cases NAME, COMMENT of inflate() for calls of any uInt size, every branch (RTH9WKit.rth_nc_stmt9v):
   round 1's proofs ported by docs/port-hl/cfg_rth9h.py (group nc), with the leave branches of RTH9HNcKit. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.roundtrip.RTH9WKit.
Require Import Zlib.proof.hl9h.roundtrip.H9HRTHCasesNC6.

Lemma rth9_nc : rth_nc_stmt9v.
Proof.
  exact rth_nc_h9h.
Qed.
