(* The header case HCRC of inflate() for calls of any uInt size, every branch (RTH9WKit.rth_hcrc_stmt9v): round 1's
   case ported by docs/port-hl/cfg_rth9h.py (group hcrc), with the breaks of NEEDBITS out of input and of a header
   CRC mismatch proved (RTH9HHcrcKit). *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.roundtrip.RTH9WKit.
Require Import Zlib.proof.hl9h.roundtrip.H9HRTH8CaseHCRC.

Lemma rth9_hcrc : rth_hcrc_stmt9v.
Proof. exact rth_hcrc8_h9h. Qed.
