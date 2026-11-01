(* The header cases EXLEN, EXTRA of inflate() for calls of any uInt size, every branch (RTH9WKit.rth_ex_stmt9v). *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.roundtrip.RTH9WKit.
Require Import Zlib.proof.hl9h.roundtrip.H9HRTHCasesEX6.

Lemma rth9_ex : rth_ex_stmt9v.
Proof.
  exact rth_ex_h9h.
Qed.
