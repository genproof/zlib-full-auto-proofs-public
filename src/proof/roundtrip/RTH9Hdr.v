(* The header cases HEAD .. HCRC of inflate() for calls of any uInt size (RTH9HDefs.cases9h_all), from the parts
   (RTH9WKit.cases9h_all_of_parts): HEAD, FLAGS/TIME/OS, EXLEN/EXTRA, NAME/COMMENT, HCRC, each proved from the port
   docs/port-hl/cfg_rth9h.py of round 1's header cases. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.roundtrip.RTH9HDefs.
Require Import Zlib.proof.roundtrip.RTH9WKit.
Require Import Zlib.proof.roundtrip.RTH9HHead.
Require Import Zlib.proof.roundtrip.RTH9HFto.
Require Import Zlib.proof.roundtrip.RTH9HEx.
Require Import Zlib.proof.roundtrip.RTH9HNc.
Require Import Zlib.proof.roundtrip.RTH9HHcrc.

Lemma cases9h_proof : cases9h_all.
Proof.
  exact (cases9h_all_of_parts rth9_head rth9_fto rth9_ex rth9_nc rth9_hcrc).
Qed.
