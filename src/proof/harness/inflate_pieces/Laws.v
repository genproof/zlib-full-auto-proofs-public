(* The three laws over any input fed to inflate() in any pieces (harness/rj_any_input.c, api_counters.c,
   api_untouched_output.c): the return codes, the exact counters, the output past what was written left untouched,
   the pointers accounted, no Z_OK without input and output space. *)
Require Import QuickProof.Contract.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.contracts.rj_any_input.
Require Zlib.contracts.api_counters.
Require Zlib.contracts.api_untouched_output.
Require Zlib.proof.inflate_api.SpecWLibProof.
Require Zlib.proof.harness.laws_session.Bodies.
Require Zlib.proof.harness.inflate_pieces.LawAsm.

Lemma inflate_pieces_ok : laws_common_ok ->
  harness_safe Zlib.contracts.rj_any_input.whole_prog /\
  harness_safe Zlib.contracts.api_counters.whole_prog /\
  harness_safe Zlib.contracts.api_untouched_output.whole_prog.
Proof.
  intro LC.
  exact (Zlib.proof.harness.inflate_pieces.LawAsm.inflate_pieces_core
           Zlib.proof.inflate_api.SpecWLibProof.specw_lib LC Zlib.proof.harness.laws_session.Bodies.laws_session_bodies).
Qed.
