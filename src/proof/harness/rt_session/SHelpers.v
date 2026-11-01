(* Law rt_session (harness/rt_session.c): the bodies of the harness's own functions any_string and same_field
   against G2MainDefs' specifications (the ones main's context SMainStmt.Gmain lists).  rt_session.c has the same
   two functions as rt_gzip_header.c, and clightgen gives the same Clight for them (the identifiers are hashes of
   their names), so rt_gzip_header's proofs (G2Helpers.v) are proofs for this program's functions. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require Zlib.harness.rt_session.code.
Require Import Zlib.proof.harness.rt_gzip_header.G2MainDefs.
Require Zlib.proof.harness.rt_gzip_header.G2Helpers.

Lemma ses_body_any_string :
  @semax_body [] Gprog_any_string Zlib.units.Adler32.CS Zlib.harness.rt_session.code.f_any_string any_string_spec.
Proof. exact Zlib.proof.harness.rt_gzip_header.G2Helpers.body_any_string. Qed.

Lemma ses_body_same_field :
  @semax_body [] Gprog_same_field Zlib.units.Adler32.CS Zlib.harness.rt_session.code.f_same_field same_field_spec.
Proof. exact Zlib.proof.harness.rt_gzip_header.G2Helpers.body_same_field. Qed.
