(* Law x_uncompress_any (harness/x_uncompress_any.c), from the inflate area's library bodies (LibStmt5.v). *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Contract.
Require Zlib.contracts.x_uncompress_any.
Require Import Zlib.proof.inflate_api.LibStmt5.
Require Zlib.proof.harness.uncompress_any.UALawAsm.

Lemma law5_uncompress_any : inflate_lib5_stmt -> Zlib.proof.uncompr.UBodies5.uncompr_bodies5_stmt -> harness_safe Zlib.contracts.x_uncompress_any.whole_prog.
Proof.
  exact Zlib.proof.harness.uncompress_any.UALawAsm.ua_law_core.
Qed.
