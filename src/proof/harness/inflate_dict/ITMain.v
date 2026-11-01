(* Law inflate_dict: main's body from its two halves and the theory. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.harness.inflate_dict.ITLawCS Zlib.proof.harness.inflate_dict.ITGlobals
               Zlib.proof.harness.inflate_dict.ITFacts Zlib.proof.harness.inflate_dict.ITMainKit
               Zlib.proof.harness.inflate_dict.ITMainEnc Zlib.proof.harness.inflate_dict.ITMainInf
               Zlib.proof.harness.inflate_dict.ITTheory.
Require Import Zlib.harness.x_inflate_dict.code.

Lemma body_main {Espec: OracleKind} : semax_body (QPvarspecs p) Gmain_k f_main (_main, main_core_spec R).
Proof.
  destruct it_theory as [I CF].
  apply main_enc. intros Es. apply (@main_inf Es I CF).
Qed.
