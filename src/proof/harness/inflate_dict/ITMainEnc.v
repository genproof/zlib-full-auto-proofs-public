(* Law inflate_dict, main: the encoder half (main's start up to `slen = w.len`: the draws, the four objects,
   the dictionary and the wrong one, the zlib header, the blocks by deflate_ref.h, the trailer), continuation
   style: main's body from ANY proof of the inflate half (seg_inf) from enc_done (ITMainKit.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessRef Zlib.proof.adler32.HarnessBytes
               Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.inflate_common.HarnessLib.
Require Import Zlib.proof.harness.inflate_common.DRefSpec.
Require Import Zlib.proof.harness.inflate_dict.ITLawCS Zlib.proof.harness.inflate_dict.ITGlobals
               Zlib.proof.harness.inflate_dict.ITFacts Zlib.proof.harness.inflate_dict.ITMainKit.
Require Import Zlib.harness.x_inflate_dict.code.
Require Import Zlib.proof.harness.inflate_dict.ITMainEncFx.

Lemma main_enc {Espec: OracleKind} : main_enc_stmt.
Proof. exact main_enc_fx. Qed.
