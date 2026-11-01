(* Law rj_bad_block, main: statements 1-28 of main's body (BBWKit.bbw_setup_stmt): the inputs (window_bits,
   kind, which, literals, stream_len, room), the objects stream, literal and out and their NULL check, the writes
   of the block (put_bits / put_literal, BWSpec.v; the stream becomes BBFacts.bb_bytes), new_stream,
   inflateInit2_ (any outcome but Z_OK returns 0), next_in, next_out and flush; then the loop's invariant at
   pos = 0, ob = [].  The proof chains the four sub-segments of BBWSetKit.v: statements 1-10 (BBWSet1.v), the NULL
   check (BBWSetNull.v), the writes (BBWSet2.v, under the bound on the literals that bbs_A1 carries) and
   statements 24-28 (BBWSet3.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5 Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.bit_writer.BWSpec.
Require Import Zlib.proof.harness.bit_writer.BBWDefs.
Require Import Zlib.proof.harness.bit_writer.BWLawCS Zlib.proof.harness.bit_writer.BWGlobals.
Require Import Zlib.proof.harness.bit_writer.BBWKit.
Require Import Zlib.proof.harness.bit_writer.BBWHelp.
Require Import Zlib.proof.harness.bit_writer.BBWSetKit.
Require Import Zlib.proof.harness.bit_writer.BBWSet1.
Require Import Zlib.proof.harness.bit_writer.BBWSetNull.
Require Import Zlib.proof.harness.bit_writer.BBWSet2.
Require Import Zlib.proof.harness.bit_writer.BBWSet3.

Lemma bbw_setup : bbw_setup_stmt.
Proof.
  intros Espec J gv vs vbt vbit FJ K.
  apply bbs_set1. intros w kind which lits S0 room strp litp outp.
  apply bbs_null.
  assert_PROP (9 * Zlength lits + 15 <= Int64.max_unsigned) as Hb by (unfold bbs_A1; entailer!).
  apply bbs_set2; [exact Hb | ].
  apply (bbs_set3 _ J); [exact FJ | ].
  intros flush A. apply K. exact A.
Qed.
