(* Law inflate_header, main: one iteration of the loop (IHMainKit.v seg_loop): pre_ok ; call_ok ; chk_ok ;
   done_ok ; fin_ok, back to the loop invariant ih_inv. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.crc32.HarnessRef.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.inflate_common.HarnessLib.
Require Import Zlib.proof.harness.inflate_header.IHLawCS Zlib.proof.harness.inflate_header.IHGlobals
               Zlib.proof.harness.inflate_header.IHHelpers Zlib.proof.harness.inflate_header.IHFacts
               Zlib.proof.harness.inflate_header.IHMainStmt.
Require Import Zlib.harness.x_inflate_header.code.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.harness.inflate_header.IHMainKit.
Local Open Scope logic.
Require Import Zlib.proof.harness.inflate_header.IHMainPre Zlib.proof.harness.inflate_header.IHMainCall
               Zlib.proof.harness.inflate_header.IHMainDone Zlib.proof.harness.inflate_header.IHMainChk.

Lemma loop_ok {Espec: OracleKind} I gv V g b P h0 H Fr pos z L:
  ih_glob I g b P h0 H -> I g (b_w b) h0 pos z L -> 0 <= pos <= Zlength (ih_src g) -> ih_Lok V H L ->
  semax Delta_m (ih_at gv V g b P h0 H Fr pos z L) seg_loop (ih_PL (ih_inv I gv V g b P h0 H Fr)).
Proof.
  intros G HI Hpos HL.
  apply (pre_ok I); auto.
  intros ain aout flush stop ibp obp q bs BF.
  apply (call_ok I gv V g b P h0 H Fr _ pos z L ain aout flush stop ibp obp q bs BF).
  intros pos' r z' L' inb cont MF.
  apply (chk_ok I gv V g b P h0 H Fr pos pos' ain r z' L' aout stop ibp obp q inb cont bs); auto.
  apply (done_ok I gv V g b P h0 H Fr pos pos' ain r z' L' aout stop ibp obp q inb cont bs); auto.
  apply (fin_ok I gv V g b P h0 H Fr pos pos' ain r z' L' aout stop ibp obp q inb cont bs); auto.
Qed.
