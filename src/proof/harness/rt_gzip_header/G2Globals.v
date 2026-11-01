(* Law rt_gzip_header on the round-2 harness: main's resources R (G2MainDefs.v) out of the program's global
   variables.  The program links the units of deflate_roundtrip (deflate.c, trees.c, crc32.c, zutil.c, inflate.c,
   inffast.c, inftrees.c, adler32.c, libc.c) and defines no variable of its own besides its ZLIB_VERSION literal,
   which comes after zutil's literals: its variables are clip_streams' [clip_vars] with that literal, and R is
   clip_streams' [R_of] at it, so the proof is clip_streams/GlobalsOk.v's [clip_vars_globals] (this file
   supersedes round 1's Globals.v for the bounded harness). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Assembly.
Require Zlib.proof.harness.clip_streams.Globals Zlib.proof.harness.clip_streams.GlobalsOk.
Require Import Zlib.proof.harness.rt_gzip_header.CS Zlib.proof.harness.rt_gzip_header.G2MainDefs.
Require Import Zlib.harness.rt_gzip_header.code.

Lemma rtg2_vars : QPprog_vars p =
  Zlib.proof.harness.clip_streams.GlobalsOk.clip_vars ___stringlit_rt_gzip_header_1 v___stringlit_rt_gzip_header_1.
Proof. vm_compute; reflexivity. Qed.

Lemma rtg2_globals : rtg2_globals_stmt.
Proof.
  intros gv HP HU. rewrite rtg2_vars.
  exact (Zlib.proof.harness.clip_streams.GlobalsOk.clip_vars_globals ___stringlit_rt_gzip_header_1 v___stringlit_rt_gzip_header_1 eq_refl gv HP HU).
Qed.
