(* Law rt_session: main's resources Rm out of the program's global variables ([SMainStmt.ses_globals_stmt]), as
   rt_stream's Globals.rts_globals and rt_gzip_header's G2Globals.  The program links the units of
   deflate_roundtrip and defines no variable of its own besides its ZLIB_VERSION literal, which comes after
   zutil's literals: its variables are clip_streams' [clip_vars] with that literal, and Rm is clip_streams'
   [R_of] at it, so the proof is clip_streams/GlobalsOk.v's [clip_vars_globals]. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import Zlib.proof.harness.rt_session.SCS.
Require Import Zlib.proof.harness.rt_session.SMainStmt.
Require Zlib.proof.harness.clip_streams.Globals Zlib.proof.harness.clip_streams.GlobalsOk.
Require Import QuickProof.Contract QuickProof.Assembly.
Require Import Zlib.harness.rt_session.code.

(* the program's global variables: clip_streams' list with the harness's literal *)
Lemma ses_vars : QPprog_vars p =
  Zlib.proof.harness.clip_streams.GlobalsOk.clip_vars ___stringlit_rt_session_1 v___stringlit_rt_session_1.
Proof. vm_compute; reflexivity. Qed.

Theorem ses_globals : ses_globals_stmt.
Proof.
  intros gv HP HU. rewrite ses_vars.
  exact (Zlib.proof.harness.clip_streams.GlobalsOk.clip_vars_globals ___stringlit_rt_session_1
           v___stringlit_rt_session_1 eq_refl gv HP HU).
Qed.
