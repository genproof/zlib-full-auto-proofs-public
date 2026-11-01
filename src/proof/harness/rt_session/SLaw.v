(* Law rt_session (harness/rt_session.c): one session of deflate and inflate, with an optional raw or zlib
   dictionary or gzip header.  The assembly (SAsm) of main's body (SMain), the globals (SGlobals), the deflate
   side's facts (SDTheory), the inflate side's (SITheory: one theory per kind of session) and the bodies of
   laws_session.h's helpers (laws_session.Bodies). *)
Require Import QuickProof.Contract.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.contracts.rt_session.
Require Zlib.proof.harness.laws_session.Bodies.
Require Zlib.proof.harness.rt_session.SDTheory.
Require Zlib.proof.harness.rt_session.SITheoryPlain.
Require Zlib.proof.harness.rt_session.SITheoryRaw.
Require Zlib.proof.harness.rt_session.SITheoryZd.
Require Zlib.proof.harness.rt_session.SITheoryGz.
Require Zlib.proof.harness.rt_session.SITheory.
Require Zlib.proof.harness.rt_session.SMain.
Require Zlib.proof.harness.rt_session.SGlobals.
Require Zlib.proof.harness.rt_session.SAsm.

Theorem ses_law : laws_common_ok -> harness_safe Zlib.contracts.rt_session.whole_prog.
Proof.
  intros L.
  exact (Zlib.proof.harness.rt_session.SAsm.ses_asm L Zlib.proof.harness.laws_session.Bodies.laws_session_bodies
    Zlib.proof.harness.rt_session.SDTheory.ses_dtheory
    (Zlib.proof.harness.rt_session.SITheory.ses_itheory_join
       Zlib.proof.harness.rt_session.SITheoryPlain.ses_itheory_plain
       Zlib.proof.harness.rt_session.SITheoryRaw.ses_itheory_raw
       Zlib.proof.harness.rt_session.SITheoryZd.ses_itheory_zdict
       Zlib.proof.harness.rt_session.SITheoryGz.ses_itheory_gz)
    Zlib.proof.harness.rt_session.SMain.ses_main Zlib.proof.harness.rt_session.SGlobals.ses_globals).
Qed.
