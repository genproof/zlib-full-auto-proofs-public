(* Law rt_gzip_header, main's body, segment 1: statement 17, head.os = os. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.Rep.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rt_gzip_header.CS.
Require Import Zlib.proof.harness.rt_gzip_header.G2MainDefs.
Require Import Zlib.proof.harness.rt_gzip_header.G2MainKit.
Require Import Zlib.proof.harness.rt_gzip_header.G2MS1Kit.
Require Import Zlib.harness.rt_gzip_header.code.
#[local] Existing Instance Zlib.proof.harness.rt_gzip_header.CS.CS.
Local Open Scope logic.

Lemma g1s17_ok {Espec : OracleKind} gv vh vg vc vd vr xl nl cl pr ut utm uo uh xp xf np nm cp cm xcp ncp ccp :
  semax Delta_m (QH gv vh vg vc vd vr xl nl cl pr ut utm uo uh xp xf np nm cp cm xcp ncp ccp (hv (vi ut) (vl utm) U
      U U U U U)) S17
    (overridePost (QH gv vh vg vc vd vr xl nl cl pr ut utm uo uh xp xf np nm cp cm xcp ncp ccp (hv (vi ut) (vl utm)
        (vi uo) U U U U U)) POST_m).
Proof.
  s1_unfold; unfold S17. cbn [app].
  unfold Delta_m; simplify_func_tycontext. abbreviate_semax.
  Intros. s1_facts.
  forward.
  destruct POST_m as [r1 r2 r3 r4]; cbn [tycontext.RA_normal].
  s1_unfold; unfold dr_ok, u32.
  cbn [app].
  entailer!.
Qed.
