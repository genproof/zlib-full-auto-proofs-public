(* Law rt_gzip_header, main's body, segment 1: statement 22, head.comment = (present & 4) ? comment : Z_NULL. *)
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

Lemma g1s22_ok {Espec : OracleKind} gv vh vg vc vd vr xl nl cl pr ut utm uo uh xp xf np nm cp cm xcp ncp ccp :
  semax Delta_m (QH gv vh vg vc vd vr xl nl cl pr ut utm uo uh xp xf np nm cp cm xcp ncp ccp (hv (vi ut) (vl utm)
      (vi uo) (psel pr 1 xp) (vi xl) (psel pr 2 np) U (vi uh))) S22
    (overridePost (QH gv vh vg vc vd vr xl nl cl pr ut utm uo uh xp xf np nm cp cm xcp ncp ccp (hfin xl pr ut utm uo
        uh xp np cp)) POST_m).
Proof.
  s1_unfold; unfold S22. cbn [app].
  unfold Delta_m; simplify_func_tycontext. abbreviate_semax.
  Intros. s1_facts.
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?S))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _t'19 (psel pr 4 cp) :: L) (SEPx S))) end.
  - forward. rewrite (psel_nz pr 4 cp) by (auto; rep_lia). entailer!.
  - forward. rewrite (psel_zero pr 4 cp) by (auto; rep_lia). entailer!.
  - forward.
    destruct POST_m as [r1 r2 r3 r4]; cbn [tycontext.RA_normal].
    s1_unfold; unfold dr_ok, u32, new0, obj0, nzbytes.
    cbn [app].
    entailer!.
Qed.
