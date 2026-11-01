(* Law rt_gzip_header, main's body, segment 1: statement 27, got.extra = malloc(extra_len). *)
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

Lemma g1s27_ok {Espec : OracleKind} gv vh vg vc vd vr xl nl cl pr ut utm uo uh xp xf np nm cp cm xcp ncp ccp ul w um
    us :
  semax Delta_m (QG gv vh vg vc vd vr xl nl cl pr ut utm uo uh xp xf np nm cp cm xcp ncp ccp ul w um us (gw U U U U
      U U) []) S27
    (overridePost (EX gxp : val, QG gv vh vg vc vd vr xl nl cl pr ut utm uo uh xp xf np nm cp cm xcp ncp ccp ul w um
        us (gw gxp U U U U U) [new0 gxp xl]) POST_m).
Proof.
  s1_unfold; unfold S27. cbn [app].
  unfold Delta_m; simplify_func_tycontext. abbreviate_semax.
  Intros. s1_facts.
  forward_call (tarray tuchar xl, gv). { simpl. rewrite Z.max_r by lia. rep_lia. } Intros gxp.
  forward.
  Exists gxp.
  destruct POST_m as [r1 r2 r3 r4]; cbn [tycontext.RA_normal].
  s1_unfold; unfold dr_ok, u32, new0.
  cbn [app].
  entailer!.
Qed.
