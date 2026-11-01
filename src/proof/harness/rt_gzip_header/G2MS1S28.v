(* Law rt_gzip_header, main's body, segment 1: statement 28, got.extra_max = (uInt) extra_len. *)
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

Lemma g1s28_ok {Espec : OracleKind} gv vh vg vc vd vr xl nl cl pr ut utm uo uh xp xf np nm cp cm xcp ncp ccp ul w um
    us gxp :
  semax Delta_m (QG gv vh vg vc vd vr xl nl cl pr ut utm uo uh xp xf np nm cp cm xcp ncp ccp ul w um us (gw gxp U U
      U U U) [new0 gxp xl]) S28
    (overridePost (QG gv vh vg vc vd vr xl nl cl pr ut utm uo uh xp xf np nm cp cm xcp ncp ccp ul w um us (gw gxp
        (vi xl) U U U U) [new0 gxp xl]) POST_m).
Proof.
  s1_unfold; unfold S28. cbn [app].
  unfold Delta_m; simplify_func_tycontext. abbreviate_semax.
  Intros. s1_facts.
  forward.
  destruct POST_m as [r1 r2 r3 r4]; cbn [tycontext.RA_normal].
  s1_unfold; unfold dr_ok, u32, new0, obj0, nzbytes.
  cbn [app].
  rewrite Int64.Z_mod_modulus_eq, Z.mod_small by rep_lia.
  entailer!.
Qed.
