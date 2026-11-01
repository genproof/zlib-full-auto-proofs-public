(* Law rt_gzip_header, main's body, segment 1: statements 23-26, the draws of level, window_bits, mem_level
   and strategy. *)
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

Lemma g1s23_ok {Espec : OracleKind} gv vh vg vc vd vr xl nl cl pr ut utm uo uh xp xf np nm cp cm xcp ncp ccp :
  semax Delta_m (QH gv vh vg vc vd vr xl nl cl pr ut utm uo uh xp xf np nm cp cm xcp ncp ccp (hfin xl pr ut utm uo
      uh xp np cp)) (Ssequence (Ssequence (Ssequence S23 S24) S25) S26)
    (overridePost (EX ul : Z, EX w : Z, EX um : Z, EX us : Z, QG gv vh vg vc vd vr xl nl cl pr ut utm uo uh xp xf np
        nm cp cm xcp ncp ccp ul w um us (gw U U U U U U) []) POST_m).
Proof.
  s1_unfold; unfold S23, S24, S25, S26. cbn [app].
  unfold Delta_m; simplify_func_tycontext. abbreviate_semax.
  Intros. s1_facts.
  forward_call. Intros ul.
  forward_call 6. Intros w.
  forward.
  { entailer!. rewrite Int64.Z_mod_modulus_eq, Z.mod_small by rep_lia. rewrite Int.signed_repr by rep_lia. rep_lia.
      }
  rewrite Int64.unsigned_repr by rep_lia. rewrite !add_repr.
  forward_call. Intros um.
  forward_call. Intros us.
  forward.
  Exists ul w um us.
  destruct POST_m as [r1 r2 r3 r4]; cbn [tycontext.RA_normal].
  s1_unfold; unfold dr_ok, u32.
  cbn [app].
  replace (16 + 9 + w) with (25 + w) by lia.
  entailer!.
Qed.
