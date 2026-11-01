(* Law rt_gzip_header, main's body, segment 1: statement 11, `if (!extra || !name || !comment) return 0;`, when
   extra is NULL or name is: main returns. *)
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

Section S11.
Context {Espec : OracleKind} (gv : globals) (vh vg vc vd vr : val) (xl nl cl pr ut utm uo uh : Z)
  (xp : val) (xf : list Z) (np : val) (nm : list Z) (cp : val) (cm : list Z).

Lemma g1s11_xn :
  xp = nullval ->
  semax Delta_m (QO gv vh vg vc vd vr xl nl cl pr ut utm uo uh xp xf np nm cp cm) S11
    (overridePost (QP gv vh vg vc vd vr xl nl cl pr ut utm uo uh xp xf np nm cp cm) POST_m).
Proof.
  intros ->. s11_start. rewrite obj0_null.
  s11_cut _t'13 (Vint Int.one); [s11_cut _t'12 (Vint Int.one) | ].
  - unfold J12; abbreviate_semax. forward_if; [forward; s11_end | s1_nob].
  - unfold J13; abbreviate_semax. forward_if; [forward; s11_end | s1_nob].
  - unfold Jret; abbreviate_semax. forward_if; [ | s1_nob]. s11_ret.
Qed.

Lemma g1s11_pn :
  xp <> nullval -> np = nullval ->
  semax Delta_m (QO gv vh vg vc vd vr xl nl cl pr ut utm uo uh xp xf np nm cp cm) S11
    (overridePost (QP gv vh vg vc vd vr xl nl cl pr ut utm uo uh xp xf np nm cp cm) POST_m).
Proof.
  intros Hx ->. s11_start. rewrite obj0_null, (obj0_cobj xp xl xf Hx) by lia. s1_mkptr xp bx ox.
  s11_cut _t'13 (Vint Int.one); [s11_cut _t'12 (Vint Int.one) | ].
  - unfold J12; abbreviate_semax. forward_if; [s1_tceq | s1_nob | forward; s11_end].
  - unfold J13; abbreviate_semax. forward_if; [forward; s11_end | s1_nob].
  - unfold Jret; abbreviate_semax. forward_if; [ | s1_nob]. s11_ret.
Qed.

End S11.
