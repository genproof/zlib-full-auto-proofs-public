(* Law rt_gzip_header, main's body, segment 1: statement 11, `if (!extra || !name || !comment) return 0;`, when
   none of extra, name and comment is NULL: main goes on; and all cases together. *)
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
Require Import Zlib.proof.harness.rt_gzip_header.G2MS1S11a.
Require Import Zlib.proof.harness.rt_gzip_header.G2MS1S11b.
Require Import Zlib.harness.rt_gzip_header.code.
#[local] Existing Instance Zlib.proof.harness.rt_gzip_header.CS.CS.
Local Open Scope logic.

Section S11.
Context {Espec : OracleKind} (gv : globals) (vh vg vc vd vr : val) (xl nl cl pr ut utm uo uh : Z)
  (xp : val) (xf : list Z) (np : val) (nm : list Z) (cp : val) (cm : list Z).

Lemma g1s11_ppp :
  xp <> nullval -> np <> nullval -> cp <> nullval ->
  semax Delta_m (QO gv vh vg vc vd vr xl nl cl pr ut utm uo uh xp xf np nm cp cm) S11
    (overridePost (QP gv vh vg vc vd vr xl nl cl pr ut utm uo uh xp xf np nm cp cm) POST_m).
Proof.
  intros Hx Hn Hc. s11_start. rewrite (obj0_cobj xp xl xf Hx) by lia.
  rewrite (obj0_cobj np (nl + 1) (nm ++ [0]) Hn) by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
  rewrite (obj0_cobj cp (cl + 1) (cm ++ [0]) Hc) by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
  s1_mkptr xp bx ox. s1_mkptr np bn on. s1_mkptr cp bc oc.
  s11_cut _t'13 (Vint Int.zero); [s11_cut _t'12 (Vint Int.zero) | ].
  - unfold J12; abbreviate_semax. forward_if; [s1_tceq | s1_nob | forward; [s1_tceq | s11_end]].
  - unfold J13; abbreviate_semax. forward_if; [s1_nob | forward; [s1_tceq | s11_end]].
  - unfold Jret; abbreviate_semax. forward_if; [s1_nob | ]. forward. s11_end.
Qed.
End S11.

(* statement 11: main goes on only with the three objects *)
Lemma g1s11_ok {Espec : OracleKind} gv vh vg vc vd vr xl nl cl pr ut utm uo uh xp xf np nm cp cm :
  semax Delta_m (QO gv vh vg vc vd vr xl nl cl pr ut utm uo uh xp xf np nm cp cm) S11
    (overridePost (QP gv vh vg vc vd vr xl nl cl pr ut utm uo uh xp xf np nm cp cm) POST_m).
Proof.
  destruct (eq_dec xp nullval); [now apply g1s11_xn |].
  destruct (eq_dec np nullval); [now apply g1s11_pn |].
  destruct (eq_dec cp nullval); [now apply g1s11_ppn | now apply g1s11_ppp].
Qed.
