(* Law rt_gzip_header, main's body, segment 7: statement 41, the check of got's os and time:
   gp_assert(got.os == (os & 255) && got.time == time); its test is G2MS7B1.s41a_ok. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.harness.rt_gzip_header.CS.
Require Import Zlib.proof.harness.rt_gzip_header.G2MainDefs.
Require Import Zlib.proof.harness.rt_gzip_header.G2MainKit.
Require Import Zlib.proof.harness.rt_gzip_header.G2MS7Kit.
Require Import Zlib.proof.harness.rt_gzip_header.G2MS7B1.
Require Import Zlib.harness.rt_gzip_header.code.
#[local] Existing Instance Zlib.proof.harness.rt_gzip_header.CS.CS.
Local Open Scope logic.

Lemma s41b_ok {Espec : OracleKind} gv vh vg vc vd vr g Fr vxf vxl :
  semax Delta_m (Q7x gv vh vg vc vd vr g Fr vxf vxl [temp _t'46 (Vint Int.one)] (rest40 g)) S41b
    (overridePost (Q7 gv vh vg vc vd vr g Fr vxf vxl (rest40 g)) POST_m).
Proof.
  unfold Q7x, Q7, S41b, lv_locals, gp_locals, gs_locals.
  unfold Delta_m; simplify_func_tycontext. abbreviate_semax.
  Intros. cbn [app].
  forward_call (Int.repr 1).
  destruct POST_m as [r1 r2 r3 r4]. cbn [tycontext.RA_normal]. unfold rest40. cbn [app]. entailer!.
Qed.

Lemma s41_ok {Espec : OracleKind} gv vh vg vc vd vr g Fr vxf vxl :
  semax Delta_m (Q7 gv vh vg vc vd vr g Fr vxf vxl (rest40 g)) S41
    (overridePost (Q7 gv vh vg vc vd vr g Fr vxf vxl (rest40 g)) POST_m).
Proof.
  rewrite S41_split. eapply semax_seq; [ | apply s41b_ok ]. apply s41a_ok.
Qed.
