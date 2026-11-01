(* Law rt_gzip_header, main's body, segment 7: the first part of statement 40 (G2MS7Kit.S40a), the test
   got.done == 1 && got.text == (text != 0) of gp_assert(got.done == 1 && got.text == (text != 0) &&
   got.hcrc == (hcrc != 0)) (text and hcrc are main's locals). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.harness.rt_gzip_header.CS.
Require Import Zlib.proof.harness.rt_gzip_header.G2MainDefs.
Require Import Zlib.proof.harness.rt_gzip_header.G2MainKit.
Require Import Zlib.proof.harness.rt_gzip_header.G2MS7Kit.
Require Import Zlib.harness.rt_gzip_header.code.
#[local] Existing Instance Zlib.proof.harness.rt_gzip_header.CS.CS.
Local Open Scope logic.

Lemma s40a_ok {Espec : OracleKind} gv vh vg vc vd vr g Fr vxf vxl :
  semax Delta_m (Q7 gv vh vg vc vd vr g Fr vxf vxl (rest40 g)) S40a
    (overridePost (Q7x gv vh vg vc vd vr g Fr vxf vxl [temp _t'44 (Vint Int.one)] (rest40 g)) POST_m).
Proof.
  unfold Q7, Q7x, S40a, lv_locals, gp_locals, gs_locals.
  unfold Delta_m; simplify_func_tycontext. abbreviate_semax.
  Intros. cbn [app].
  pose proof H as (_ & _ & _ & _ & Rt & _).
  unfold gotv, rest40.
  freeze FR0 := (data_at Tsh t_g _ vh) Fr (mem_mgr gv) (R gv) (gfield g 1 _ _ _) (gfield g 2 _ _ _)
    (gfield g 4 _ _ _) (hx7 g) (hn7 g) (hc7 g).
  forward.
  forward_if.
  { forward. forward. rewrite (flag_eq (g_text g) Rt).
    destruct POST_m as [r1 r2 r3 r4]. cbn [tycontext.RA_normal]. thaw FR0.
    unfold gotv, rest40. cbn [app]. entailer!. }
  { exfalso. auto. }
Qed.
