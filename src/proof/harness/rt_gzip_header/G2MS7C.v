(* Law rt_gzip_header, main's body, segment 7: statement 42, the check of the extra field:
   gp_assert(same_field(present & 1, got.extra, extra_copy, extra_len)). *)
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

Lemma s42_ok {Espec : OracleKind} gv vh vg vc vd vr g Fr vxf vxl :
  semax Delta_m (Q7 gv vh vg vc vd vr g Fr vxf vxl (rest40 g)) S42
    (overridePost (Q7 gv vh vg vc vd vr g Fr vxf vxl (rest42 g)) POST_m).
Proof.
  unfold Q7, S42, lv_locals, gp_locals, gs_locals.
  unfold Delta_m; simplify_func_tycontext. abbreviate_semax.
  Intros. cbn [app].
  pose proof H as (Rxl & Rnl & Rcl & Rpr & _ & _ & _ & _ & _ & _ & _ & _ & Lx & Bx & Ln & Bn & Lc & Bc &
                   Px & Pn & Pc & Pgx & Pgn & Pgc & _).
  pose proof (gq_pn g 1 _ Pgx).
  unfold gotv, rest40, hx7.
  freeze FR0 := (data_at Tsh t_g _ vh) Fr (mem_mgr gv) (R gv) (gfield g 2 _ _ _) (gfield g 4 _ _ _) (hn7 g)
    (hc7 g).
  forward.
  sep_apply (sf_pre g 1 (g_gxp g) (g_xcp g) (g_xl g) (g_xf g)). Intros.
  freeze FR1 := (data_at Tsh t_g _ vg).
  forward_call (Z.land (g_pr g) 1, gq g 1 (g_gxp g), g_xcp g, g_xl g, Ews, Ews, g_xf g, g_xf g).
  { split; [ pose proof (land_range (g_pr g) 1 Rpr ltac:(lia)); rep_lia | ].
    split; [ intros E; unfold gq; rewrite E; reflexivity | split; apply is_bytes_r; exact Bx ]. }
  rewrite (sf_one g 1 (g_gxp g) (g_xf g) Pgx).
  forward_call (Int.repr 1).
  destruct POST_m as [r1 r2 r3 r4]. cbn [tycontext.RA_normal]. thaw FR1. thaw FR0.
  unfold gotv, rest42. cbn [app]. entailer!.
Qed.
