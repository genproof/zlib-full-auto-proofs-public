(* Law rt_gzip_header, main's body, segment 7: statement 44, the check of the name:
   gp_assert(same_field(present & 2, got.name, name_copy, name_len + 1)). *)
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

Lemma s44_ok {Espec : OracleKind} gv vh vg vc vd vr g Fr vxf vxl :
  semax Delta_m (Q7 gv vh vg vc vd vr g Fr vxf vxl (rest42 g)) S44
    (overridePost (Q7 gv vh vg vc vd vr g Fr vxf vxl (rest44 g)) POST_m).
Proof.
  unfold Q7, S44, lv_locals, gp_locals, gs_locals.
  unfold Delta_m; simplify_func_tycontext. abbreviate_semax.
  Intros. cbn [app].
  pose proof H as (Rxl & Rnl & Rcl & Rpr & _ & _ & _ & _ & _ & _ & _ & _ & Lx & Bx & Ln & Bn & Lc & Bc &
                   Px & Pn & Pc & Pgx & Pgn & Pgc & _).
  pose proof (gq_pn g 2 _ Pgn).
  assert (Ln1 : Zlength (g_nm g ++ [0]) = g_nl g + 1) by (rewrite Zlength_app, Ln; reflexivity).
  unfold gotv, rest42, hn7.
  freeze FR0 := Fr (mem_mgr gv) (R gv) (gfield g 4 _ _ _) (hc7 g) (data_at Tsh t_g _ vh).
  forward.
  sep_apply (sf_pre g 2 (g_gnp g) (g_ncp g) (g_nl g + 1) (g_nm g ++ [0])). Intros.
  freeze FR1 := (data_at Tsh t_g _ vg).
  forward_call (Z.land (g_pr g) 2, gq g 2 (g_gnp g), g_ncp g, g_nl g + 1, Ews, Ews, g_nm g ++ [0], g_nm g ++ [0]).
  { split; [ pose proof (land_range (g_pr g) 2 Rpr ltac:(lia)); rep_lia | ].
    split; [ intros E; unfold gq; rewrite E; reflexivity | split; apply is_bytes_nz; exact Bn ]. }
  rewrite (sf_one g 2 (g_gnp g) (g_nm g ++ [0]) Pgn).
  forward_call (Int.repr 1).
  destruct POST_m as [r1 r2 r3 r4]. cbn [tycontext.RA_normal]. thaw FR1. thaw FR0.
  unfold gotv, rest44. cbn [app]. entailer!.
Qed.
