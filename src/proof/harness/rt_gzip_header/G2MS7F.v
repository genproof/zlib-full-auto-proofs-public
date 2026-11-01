(* Law rt_gzip_header, main's body, segment 7: statements 45 and 46, the check of the comment and the return:
   gp_assert(same_field(present & 4, got.comment, comment_copy, comment_len + 1)), return 0. *)
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

Lemma s45_ok {Espec : OracleKind} gv vh vg vc vd vr g Fr vxf vxl :
  semax Delta_m (Q7 gv vh vg vc vd vr g Fr vxf vxl (rest44 g)) S45
    (overridePost (Q7 gv vh vg vc vd vr g Fr vxf vxl []) POST_m).
Proof.
  unfold Q7, S45, lv_locals, gp_locals, gs_locals.
  unfold Delta_m; simplify_func_tycontext. abbreviate_semax.
  Intros. cbn [app].
  pose proof H as (Rxl & Rnl & Rcl & Rpr & _ & _ & _ & _ & _ & _ & _ & _ & Lx & Bx & Ln & Bn & Lc & Bc &
                   Px & Pn & Pc & Pgx & Pgn & Pgc & _).
  pose proof (gq_pn g 4 _ Pgc).
  assert (Lc1 : Zlength (g_cm g ++ [0]) = g_cl g + 1) by (rewrite Zlength_app, Lc; reflexivity).
  unfold gotv, rest44, hc7.
  freeze FR0 := Fr (mem_mgr gv) (R gv) (data_at Tsh t_g _ vh).
  forward.
  sep_apply (sf_pre g 4 (g_gcp g) (g_ccp g) (g_cl g + 1) (g_cm g ++ [0])). Intros.
  freeze FR1 := (data_at Tsh t_g _ vg).
  forward_call (Z.land (g_pr g) 4, gq g 4 (g_gcp g), g_ccp g, g_cl g + 1, Ews, Ews, g_cm g ++ [0], g_cm g ++ [0]).
  { split; [ pose proof (land_range (g_pr g) 4 Rpr ltac:(lia)); rep_lia | ].
    split; [ intros E; unfold gq; rewrite E; reflexivity | split; apply is_bytes_nz; exact Bc ]. }
  rewrite (sf_one g 4 (g_gcp g) (g_cm g ++ [0]) Pgc).
  forward_call (Int.repr 1).
  destruct POST_m as [r1 r2 r3 r4]. cbn [tycontext.RA_normal]. thaw FR1. thaw FR0.
  unfold gotv, hvals, hval. cbn [app]. entailer!.
Qed.

(* return 0: main's five locals are given back (head and got from their structs, the other three by dback), the
   rest goes to TT *)
Lemma s46_ok {Espec : OracleKind} gv vh vg vc vd vr g Fr vxf vxl :
  semax Delta_m (Q7 gv vh vg vc vd vr g Fr vxf vxl []) S46 POST_m.
Proof.
  unfold Q7, S46, POST_m, lv_locals, gp_locals, gs_locals.
  unfold Delta_m; simplify_func_tycontext. abbreviate_semax.
  Intros. cbn [app].
  forward. Exists (Int.repr 0). apply andp_right; [ apply prop_right; reflexivity | ].
  do 2 match goal with |- context [data_at Tsh t_g ?v ?p] => sep_apply (data_at_data_at_ Tsh t_g v p) end.
  match goal with Hb : dback _ _ _ _ |- _ => unfold dback in Hb; sep_apply Hb end. cancel.
Qed.
