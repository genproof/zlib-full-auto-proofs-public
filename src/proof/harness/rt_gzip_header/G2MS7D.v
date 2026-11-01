(* Law rt_gzip_header, main's body, segment 7: statement 43, the check of the extra field's length:
   gp_assert(!(present & 1) || got.extra_len == extra_len). *)
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

Lemma s43_ok {Espec : OracleKind} gv vh vg vc vd vr g Fr vxf vxl :
  semax Delta_m (Q7 gv vh vg vc vd vr g Fr vxf vxl (rest42 g)) S43
    (overridePost (Q7 gv vh vg vc vd vr g Fr vxf vxl (rest42 g)) POST_m).
Proof.
  unfold Q7, S43, lv_locals, gp_locals, gs_locals.
  unfold Delta_m; simplify_func_tycontext. abbreviate_semax.
  Intros. cbn [app].
  pose proof H as (Rxl & Rnl & Rcl & Rpr & _).
  unfold gotv, rest42.
  freeze FR := (data_at Tsh t_g _ vh) Fr (mem_mgr gv) (R gv) (gfield g 2 _ _ _) (gfield g 4 _ _ _) (hn7 g) (hc7 g).
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _t'48 (Vint Int.one) :: Q) (SEPx R))) end.
  { forward. entailer!. }
  { assert (E : Z.land (g_pr g) 1 =? 0 = false).
    { match goal with Hc : Int.and _ _ <> Int.zero |- _ => rewrite land_repr in Hc by lia end.
      destruct (Z.eqb_spec (Z.land (g_pr g) 1) 0) as [E0 | ]; [ | reflexivity ].
      exfalso. rewrite E0 in *. contradiction. }
    match goal with Hx : _ = false -> vxl = _ |- _ => rewrite (Hx E) end.
    forward.
    forward.
    match goal with Hx : _ = false -> vxl = _ |- _ => rewrite (Hx E) end.
    rewrite Int.unsigned_repr by rep_lia. destruct (zeq (g_xl g) (g_xl g)); [ | congruence ].
    freeze FR2 := (data_at Tsh t_g _ vg). entailer!. thaw FR2. cancel. }
  forward_call (Int.repr 1).
  destruct POST_m as [r1 r2 r3 r4]. cbn [tycontext.RA_normal]. thaw FR.
  unfold gotv, rest42. cbn [app]. entailer!.
Qed.
