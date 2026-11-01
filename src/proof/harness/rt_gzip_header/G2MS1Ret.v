(* Law rt_gzip_header, main's body, segment 1, statement 33: the test of _t'31: main returns 0, or goes on with
   none of the nine objects NULL (A26). *)
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

Lemma g1ret_ok {Espec : OracleKind} gv vh vg vc vd vr g :
  semax Delta_m (NS gv vh vg vc vd vr g [temp _t'31 (vb (f31 g))]) Iret
    (overridePost (EX g' : gsetup, A26 gv vh vg vc vd vr g') POST_m).
Proof.
  unfold NS, Iret, gp_locals, gs_locals, lv_locals. cbn [app].
  unfold Delta_m; simplify_func_tycontext. abbreviate_semax.
  Intros.
  destruct (f31 g) eqn:E.
  - change (vb true) with (Vint Int.one). forward_if; [ | s1_nob].
    forward. Exists (Int.repr 0). apply andp_right; [apply prop_right; reflexivity |].
    do 2 match goal with |- context [data_at Tsh t_g ?v ?p] => sep_apply (data_at_data_at_ Tsh t_g v p) end.
    cancel.
  - change (vb false) with (Vint Int.zero). forward_if; [s1_nob | ].
    unfold f31, f30, f29, f28, f27, nb in E. rewrite !orb_false_iff in E.
    destruct E as [[[[[E1 E2] E3] E4] E5] E6].
    apply nb_false in E1, E2, E3, E4, E5, E6.
    match goal with H : gs_ok0 g |- _ => pose proof H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Lx & _ &
      Ln & _ & Lc & _) end.
    rewrite (obj0_cobj _ _ _ E1) by lia.
    rewrite (obj0_cobj _ _ _ E2) by (rewrite Zlength_z0; lia).
    rewrite (obj0_cobj _ _ _ E3) by (rewrite Zlength_z0; lia).
    rewrite (new0_cnew _ _ E4), (new0_cnew _ _ E5), (new0_cnew _ _ E6).
    assert_PROP (isptr (g_xp g)) as I1 by (sep_apply (cobj_isptr (g_xp g) (g_xf g)); entailer!).
    assert_PROP (isptr (g_np g)) as I2 by (sep_apply (cobj_isptr (g_np g) (g_nm g ++ [0])); entailer!).
    assert_PROP (isptr (g_cp g)) as I3 by (sep_apply (cobj_isptr (g_cp g) (g_cm g ++ [0])); entailer!).
    assert_PROP (isptr (g_xcp g)) as I7 by (sep_apply (cobj_isptr (g_xcp g) (g_xf g)); entailer!).
    assert_PROP (isptr (g_ncp g)) as I8 by (sep_apply (cobj_isptr (g_ncp g) (g_nm g ++ [0])); entailer!).
    assert_PROP (isptr (g_ccp g)) as I9 by (sep_apply (cobj_isptr (g_ccp g) (g_cm g ++ [0])); entailer!).
    assert_PROP (isptr (g_gxp g)) as I4 by (sep_apply (cnew_isptr (g_gxp g) (g_xl g)); entailer!).
    assert_PROP (isptr (g_gnp g)) as I5 by (sep_apply (cnew_isptr (g_gnp g) (g_nl g + 1)); entailer!).
    assert_PROP (isptr (g_gcp g)) as I6 by (sep_apply (cnew_isptr (g_gcp g) (g_cl g + 1)); entailer!).
    forward.
    destruct POST_m as [r1 r2 r3 r4]. cbn [tycontext.RA_normal].
    Exists g. unfold A26, hobjs, hcopies, gbufs, gp_locals, gs_locals, lv_locals. cbn [app].
    entailer!.
    apply gs_ok_of; assumption.
Qed.
