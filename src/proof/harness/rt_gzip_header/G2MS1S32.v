(* Law rt_gzip_header, main's body, segment 1: statement 32, got.comm_max = (uInt) (comment_len + 1); the values
   drawn and the objects as a gsetup. *)
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

Lemma g1s32_ok {Espec : OracleKind} gv vh vg vc vd vr xl nl cl pr ut utm uo uh xp xf np nm cp cm xcp ncp ccp ul w um
    us gxp gnp gcp :
  semax Delta_m (QG gv vh vg vc vd vr xl nl cl pr ut utm uo uh xp xf np nm cp cm xcp ncp ccp ul w um us (gw gxp (vi
      xl) gnp (vi (nl + 1)) gcp U) [new0 gxp xl; new0 gnp (nl + 1); new0 gcp (cl + 1)]) S32
    (overridePost (EX g : gsetup, NS gv vh vg vc vd vr g []) POST_m).
Proof.
  s1_unfold; unfold S32. cbn [app].
  unfold Delta_m; simplify_func_tycontext. abbreviate_semax.
  Intros. s1_facts.
  forward.
  Exists (mkGS xl nl cl pr (Int.signed (Int.repr ut)) utm (Int.signed (Int.repr uo)) (Int.signed (Int.repr uh))
            (Int.signed (Int.repr ul)) (25 + w) (Int.signed (Int.repr um)) (Int.signed (Int.repr us))
            xp np cp gxp gnp gcp xf nm cm xcp ncp ccp).
  destruct POST_m as [r1 r2 r3 r4]; cbn [tycontext.RA_normal].
  unfold NS, gs_ok0, gp_locals, gs_locals, lv_locals, hvals, hval, gval. rewrite !selp_psel.
  cbn [g_xl g_nl g_cl g_pr g_text g_time g_os g_hcrc g_level g_wb g_mem g_strat g_xp g_np g_cp g_gxp g_gnp g_gcp
       g_xf g_nm g_cm g_xcp g_ncp g_ccp app].
  unfold vi, vl. rewrite !Int.repr_signed.
  rewrite !Int64.Z_mod_modulus_eq, (Z.mod_small cl), (Z.mod_small (cl + 1)) by rep_lia.
  pose proof (Int.signed_range (Int.repr ut)). pose proof (Int.signed_range (Int.repr uo)).
  pose proof (Int.signed_range (Int.repr uh)). pose proof (Int.signed_range (Int.repr ul)).
  pose proof (Int.signed_range (Int.repr um)). pose proof (Int.signed_range (Int.repr us)).
  entailer!.
  unfold RTDIface.rbytes, is_bytes in *.
  eapply Forall_impl; [ | eassumption]; simpl; intros; rep_lia.
Qed.
