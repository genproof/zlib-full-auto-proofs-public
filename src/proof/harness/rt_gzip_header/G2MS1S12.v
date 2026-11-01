(* Law rt_gzip_header, main's body, segment 1: statements 12-14, extra_copy = copy_of(extra, extra_len),
   name_copy = copy_of(name, name_len + 1), comment_copy = copy_of(comment, comment_len + 1). *)
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

Lemma g1s12_ok {Espec : OracleKind} gv vh vg vc vd vr xl nl cl pr ut utm uo uh xp xf np nm cp cm :
  semax Delta_m (QP gv vh vg vc vd vr xl nl cl pr ut utm uo uh xp xf np nm cp cm) (Ssequence (Ssequence S12 S13)
      S14)
    (overridePost (EX xcp : val, EX ncp : val, EX ccp : val, QH gv vh vg vc vd vr xl nl cl pr ut utm uo uh xp xf np
        nm cp cm xcp ncp ccp h00) POST_m).
Proof.
  unfold QP, Qs, fs2, cobjs3, dr_temps, sc_temps, ob_temps, lv_locals, S12, S13, S14. cbn [app].
  unfold Delta_m; simplify_func_tycontext. abbreviate_semax.
  Intros. s1_facts.
  assert_PROP (isptr xp) as Ix by (sep_apply (cobj_isptr xp xf); entailer!).
  assert_PROP (isptr np) as In by (sep_apply (cobj_isptr np (nm ++ [0])); entailer!).
  assert_PROP (isptr cp) as Ic by (sep_apply (cobj_isptr cp (cm ++ [0])); entailer!).
  assert (Ln : Zlength (nm ++ [0]) = nl + 1) by (rewrite Zlength_z0; lia).
  assert (Lc : Zlength (cm ++ [0]) = cl + 1) by (rewrite Zlength_z0; lia).
  rewrite (cobj_cs xp xf xl), (cobj_cs np (nm ++ [0]) (nl + 1)), (cobj_cs cp (cm ++ [0]) (cl + 1)) by assumption.
  flatten_sepcon_in_SEP.
  forward_call (xp, Ews, xp, 0, xl, map vi xf, xl, xf, gv).
  { apply cobj_cbuf; auto. }
  Intros xcp.
  forward_call (np, Ews, np, 0, nl + 1, map vi (nm ++ [0]), nl + 1, nm ++ [0], gv).
  { apply cobj_cbuf; auto using nz_is_bytes. }
  Intros ncp.
  forward_call (cp, Ews, cp, 0, cl + 1, map vi (cm ++ [0]), cl + 1, cm ++ [0], gv).
  { apply cobj_cbuf; auto using nz_is_bytes. }
  Intros ccp. forward.
  Exists xcp ncp ccp.
  destruct POST_m as [r1 r2 r3 r4]; cbn [tycontext.RA_normal].
  unfold QH, Qs, fs2, objs3, cobjs3, dr_temps, sc_temps, ob_temps, cp_temps, lv_locals, dr_ok, u32, obj0.
  cbn [app].
  rewrite (cobj_cs xp xf xl), (cobj_cs np (nm ++ [0]) (nl + 1)), (cobj_cs cp (cm ++ [0]) (cl + 1)) by assumption.
  entailer!.
Qed.
