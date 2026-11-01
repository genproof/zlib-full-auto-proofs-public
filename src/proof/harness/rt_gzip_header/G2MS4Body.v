(* Law rt_gzip_header on the round-2 harness, main's body, segment 4: one iteration of the deflate loop
   (s4_LI -> s4_LC): avail_out = clip(capacity - (next_out - compressed)), then the call (G2MS4Call.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.harness.rt_gzip_header.CS.
Require Import Zlib.proof.harness.rt_gzip_header.G2MainDefs.
Require Import Zlib.proof.deflate.Rep.
Require Import Zlib.proof.deflate.DSpec Zlib.proof.deflate.DSpecN.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rt_gzip_header.G2DFacts.
Require Import Zlib.proof.harness.rt_gzip_header.G2MainKit.
Require Import Zlib.proof.harness.rt_gzip_header.G2MS4Kit.
Require Import Zlib.proof.harness.rt_gzip_header.G2MS4Call.
Require Import Zlib.harness.rt_gzip_header.code.
#[local] Existing Instance Zlib.proof.harness.rt_gzip_header.CS.CS.
Local Open Scope logic.

Ltac simplify_remove_localdef_temp ::= s4_rlt.

Lemma s4_body_ok {Espec : OracleKind} J0 J gv vh vg vc vd vr g hx Hr b cbp :
  g2_dfacts J0 J ->
  semax Delta_m (s4_LI gv vh vg vc vd vr J g hx Hr b cbp) s4_body
    (normal_ret_assert (s4_LC gv vh vg vc vd vr J g hx Hr b cbp)).
Proof.
  intros DF.
  unfold s4_body. abbreviate_semax.
  unfold s4_LI. Intros O s tin tout adler ao msg msgv.
  match goal with Hj : J _ _ _ _ _ _ _ _ |- _ => rename Hj into HJ end.
  destruct (gd_range _ _ DF _ _ _ _ _ _ _ _ HJ) as (Hwb & Hgh & HO & Hb & RO & Hgz & Htin & Htout & Had).
  unfold s4_mem, s4_locals, gp_locals, gs_locals, lv_locals. cbn [app].
  rewrite s4_fields_L. unfold s4_fieldsL. Intros.
  forward.
  forward_call (b - Zlength O).
  { apply prop_right. apply s4_sameblock; auto. }
  { entailer!.
    replace (force_val (sem_sub_pp tuchar (offset_val (Zlength O) cbp) cbp)) with (Vlong (Int64.repr (Zlength O)))
      by (symmetry; apply (s4_sub_ptr cbp (Zlength O)); auto; unfold max_u64 in *; rep_lia).
    simpl. do 3 f_equal. apply Int64.eqm_samerepr.
    apply Int64.eqm_sub; apply Int64.eqm_sym; apply Int64.eqm_unsigned_repr. }
  { unfold max_u64 in *; rep_lia. }
  forward.
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
  eapply semax_pre; [ | apply (s4_call_ok J0 J gv vh vg vc vd vr g hx Hr b cbp O s tin tout adler msg msgv DF) ].
  assert (Hcl : clipz (b - Zlength O) = Z.min (b - Zlength O) Int.max_unsigned) by reflexivity.
  rewrite <- Hcl.
  assert (U2 : u32_ok (clipz (b - Zlength O))) by (rewrite Hcl; unfold u32_ok, max_u64 in *; rep_lia).
  sep_apply (s4_fields_fold vc nullval 0 tin (offset_val (Zlength O) cbp) (clipz (b - Zlength O)) tout msgv adler);
    auto.
  unfold s4_X1, s4_mem, s4_locals, gp_locals, gs_locals, lv_locals. cbn [app].
  entailer!.
Qed.
