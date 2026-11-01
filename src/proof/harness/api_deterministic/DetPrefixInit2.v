(* Law api_deterministic (data of any length): the two deflateInit2_ calls of main (DetPrefixKit2.det_init_stmt),
   on the streams made by new_stream; each call is defined for the parameters drawn (DetFacts2.df2_init). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Rep.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.deflate.DetFacts2.
Require Zlib.proof.deflate.DModel5.
Require Import Zlib.proof.deflate.DetGz.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.api_deterministic.DetCS2.
Require Import Zlib.proof.harness.api_deterministic.DetMainStmt2.
Require Import Zlib.proof.harness.api_deterministic.DetKit2.
Require Import Zlib.proof.harness.api_deterministic.DetPrefixKit2.
Require Import Zlib.harness.api_deterministic.code.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.

(* after_forward_call builds [remove_localdef_temp] syntactically (DetPrefixKit2.rlt_list) *)
Local Ltac simplify_remove_localdef_temp ::=
  match goal with |- context [remove_localdef_temp ?i ?L] =>
    let u' := rlt_list i L in change (remove_localdef_temp i L) with u' end.

Lemma det_init : det_init_stmt.
Proof.
  intros Espec v1 v2 gv J JF level wbits mem strategy n bs datap K.
  unfold P10, P_loc, new_strm, msuf10, Delta_m, Gmain, POST_m. simplify_func_tycontext.
  abbreviate_semax. Intros.
  rename H into Hpre, H0 into Hv. pose proof Hpre as (H3 & H4 & H5 & H6 & H & H0 & H1 & Pdp).
  sep_apply (det_new_stream_split v1). sep_apply (det_new_stream_split v2).
  unfold version_at.
  assert (S : s32 level /\ s32 wbits /\ s32 mem /\ s32 strategy) by (unfold s32; rep_lia).
  destruct S as (S1 & S3 & S4 & S5).
  pose proof (fun a1 a2 a3 a4 a5 => df2_init _ JF level wbits mem strategy a1 a2 a3 a4 a5 zrst0
                S1 S3 S4 S5) as FIN.
  forward_call (v1, level, 8, wbits, mem, strategy, gv vlit, Ers, [49; 46; 51; 46; 50; 0], 112,
                nullval, Vundef, Vundef, Vundef, Vundef, nullval, Vundef, Vundef, gv).
  { split; [unfold s32_ok; rep_lia|]. split; [unfold s32_ok; rep_lia|]. split; [list_solve|].
    split; [cbn; rep_lia|].
    intros a1 a2 a3 a4 a5. exact (proj1 (FIN a1 a2 a3 a4 a5)). }
  Intros vret. destruct vret as [[[[[a1 a2] a3] a4] a5] [[os z'] code]]. cbn [fst snd] in *.
  match goal with H : c_deflateInit2_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _ |- _ => rename H into HI end.
  change (Znth 0 [49; 46; 51; 46; 50; 0] =? 49) with true in HI. change (112 =? 112) with true in HI.
  Intros msgv1.
  forward_call (v2, level, 8, wbits, mem, strategy, gv vlit, Ers, [49; 46; 51; 46; 50; 0], 112,
                nullval, Vundef, Vundef, Vundef, Vundef, nullval, Vundef, Vundef, gv).
  { split; [unfold s32_ok; rep_lia|]. split; [unfold s32_ok; rep_lia|]. split; [list_solve|].
    split; [cbn; rep_lia|].
    intros b1 b2 b3 b4 b5. exact (proj1 (FIN b1 b2 b3 b4 b5)). }
  Intros vret. destruct vret as [[[[[b1 b2] b3] b4] b5] [[os2 z2] code2]]. cbn [fst snd] in *.
  match goal with H : c_deflateInit2_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _ |- _ => rename H into HI2 end.
  change (Znth 0 [49; 46; 51; 46; 50; 0] =? 49) with true in HI2. change (112 =? 112) with true in HI2.
  Intros msgv2.
  (* the outcomes of the two calls *)
  assert (R1 : init_run level wbits mem strategy os z' code) by (exists a1, a2, a3, a4, a5; exact HI).
  assert (R2 : init_run level wbits mem strategy os2 z2 code2) by (exists b1, b2, b3, b4, b5; exact HI2).
  eapply semax_pre; [| apply (K os z' code msgv1 os2 z2 code2 msgv2)].
  unfold P12, P_loc, init_res, init_msg, version_at. entailer!.
Qed.
