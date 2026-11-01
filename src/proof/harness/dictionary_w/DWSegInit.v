(* Laws rt_dictionary and api_dict_id, main (DWKit.v): statements 13-14 (rt_dictionary's numbers; 12-13 in api_dict_id), new_stream(&compressor) and deflateInit2 with its test (A10 -> A12, DWFacts.dw_init), in each program's context (the version literal differs). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.EnvBodies.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Zlib.proof.deflate.DSpec9.
Require Zlib.proof.deflate.GlobalsInit.
Require Zlib.proof.deflate.InitStrm.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.clip_streams.CS.
Require Import Zlib.proof.harness.clip_streams.Globals.
Require Import Zlib.proof.harness.clip_streams.RTKit.
Require Import Zlib.proof.harness.clip_streams.RTMem.
Require Zlib.proof.harness.clip_streams.RTSegInit.
Require Zlib.proof.harness.deflate_bound.MainInit.
Require Import Zlib.proof.harness.dictionary_w.DWCS.
Require Import Zlib.proof.harness.dictionary_w.DWFacts.
Require Import Zlib.proof.harness.dictionary_w.DWMainDefs.
Require Import Zlib.proof.harness.dictionary_w.DWKit.
#[local] Existing Instance CS.CS.
Local Open Scope logic.

Ltac simplify_remove_localdef_temp ::= rt_rlt.

(* rt_dictionary (main's context Delta_drt, version literal lit_drt) *)
Lemma seg_init_drt_ok : seg_init_drt_stmt.
Proof.
  intros Espec J0 J1 J gv vc vd n D dp op dict ddp level wbits mem strategy DF.
  unfold seg_init_drt, A10, POST_drt, POST_of. abbreviate_semax.
  Intros.
  rename H into Hcf. rename H0 into Hl. rename H1 into Hm. rename H2 into Hs.
  pose proof Hcf as (Hn & HD & HB & Pdp & Pop & Hdl & Hdb & Pddp & Hw).
  rewrite RTSegInit.rt_strm_undef.
  forward_call (vc, Tsh, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef,
                Vundef, Vundef, Vundef).
  rewrite RTSegInit.rt_ns_dcs.
  sep_apply (BoundKit.data_at_Tsh_split (cs := Zlib.proof.deflate.DCS.CS) t_strm
    (nullval, (vi 0, (Vundef, (nullval, (vi 0, (Vundef, (Vundef, (Vundef,
     (nullval, (nullval, (nullval, (Vundef, (Vundef, Vundef))))))))))))) vc).
  rewrite rt_strm_data_at__cs.
  sep_apply (RTSegInit.rt_ns_split vc).
  unfold R_of. Intros.
  unfold GlobalsInit.version_at, lit_drt.
  forward_call (vc, level, 8, wbits, mem, strategy, gv DRT.___stringlit_rt_dictionary_1, Ers,
                [49; 46; 51; 46; 50; 0], 112, nullval, Vundef, Vundef, Vundef, Vundef, nullval, Vundef, Vundef, gv).
  { unfold s32_ok. repeat (split; [solve [rep_lia | list_solve | cbn; rep_lia] |]).
    intros a1 a2 a3 a4 a5. exact (proj1 (dw_init _ _ _ DF level wbits mem strategy a1 a2 a3 a4 a5 Hl Hm Hs Hw)). }
  Intros vret. destruct vret as [[[[[a1 a2] a3] a4] a5] [[os z'] code]]. cbn [fst snd] in *.
  match goal with H : c_deflateInit2_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _ |- _ => rename H into HI end.
  change (Znth 0 [49; 46; 51; 46; 50; 0] =? 49) with true in HI. change (112 =? 112) with true in HI.
  pose proof (proj2 (dw_init _ _ _ DF level wbits mem strategy a1 a2 a3 a4 a5 Hl Hm Hs Hw) _ _ _ HI) as Hok.
  pose proof HI as HC. apply MainInit.pi_init_code in HC.
  Intros msgv'.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx ((code = 0) :: P) (LOCALx Q (SEPx R))) end.
  { destruct HC as [-> | [-> Hc]]; [contradiction|].
    Intros st za zf op' dt'.
    change (BoundKit.strm_pad vc) with (MainInit.pi_strm_pad vc).
    sep_apply (MainInit.pi_init_fail9 vc st za zf op' dt' gv nullval
                 (DSpec9.rfv (code =? Z_OK) (z_total_in z') Vundef) (DSpec9.rfv (code =? Z_OK) (z_total_out z') Vundef)
                 msgv' (DSpec9.rfv (code =? Z_OK) (z_adler z') Vundef)).
    sep_apply (RTSegInit.rt_join vc).
    ret0. }
  { forward. entailer!.
    destruct HC as [-> | [_ [-> | ->]]]; [reflexivity | |];
      match goal with Hx : Int.repr _ = _ |- _ => apply (f_equal Int.unsigned) in Hx; vm_compute in Hx; discriminate end. }
  Intros. subst code.
  destruct (Hok eq_refl) as (s & -> & HJ0).
  destruct (InitStrm.init_ok_strm _ _ _ _ _ _ _ _ _ _ _ _ _ HI) as (T1 & T2 & T3 & _).
  change (0 =? Z_OK) with true in *. change (0 =? Z_VERSION_ERROR) with false in *. unfold DSpec9.rfv.
  assert (U : u64_ok (z_total_in z') /\ u64_ok (z_total_out z') /\ u64_ok (z_adler z')).
  { rewrite T1, T2. unfold u64_ok. destruct T3 as [-> | ->]; rep_lia. }
  destruct U as (U1 & U2 & U3).
  sep_apply (MainInit.pi_ok_fields vc (z_total_in z') (z_total_out z') (z_adler z') msgv' U1 U2 U3).
  Exists s (z_total_in z') (z_total_out z') (z_adler z') (z_msg z') msgv'.
  unfold A12, rt_srest, R_of, lit_drt.
  change (MainInit.pi_strm_pad vc) with (BoundKit.strm_pad vc).
  entailer!.
Qed.

(* api_dict_id: the same proof with its own context and literal *)
Lemma seg_init_dai_ok : seg_init_dai_stmt.
Proof.
  intros Espec J0 J1 J gv vc vd n D dp op dict ddp level wbits mem strategy DF.
  unfold seg_init_dai, A10, POST_dai, POST_of. abbreviate_semax.
  Intros.
  rename H into Hcf. rename H0 into Hl. rename H1 into Hm. rename H2 into Hs.
  pose proof Hcf as (Hn & HD & HB & Pdp & Pop & Hdl & Hdb & Pddp & Hw).
  rewrite RTSegInit.rt_strm_undef.
  forward_call (vc, Tsh, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef,
                Vundef, Vundef, Vundef).
  rewrite RTSegInit.rt_ns_dcs.
  sep_apply (BoundKit.data_at_Tsh_split (cs := Zlib.proof.deflate.DCS.CS) t_strm
    (nullval, (vi 0, (Vundef, (nullval, (vi 0, (Vundef, (Vundef, (Vundef,
     (nullval, (nullval, (nullval, (Vundef, (Vundef, Vundef))))))))))))) vc).
  rewrite rt_strm_data_at__cs.
  sep_apply (RTSegInit.rt_ns_split vc).
  unfold R_of. Intros.
  unfold GlobalsInit.version_at, lit_dai.
  forward_call (vc, level, 8, wbits, mem, strategy, gv DAI.___stringlit_api_dict_id_1, Ers,
                [49; 46; 51; 46; 50; 0], 112, nullval, Vundef, Vundef, Vundef, Vundef, nullval, Vundef, Vundef, gv).
  { unfold s32_ok. repeat (split; [solve [rep_lia | list_solve | cbn; rep_lia] |]).
    intros a1 a2 a3 a4 a5. exact (proj1 (dw_init _ _ _ DF level wbits mem strategy a1 a2 a3 a4 a5 Hl Hm Hs Hw)). }
  Intros vret. destruct vret as [[[[[a1 a2] a3] a4] a5] [[os z'] code]]. cbn [fst snd] in *.
  match goal with H : c_deflateInit2_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _ |- _ => rename H into HI end.
  change (Znth 0 [49; 46; 51; 46; 50; 0] =? 49) with true in HI. change (112 =? 112) with true in HI.
  pose proof (proj2 (dw_init _ _ _ DF level wbits mem strategy a1 a2 a3 a4 a5 Hl Hm Hs Hw) _ _ _ HI) as Hok.
  pose proof HI as HC. apply MainInit.pi_init_code in HC.
  Intros msgv'.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx ((code = 0) :: P) (LOCALx Q (SEPx R))) end.
  { destruct HC as [-> | [-> Hc]]; [contradiction|].
    Intros st za zf op' dt'.
    change (BoundKit.strm_pad vc) with (MainInit.pi_strm_pad vc).
    sep_apply (MainInit.pi_init_fail9 vc st za zf op' dt' gv nullval
                 (DSpec9.rfv (code =? Z_OK) (z_total_in z') Vundef) (DSpec9.rfv (code =? Z_OK) (z_total_out z') Vundef)
                 msgv' (DSpec9.rfv (code =? Z_OK) (z_adler z') Vundef)).
    sep_apply (RTSegInit.rt_join vc).
    ret0. }
  { forward. entailer!.
    destruct HC as [-> | [_ [-> | ->]]]; [reflexivity | |];
      match goal with Hx : Int.repr _ = _ |- _ => apply (f_equal Int.unsigned) in Hx; vm_compute in Hx; discriminate end. }
  Intros. subst code.
  destruct (Hok eq_refl) as (s & -> & HJ0).
  destruct (InitStrm.init_ok_strm _ _ _ _ _ _ _ _ _ _ _ _ _ HI) as (T1 & T2 & T3 & _).
  change (0 =? Z_OK) with true in *. change (0 =? Z_VERSION_ERROR) with false in *. unfold DSpec9.rfv.
  assert (U : u64_ok (z_total_in z') /\ u64_ok (z_total_out z') /\ u64_ok (z_adler z')).
  { rewrite T1, T2. unfold u64_ok. destruct T3 as [-> | ->]; rep_lia. }
  destruct U as (U1 & U2 & U3).
  sep_apply (MainInit.pi_ok_fields vc (z_total_in z') (z_total_out z') (z_adler z') msgv' U1 U2 U3).
  Exists s (z_total_in z') (z_total_out z') (z_adler z') (z_msg z') msgv'.
  unfold A12, rt_srest, R_of, lit_dai.
  change (MainInit.pi_strm_pad vc) with (BoundKit.strm_pad vc).
  entailer!.
Qed.

Lemma seg_init_ok : seg_init_drt_stmt /\ seg_init_dai_stmt.
Proof. exact (conj seg_init_drt_ok seg_init_dai_ok). Qed.
