(* Law rfc_level0_size, main: statements 16-19 (l0_A16 -> l0_LI): new_stream(&strm), `if (deflateInit2(&strm,
   0, Z_DEFLATED, window_bits, mem_level, strategy) != Z_OK) return 0;`, strm.next_in = data,
   strm.next_out = compressed.  After Z_OK the loop starts from Level0CallsFit.ff_init's invariant at pos 0 with
   nothing produced; any other code returns, the stream given back as the local's memory. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DCS Zlib.proof.deflate.Rep Zlib.proof.deflate.DSpec Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.deflate.LawFacts.
Require Import Zlib.proof.deflate.GlobalsInit.
Require Zlib.proof.deflate.InitStrm.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Zlib.proof.harness.deflate_bound.MainInit.
Require Zlib.proof.harness.rj_deflate_params.RJPMain.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.deflate.Level0CallsFit.
Require Import Zlib.proof.harness.rfc_level0_size.L0S2MainStmt.
Require Import Zlib.proof.harness.rfc_level0_size.L0Kit2.
Require Import Zlib.proof.harness.rfc_level0_size.L0S2Kit.
Require Import Zlib.harness.rfc_level0_size.code.
Module DC := Zlib.deflate.code.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.

Ltac simplify_remove_localdef_temp ::= l0_rlt.

(* `return 0` *)
Ltac ret0 := forward; Exists (Int.repr 0); entailer!.

(* the Ews half of the local (the deflate API's view) and the rest back to the local's memory *)
Lemma l0_join (q : val) : data_at_ Ews t_strm q * data_at_ BoundKit.Ecomp t_zsl q |-- data_at_ Tsh t_zsl q.
Proof. change t_strm with t_zsl. rewrite (BoundKit.data_at__Tsh_split t_zsl q). cancel. Qed.

Lemma seg_init_ok : seg_init_stmt.
Proof.
  intros Espec J gv vs n D dp cp wbits mem strategy room LF K.
  unfold l0_seg16, l0_A16, POST_B, POST_l0. abbreviate_semax.
  Intros.
  match goal with H : l0_cf _ _ _ _ _ _ _ _ |- _ => destruct H as (Hn & HD & HB & Pdp & Pcp & Hw & Hm & Hs & HR) end.
  (* new_stream(&strm) on the Ews half of the local *)
  rewrite (BoundKit.data_at__Tsh_split t_zsl vs). Intros.
  change (data_at_ Ews t_zsl vs) with (data_at_ Ews t_strm vs).
  sep_apply (l0_strm_undef vs).
  forward_call (vs, Ews, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef,
                Vundef, Vundef, Vundef, Vundef).
  sep_apply (Zlib.proof.harness.rj_deflate_params.RJPMain.rjp_new_stream_split vs).
  (* deflateInit2(&strm, 0, Z_DEFLATED, window_bits, mem_level, strategy) *)
  unfold R, version_at.
  forward_call (vs, 0, 8, wbits, mem, strategy, gv vlit, Ers, [49; 46; 51; 46; 50; 0], 112,
                nullval, Vundef, Vundef, Vundef, Vundef, nullval, Vundef, Vundef, gv).
  { change (Zlength [49; 46; 51; 46; 50; 0]) with 6. cancel. }
  { split; [unfold s32_ok; rep_lia|]. split; [unfold s32_ok; rep_lia|].
    split; [unfold s32_ok; rep_lia|]. split; [list_solve|]. split; [cbn; rep_lia|].
    intros a1 a2 a3 a4 a5. apply l0_init_total. }
  Intros vret. destruct vret as [[[[[a1 a2] a3] a4] a5] [[os z1] code]]. cbn [fst snd] in *.
  match goal with H : c_deflateInit2_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _ |- _ => rename H into HI end.
  change (Znth 0 [49; 46; 51; 46; 50; 0] =? 49) with true in HI. change (112 =? 112) with true in HI.
  pose proof HI as HC. apply MainInit.pi_init_code in HC.
  Intros msgv'.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx ((code = 0) :: P) (LOCALx Q (SEPx R))) end.
  { (* deflateInit2_ failed: the stream's memory back to the local's *)
    destruct HC as [-> | [-> Hc]]; [contradiction|].
    Intros st za zf op' dt'.
    change (BoundKit.strm_pad vs) with (MainInit.pi_strm_pad vs).
    sep_apply (MainInit.pi_init_fail9 vs st za zf op' dt' gv nullval
                 (rfv (code =? Z_OK) (z_total_in z1) Vundef) (rfv (code =? Z_OK) (z_total_out z1) Vundef)
                 msgv' (rfv (code =? Z_OK) (z_adler z1) Vundef)).
    sep_apply (l0_join vs).
    ret0. }
  { forward. entailer!.
    destruct HC as [-> | [_ [-> | ->]]]; [reflexivity | |];
      match goal with Hx : Int.repr _ = _ |- _ => apply (f_equal Int.unsigned) in Hx; vm_compute in Hx; discriminate end. }
  Intros. subst code.
  destruct (ff_init _ _ J LF true true false wbits mem strategy a1 a2 a3 a4 a5 zrst0 os z1 D room HI
              HB ltac:(rewrite HD; lia) ltac:(rewrite HD; unfold l0s_slack; lia))
    as (s & -> & HJ0).
  destruct (InitStrm.init_ok_strm _ _ _ _ _ _ _ _ _ _ _ _ _ HI) as (T1 & T2 & T3 & _).
  change (0 =? Z_OK) with true in *. change (0 =? Z_VERSION_ERROR) with false in *. unfold rfv.
  assert (U : u64_ok (z_total_in z1) /\ u64_ok (z_total_out z1) /\ u64_ok (z_adler z1)).
  { rewrite T1, T2. unfold u64_ok. destruct T3 as [-> | ->]; rep_lia. }
  destruct U as (U1 & U2 & U3).
  sep_apply (MainInit.pi_ok_fields vs (z_total_in z1) (z_total_out z1) (z_adler z1) msgv' U1 U2 U3).
  (* strm.next_in = data; strm.next_out = compressed *)
  unfold api_fields. Intros.
  forward. forward.
  sep_apply (l0_api_fold vs dp 0 (z_total_in z1) cp 0 (z_total_out z1) msgv' (z_adler z1)); auto.
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
  eapply semax_pre; [ | apply K ].
  unfold l0_LI. Exists 0 (@nil Z) s (z_total_in z1) (z_total_out z1) (z_adler z1) 0 0 (z_msg z1) msgv'.
  unfold l0_comp, l0_srest, R, version_at.
  rewrite !isptr_offset_val_zero by auto.
  change (Zlength (@nil Z)) with 0. rewrite Z.sub_0_r.
  assert (HJ : J wbits D room 0 [] s (z_total_in z1) (z_total_out z1) (z_adler z1)) by exact HJ0.
  entailer!.
Qed.
