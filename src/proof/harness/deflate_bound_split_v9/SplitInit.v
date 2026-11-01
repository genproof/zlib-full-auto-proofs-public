(* Law deflate_bound_split, main: r = deflateInit2(..); if (r != Z_OK) return 0; (statements 35, 36) (SplitKit.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DCS Zlib.proof.deflate.DSpec Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.deflate.LawFacts Zlib.proof.deflate.HarnessLib Zlib.proof.deflate.GlobalsInit.
Require Zlib.proof.deflate.Obligations.
Require Import Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.harness.x_deflate_bound_split.code.
Require Import Zlib.proof.harness.deflate_bound_split_v9.SplitMain Zlib.proof.harness.deflate_bound_split_v9.SplitKit.
Require Import Zlib.proof.deflate.InitStrm.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.

Lemma pi_keep s z s' z' r :
  c_deflateResetKeep s z = Some (s', z', r) -> bad_state s = false -> r = Z_OK.
Proof.
  unfold c_deflateResetKeep. intros H Hb. rewrite Hb in H.
  destruct (if d_wrap _ <? 0 then _ else _) as [s1|]; [|discriminate].
  simpl in H.
  do 4 (try match type of H with context [bind ?x _] =>
    lazymatch x with Some _ => fail | None => fail | _ => destruct x; simpl in H; try discriminate end end).
  inversion H; reflexivity.
Qed.

Lemma pi_reset s z s' z' r :
  c_deflateReset s z = Some (s', z', r) -> bad_state s = false -> r = Z_OK.
Proof.
  unfold c_deflateReset. intros H Hb.
  destruct (c_deflateResetKeep s z) as [[[a b] c]|] eqn:E; [|discriminate].
  pose proof (pi_keep _ _ _ _ _ E Hb); subst c. simpl in H.
  destruct (c_lm_init a); [|discriminate]. inversion H; reflexivity.
Qed.

Lemma pi_bs_init w b h l t m : bad_state (set_d_method (set_d_tr (init_dstate w b h l) t) m) = false.
Proof. reflexivity. Qed.

Lemma pi_bs_fin s : bad_state (set_d_status s FINISH_STATE) = false.
Proof. reflexivity. Qed.

Lemma pi_end_bind S Z os z' code :
  bind (c_deflateEnd (set_d_status S FINISH_STATE) Z)
    (fun p => let '(os0, z1, _) := p in Some (os0, z1, Z_MEM_ERROR)) = Some (os, z', code) ->
  os = None /\ code = Z_MEM_ERROR.
Proof.
  intros H. unfold c_deflateEnd in H. rewrite pi_bs_fin in H. simpl in H.
  injection H as <- <- <-. split; reflexivity.
Qed.

Lemma pi_reset_bind S Z f os z' code :
  bad_state S = false -> (forall s z0 r, f (s, z0, r) = Some (Some s, z0, r)) ->
  bind (c_deflateReset S Z) f = Some (os, z', code) -> code = Z_OK.
Proof.
  intros Hb Hf H. destruct (c_deflateReset S Z) as [[[a b] c]|] eqn:E; [|discriminate].
  apply pi_reset in E; [|exact Hb]. simpl in H. rewrite Hf in H. injection H as <- <- <-. exact E.
Qed.

Local Opaque c_deflateReset c_deflateEnd init_dstate.
Lemma pi_init_code level method wbits mem strategy a1 a2 a3 a4 a5 z os z' code :
  c_deflateInit2_ true true false level method wbits mem strategy a1 a2 a3 a4 a5 z = Some (os, z', code) ->
  code = Z_OK \/ (os = None /\ (code = Z_STREAM_ERROR \/ code = Z_MEM_ERROR)).
Proof.
  intros H. unfold c_deflateInit2_ in H. cbn [negb orb] in H.
  destruct (if wbits <? 0 then _ else _) as [[wb wr]|];
    [|injection H as <- _ <-; right; split; [reflexivity | left; reflexivity]].
  destruct (_ || _)%bool; [injection H as <- _ <-; right; split; [reflexivity | left; reflexivity]|].
  destruct a1; cbn [negb] in H; [|injection H as <- _ <-; right; split; [reflexivity | right; reflexivity]].
  destruct (a2 && a3 && a4 && a5)%bool; cbn [negb] in H.
  - left. apply pi_reset_bind in H; [exact H | apply pi_bs_init | intros; reflexivity].
  - apply pi_end_bind in H. right. destruct H as [-> ->]. split; [reflexivity | right; reflexivity].
Qed.
Local Transparent c_deflateReset c_deflateEnd init_dstate.

Lemma pi_override_normal Delta (P Q : environ -> mpred) (R : ret_assert) :
  ENTAIL Delta, P |-- Q -> ENTAIL Delta, P |-- RA_normal (overridePost Q R).
Proof. intros H. destruct R. exact H. Qed.

(* v9: the caller's fields as deflateInit2__spec_v9's precondition pieces (next_in, reset_fields) and the three
   fields it does not mention (avail_in, next_out, avail_out) *)
Lemma si_split9 (sp : val) (tin tout : Z) (msgv : val) (adler : Z) :
  api_fields sp nullval 0 tin nullval 0 tout msgv adler
  |-- @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._next_in) nullval sp *
      reset_fields sp (vl tin) (vl tout) msgv (vl adler) *
      (@field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._avail_in) (vi 0) sp *
       @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._next_out) nullval sp *
       @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._avail_out) (vi 0) sp).
Proof. unfold api_fields, reset_fields. entailer!. Qed.

Lemma si_join9 (sp : val) (tin tout : Z) (msgv : val) (adler : Z) :
  u64_ok tin -> u64_ok tout -> u64_ok adler ->
  @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._next_in) nullval sp *
  reset_fields sp (vl tin) (vl tout) msgv (vl adler) *
  (@field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._avail_in) (vi 0) sp *
   @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._next_out) nullval sp *
   @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._avail_out) (vi 0) sp)
  |-- api_fields sp nullval 0 tin nullval 0 tout msgv adler.
Proof. intros. unfold api_fields, reset_fields. entailer!. unfold u32_ok; rep_lia. Qed.

Lemma part_init {Espec : OracleKind} Bpre Brun sp hp vosn gv bs f dt :
  (forall s f', semax Delta_m (SA Bpre Brun sp hp vosn gv bs false false s f') msuf37 Rm_ret) ->
  semax Delta_m (A2 Bpre Brun sp hp vosn gv bs f dt) msuf35 Rm_ret.
Proof.
  intros HK.
  unfold msuf35, A2.
  abbreviate_semax.
  Intros.
  destruct f as [nin ain tin nout aout tout msg msgv adler]; cbn [sf_nin sf_ain sf_tin sf_nout sf_aout sf_tout sf_msg sf_msgv sf_adler] in *; subst.
  unfold draw_locals; cbn [app].
  change (sf_at sp (mkSF nullval 0 tin nullval 0 tout None msgv adler))
    with (api_fields sp nullval 0 tin nullval 0 tout msgv adler).
  assert_PROP (u64_ok tin /\ u64_ok tout /\ u64_ok adler) as Ur by (unfold api_fields; entailer!).
  destruct Ur as (Utin & Utout & Uadl).
  sep_apply (si_split9 sp tin tout msgv adler).
  unfold version_at.
  change (field_at_ Ews t_strm [StructField _reserved] sp) with (field_at_ Ews t_strm [StructField deflate.code._reserved] sp).
  match goal with H : bs_ok bs |- _ => pose proof H as BS; destruct H as (BD & _) end.
  pose proof BD as BD'. destruct BD' as (Hlev & Hwb & Hmem & Hstr & Hp & _).
  match goal with H : bound_facts _ _ |- _ => rename H into BF end.
  pose proof (bf_init _ _ BF (bd_level (bs_d bs)) (bd_wbits (bs_d bs)) (bd_mem (bs_d bs)) (bd_strategy (bs_d bs))) as FIN.
  Intros.
  forward_call (sp, bd_level (bs_d bs), 8, bd_wbits (bs_d bs), bd_mem (bs_d bs), bd_strategy (bs_d bs), gv vlit, Ers,
                [49; 46; 51; 46; 50; 0], 112, nullval, vl tin, vl tout, msgv, vl adler, nullval, vi dt,
                Vundef, gv).
  { split; [unfold s32_ok; rep_lia|]. split; [unfold s32_ok; rep_lia|]. split; [list_solve|].
    split; [cbn; rep_lia|].
    intros a1 a2 a3 a4 a5. exact (proj1 (FIN a1 a2 a3 a4 a5 zrst0 Hp)). }
  Intros vret. destruct vret as [[[[[a1 a2] a3] a4] a5] [[os z'] code]]. cbn [fst snd] in *.
  match goal with H : c_deflateInit2_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _ |- _ => rename H into HI end.
  change (Znth 0 [49; 46; 51; 46; 50; 0] =? 49) with true in HI. change (112 =? 112) with true in HI.
  pose proof (proj2 (FIN a1 a2 a3 a4 a5 zrst0 Hp) _ _ _ HI) as Hok. clear FIN.
  pose proof HI as HC. apply pi_init_code in HC.
  Intros msgv'.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx ((code = 0) :: P) (LOCALx Q (SEPx R))) end.
  { destruct HC as [-> | [-> Hc]]; [contradiction|].
    assert (Hk : (code =? Z_OK) = false) by (destruct Hc as [-> | ->]; reflexivity).
    rewrite Hk. unfold rfv.
    Intros st za zf op' dt'.
    sep_apply (si_join9 sp tin tout msgv' adler Utin Utout Uadl).
    sep_apply (init_fail_data_at_ sp st za zf op' dt' gv nullval 0 tin nullval 0 tout msgv' adler).
    Intros.
    gather_SEP (data_at_ Ews t_strm sp) (data_at_ Ecomp t_strm sp).
    rewrite <- data_at__Tsh_split.
    unfold hmem; cbn [andb].
    forward.
    Exists (Int.repr 0). entailer!. }
  { eapply semax_pre; [| apply semax_skip]. apply pi_override_normal. entailer!.
    destruct HC as [-> | [_ [-> | ->]]]; [reflexivity | |];
      match goal with H : Int.repr _ = Int.repr _ |- _ => apply (f_equal Int.unsigned) in H; vm_compute in H; discriminate end. }
  Intros. subst code.
  destruct (Hok eq_refl) as (s & -> & Hgz & HB). clear Hok HC.
  destruct (init_ok_strm _ _ _ _ _ _ _ _ _ _ _ _ _ HI) as (T1 & T2 & T3 & _).
  change (0 =? Z_OK) with true in *. change (0 =? Z_VERSION_ERROR) with false in *. unfold rfv.
  assert (U : u64_ok (z_total_in z') /\ u64_ok (z_total_out z') /\ u64_ok (z_adler z')).
  { rewrite T1, T2. unfold u64_ok. destruct T3 as [-> | ->]; rep_lia. }
  destruct U as (U1 & U2 & U3).
  sep_apply (si_join9 sp (z_total_in z') (z_total_out z') msgv' (z_adler z') U1 U2 U3).
  eapply semax_pre;
    [| apply (HK s (mkSF nullval 0 (z_total_in z') nullval 0 (z_total_out z') (z_msg z') msgv' (z_adler z')))].
  unfold SA, live, draw_locals, ghp_of, sf_at, hdr_at;
    cbn [app andb sf_nin sf_ain sf_tin sf_nout sf_aout sf_tout sf_msg sf_msgv sf_adler].
  rewrite Hgz.
  entailer!.
Qed.
