(** * deflate(): the body against DSpecV.deflate_specV

    MainDeflate's assembly of deflate's body from its stage triples, with the caller's witness of the weak
    validity of next_out taken from DSpecV ([wvw2]: DSpec's witnesses or a readable byte at next_out).  The
    witness is a frame of every stage except the entry stage, which uses it for the test next_out == Z_NULL
    (StageEntryV.stage_entryV); the definitions and lemmas below are MainDeflate's with that witness type. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.DeflateKit.
Require Import Zlib.proof.deflate.StageEntry.
Require Import Zlib.proof.deflate.StageZlib.
Require Import Zlib.proof.deflate.StageGzip.
Require Import Zlib.proof.deflate.StageExtra.
Require Import Zlib.proof.deflate.StageName.
Require Import Zlib.proof.deflate.StageComment.
Require Import Zlib.proof.deflate.StageHcrc.
Require Import Zlib.proof.deflate.StageCompress.
Require Import Zlib.proof.deflate.StageTrailer.
Require Import Zlib.proof.deflate.GrowCompress.
Require Import Zlib.proof.deflate.DeflateFacts.
Require Import Zlib.proof.deflate.InFacts.
Require Zlib.proof.deflate.GrowCompressR.
Require Import Zlib.proof.deflate.MainDeflate.
Require Import Zlib.proof.deflate.DSpecV.
Require Import Zlib.proof.deflate.StageEntryV.
#[export] Existing Instance DCS.CS.
Open Scope cmodel_scope.

(** The frame of the stages: the gz_header of the state, the rest of dstream, the output witness. *)
Definition dframeV (s0 : dstate) (p : dptrs) (hx : share * val * val * val) (W : wvw2) (pout : val) (gv : globals)
    : mpred :=
  (hdr_res (d_gzhead s0) (p_gzhead p) hx * ((dtokens s0 p * zfuncs gv) * wv2_at W pout))%logic.

(** Back to the abstract stream at a return. *)
Lemma dfull_closeV s0 s1 z1 p pin pout ish rest msgv gv inb nin ain tin tout adler msg hx W :
  out_grow (zmk inb nin ain tin (Zlength rest) tout adler msg) z1 -> dkeep s0 s1 -> z_in z1 = inb ->
  (d_gzhead s0 = None -> p_gzhead p = nullval) -> dsizes s0 ->
  dfull s1 z1 p pin pout ish (rest_after (zmk inb nin ain tin (Zlength rest) tout adler msg) z1 rest) msgv gv *
  dframeV s0 p hx W pout gv
  |-- dstream_sp 2 (Some s1) (p_strm p) (p_gzhead p) (p_s p) gv *
      (!! msg_ok (z_msg z1) msgv &&
       api_fields (p_strm p) (offset_val (z_next_in z1) pin) (z_avail_in z1) (z_total_in z1)
         (offset_val (Zlength (z_out z1)) pout) (z_avail_out z1) (z_total_out z1) msgv (z_adler z1)) *
      @data_at DCS.CS ish (tarray tuchar (Zlength inb)) (map vi inb) pin *
      @data_at DCS.CS Ews (tarray tuchar (Zlength rest))
        (map vi (z_out z1) ++ sublist (Zlength (z_out z1)) (Zlength rest) rest) pout *
      hdr_at (Some s0) (p_gzhead p) hx * wv2_at W pout.
Proof.
  intros [d [Eo Ea]] Hk Ei Hg Hd0. cbn [z_out z_avail_out zmk] in Eo, Ea. simpl app in Eo.
  assert (Hd1 : dsizes s1) by (apply Hk; exact Hd0).
  unfold dfull, dframeV, dstream_sp, out_space, in_obj, rest_after, api_fields. rewrite strm_at_open.
  unfold strm_zfuncs. rewrite Ei, Eo. cbn [z_out zmk]. rewrite Zlength_nil, Z.sub_0_r.
  Intros. Exists p. rewrite (dtokens_keep s0 s1 p Hk).
  assert (Hlen : Zlength d + z_avail_out z1 = Zlength rest) by lia. rewrite Hlen.
  unfold dstate_at'. simpl Z.eqb. cbv iota.
  destruct (d_gzhead s0) eqn:Eg; unfold hdr_res, hdr_at; rewrite Eg.
  - entailer!. unfold strm_ranges, u32_ok, u64_ok in *. tauto.
  - entailer!. unfold strm_ranges, u32_ok, u64_ok in *. tauto.
Qed.

Definition at_stageV (p : dptrs) (pin pout : val) (ish : share) (rest : list val) (gv : globals) (flush : Z)
    (z0 : strm) (s0 : dstate) (hx : share * val * val * val) (W : wvw2) (s : dstate) (z : strm)
    : environ -> mpred :=
  EX msgv : val, PROPx [] (LOCALx (df_locals p flush gv)
    (SEPx [dfull s z p pin pout ish (rest_after z0 z rest) msgv gv; deflate_globals gv; dframeV s0 p hx W pout gv])).

Lemma step_genV {Espec : OracleKind} (S rest_stmt : statement) (r : option dres) (Kont : dstate -> strm -> option dres)
    p pin pout ish rest gv flush z0 s0 hx W s z final Post :
  Zlength rest = z_avail_out z0 ->
  then_stage r Kont = Some final ->
  (strm_ranges z -> forall s' z' o, r = Some (s', z', o) -> out_grow z z' /\ dkeep s s' /\ z_in z' = z_in z) ->
  out_grow z0 z -> dkeep s0 s -> z_in z = z_in z0 ->
  (forall res msgv, r = Some res ->
     @semax DCS.CS Espec Delta_df
       (stage_pre p pin pout ish (rest_after z0 z rest) msgv gv flush s z (dframeV s0 p hx W pout gv)) S
       (stage_post p pin pout ish (rest_after z0 z rest) gv flush z (dframeV s0 p hx W pout gv) res)) ->
  (forall s' z' rc, final = (s', z', Some rc) -> out_grow z0 z' -> dkeep s0 s' -> z_in z' = z_in z0 ->
     forall msgv,
     ENTAIL Delta_df, PROPx [] (LOCALx [] (SEPx [dfull s' z' p pin pout ish (rest_after z0 z' rest) msgv gv;
       deflate_globals gv; dframeV s0 p hx W pout gv])) |-- RA_return Post (Some (vi rc))) ->
  (forall s' z', r = Some (s', z', None) -> Kont s' z' = Some final -> out_grow z0 z' -> dkeep s0 s' ->
     z_in z' = z_in z0 ->
     @semax DCS.CS Espec Delta_df (at_stageV p pin pout ish rest gv flush z0 s0 hx W s' z') rest_stmt Post) ->
  @semax DCS.CS Espec Delta_df (at_stageV p pin pout ish rest gv flush z0 s0 hx W s z) (Ssequence S rest_stmt) Post.
Proof.
  intros Hr Hm Hf G0 K0 I0 HS HR HK.
  destruct r as [[[s' z'] o]|]; [|discriminate].
  unfold at_stageV. Intros msgv.
  unfold df_locals. assert_PROP (strm_ranges z) as Hz by (unfold dfull; entailer!). fold (df_locals p flush gv).
  destruct (Hf Hz s' z' o eq_refl) as (G1 & K1 & I1).
  apply (stage_step _ _ S rest_stmt
    (stage_post p pin pout ish (rest_after z0 z rest) gv flush z (dframeV s0 p hx W pout gv) (s', z', o)) Post).
  - reflexivity.
  - reflexivity.
  - apply (HS (s', z', o) msgv eq_refl).
  - intros vl. destruct o as [rc|]; simpl RA_return.
    + apply (derives_trans _ (local (tc_environ Delta_df) && (EX x : val, PROP (vl = Some (vi rc)) LOCAL ()
        SEP (dfull s' z' p pin pout ish (rest_after z z' (rest_after z0 z rest)) x gv; deflate_globals gv;
             dframeV s0 p hx W pout gv)))); [apply derives_refl|].
      Intros msgv'. subst vl. sep_apply (dfull_rest_trans s' z0 z z' p pin pout ish rest msgv' gv Hr G0 G1).
      simpl in Hm. inversion Hm; subst final.
      eapply HR; eauto using out_grow_trans, dkeep_trans. congruence.
    + apply andp_left2. intro rho. apply FF_left.
  - destruct o as [rc|]; simpl RA_normal.
    + apply semax_ff.
    + eapply semax_pre; [|apply (HK s' z' eq_refl Hm); eauto using out_grow_trans, dkeep_trans; congruence].
      apply (derives_trans _ (local (tc_environ Delta_df) && (EX x : val, PROPx [] (LOCALx (df_locals p flush gv)
        (SEPx [dfull s' z' p pin pout ish (rest_after z z' (rest_after z0 z rest)) x gv; deflate_globals gv;
             dframeV s0 p hx W pout gv]))))); [apply derives_refl|].
      Intros msgv'. unfold at_stageV. Exists msgv'. unfold df_locals.
      sep_apply (dfull_rest_trans s' z0 z z' p pin pout ish rest msgv' gv Hr G0 G1). entailer!.
Qed.

(** The last stage (the trailer) always returns. *)
Lemma step_lastV {Espec : OracleKind} (S : statement) (r : option dres)
    p pin pout ish rest gv flush z0 s0 hx W s z final Post :
  Zlength rest = z_avail_out z0 ->
  r = Some final -> (exists rc, snd final = Some rc) ->
  (strm_ranges z -> forall s' z' o, r = Some (s', z', o) -> out_grow z z' /\ dkeep s s' /\ z_in z' = z_in z) ->
  out_grow z0 z -> dkeep s0 s -> z_in z = z_in z0 ->
  (forall msgv,
     @semax DCS.CS Espec Delta_df
       (stage_pre p pin pout ish (rest_after z0 z rest) msgv gv flush s z (dframeV s0 p hx W pout gv)) S
       (stage_post p pin pout ish (rest_after z0 z rest) gv flush z (dframeV s0 p hx W pout gv) final)) ->
  (forall s' z' rc, final = (s', z', Some rc) -> out_grow z0 z' -> dkeep s0 s' -> z_in z' = z_in z0 ->
     forall msgv,
     ENTAIL Delta_df, PROPx [] (LOCALx [] (SEPx [dfull s' z' p pin pout ish (rest_after z0 z' rest) msgv gv;
       deflate_globals gv; dframeV s0 p hx W pout gv])) |-- RA_return Post (Some (vi rc))) ->
  @semax DCS.CS Espec Delta_df (at_stageV p pin pout ish rest gv flush z0 s0 hx W s z) S Post.
Proof.
  intros Hr Hm [rc Hrc] Hf G0 K0 I0 HS HR.
  destruct final as [[s' z'] o]. simpl in Hrc. subst o. subst r.
  unfold at_stageV. Intros msgv.
  unfold df_locals. assert_PROP (strm_ranges z) as Hz by (unfold dfull; entailer!). fold (df_locals p flush gv).
  destruct (Hf Hz s' z' (Some rc) eq_refl) as (G1 & K1 & I1).
  eapply semax_post; [| | | | apply (HS msgv)]; simpl RA_normal; simpl RA_break; simpl RA_continue;
    simpl RA_return.
  - apply andp_left2. intro rho. apply FF_left.
  - apply andp_left2. intro rho. apply FF_left.
  - apply andp_left2. intro rho. apply FF_left.
  - intros vl.
    apply (derives_trans _ (local (tc_environ Delta_df) && (EX x : val, PROP (vl = Some (vi rc)) LOCAL ()
        SEP (dfull s' z' p pin pout ish (rest_after z z' (rest_after z0 z rest)) x gv; deflate_globals gv;
             dframeV s0 p hx W pout gv)))); [apply derives_refl|].
    Intros msgv'. subst vl. sep_apply (dfull_rest_trans s' z0 z z' p pin pout ish rest msgv' gv Hr G0 G1).
    eapply HR; eauto using out_grow_trans, dkeep_trans. congruence.
Qed.

Lemma dframe_gzV s s0 p hx W pout gv : dkeep s0 s ->
  dframeV s0 p hx W pout gv =
  (hdr_res (d_gzhead s) (p_gzhead p) hx * ((dtokens s0 p * zfuncs gv) * wv2_at W pout))%logic.
Proof. intros (E & _). unfold dframeV. rewrite E. reflexivity. Qed.

Lemma dframe_entryV s0 p hx W pout gv :
  dframeV s0 p hx W pout gv =
  ((hdr_res (d_gzhead s0) (p_gzhead p) hx * (dtokens s0 p * zfuncs gv)) * wv2_at W pout)%logic.
Proof. unfold dframeV. rewrite (sepcon_assoc (hdr_res _ _ _) (dtokens s0 p * zfuncs gv)%logic (wv2_at W pout)). reflexivity. Qed.

Lemma chain_okV {Espec : OracleKind} p pin pout ish rest gv flush s0 hx W inb nin ain tin tout adler msg final Post ef :
  ef_ok gv ef -> 0 <= flush <= 5 -> (Zlength rest = 0 -> wv2_ok W) ->
  (d_gzhead s0 = None -> p_gzhead p = nullval) ->
  (forall h, d_gzhead s0 = Some h -> readable_share (fst (fst (fst hx)))) ->
  chain_model ef flush s0 (zmk inb nin ain tin (Zlength rest) tout adler msg) = Some final ->
  (forall s' z' rc, final = (s', z', Some rc) -> out_grow (zmk inb nin ain tin (Zlength rest) tout adler msg) z' ->
     dkeep s0 s' -> z_in z' = inb ->
     forall msgv,
     ENTAIL Delta_df, PROPx [] (LOCALx [] (SEPx [dfull s' z' p pin pout ish
       (rest_after (zmk inb nin ain tin (Zlength rest) tout adler msg) z' rest) msgv gv;
       deflate_globals gv; dframeV s0 p hx W pout gv])) |-- RA_return Post (Some (vi rc))) ->
  @semax DCS.CS Espec Delta_df
    (at_stageV p pin pout ish rest gv flush (zmk inb nin ain tin (Zlength rest) tout adler msg) s0 hx W s0
       (zmk inb nin ain tin (Zlength rest) tout adler msg))
    (chain_from df_body 2) Post.
Proof.
  set (z0 := zmk inb nin ain tin (Zlength rest) tout adler msg).
  intros Hef Hfl HW Hg Hrd Hm HR.
  pose proof deflate_facts_proved as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & _ & F9).
  pose proof deflate_in_proved as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9).
  assert (Hr : Zlength rest = z_avail_out z0) by reflexivity.
  assert (HR' : forall s' z' rc, final = (s', z', Some rc) -> out_grow z0 z' -> dkeep s0 s' ->
     z_in z' = z_in z0 -> forall msgv,
     ENTAIL Delta_df, PROPx [] (LOCALx [] (SEPx [dfull s' z' p pin pout ish (rest_after z0 z' rest) msgv gv;
       deflate_globals gv; dframeV s0 p hx W pout gv])) |-- RA_return Post (Some (vi rc))).
  { intros. eapply HR; eauto. }
  clear HR.
  unfold chain_model in Hm.
  (* entry: e2 .. e8 *)
  chain_next 2%nat. chain_next 3%nat. chain_next 4%nat. chain_next 5%nat. chain_next 6%nat. chain_next 7%nat.
  chain_next 8%nat.
  do 6 (apply <- seq_assoc).
  eapply step_genV; [exact Hr | exact Hm | apply (facts3 _ (sf_r _ F1) I1 flush) | apply out_grow_refl | apply dkeep_refl
    | reflexivity | | exact HR' | ].
  { intros res msgv E. rewrite dframe_entryV. do 5 (apply -> seq_assoc).
    rewrite rest_after_refl. eapply stage_entryV; eauto. }
  intros s1 z1 E1 Hm1 G1 K1 J1. cbv beta in Hm1.
  (* zlib *)
  chain_next 9%nat. change (nth_stmt df_body 9) with S_zlib.
  eapply step_genV; [exact Hr | exact Hm1 | apply (facts3 _ (sf_r _ F2) I2 flush) | exact G1 | exact K1 | exact J1 | | exact HR' | ].
  { intros res msgv E. eapply stage_zlib; eauto. }
  intros s2 z2 E2 Hm2 G2 K2 J2. cbv beta in Hm2.
  (* gzip *)
  chain_next 10%nat. change (nth_stmt df_body 10) with S_gzip.
  eapply step_genV; [exact Hr | exact Hm2 | apply (facts3 _ (sf_r _ F3) I3 flush) | exact G2 | exact K2 | exact J2 | | exact HR' | ].
  { intros res msgv E. rewrite (dframe_gzV s2 s0 p hx W pout gv K2). eapply stage_gzip; eauto.
    rewrite (proj1 K2). apply gz_ok_of; auto. }
  intros s3 z3 E3 Hm3 G3 K3 J3. cbv beta in Hm3.
  (* extra *)
  chain_next 11%nat. change (nth_stmt df_body 11) with S_extra.
  eapply step_genV; [exact Hr | exact Hm3 | apply (facts3 _ (sf_r _ F4) I4 flush) | exact G3 | exact K3 | exact J3 | | exact HR' | ].
  { intros res msgv E. rewrite (dframe_gzV s3 s0 p hx W pout gv K3). eapply stage_extra; eauto.
    rewrite (proj1 K3). apply gz_ok_of; auto. }
  intros s4 z4 E4 Hm4 G4 K4 J4. cbv beta in Hm4.
  (* name *)
  chain_next 12%nat. change (nth_stmt df_body 12) with S_name.
  eapply step_genV; [exact Hr | exact Hm4 | apply (facts3 _ (sf_r _ F5) I5 flush) | exact G4 | exact K4 | exact J4 | | exact HR' | ].
  { intros res msgv E. rewrite (dframe_gzV s4 s0 p hx W pout gv K4). eapply stage_name; eauto.
    rewrite (proj1 K4). apply gz_ok_of; auto. }
  intros s5 z5 E5 Hm5 G5 K5 J5. cbv beta in Hm5.
  (* comment *)
  chain_next 13%nat. change (nth_stmt df_body 13) with S_comment.
  eapply step_genV; [exact Hr | exact Hm5 | apply (facts3 _ (sf_r _ F6) I6 flush) | exact G5 | exact K5 | exact J5 | | exact HR' | ].
  { intros res msgv E. rewrite (dframe_gzV s5 s0 p hx W pout gv K5). eapply stage_comment; eauto.
    rewrite (proj1 K5). apply gz_ok_of; auto. }
  intros s6 z6 E6 Hm6 G6 K6 J6. cbv beta in Hm6.
  (* hcrc *)
  chain_next 14%nat. change (nth_stmt df_body 14) with S_hcrc.
  eapply step_genV; [exact Hr | exact Hm6 | apply (facts3 _ (sf_r _ F7) I7 flush) | exact G6 | exact K6 | exact J6 | | exact HR' | ].
  { intros res msgv E. rewrite (dframe_gzV s6 s0 p hx W pout gv K6). eapply stage_hcrc; eauto.
    rewrite (proj1 K6). apply gz_ok_of; auto. }
  intros s7 z7 E7 Hm7 G7 K7 J7. cbv beta in Hm7.
  (* compress *)
  chain_next 15%nat. change (nth_stmt df_body 15) with S_compress.
  eapply step_genV; [exact Hr | exact Hm7 | apply (facts3 (fun f s z => c_deflate_compress_g ef s z f) (facts_compress_r ef) (InFacts.in_compress_g ef) flush) | exact G7 | exact K7 | exact J7 | | exact HR' | ].
  { intros res msgv E. eapply (stage_compress Espec _ _ _ _ _ _ _ _ _ _ _ _ ef Hef); eauto. }
  intros s8 z8 E8 Hm8 G8 K8 J8. cbv beta in Hm8.
  (* trailer *)
  change (chain_from df_body 16) with S_trailer.
  eapply step_lastV; [exact Hr | exact Hm8 | | apply (facts3 _ (sf_r _ F9) I9 flush) | exact G8 | exact K8 | exact J8 | | exact HR'].
  { unfold c_trailer2 in Hm8. destruct (c_deflate_trailer s8 z8 flush) as [[[? ?] ?]|]; inversion Hm8. eexists; reflexivity. }
  intros msgv. eapply stage_trailer; eauto.
Qed.

(** deflate's body against deflate_specV. *)
Lemma body_deflateV : deflate_bodyV_stmt.
Proof.
  unfold deflate_bodyV_stmt. start_function.
  match goal with H : exists ef, _ |- _ => destruct H as (ef & Hef & H3') end.
  destruct os as [s0|].
  2: {
    simpl in H3'. inversion H3'; subst r; clear H3'.
    unfold dstream_sp. Intros za zf op dt. subst ghp sp.
    sep_apply (dcheck_none_fold strmp za zf gv ltac:(assumption) ltac:(assumption)).
    sep_apply (api_fields_split strmp (offset_val nin pin) ain tin pout (Zlength rest) tout msgv adler). Intros.
    forward_call (@None dstate, strmp, nullval, za, zf, offset_val nin pin, gv).
    sep_apply (api_fields_join strmp (offset_val nin pin) ain tin pout (Zlength rest) tout msgv adler).
    simpl c_deflateStateCheck.
    forward_if (temp _t'2 (vi 1)); [forward; entailer! | discriminate |].
    forward_if (temp _t'3 (vi 1)); [forward; entailer! | discriminate |].
    forward_if; [|discriminate].
    forward.
    Exists msgv. unfold dcheck_at, dstream_sp. Intros. Exists za zf op dt.
    cbn [z_msg z_next_in z_avail_in z_total_in z_avail_out z_total_out z_adler z_out zmk app].
    rewrite Zlength_nil, sublist_same by auto. unfold hdr_at. entailer!. }
  set (z0 := zmk inb nin ain tin (Zlength rest) tout adler msg) in *.
  simpl in H3'. destruct (c_deflate_g ef s0 z0 flush) as [[[s1 z1] rc]|] eqn:Hc; [|discriminate].
  inversion H3'; subst r; clear H3'.
  sep_apply (dstream_open s0 strmp ghp sp gv). Intros p. subst strmp ghp sp.
  match goal with H : dsizes s0 |- _ => rename H into Hds end.
  rewrite hdr_at_res. Intros.
  match goal with H : d_gzhead s0 = None -> _ |- _ => rename H into Hgz end.
  unfold dopen. Intros.
  sep_apply (api_fields_split (p_strm p) (offset_val nin pin) ain tin pout (Zlength rest) tout msgv adler). Intros.
  forward_call (Some s0, p_strm p, p_s p, zca gv, zcf gv, offset_val nin pin, gv).
  sep_apply (api_fields_join (p_strm p) (offset_val nin pin) ain tin pout (Zlength rest) tout msgv adler).
  fold (dopen s0 p gv).
  unfold c_deflate_g in Hc.
  change DState.Z_BLOCK with 5 in Hc.
  assert (Hret : (bad_state s0 || (flush >? 5) || (flush <? 0))%bool = true ->
    forall v1 v2 v3 c, semax Delta (PROPx [] (LOCALx [temp _t'3 v3; temp _t'2 v2; temp _t'1 v1; gvars gv;
      temp _strm (p_strm p); temp _flush (vi flush)] (SEPx [
           api_fields (p_strm p) (offset_val nin pin) ain tin pout (Zlength rest) tout msgv adler;
           dcheck_at (Some s0) (p_strm p) (p_s p) (zca gv) (zcf gv) gv; dcheck_frame s0 p gv; dtokens s0 p;
           field_at Ews t_strm (DOT _opaque) nullval (p_strm p) ; field_at_ Ews t_strm (DOT _reserved) (p_strm p);
           data_at ish (tarray tuchar (Zlength inb)) (map vi inb) pin;
           data_at Ews (tarray tuchar (Zlength rest)) rest pout;
           hdr_res (d_gzhead s0) (p_gzhead p) hx; deflate_globals gv; wv2_at W pout])))
      (Ssequence (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 2) tint) tint))) c) POSTCONDITION).
  { intros Eb v1 v2 v3 c. rewrite Eb in Hc. inversion Hc; subst s1 z1 rc; clear Hc.
    forward. Exists msgv. sep_apply (dstream_close s0 p gv Hds). rewrite hdr_at_res.
    subst z0. cbn [z_msg z_next_in z_avail_in z_total_in z_avail_out z_total_out z_adler z_out zmk app].
    rewrite Zlength_nil, sublist_same by auto. entailer!. }
  destruct (status_ok (d_status s0)) eqn:Est.
  2: {
    assert (Hck : c_deflateStateCheck (Some s0) = 1) by (simpl; rewrite Est; auto). rewrite Hck.
    forward_if (temp _t'2 (vi 1)); [forward; entailer! | ctr |].
    forward_if (temp _t'3 (vi 1)); [forward; entailer! | ctr |].
    forward_if; [|ctr].
    apply Hret. unfold bad_state. rewrite Hck. reflexivity. }
  assert (Hck : c_deflateStateCheck (Some s0) = 0) by (simpl; rewrite Est; auto). rewrite Hck.
  assert (Hbs : bad_state s0 = false) by (unfold bad_state; rewrite Hck; reflexivity).
  open_dranges H1.
  forward_if (temp _t'2 (vi (if flush >? 5 then 1 else 0))).
  { ctr. }
  { forward. entailer!. unfold bool2val, vi. zfin. }
  forward_if (temp _t'3 (vi (if ((flush >? 5) || (flush <? 0))%bool then 1 else 0))).
  { forward. entailer!. destruct (flush >? 5); [reflexivity | ctr]. }
  { forward. entailer!. destruct (flush >? 5) eqn:E5; [ctr|]. unfold bool2val, vi. simpl. zfin. }
  destruct ((flush >? 5) || (flush <? 0))%bool eqn:Ef.
  { forward_if; [|ctr]. apply Hret. rewrite Hbs. exact Ef. }
  forward_if; [ctr|].
  assert (Hfl : 0 <= flush <= 5).
  { apply orb_false_iff in Ef. destruct Ef as [E1 E2]. revert E1 E2. zfin. }
  rewrite Hbs in Hc. cbn [orb] in Hc. rewrite Ef in Hc.
  pose proof (status_ok_range _ Est) as Hst.
  rewrite dcheck_some_eq by exact Hst. Intros.
  forward.
  sep_apply (dcheck_some_fold s0 (p_strm p) (p_s p) gv Hst).
  sep_apply (dfull_build s0 p gv pin ish inb nin ain tin pout rest tout msgv msg adler H2 H SH).
  fold z0.
  Intros. unfold MORE_COMMANDS, abbreviate.
  match goal with |- semax _ _ ?c _ => change c with (chain_from df_body 2) end.
  match goal with |- semax ?D _ _ _ => change D with Delta_df end.
  apply chain_of_deflate in Hc.
  assert_PROP (forall h, d_gzhead s0 = Some h -> readable_share (fst (fst (fst hx)))) as Hrd.
  { destruct (d_gzhead s0) as [h|] eqn:Eg; unfold hdr_res.
    - destruct hx as [[[hsh xp] np] cp]. unfold gzh_at. Intros. entailer!.
    - entailer!. }
  eapply semax_pre; [|eapply (chain_okV p pin pout ish rest gv flush s0 hx W inb nin ain tin tout adler msg); eauto].
  - unfold at_stageV, dframeV, df_locals. Exists msgv. subst z0. rewrite rest_after_refl. entailer!.
  - intros s' z' rc' E G K I msgv'. inversion E; subst s' z' rc'; clear E.
    sep_apply (dfull_closeV s0 s1 z1 p pin pout ish rest msgv' gv inb nin ain tin tout adler msg hx W G K I Hgz Hds).
    unfold POSTCONDITION, abbreviate. simpl RA_return. go_lowerx. unfold stackframe_of. simpl fn_vars.
    simpl fold_right. rewrite sepcon_emp. unfold liftx. simpl. unfold PROPx, LOCALx, SEPx, local, lift1. simpl.
    normalize.
    Exists msgv'. apply andp_right.
    { apply prop_right. split; [|auto]. unfold lift; simpl. split; [|discriminate]. unfold eval_id. simpl.
      reflexivity. }
    match goal with Hm : msg_ok (z_msg z1) _ |- _ => rewrite (prop_true_andp _ _ Hm) end. cancel.
Qed.
