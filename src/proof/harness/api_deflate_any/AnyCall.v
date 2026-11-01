(* Law api_deflate_any: deflate (AnyKit.any_call_stmt): with a valid flush the model run of DetFacts2.df2_deflate
   and the codes of AnyCodes.deflate_codes, with an invalid flush AnyCodes.deflate_bad_flush (nothing changes);
   the stream and the output space as D_at. *)
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
Require Import Zlib.proof.harness.api_deflate_any.AnyFacts.
Require Zlib.proof.harness.api_deflate_any.AnyCodes.
Require Zlib.proof.deflate.DModel5.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.proof.harness.api_deterministic.DetMem2.
Require Zlib.proof.harness.api_deterministic.DetMem2b.
Require Zlib.proof.harness.api_deterministic.DetKit2.
Require Zlib.proof.harness.api_deterministic.DetCall2.
Require Import Zlib.proof.harness.api_deflate_any.AnyCS.
Require Import Zlib.proof.harness.api_deflate_any.AnyMainStmt.
Require Import Zlib.proof.harness.api_deflate_any.AnyKit.
Require Import Zlib.proof.harness.api_deflate_any.AnyCallOut.
Require Zlib.proof.harness.api_deflate_any.AnyAt.
Require Import Zlib.harness.api_deflate_any.code.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.

(** ** deflate's model run at main's call

    With a flush in Z_NO_FLUSH..Z_BLOCK, the run of DetFacts2.df2_deflate (the invariant again after it unless
    Z_STREAM_END) and the codes of AnyCodes.deflate_codes; with any other flush, Z_STREAM_ERROR and nothing
    changed (AnyCodes.deflate_bad_flush): then Z_FINISH was never given (it would be the flush), so the state
    is still one of the invariant without Z_FINISH. *)
Lemma any_dres (J : det_inv) (n : Z) (data : list Z) (datap : val) (ls : lstate) (ci : citer) (c : cstate) :
  J_ok J n data datap ls -> ci_ok n ls ci -> cs_ok J ls ci c ->
  exists s' z' code,
    c_deflate (cs_s c) (d_call data ls ci c) (ci_flush ci) = Some (s', z', code) /\
    forall msgv, msg_ok (z_msg z') msgv -> dr_ok J data ls ci c (mkDR s' z' code msgv).
Proof.
  intros HJ Hci Hc.
  destruct HJ as [[Hdf [Hn [Hlen [Hbytes Hdp]]]] [HJls [Hrd [Hleft [Hfin [Htout Hmsg]]]]]].
  destruct Hci as (Htake & Hrn & Hfl & Hfin4 & Hroom & Hbs & Hbsb & Hp1 & Hp2 & Hp3).
  destruct Hc as (HJc & Hnin & HO & HOb & Hnin0 & Hct & Hcm).
  assert (Hinb : Zlength (ci_inb data ls ci) = ci_take ci)
    by (unfold ci_inb; rewrite Zlength_sublist; lia).
  assert (Hinbb : bytes (ci_inb data ls ci)) by (apply Forall_sublist; auto).
  destruct (ay_live J Hdf _ _ _ _ HJc) as (Hbad & Hgz & Hlive).
  pose proof (Zlength_nonneg (cs_out c)) as HOn.
  destruct (Z_le_dec 0 (ci_flush ci)) as [F0 | F0]; [destruct (Z_le_dec (ci_flush ci) 5) as [F5 | F5] |].
  - destruct (df2_deflate J (ay_det J Hdf) (ls_fin ls) (cs_s c) (ls_read ls + cs_nin c) (cs_adler c)
                (ci_inb data ls ci) (cs_nin c) (ci_room ci - Zlength (cs_out c)) (cs_tout c) (ci_flush ci) (cs_msg c))
      as (s' & z' & code & Hrun & Hcall & HJ'); try rewrite Hinb; try solve [auto | lia].
    { intros R HR. assert (Hf : ls_fin ls <> None) by congruence.
      destruct (Hfin4 Hf) as [Hf4 Ht]. split; [exact Hf4 |].
      rewrite (Hnin0 Hf), HR in *. destruct Hfin as [_ HRd]. rewrite HRd.
      unfold ci_inb. rewrite Ht, sublist_sublist by lia. f_equal; lia. }
    rewrite Hinb in Hrun, HJ'.
    assert (Hfz : d_status (cs_s c) = FINISH_STATE -> ci_flush ci = Z_FINISH).
    { intros HS. destruct (ls_fin ls) eqn:Ef.
      - exact (proj1 (Hfin4 ltac:(discriminate))).
      - exfalso. exact (Hlive eq_refl HS). }
    destruct (AnyCodes.deflate_codes _ _ _ _ _ _ Hbad (conj F0 F5) Hfz Hrun) as [Hc1 Hc2].
    exists s', z', code. split; [exact Hrun |]. intros msgv Hm.
    unfold dr_ok; cbn [dr_s dr_z dr_code dr_msgv].
    split; [exact Hrun |]. split; [exact Hcall |]. split; [exact HJ' |].
    split; [| split; [| split; [exact Hc2 | split; [| exact Hm]]]].
    + unfold Z_STREAM_ERROR, Z_OK, Z_BUF_ERROR, Z_STREAM_END in *. split; intros; lia.
    + tauto.
    + (* no output space: AnyCodes.deflate_no_room *)
      intros Hr _.
      assert (Ha : z_avail_out (d_call data ls ci c) = 0) by (unfold d_call, zcall; cbn; lia).
      pose proof (AnyCodes.deflate_no_room _ _ _ Hbad (conj F0 F5) Hfz Ha) as E.
      unfold d_call in E. rewrite Hrun in E. inversion E; subst.
      unfold zcall, set_z_msg; cbn. repeat split; lia.
  - assert (Hbf : ci_flush ci < 0 \/ 5 < ci_flush ci) by lia.
    exists (cs_s c), (d_call data ls ci c), Z_STREAM_ERROR.
    pose proof (AnyCodes.deflate_bad_flush (cs_s c) (d_call data ls ci c) _ Hbf) as Hrun.
    split; [exact Hrun |]. intros msgv Hm.
    unfold dr_ok; cbn [dr_s dr_z dr_code dr_msgv].
    split; [exact Hrun |].
    split.
    { unfold call_okw, d_call, zcall; cbn. rewrite Hinb.
      unfold u64. rewrite Z.mod_small by (unfold u64r in Hct; lia).
      repeat split; try lia. constructor. }
    split.
    { intros _. assert (Hf : ls_fin ls = None).
      { destruct (ls_fin ls) eqn:E; auto. destruct (Hfin4 ltac:(discriminate)) as [Hf4 _].
        unfold Z_FINISH in Hf4. lia. }
      rewrite (proj2 (Z.eqb_neq _ _)) by (unfold Z_FINISH; lia).
      unfold d_call, zcall; cbn. rewrite Hf in HJc. exact HJc. }
    split; [tauto |]. split; [tauto |].
    split; [unfold Z_STREAM_ERROR, Z_STREAM_END; lia |].
    split; [intros _ HF; lia | exact Hm].
  - assert (Hbf : ci_flush ci < 0 \/ 5 < ci_flush ci) by lia.
    exists (cs_s c), (d_call data ls ci c), Z_STREAM_ERROR.
    pose proof (AnyCodes.deflate_bad_flush (cs_s c) (d_call data ls ci c) _ Hbf) as Hrun.
    split; [exact Hrun |]. intros msgv Hm.
    unfold dr_ok; cbn [dr_s dr_z dr_code dr_msgv].
    split; [exact Hrun |].
    split.
    { unfold call_okw, d_call, zcall; cbn. rewrite Hinb.
      unfold u64. rewrite Z.mod_small by (unfold u64r in Hct; lia).
      repeat split; try lia. constructor. }
    split.
    { intros _. assert (Hf : ls_fin ls = None).
      { destruct (ls_fin ls) eqn:E; auto. destruct (Hfin4 ltac:(discriminate)) as [Hf4 _].
        unfold Z_FINISH in Hf4. lia. }
      rewrite (proj2 (Z.eqb_neq _ _)) by (unfold Z_FINISH; lia).
      unfold d_call, zcall; cbn. rewrite Hf in HJc. exact HJc. }
    split; [tauto |]. split; [tauto |].
    split; [unfold Z_STREAM_ERROR, Z_STREAM_END; lia |].
    split; [intros _ HF; lia | exact Hm].
Qed.

(* Floyd's simplify_remove_localdef_temp (simpl on ident_eq of the large idents of main's locals, among them
   _out and _out_size) is slow here: remove the temp by rewriting instead (as in DetCall2.v) *)
Lemma rlt_nil i : remove_localdef_temp i [] = [].
Proof. reflexivity. Qed.
Lemma rlt_gvars i g l : remove_localdef_temp i (gvars g :: l) = gvars g :: remove_localdef_temp i l.
Proof. reflexivity. Qed.
Lemma rlt_lvar i j t v l : remove_localdef_temp i (lvar j t v :: l) = lvar j t v :: remove_localdef_temp i l.
Proof. reflexivity. Qed.
Lemma rlt_same i v l : remove_localdef_temp i (temp i v :: l) = remove_localdef_temp i l.
Proof. simpl. unfold rlt_ident_eq. rewrite if_true by auto. reflexivity. Qed.
Lemma rlt_cons i j v l :
  i <> j -> remove_localdef_temp i (temp j v :: l) = temp j v :: remove_localdef_temp i l.
Proof. intros. simpl. unfold rlt_ident_eq. rewrite if_false by auto. reflexivity. Qed.

Ltac simplify_remove_localdef_temp ::=
  repeat first [ rewrite rlt_nil | rewrite rlt_gvars | rewrite rlt_lvar | rewrite rlt_same
               | rewrite rlt_cons by (let X := fresh in intro X; discriminate X) ].

Lemma any_call : any_call_stmt.
Proof.
  intros Espec J n data datap v sp gv ap ls ci c HK.
  (* position_of and deflate end in D_at for the model run of any_dres; the rest is the continuation *)
  unfold lsuf10.
  match goal with |- semax _ _ (Ssequence _ (Ssequence _ ?k)) _ => change k with lsuf12 end.
  rewrite seq_assoc.
  eapply semax_seq' with (P' := EX d : dres, D_at J n data datap v sp gv ap ls ci c d).
  2: { apply extract_exists_pre; intro d. apply HK. }
  clear HK.
  unfold C_at, C_sep, B_loc.
  Intros.
  destruct (any_dres J n data datap ls ci c H H0 H1) as (s' & z' & code & Hrun & Hdr).
  pose proof H as [[Hdf [Hn [Hlen [Hbytes Hdp]]]] [_ [Hrd _]]].
  pose proof H0 as (Htake & Hrn & Hfl & Hfin4 & Hroom & Hbs & Hbsb & Hp1 & Hp2 & Hp3).
  pose proof H1 as (HJc & Hnin & HO & HOb & Hnin0 & Hct & Hcm).
  pose proof (Zlength_nonneg (cs_out c)) as HOn.
  (* position_of(&strm, &at): the stream lent as one z_stream *)
  sep_apply AnyAt.any_strm_lend. Intros r.
  change (AnyAt.sposz _ _ _ _ _ _) with (c_pos ls ci c).
  unfold at_free.
  abbreviate_semax.
  forward_call (v, Ews, c_pos ls ci c, r, ap, Tsh).
  { unfold LS.posz_ok, c_pos;
      cbn [LS.pz_next_in LS.pz_next_out LS.pz_avail_in LS.pz_avail_out LS.pz_total_in LS.pz_total_out].
    unfold u64r in Hct. destruct (ci_piece ci); try contradiction. destruct (ci_out ci); try contradiction.
    simpl. repeat split; auto; rep_lia. }
  (* the stream given back; [at] holds the position until the checks *)
  sep_apply (modus_ponens_wand (@data_at LS.CS_session Ews t_zs (LS.zs_of (c_pos ls ci c) r) v)).
  (* deflate(&strm, flush) *)
  assert (Hinb : Zlength (ci_inb data ls ci) = ci_take ci)
    by (unfold ci_inb; rewrite Zlength_sublist; lia).
  assert (Hinbb : bytes (ci_inb data ls ci)) by (apply Forall_sublist; auto).
  destruct (ay_live J Hdf _ _ _ _ HJc) as (Hbad & Hgz & _).
  pose proof (df2_adler J (ay_det J Hdf) _ _ _ _ HJc) as Had.
  assert_PROP (field_compatible (tarray tuchar (ci_room ci)) [] (ci_out ci)) as FC
    by (unfold DK.out_at; entailer!).
  rewrite (out_split_bytes (ci_out ci) (ci_room ci) (ci_bs ci) (cs_out c)) by (auto; lia).
  unfold DK.strm_at, BoundKit.obj.
  flatten_sepcon_in_SEP.
  forward_call (Some (cs_s c), v, nullval, sp, (Ews, nullval, nullval, nullval), ci_piece ci, Ews,
                ci_inb data ls ci, cs_nin c, ci_take ci - cs_nin c, ls_read ls + cs_nin c,
                offset_val (Zlength (cs_out c)) (ci_out ci), orest (ci_room ci) (ci_bs ci) (cs_out c),
                DC2.owit (ci_room ci) (cs_out c), cs_tout c, cs_msgv c, cs_msg c, cs_adler c, ci_flush ci,
                (Some s', z', code), gv).
  { rewrite (DC2.hdr_none (cs_s c)) by auto. rewrite Hinb, orest_len by (auto; lia). cancel. }
  { rewrite orest_len by (auto; lia).
    split; [| split].
    - intros; apply DC2.owit_ok; lia.
    - unfold strm_ranges, zmk; simpl; rewrite Zlength_nil, Hinb; unfold bytes in Hinbb;
      unfold u32_ok, u64_ok, u64r in *; repeat split; auto; try rep_lia.
    - exists (fun f => f); split; [apply ef_ok_id |]; unfold on_state, c_on_state.
      rewrite DModel5.c_deflate_g_id; change (zmk ?a ?b ?c ?d ?e ?f ?g ?h) with (zcall a b c d e f g h).
      unfold d_call in Hrun. rewrite Hrun. reflexivity. }
  cbn [fst snd]. Intros msgv'.
  forward.
  Exists (mkDR s' z' code msgv').
  specialize (Hdr msgv' H2).
  pose proof Hdr as (_ & Hcall & _). cbn [dr_z] in Hcall.
  pose proof Hcall as (Hzin & Hnx & Hav & Htin & Haout & Hzout & Htot & Hzb).
  unfold D_at, D_sep, B_loc, DK.strm_at. cbn [dr_s dr_z dr_code dr_msgv].
  rewrite (DC2.hdr_none (cs_s c)) by auto.
  rewrite orest_len by (auto; lia).
  sep_apply (out_join_bytes (ci_out ci) (ci_room ci) (ci_bs ci) (cs_out c) (z_out z') Hbs ltac:(lia) FC).
  rewrite !offset_offset_val, Zlength_app.
  replace (Zlength (z_out z') + Zlength (cs_out c)) with (Zlength (cs_out c) + Zlength (z_out z')) by lia.
  unfold BoundKit.obj. rewrite Hinb.
  entailer!.
Qed.
