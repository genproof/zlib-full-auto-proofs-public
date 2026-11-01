(* Law deflate_roundtrip, main (kit: RTRMKit.v): position 16 of b0, the zlib dictionary block
   `if (R.wrap == 1 && R.dict_set) { gp_assert(r == Z_NEED_DICT); gp_assert(t.adler == ref_adler32(1, R.dict,
   R.dlen)); r = inflateSetDictionary(&t, R.dict, R.dlen); if (r == Z_MEM_ERROR) return 0; gp_assert(r == Z_OK);
   r = inflate(&t, Z_FINISH); }` (call1_ok's zd_cont gives the second call's rdone on O[6..]); establishes A17
   (fin_ok); without a zlib dictionary call1_ok is fin_ok already. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.HarnessRef.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Zlib.proof.deflate.Obligations.
Require Import Zlib.proof.deflate.LawFacts Zlib.proof.deflate.HarnessLib Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.roundtrip.RTXFacts.
Require Import Zlib.proof.roundtrip.RTRCS Zlib.proof.roundtrip.RTRRunSpec Zlib.proof.roundtrip.RTRRunKit Zlib.proof.roundtrip.RTRApiConv Zlib.proof.roundtrip.RTRMainSpec.
Require Import Zlib.proof.roundtrip.RTIIface.
Require Import Zlib.harness.x_deflate_roundtrip.code.
Require Import Zlib.proof.roundtrip.RTRMKit.
Require Zlib.proof.uncompr.URunFrame.
#[local] Existing Instance RTRCS.CS.
Local Open Scope logic.

(* rm_dside opened at the fields position 16 reads (R.wrap, R.dict_set, R.dict, R.dlen) and the dictionary
   object *)
Definition rm16_rest (rf : rfinal) (vR : val) : mpred :=
  let rs := rf_rs rf in let Rp := vR in
  field_at Ews t_drun (DOT _level) (vi (rs_level rs)) Rp *
  field_at Ews t_drun (DOT _method) (vi (rs_method rs)) Rp *
  field_at Ews t_drun (DOT _wbits) (vi (rs_wbits rs)) Rp *
  field_at Ews t_drun (DOT _mem) (vi (rs_mem rs)) Rp *
  field_at Ews t_drun (DOT _strategy) (vi (rs_strategy rs)) Rp *
  field_at Ews t_drun (DOT _init) (vi 0) Rp *
  field_at Ews t_drun (DOT _wb) (vi (wb_of (rs_wbits rs))) Rp *
  field_at Ews t_drun (DOT _data) (rs_datap rs) Rp *
  field_at Ews t_drun (DOT _n) (vi (Zlength (rs_data rs))) Rp *
  field_at Ews t_drun (DOT _nf) (vi (rf_nf rf)) Rp *
  field_at Ews t_drun (DOT _head_set) (vi (rf_hset rf)) Rp *
  field_at Ews t_drun (DOT _xf) (rs_xfp rs) Rp *
  field_at Ews t_drun (DOT _nf_) (rs_nfp rs) Rp *
  field_at Ews t_drun (DOT _cf) (rs_cfp rs) Rp *
  field_at Ews t_drun (DOT _xlen) (vi (Zlength (rs_xf rs))) Rp *
  field_at Ews t_drun (DOT _nl) (vi (Zlength (rs_nm rs))) Rp *
  field_at Ews t_drun (DOT _cl) (vi (Zlength (rs_cm rs))) Rp *
  field_at Ews t_drun (DOT _comp) (rs_compp rs) Rp *
  field_at Ews t_drun (DOT _clen) (vl (Zlength (rf_O rf))) Rp *
  field_at Ews t_drun (DOT _ended) (vi 1) Rp *
  field_at Ews t_drun (DOT _api_ok) (vi 1) Rp *
  drun_pad Rp *
  hpart (rf_hset rf) vR * hdr_at (Some (rf_s rf)) (rf_ghp rf) (hx_of rs) *
  obj (rs_datap rs) (rs_data rs) * comp_at (rf_O rf) (rs_compp rs) *
  data_at_ (Share.comp Ews) t_drun vR.

Definition rm16_open (rf : rfinal) (vR : val) : mpred :=
  let rs := rf_rs rf in
  field_at Ews t_drun (DOT _wrap) (vi (rf_wrap rf)) vR *
  field_at Ews t_drun (DOT _dict) (rs_dictp rs) vR *
  field_at Ews t_drun (DOT _dlen) (vi (Zlength (rs_dict rs))) vR *
  field_at Ews t_drun (DOT _dict_set) (vi (rf_dset rf)) vR *
  malloc_token Ews (tarray tuchar (Zlength (rs_dict rs))) (rs_dictp rs) *
  data_at Ews (tarray tuchar (Zlength (rs_dict rs))) (map vi (rs_dict rs)) (rs_dictp rs) *
  rm16_rest rf vR.

Lemma rm16_open_eq rf vR : rm_dside rf vR = rm16_open rf vR.
Proof. unfold rm_dside, drun_rest, rm16_open, rm16_rest, obj. apply pred_ext; cancel. Qed.

Lemma rm16_close rf vR :
  field_at Ews t_drun (DOT _wrap) (vi (rf_wrap rf)) vR *
  field_at Ews t_drun (DOT _dict) (rs_dictp (rf_rs rf)) vR *
  field_at Ews t_drun (DOT _dlen) (vi (Zlength (rs_dict (rf_rs rf)))) vR *
  field_at Ews t_drun (DOT _dict_set) (vi (rf_dset rf)) vR *
  malloc_token Ews (tarray tuchar (Zlength (rs_dict (rf_rs rf)))) (rs_dictp (rf_rs rf)) *
  data_at Ews (tarray tuchar (Zlength (rs_dict (rf_rs rf)))) (map vi (rs_dict (rf_rs rf))) (rs_dictp (rf_rs rf)) *
  rm16_rest rf vR |-- rm_dside rf vR.
Proof. rewrite rm16_open_eq. unfold rm16_open. apply derives_refl. Qed.

Lemma rm16_wrap rf : rf_wrap rf = 0 \/ rf_wrap rf = 1 \/ rf_wrap rf = 2.
Proof. unfold rf_wrap, wrap_of. destruct (_ <? 0); [ | destruct (_ >? 15)]; auto. Qed.

Lemma rm16_iopt gv sh p z st : isptr p -> istream_opt gv sh p z st = istream gv sh p z st.
Proof. intros P. unfold istream_opt. destruct (eq_dec p nullval); [subst; contradiction | reflexivity]. Qed.

Lemma rm16_is_live p st : isptr p -> is_live p st = st.
Proof. intros P. unfold is_live. destruct (eq_dec p nullval); [subst; contradiction | reflexivity]. Qed.

Lemma rm16_on_live p z L f : isptr p ->
  on_live p z (Some L) f = (fst3 (f z L), snd3 (f z L), Some (thd3 (f z L))).
Proof.
  intros P. unfold on_live, is_live. destruct (eq_dec p nullval); [subst; contradiction | ].
  destruct (f z L) as [[? ?] ?]; reflexivity.
Qed.

Lemma rm16_head_uw s d : i_head (updatewindow s d) = i_head s.
Proof.
  unfold updatewindow. cbv zeta.
  destruct (i_wsize s =? 0);
    repeat match goal with |- context [if ?b then _ else _] => destruct b end; reflexivity.
Qed.

Lemma rm16_head_sd dict aok winp z L :
  i_head (l_s (thd3 (setdict_f dict aok winp z L))) = i_head (l_s L).
Proof.
  unfold setdict_f. destruct (setdict_check (l_s L) dict); try reflexivity.
  destruct (i_win (l_s L)); [ | destruct aok]; simpl; try apply rm16_head_uw; reflexivity.
Qed.

Lemma rm16_z_sd dict aok winp z L : snd3 (setdict_f dict aok winp z L) = z.
Proof.
  unfold setdict_f. destruct (setdict_check (l_s L) dict); try reflexivity.
  destruct (i_win (l_s L)); [ | destruct aok]; reflexivity.
Qed.

(* the fields of t at the law's compspecs *)
Definition rm16_tup (gv : globals) (z : zfields) (sp : val) : rm_strm_tuple :=
  (zf_ni z, (Vint (Int.repr (zf_ai z)), (Vlong (Int64.repr (zf_tin z)), (zf_no z,
   (Vint (Int.repr (zf_ao z)), (Vlong (Int64.repr (zf_tout z)), (Zlib.proof.inflate.Rep.msg_val gv (zf_msg z),
   (sp, (gv Zlib.inflate.code._zcalloc, (gv Zlib.inflate.code._zcfree, (nullval, (Vint (Int.repr (zf_dt z)), (Vlong (Int64.repr (zf_adler z)),
    zf_res z))))))))))))).

Lemma rm16_istream_unfold gv shs vt z L :
  istream gv shs vt z (Some L) =
  !! (zf_ok z /\ writable_share shs /\ live_ok L) &&
  (@data_at CS shs t_strmL (rm16_tup gv z (l_sp L)) vt * state_mem gv vt L).
Proof.
  unfold istream, zstrm_at, Zlib.proof.inflate.Rep.strm_rep.
  rewrite <- (rm_strm_cs shs (rm16_tup gv z (l_sp L)) vt). unfold rm16_tup.
  apply pred_ext; entailer!.
Qed.

Lemma rm16_istream_fold gv shs vt z L :
  zf_ok z -> writable_share shs -> live_ok L ->
  @data_at CS shs t_strmL (rm16_tup gv z (l_sp L)) vt * state_mem gv vt L |-- istream gv shs vt z (Some L).
Proof. intros. rewrite rm16_istream_unfold. entailer!. Qed.

Lemma rm16_hmem_sd dict aok winp z L :
  head_mem (thd3 (setdict_f dict aok winp z L)) = head_mem L.
Proof.
  unfold head_mem. rewrite rm16_head_sd.
  unfold setdict_f. destruct (setdict_check (l_s L) dict); try reflexivity.
  destruct (i_win (l_s L)); [ | destruct aok]; reflexivity.
Qed.

(* outside HEAD..BAD (MEM, SYNC, ...) inflate()'s step returns at once, the machine unchanged *)
Lemma rm16_step_out flush fx dx m :
  ~ Zlib.proof.uncompr.URunFrame.vmode (i_mode (m_s m)) ->
  exists r, Zlib.proof.inflate.Model2.stepf2 flush fx dx m = Zlib.proof.inflate.Model.IRet r m.
Proof.
  intros V. unfold Zlib.proof.uncompr.URunFrame.vmode in V.
  unfold Zlib.proof.inflate.Model2.stepf2, Zlib.proof.inflate.Model2.step2, Zlib.proof.inflate.Model.m_mode.
  repeat match goal with |- context [if Z.eqb ?a ?b then _ else _] =>
    let E := fresh "E" in destruct (Z.eqb a b) eqn:E;
    [apply Z.eqb_eq in E; rewrite E in V; exfalso; apply V; compute; split; discriminate | ] end.
  destruct (_ =? MEM); eexists; reflexivity.
Qed.

(* inflate()'s machine keeps its input *)
Lemma rm16_inp flush z L inp res :
  Zlib.proof.inflate.Model2.run2 flush lenfix_list distfix_list (m_init z L inp) res -> m_inp (r_m res) = inp.
Proof.
  intros R.
  assert (D: Zlib.proof.uncompr.URunFrame.vmode (i_mode (m_s (m_init z L inp))) \/
             ~ Zlib.proof.uncompr.URunFrame.vmode (i_mode (m_s (m_init z L inp))))
    by (unfold Zlib.proof.uncompr.URunFrame.vmode; lia).
  destruct D as [V | V].
  - destruct (Zlib.proof.uncompr.URunFrame.run2_frame _ _ _ _ _ V R) as (Fi & _). rewrite Fi. reflexivity.
  - destruct (rm16_step_out flush lenfix_list distfix_list _ V) as [r E].
    destruct R as (o & Lp & Ro).
    inversion Lp; subst; rewrite E in *; try discriminate.
    match goal with Hx: Zlib.proof.inflate.Model.IRet _ _ = Zlib.proof.inflate.Model.IRet _ _ |- _ =>
      injection Hx as <- <- end.
    subst res. reflexivity.
Qed.

Lemma rm_seg16 {Espec : OracleKind} I Iend rf vR vs vt vih gv ibp obp r z1 L1 ow cont :
  (forall r' z' L' ow' cont',
     semax (Delta_m I Iend) (A17 Iend rf vR vs vt vih gv ibp obp r' z' L' ow' cont') seg17 POST_b) ->
  semax (Delta_m I Iend) (A16 Iend rf vR vs vt vih gv ibp obp r z1 L1 ow cont) seg16 POST_b.
Proof.
  intros K.
  unfold seg16.
  apply semax_seq with (Q := EX r' : Z, EX z' : zfields, EX L' : live, EX ow' : list Z,
                               A17 Iend rf vR vs vt vih gv ibp obp r' z' L' ow' cont);
    [ | repeat (apply extract_exists_pre; intro); apply K].
  unfold A16. Intros.
  rewrite rm16_open_eq. unfold rm16_open. Intros.
  assert (DS: (rf_dset rf = 1 /\ rf_dict rf = rs_dict (rf_rs rf) /\ rs_dict (rf_rs rf) <> []) \/
              (rf_dset rf = 0 /\ rf_dict rf = []))
    by (destruct H as (_ & _ & _ & _ & _ & _ & X & _); exact X).
  assert (RS: rs_ok (rf_rs rf)) by (destruct H; auto).
  unfold Delta_m, Gm5, POST_b, POST_m. simplify_func_tycontext. abbreviate_semax.
  forward.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _t'21 (Vint (if rm_zd rf then Int.one else Int.zero)) :: Q) (SEPx R))) end.
  { assert (W1: rf_wrap rf = 1).
    { destruct (rm16_wrap rf) as [E | [E | E]]; rewrite E in *; auto;
        apply repr_inj_signed in H3; rep_lia. }
    forward. forward. entailer!. unfold rm_zd. rewrite W1. destruct DS as [[D _] | [D _]]; rewrite D; reflexivity. }
  { forward. entailer!. unfold rm_zd.
    rewrite (proj2 (Z.eqb_neq _ _) (fun E => H3 (f_equal (fun x => Int.repr x) E))). reflexivity. }
  unfold call1_ok in H1.
  forward_if.
  { destruct (rm_zd rf) eqn:ZD; [ | contradiction H3; reflexivity].
    destruct H1 as (Hr & Hni & Hai & Hno & Hao & Hto & Had & Ho & ZC). subst r ow.
    assert (WD: rf_wrap rf = 1 /\ rf_dset rf = 1)
      by (unfold rm_zd in ZD; apply andb_true_iff in ZD; destruct ZD as [E1 E2];
          apply Z.eqb_eq in E1; apply Z.eqb_eq in E2; auto).
    destruct WD as [W D].
    destruct DS as [[_ [ED NE]] | [D' _]]; [ | lia].
    forward_call (Int.repr 1).
    forward. forward.
    destruct RS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & DDL & DL & _ & _ & _ & _ &
                    BD & _ & _ & _ & _ & PD & _).
    rewrite (bytes_cs CS Zlib.units.Adler32.CS Ews).
    forward_call (1, rs_dictp (rf_rs rf), Ews, rs_dictp (rf_rs rf), 0, Zlength (rs_dict (rf_rs rf)),
                  map vi (rs_dict (rf_rs rf)), Zlength (rs_dict (rf_rs rf)), rs_dict (rf_rs rf)).
    { unfold cbuf_ok. rewrite isptr_offset_val_zero by auto.
      repeat split; auto; try lia.
      - unfold bytes in BD. unfold is_bytes. eapply Forall_impl; [| exact BD]. simpl. intros; rep_lia.
      - rewrite sublist_same by (rewrite ?Zlength_map; lia). reflexivity. }
    rewrite (bytes_cs Zlib.units.Adler32.CS CS Ews).
    rewrite rm16_istream_unfold. Intros.
    unfold rm16_tup.
    forward.
    forward_call (Int.repr 1).
    { entailer!. rewrite Had, ED. simpl. rewrite Int64.eq_true. reflexivity. }
    fold (rm16_tup gv z1 (l_sp L1)).
    sep_apply (rm16_istream_fold gv Tsh vt z1 L1); auto.
    forward. forward.
    assert_PROP (isptr vt) as Pvt by entailer!.
    rewrite (bytes_cs CS Zlib.units.Inflate.CS Ews).
    forward_call (gv, Tsh, vt, z1, Some L1, Ews, rs_dictp (rf_rs rf), 0,
                  Zlength (rs_dict (rf_rs rf)), map vi (rs_dict (rf_rs rf)), rs_dict (rf_rs rf), false).
    { rewrite rm16_iopt by auto. cancel. }
    { split; [apply Zlength_map | ].
      split; [intros E; apply Zlength_nil_inv in E; contradiction | ].
      split; [rewrite sublist_same by (rewrite ?Zlength_map; lia); reflexivity | ].
      eapply Forall_impl; [ | exact BD]. intros b Hb; simpl in *; rep_lia. }
    Intros vret. destruct vret as [aok winp]. simpl fst; simpl snd.
    rewrite rm16_iopt by auto. rewrite !rm16_on_live by auto.
    pose proof (ZC aok winp z1 H5) as SD. cbv zeta in SD. rewrite ED in SD.
    pose proof (rm16_z_sd (rs_dict (rf_rs rf)) aok winp z1 L1) as ZS.
    pose proof (rm16_hmem_sd (rs_dict (rf_rs rf)) aok winp z1 L1) as HS.
    destruct (setdict_f (rs_dict (rf_rs rf)) aok winp z1 L1) as [[r z'] L'] eqn:E.
    unfold fst3, snd3, thd3 in *; simpl fst in *; simpl snd in *. subst z'.
    rewrite (bytes_cs Zlib.units.Inflate.CS CS Ews).
    destruct SD as [Hr HOK].
    forward.
    forward_if.
    { sep_apply (rm16_close rf vR). sep_apply (rm_dside_ret Iend vR rf H). sep_apply rm_istream_ret.
      forward. Exists (Int.repr 0). entailer!. }
    assert (r = Z_OK) by (destruct Hr; auto; subst; contradiction). subst r.
    specialize (HOK eq_refl).
    forward_call (Int.repr 1).
    rewrite <- HS.
    assert_PROP (live_ok L') as LOK' by (unfold istream; entailer!).
    pose proof H as Hok. destruct Hok as (_ & _ & _ & FO & Hnf & HO & _).
    pose proof (proj1 FO) as BO.
    set (O := rf_O rf) in *.
    set (inp := sublist 6 (Zlength O) O).
    assert (HO6: 6 <= Zlength O) by (destruct H1 as (? & _); lia).
    assert (Hinp: Zlength inp = Zlength O - 6) by (unfold inp; rewrite Zlength_sublist; lia).
    assert (HD: Zlength (rm_D rf) = rf_nf rf)
      by (unfold rm_D; rewrite Zlength_sublist; lia).
    set (ib2 := InBuf Ews ibp 6 (Zlength O) (byte_vals O)).
    set (ob2 := rm_ob rf obp cont).
    assert_PROP (isptr ibp /\ isptr obp) as Pio.
    { unfold ob2, in_rep, rm_ib, out_rep, rm_ob. entailer!.
      split; match goal with Hf: @field_compatible ?cs _ _ ?p |- isptr ?p =>
                       exact (@field_compatible_isptr cs _ _ _ Hf) end. }
    destruct Pio as [Pib Pob].
    unfold Rm, deflate_globals. Intros.
    forward_call (gv, Tsh, vt, z1, Some L', ib2, inp, Some ob2, 4, Ers, Ers, true, true).
    { rewrite rm16_iopt, rm16_is_live by auto. simpl head_opt.
      unfold bufs_opt, out_opt, ib2, in_rep, in_tok, rm_ib. cancel. }
    { unfold ib2, ob2, rm_ob, in_ok, out_ok. rewrite ?Hai, ?Hao, ?HD, ?Hinp.
      unfold COMP_MAX in HO.
      repeat match goal with |- _ /\ _ => split end; auto with share; try rep_lia.
      all: first [ unfold byte_vals; rewrite Zlength_map; reflexivity
                 | unfold inp, byte_vals; rewrite <- sublist_map; f_equal; lia
                 | unfold inp, bytes_ok; apply Forall_sublist; eapply Forall_impl; [| exact BO]; simpl; intros; rep_lia ]. }
    Intros vret. destruct vret as [[[r2 z2] st2] ow2]. simpl fst in *; simpl snd in *.
    match goal with Hx: inflate_rel _ _ _ _ _ _ _ _ _ _ _ |- _ => rename Hx into Hrel end.
    destruct Hrel as [[BAD _] | (_ & L0 & o & res & winp2 & E0 & E1 & Hrun & Hsnx & -> & -> & -> & _ & ->)].
    { exfalso. unfold inflate_bad in BAD. rewrite rm16_is_live in BAD by auto.
      destruct BAD as [B | [B | [B _]]]; discriminate. }
    injection E0 as <-. injection E1 as <-.
    assert (FIN: fin_ok rf (r_ret res) (z_after z1 ib2 ob2 res) (m_ow (r_m res))).
    { assert (ZK: zcall_ok z1 inp (rm_D rf)) by (unfold zcall_ok; split; [exact H1 | split; [lia | split; [exact Hao | exact Hto]]]).
      pose proof (HOK z1 res LOK' ZK Hrun) as RD.
      pose proof (rm16_inp _ _ _ _ _ Hrun) as Ein.
      unfold fin_ok, z_after. cbn [zf_ai zf_ao].
      destruct RD as [M | (Hend & Hs & Hw & Hsw & Ha)]; [left; auto | right].
      fold inp in Hs. rewrite Ein, Hs, Hsw, Ha, Hw. repeat split; auto; lia. }
    rewrite rm16_iopt, !rm16_is_live by auto.
    forward.
    sep_apply (rm16_close rf vR).
    Exists (r_ret res) (z_after z1 ib2 ob2 res)
      (Live (l_sp L') winp2 (m_s (r_m res)) (m_h (r_m res)) (l_headp L') (l_hsh L') (l_xb L') (l_nb L') (l_cb L'))
      (m_ow (r_m res)).
    unfold A17, Rm, deflate_globals. simpl head_opt.
    unfold bufs_opt, out_opt, ob2, ib2, in_rep, in_tok, rm_ib.
    entailer!. }
  { destruct (rm_zd rf) eqn:ZD; [ apply Int.one_not_zero in H3; contradiction | ].
    forward.
    Exists r z1 L1 ow. unfold A17. rewrite rm16_open_eq. unfold rm16_open. entailer!. }
Qed.
