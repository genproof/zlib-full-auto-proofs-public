(* Law deflate_roundtrip, main (kit: RTRMKit.v): positions 8-15 of b0: ib = exact_copy(R.comp, R.clen)
   (deflate HarnessLib), ob = malloc(R.nf), `if (ib == NULL || ob == NULL) return 0;`, the four stores into t
   (next_in, avail_in, next_out, avail_out: t's fields at the law's compspecs, then back to istream), and
   r = inflate(&t, Z_FINISH) (Spec5.inflate_spec with tables_rep Ers gv, crc_table_at Ers gv out of Rm's
   deflate_globals, itok = otok = true; inflate_rel's run2 from m_init; first_ok gives res_ok; z_after and
   URunFrame.run2_frame (m_inp kept) give call1_ok). *)
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

(* outside HEAD..BAD (MEM, SYNC, ...) inflate()'s step returns at once, the machine unchanged *)
Lemma rm8_step_out flush fx dx m :
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
Lemma rm8_inp flush z L inp res :
  Zlib.proof.inflate.Model2.run2 flush lenfix_list distfix_list (m_init z L inp) res -> m_inp (r_m res) = inp.
Proof.
  intros R.
  assert (D: Zlib.proof.uncompr.URunFrame.vmode (i_mode (m_s (m_init z L inp))) \/
             ~ Zlib.proof.uncompr.URunFrame.vmode (i_mode (m_s (m_init z L inp))))
    by (unfold Zlib.proof.uncompr.URunFrame.vmode; lia).
  destruct D as [V | V].
  - destruct (Zlib.proof.uncompr.URunFrame.run2_frame _ _ _ _ _ V R) as (Fi & _). rewrite Fi. reflexivity.
  - destruct (rm8_step_out flush lenfix_list distfix_list _ V) as [r E].
    destruct R as (o & Lp & Ro).
    inversion Lp; subst; rewrite E in *; try discriminate.
    match goal with Hx: Zlib.proof.inflate.Model.IRet _ _ = Zlib.proof.inflate.Model.IRet _ _ |- _ =>
      injection Hx as <- <- end.
    subst res. reflexivity.
Qed.

(* the first call's result in main's terms *)
Lemma rm8_call1 rf ibp obp cont z res L1 :
  m_inp (r_m res) = rf_O rf -> res_ok rf res -> l_s L1 = m_s (r_m res) -> l_h L1 = m_h (r_m res) ->
  call1_ok rf ibp obp (r_ret res) (z_after z (rm_ib rf ibp) (rm_ob rf obp cont) res) L1 (m_ow (r_m res)).
Proof.
  intros Ei OK E1 E2. unfold res_ok in OK. unfold call1_ok, z_after, rm_ib, rm_ob.
  destruct (rm_zd rf); simpl; rewrite ?Ei.
  - destruct OK as (Hr & Hs & Hw & Hsw & Ha & Ht & Had & Hc).
    rewrite Hs, Hsw, Ha, Ht, Had, Hw. pose proof (Hc L1 E1 E2) as Hz. clear Hc. revert Hz.
    generalize (zd_cont rf L1). intros P HP. repeat split; auto. lia.
  - unfold fin_ok. destruct OK as [Hm | (Hr & Hs & Hw & Hsw & Ha)]; [left; auto | right].
    rewrite Hs, Hsw, Ha, Hw. cbn [zf_ai zf_ao]. repeat split; auto; lia.
Qed.

Lemma rm8_fold rf vR :
  ltac:(let x := eval cbv [rm_dside drun_rest] in (rm_dside rf vR) in exact (x |-- rm_dside rf vR)).
Proof. apply derives_refl. Qed.

Lemma rm8_comp_fold O p :
  malloc_token Ews (tarray tuchar COMP_MAX) p *
  data_at Ews (tarray tuchar COMP_MAX) (map vi O ++ Zrepeat Vundef (COMP_MAX - Zlength O)) p |-- comp_at O p.
Proof. apply derives_refl. Qed.

(* the stream t at the law's compspecs *)
Definition rm8_tup (gv : globals) (z : zfields) (sp : val) : rm_strm_tuple :=
  (zf_ni z, (Vint (Int.repr (zf_ai z)), (Vlong (Int64.repr (zf_tin z)), (zf_no z, (Vint (Int.repr (zf_ao z)),
   (Vlong (Int64.repr (zf_tout z)), (msg_val gv (zf_msg z), (sp, (gv Zlib.inflate.code._zcalloc,
   (gv Zlib.inflate.code._zcfree, (nullval, (Vint (Int.repr (zf_dt z)), (Vlong (Int64.repr (zf_adler z)),
   zf_res z))))))))))))).

Lemma rm8_istream_unfold gv shs vt z L :
  istream gv shs vt z (Some L) =
  !! (zf_ok z /\ writable_share shs /\ live_ok L) &&
  (@data_at CS shs t_strmL (rm8_tup gv z (l_sp L)) vt * state_mem gv vt L).
Proof.
  unfold istream, zstrm_at, Zlib.proof.inflate.Rep.strm_rep.
  rewrite rm_strm_cs.
  apply pred_ext; entailer!.
Qed.

Lemma rm8_istream_fold gv shs vt z L :
  zf_ok z -> writable_share shs -> live_ok L ->
  @data_at CS shs t_strmL (rm8_tup gv z (l_sp L)) vt * state_mem gv vt L |-- istream gv shs vt z (Some L).
Proof. intros. rewrite rm8_istream_unfold. entailer!. Qed.

(* the stream fields offered to the call *)
Definition rm8_z (z : zfields) (ni : val) (ai : Z) (no : val) (ao : Z) : zfields :=
  ZF ni ai (zf_tin z) no ao (zf_tout z) (zf_msg z) (zf_dt z) (zf_adler z) (zf_res z).

Lemma rm8_tup_set gv z sp ni ai no ao :
  rm8_tup gv (rm8_z z ni ai no ao) sp =
  (ni, (Vint (Int.repr ai), (fst (snd (snd (rm8_tup gv z sp))), (no, (Vint (Int.repr ao),
   snd (snd (snd (snd (snd (rm8_tup gv z sp)))))))))).
Proof. reflexivity. Qed.

Lemma rm8_tok_cs sh n q :
  @malloc_token Zlib.units.Inflate.CS sh (tarray tuchar n) q = @malloc_token CS sh (tarray tuchar n) q.
Proof. apply equal_f; apply (@malloc_token_change_composite _ _ CC_inflate). reflexivity. Qed.

(* the copy of O and the output space as inflate() takes them *)
Lemma rm8_bufs_pre L rf ibp obp :
  0 <= rf_nf rf ->
  @data_at CS Ews (tarray tuchar (Zlength (rf_O rf))) (bytes_rep (rf_O rf)) ibp *
  @malloc_token CS Ews (tarray tuchar (Zlength (rf_O rf))) ibp *
  @data_at_ CS Ews (tarray tuchar (rf_nf rf)) obp * @malloc_token CS Ews (tarray tuchar (rf_nf rf)) obp
  |-- bufs_opt (Some L) (rm_ib rf ibp) (Some (rm_ob rf obp (Zrepeat Vundef (rf_nf rf)))) [] true true.
Proof.
  intros Hn. unfold bufs_opt, in_rep, out_opt, out_rep, in_tok, out_tok, rm_ib, rm_ob.
  rewrite !rm8_tok_cs, !(bytes_cs Zlib.units.Inflate.CS CS).
  assert (E: sublist 0 0 (Zrepeat Vundef (rf_nf rf)) ++ byte_vals [] ++
             sublist (0 + Zlength (@nil Z)) (rf_nf rf) (Zrepeat Vundef (rf_nf rf)) = Zrepeat Vundef (rf_nf rf)).
  { rewrite sublist_nil. simpl. rewrite sublist_same by (rewrite ?Zlength_Zrepeat; lia). reflexivity. }
  rewrite E. unfold data_at_. cancel.
Qed.

Lemma rm8_iopt gv shs (vt : val) z st : isptr vt -> istream_opt gv shs vt z st = istream gv shs vt z st.
Proof. intros P. unfold istream_opt. destruct (eq_dec vt nullval); [subst; contradiction | reflexivity]. Qed.

Lemma rm8_islive (vt : val) st : isptr vt -> is_live vt st = st.
Proof. intros P. unfold is_live. destruct (eq_dec vt nullval); [subst; contradiction | reflexivity]. Qed.

Lemma rm8_out_opt o ow : out_opt (Some o) ow = out_rep o ow.
Proof. reflexivity. Qed.

(* return 0 with R, t given back as their locals' memory *)
Ltac rm8_ret H := forward; Exists (Int.repr 0); sep_apply rm8_comp_fold; sep_apply rm8_fold;
  sep_apply (rm_dside_ret _ _ _ H); sep_apply rm_istream_ret; entailer!.

Lemma rm_seg8 {Espec : OracleKind} I Iend rf vR vs vt vih gv z L :
  (forall ibp obp r z1 L1 ow cont,
     semax (Delta_m I Iend) (A16 Iend rf vR vs vt vih gv ibp obp r z1 L1 ow cont) seg16 POST_b) ->
  semax (Delta_m I Iend) (A8 Iend rf vR vs vt vih gv z L) seg8 POST_b.
Proof.
  intros K.
  unfold A8. Intros.
  pose proof H as Hok. destruct Hok as (RS & _ & _ & FO & Hnf & HO & Hd & _).
  pose proof (proj1 FO) as BO.
  assert (Pc: isptr (rs_compp (rf_rs rf))) by (unfold rs_ok in RS; tauto).
  assert (Hdl: Zlength (rs_data (rf_rs rf)) <= 1048576) by (unfold rs_ok in RS; tauto).
  unfold rm_dside, drun_rest, comp_at. Intros.
  unfold seg8, Delta_m, Gm5, POST_b, POST_m. simplify_func_tycontext. abbreviate_semax.
  forward. forward.
  forward_call (rs_compp (rf_rs rf), Ews, rs_compp (rf_rs rf), 0, COMP_MAX,
                map vi (rf_O rf) ++ Zrepeat Vundef (COMP_MAX - Zlength (rf_O rf)), Zlength (rf_O rf), rf_O rf, gv).
  { entailer!. unfold vl; simpl. rewrite Int64.Z_mod_modulus_eq, Z.mod_small by (unfold COMP_MAX in HO; rep_lia).
    reflexivity. }
  { rewrite (bytes_cs DCS.CS CS). cancel. }
  { split; [unfold COMP_MAX in HO; rep_lia |].
    unfold cbuf_ok. rewrite isptr_offset_val_zero by auto.
    repeat split; auto; try lia.
    - unfold bytes in BO. unfold is_bytes. eapply Forall_impl; [| exact BO]. simpl. intros; rep_lia.
    - rewrite Z.add_0_l, sublist_app1 by list_solve. rewrite sublist_same by list_solve.
      reflexivity. }
  Intros ibp.
  rewrite !(bytes_cs DCS.CS CS), !tok_tuchar_cs.
  forward. forward.
  forward_call (tarray tuchar (rf_nf rf), gv).
  { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros obp.
  forward.
  destruct (eq_dec ibp nullval) as [Eib | Nib]; [ | destruct (eq_dec obp nullval) as [Eob | Nob]].
  { ifpost _t'16 Int.one.
    { forward. entailer!. }
    { contradiction. }
    forward_if.
    { rm8_ret H. }
    exfalso; apply Int.one_not_zero; assumption. }
  { destruct (eq_dec ibp nullval); [contradiction | ]. Intros.
    ifpost _t'16 Int.one.
    { forward. entailer!. }
    { forward. entailer!. }
    forward_if.
    { rm8_ret H. }
    exfalso; apply Int.one_not_zero; assumption. }
  destruct (eq_dec ibp nullval); [contradiction | ]. destruct (eq_dec obp nullval); [contradiction | ]. Intros.
  ifpost _t'16 Int.zero.
  { forward. entailer!. }
  { forward. entailer!. destruct obp; simpl in PNobp; try contradiction; reflexivity. }
  forward_if.
  { contradiction. }
  rewrite rm8_istream_unfold. Intros.
  forward. forward. forward. forward. forward. forward.
  rewrite Int64.Z_mod_modulus_eq, Z.mod_small by (unfold COMP_MAX in HO; rep_lia).
  rewrite <- rm8_tup_set.
  assert_PROP (isptr vt /\ field_compatible (tarray tuchar (Zlength (rf_O rf))) [] ibp /\
               field_compatible (tarray tuchar (rf_nf rf)) [] obp) as FC by entailer!.
  destruct FC as (Pvt & FCi & FCo).
  assert (Pib: isptr ibp) by (apply field_compatible_isptr in FCi; auto).
  assert (Pob: isptr obp) by (apply field_compatible_isptr in FCo; auto).
  set (z1 := rm8_z z ibp (Zlength (rf_O rf)) obp (rf_nf rf)).
  assert (Z1ok: zf_ok z1).
  { destruct H1 as (Zk & _). unfold zf_ok in Zk. unfold z1, rm8_z, zf_ok; simpl. unfold COMP_MAX in HO. rep_lia. }
  sep_apply (rm8_istream_fold gv Tsh vt z1 L); auto.
  sep_apply (rm8_bufs_pre L rf ibp obp); [lia | ].
  unfold Rm, deflate_globals. Intros.
  forward_call (gv, Tsh, vt, z1, Some L, rm_ib rf ibp, rf_O rf, Some (rm_ob rf obp (Zrepeat Vundef (rf_nf rf))),
                4, Ers, Ers, true, true).
  { rewrite rm8_iopt, rm8_islive by auto. simpl head_opt. cancel. }
  { unfold z1, rm8_z, rm_ib, rm_ob, in_ok, out_ok, in_ptr, out_ptr; simpl.
    rewrite !isptr_offset_val_zero by auto.
    assert (Bo: bytes_ok (rf_O rf)).
    { unfold bytes in BO. unfold bytes_ok. eapply Forall_impl; [| exact BO]. simpl. intros; rep_lia. }
    unfold COMP_MAX in HO.
    repeat match goal with |- _ /\ _ => split end; auto with share; try rep_lia.
    all: first [ rewrite Zlength_byte_vals; reflexivity
               | rewrite Z.add_0_l, sublist_same by (rewrite ?Zlength_byte_vals; lia); reflexivity
               | rewrite Zlength_Zrepeat by lia; reflexivity ]. }
  Intros vret. destruct vret as [[[r z'] st'] ow]. cbn [fst snd] in *.
  match goal with Hx: inflate_rel _ _ _ _ _ _ _ _ _ _ _ |- _ => rename Hx into Hrel end.
  destruct Hrel as [(Bad & _) | (_ & L0 & o & res & winp & EL & Eo & Hrun & Hsnx & Er & Eow & Ez & Hw & Est)].
  { exfalso. unfold inflate_bad in Bad. rewrite rm8_islive in Bad by auto.
    destruct Bad as [B | [B | (B & _)]]; discriminate. }
  injection EL as <-. injection Eo as <-. subst r ow z' st'.
  match goal with Hx: live_ok L |- _ => rename Hx into Lok end.
  assert (Zc: zcall_ok z1 (rf_O rf) (rm_D rf)).
  { destruct H1 as (_ & _ & _ & _ & _ & Ht & _).
    unfold zcall_ok. split; [exact Z1ok | ]. unfold z1, rm8_z, rm_D; simpl.
    rewrite Zlength_sublist by lia. repeat split; auto; lia. }
  pose proof (H2 z1 res Lok Zc Hrun) as Rok.
  pose proof (rm8_inp _ _ _ _ _ Hrun) as Ei.
  set (L1 := Live (l_sp L) winp (m_s (r_m res)) (m_h (r_m res)) (l_headp L) (l_hsh L) (l_xb L) (l_nb L) (l_cb L)).
  pose proof (rm8_call1 rf ibp obp (Zrepeat Vundef (rf_nf rf)) z1 res L1 Ei Rok eq_refl eq_refl) as C1.
  rewrite !rm8_iopt, !rm8_islive by auto. simpl head_opt. unfold bufs_opt. rewrite rm8_out_opt.
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
  eapply semax_pre; [ | apply (K ibp obp (r_ret res)
                                  (z_after z1 (rm_ib rf ibp) (rm_ob rf obp (Zrepeat Vundef (rf_nf rf))) res) L1
                                  (m_ow (r_m res)) (Zrepeat Vundef (rf_nf rf))) ].
  unfold A16, Rm, deflate_globals.
  sep_apply rm8_comp_fold. sep_apply rm8_fold.
  entailer!.
  rewrite Zlength_Zrepeat by lia. reflexivity.
Qed.
