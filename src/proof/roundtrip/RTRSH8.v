(* Law deflate_roundtrip, the gzip run with a header (R.head_set = 1), part H8: positions 8-15 of
   b0 from AH8: exact_copy(R.comp, R.clen), malloc(R.nf), the NULL test (return 0), the stores into t, and
   r = inflate(&t, Z_FINISH) by RTHSpec.inflate_spec6 (hd6_ok from gz_first_ok; head_opt6 = head_mem6);
   establishes AH16 (gz_call_ok from gz_first_ok's result; i_head kept: RTRSKit.rmh_run_head).  As
   RTRMSeg8.v. *)
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
Require Import Zlib.proof.roundtrip.RTHSpec Zlib.proof.roundtrip.RTHIfDefs.
Require Import Zlib.harness.x_deflate_roundtrip.code.
Require Import Zlib.proof.roundtrip.RTRMKit Zlib.proof.roundtrip.RTRSKit.
Require Zlib.proof.uncompr.URunFrame.
Require Import Zlib.proof.roundtrip.RTRMSeg8.
#[local] Existing Instance RTRCS.CS.
Local Open Scope logic.

(* the call's result in main's terms *)
Lemma rmh8_call1 rf ibp obp cont z res L1 :
  m_inp (r_m res) = rf_O rf -> gz_res_ok rf res -> l_s L1 = m_s (r_m res) -> l_h L1 = m_h (r_m res) ->
  gz_call_ok rf (r_ret res) (z_after z (rm_ib rf ibp) (rm_ob rf obp cont) res) L1 (m_ow (r_m res)).
Proof.
  intros Ei (OK & Hend) E1 E2. unfold gz_call_ok. split.
  - unfold z_after, rm_ib, rm_ob. rewrite ?Ei.
    unfold fin_ok. destruct OK as [Hm | (Hr & Hs & Hw & Hsw & Ha)]; [left; auto | right].
    rewrite Hs, Hsw, Ha, Hw. cbn [zf_ai zf_ao]. repeat split; auto; lia.
  - intros Hr. rewrite E1, E2. apply Hend; exact Hr.
Qed.

(* return 0 with R, t, ih given back as their locals' memory *)
Ltac rmh8_ret H Hh := forward; Exists (Int.repr 0); sep_apply rm8_comp_fold; sep_apply rm8_fold;
  sep_apply (rm_dside_ret _ _ _ H); sep_apply rm_istream_ret; sep_apply Hh; entailer!.

Lemma rmh_seg8 {Espec : OracleKind} I Iend rf vR vs vt vih gv z L :
  (forall ibp obp r z1 L1 ow cont,
     semax (Delta_m6 I Iend) (AH16 Iend rf vR vs vt vih gv ibp obp r z1 L1 ow cont) seg16 POST_b) ->
  semax (Delta_m6 I Iend) (AH8 Iend rf vR vs vt vih gv z L) seg8 POST_b.
Proof.
  intros K.
  unfold AH8. Intros.
  pose proof (rm_head6_ret L vih H3 H4 H5) as HR.
  pose proof H as Hok. destruct Hok as (RS & _ & _ & FO & Hnf & HO & Hd & _).
  pose proof (proj1 FO) as BO.
  assert (Pc: isptr (rs_compp (rf_rs rf))) by (unfold rs_ok in RS; tauto).
  assert (Hdl: Zlength (rs_data (rf_rs rf)) <= 1048576) by (unfold rs_ok in RS; tauto).
  unfold rm_dside, drun_rest, comp_at. Intros.
  unfold seg8, Delta_m6, Gm6, POST_b, POST_m. simplify_func_tycontext. abbreviate_semax.
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
    { rmh8_ret H HR. }
    exfalso; apply Int.one_not_zero; assumption. }
  { destruct (eq_dec ibp nullval); [contradiction | ]. Intros.
    ifpost _t'16 Int.one.
    { forward. entailer!. }
    { forward. entailer!. }
    forward_if.
    { rmh8_ret H HR. }
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
  match goal with Hx: live_ok L |- _ => rename Hx into Lok end.
  assert (Zc: zcall_ok z1 (rf_O rf) (rm_D rf)).
  { destruct H1 as (_ & _ & _ & _ & _ & Ht & _).
    unfold zcall_ok. split; [exact Z1ok | ]. unfold z1, rm8_z, rm_D; simpl.
    rewrite Zlength_sublist by lia. repeat split; auto; lia. }
  destruct (H2 z1 Lok Zc) as (Hpass & Hres).
  sep_apply (rm8_istream_fold gv Tsh vt z1 L); auto.
  sep_apply (rm8_bufs_pre L rf ibp obp); [lia | ].
  unfold Rm, deflate_globals. Intros.
  forward_call (gv, Tsh, vt, z1, Some L, rm_ib rf ibp, rf_O rf, Some (rm_ob rf obp (Zrepeat Vundef (rf_nf rf))),
                4, Ers, Ers, true, true).
  { rewrite rm8_iopt, rm8_islive by auto. simpl head_opt6. cancel. }
  { unfold z1, rm8_z, rm_ib, rm_ob, in_ok, out_ok, in_ptr, out_ptr; simpl.
    rewrite !isptr_offset_val_zero by auto.
    assert (Bo: bytes_ok (rf_O rf)).
    { unfold bytes in BO. unfold bytes_ok. eapply Forall_impl; [| exact BO]. simpl. intros; rep_lia. }
    unfold COMP_MAX in HO.
    repeat match goal with |- _ /\ _ => split end; auto with share; try rep_lia.
    all: first [ rewrite Zlength_byte_vals; reflexivity
               | rewrite Z.add_0_l, sublist_same by (rewrite ?Zlength_byte_vals; lia); reflexivity
               | rewrite Zlength_Zrepeat by lia; reflexivity
               | unfold hd6_ok; rewrite rm8_islive by auto; intros _ _; exact Hpass ]. }
  Intros vret. destruct vret as [[[r z'] st'] ow]. cbn [fst snd] in *.
  match goal with Hx: inflate_rel _ _ _ _ _ _ _ _ _ _ _ |- _ => rename Hx into Hrel end.
  destruct Hrel as [(Bad & _) | (_ & L0 & o & res & winp & EL & Eo & Hrun & Hsnx & Er & Eow & Ez & Hw & Est)].
  { exfalso. unfold inflate_bad in Bad. rewrite rm8_islive in Bad by auto.
    destruct Bad as [B | [B | (B & _)]]; discriminate. }
  injection EL as <-. injection Eo as <-. subst r ow z' st'.
  pose proof (Hres res Hrun) as Rok.
  pose proof (rm8_inp _ _ _ _ _ Hrun) as Ei.
  pose proof (rmh_run_head _ _ _ _ _ Hrun) as Eh.
  set (L1 := Live (l_sp L) winp (m_s (r_m res)) (m_h (r_m res)) (l_headp L) (l_hsh L) (l_xb L) (l_nb L) (l_cb L)).
  pose proof (rmh8_call1 rf ibp obp (Zrepeat Vundef (rf_nf rf)) z1 res L1 Ei Rok eq_refl eq_refl) as C1.
  rewrite !rm8_iopt, !rm8_islive by auto. simpl head_opt6. unfold bufs_opt. rewrite rm8_out_opt.
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
  eapply semax_pre; [ | apply (K ibp obp (r_ret res)
                                  (z_after z1 (rm_ib rf ibp) (rm_ob rf obp (Zrepeat Vundef (rf_nf rf))) res) L1
                                  (m_ow (r_m res)) (Zrepeat Vundef (rf_nf rf))) ].
  unfold AH16, Rm, deflate_globals.
  sep_apply rm8_comp_fold. sep_apply rm8_fold.
  entailer!.
  rewrite Zlength_Zrepeat by lia. split; [reflexivity | ]. unfold L1; cbn [S5.l_s]. rewrite Eh; assumption.
  unfold L1; cbn [S5.l_xb S5.l_nb S5.l_cb]. apply derives_refl.
Qed.
