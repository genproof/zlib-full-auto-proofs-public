(* Law inflate_codes, main: the branch `op >= 24` of the loop (inflate(&s, flush) on ib/ob or Z_NULL, and its checks). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessRef Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.inflate_common.HarnessLib.
Require Import Zlib.proof.harness.inflate_codes.LawCS Zlib.proof.harness.inflate_codes.Globals
               Zlib.proof.harness.inflate_codes.Facts Zlib.proof.harness.inflate_codes.MainKit.
Require Import Zlib.harness.x_inflate_codes.code.

Require Import Zlib.proof.harness.inflate_codes.MainInfKit Zlib.proof.harness.inflate_codes.MainInfA
               Zlib.proof.harness.inflate_codes.MainInfB Zlib.proof.harness.inflate_codes.MainInfC.

Lemma seg_inflate_ok {Espec: OracleKind} I gv vs vo vosn vb vdl w srcp src pos final indict z L
    ain aout flush innull outnull stop ibp obp bs Fr (Post: ret_assert) :
  br_facts I w srcp src pos final indict z L ain aout flush innull outnull stop ibp obp bs ->
  semax Delta_m
    (br_pre gv vs vo vosn vb vdl w srcp src pos final indict z L ain aout flush innull outnull stop ibp obp bs Fr)
    seg_inflate
    (overridePost (br_post I gv vs vo vosn vb vdl w srcp src pos ain aout stop ibp obp Fr) Post).
Proof.
  intros BF.
  destruct BF as (CF & HI & Hwok & Hw & Hpos & Hain & Hpa & Hsrc & Hsb & Haout & Hbsl & Hbsb & Hfl & Hin & Hout & Hst & Psrc & Pib & Pob).
  unfold br_pre.
  rewrite mi_istream_unfold. Intros.
  assert_PROP (isptr vs) as Pvs by entailer!.
  unfold seg_inflate.
  ifpostv _t'35 (if innull =? 0 then nullval else ibp).
  { forward. entailer!; eqz. }
  { forward. entailer!; eqz. }
  forward.
  forward.
  ifpostv _t'36 (if outnull =? 0 then nullval else obp).
  { forward. entailer!; eqz. }
  { forward. entailer!; eqz. }
  forward.
  forward.
  set (sub := sublist pos (pos + ain) src) in *.
  rewrite <- (mi_in_ptr innull ibp ain (bytes_rep sub)) by auto.
  rewrite <- (mi_ob_ptr outnull obp aout (bytes_rep bs)) by auto.
  rewrite <- mi_tup_set.
  set (ib := mi_ib innull ibp ain (bytes_rep sub)).
  set (ob := mi_ob outnull obp aout (bytes_rep bs)).
  set (inp := if innull =? 0 then [] else sub).
  set (z1 := set_zf_call z (in_ptr ib 0) ain (ob_ptr ob) aout).
  assert (Z1ok: zf_ok z1).
  { destruct H as (? & ? & ? & ? & ? & ?). unfold z1, set_zf_call, zf_ok; simpl. rep_lia. }
  assert (Hsub: Zlength sub = ain) by (unfold sub; rewrite Zlength_sublist; lia).
  sep_apply (mi_istream_fold gv Tsh vs z1 L); auto.
  sep_apply (mi_bufs_pre L innull outnull ibp obp ain aout (bytes_rep sub) (bytes_rep bs)).
  { rewrite Zlength_bytes_rep; auto. }
  fold ib ob.
  assert (Hhd: i_head (l_s L) = false) by (eapply (cf_head I CF); eauto).
  forward_call (gv, Tsh, vs, z1, Some L, ib, inp, ob, flush, Ers, Ers, true, true).
  { rewrite mi_istream_opt, mi_is_live by auto. simpl head_opt. unfold head_mem; rewrite Hhd. cancel. }
  { unfold z1, set_zf_call; simpl zf_ai; simpl zf_ao; simpl zf_no.
    unfold ib, ob, inp, mi_ib, mi_ob.
    assert (bytes_ok sub) by (apply Forall_sublist; exact Hsb).
    destruct (innull =? 0), (outnull =? 0); simpl; repeat match goal with |- _ /\ _ => split end; auto with share; try rep_lia;
    rewrite ?Zlength_bytes_rep; try rep_lia;
    try (rewrite Hsub, sublist_same by (rewrite ?Zlength_bytes_rep; lia); reflexivity). }
  Intros vret. destruct vret as [[[r z'] st'] ow]. simpl fst; simpl snd.
  match goal with H: inflate_rel _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H into Hrel end.
  assert (Hcin: call_in_ok src pos ain ib inp).
  { unfold call_in_ok, ib, inp, mi_ib. destruct (innull =? 0); [left; auto | right; split; [discriminate | auto]]. }
  destruct (cf_inflate I CF w src pos final indict z L vs flush ib inp ob ain aout r z' st' ow
              HI H1 H ltac:(destruct vs; try contradiction; discriminate) Hpos Hain Hpa Hsrc Hsb Haout Hfl Hcin Hrel)
    as [L' [Est IP]].
  subst st'. clear Hrel.
  rewrite mi_istream_opt, !mi_is_live by auto.
  cbv beta zeta delta [inflate_post] in IP.
  destruct IP as (Hcode & Hai & Hao & Hbad & Hok & Hbuf & Hdata & Hfin & Hnd & HI').
  assert (Hhd': i_head (l_s L') = false) by (eapply (cf_head I CF); exact HI').
  simpl head_opt. unfold head_mem at 1; rewrite Hhd'.
  pose proof (mi_bufs_post L innull outnull ibp obp ain aout (bytes_rep sub) (bytes_rep bs) ow) as BP.
  fold ib ob in BP. sep_apply BP. clear BP. Intros cont.
  rewrite mi_istream_unfold. Intros.
  unfold ib, ob in Hbad, Hfin, HI'. rewrite mi_badptr in Hbad, Hfin, HI'.
  assert (MF: mi_facts w src pos final indict ain aout flush innull outnull r z').
  { destruct (cf_range I CF _ _ _ _ _ _ _ HI) as [Hfr Hidr].
    exact (conj Hw (conj Hpos (conj Hain (conj Hpa (conj Hsrc (conj Hsb (conj Haout (conj Hfl (conj Hin (conj Hout (conj Hfr (conj Hidr (conj H2 (conj Hcode (conj Hai (conj Hao (conj Hbad (conj Hok (conj Hbuf (conj Hdata (conj Hfin Hnd))))))))))))))))))))). }
  match goal with |- semax _ _ ?c _ => change c with seg_inf_rest end.
  eapply semax_pre; [ | apply (mi_A_ok gv vs vo vosn vb vdl w srcp src pos final indict ain aout flush innull outnull
                                stop ibp obp r z' (l_sp L')
     (data_at Ews (tarray tuchar ain) (bytes_rep sub) ibp * malloc_token Ews (tarray tuchar ain) ibp *
      data_at Ews (tarray tuchar aout) cont obp * malloc_token Ews (tarray tuchar aout) obp *
      state_mem gv vs L' * tables_rep Ers gv * Spec.crc_table_at Ers gv * mem_mgr gv * zfuncs gv *
      malloc_token Ews (tarray tuchar (Zlength src)) srcp * Fr)%logic _ MF Psrc) ].
  { unfold mi_pre_A. entailer!. }
  rewrite seg_inf_BC_eq.
  eapply semax_seq; [eapply mi_B_ok; [exact MF | exact Psrc] | ].
  unfold POSTCONDITION, abbreviate. destruct Post as [Pn Pb Pc Pr]; unfold overridePost; simpl RA_normal.
  match goal with |- semax _ _ _ (normal_ret_assert ?X) =>
    eapply semax_post_flipped';
    [ exact (mi_C_ok gv vs vo vosn vb vdl w srcp src pos final indict ain aout flush innull outnull stop ibp obp r z'
               (l_sp L') _ (normal_ret_assert X) MF) | ] end.
  unfold br_post, mi_post_C.
  Exists (pos + (ain - zf_ai z')) (final_after (mi_bad innull outnull ain) final r)
         (indict_after (mi_bad innull outnull ain) indict r) z' L' cont.
  rewrite mi_istream_unfold. entailer!.
Qed.
