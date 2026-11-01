(* Law inflate_check, main: from the stores into s to the update of rc (IKMainKit.v seg_L1 up to seg_L2):
   s.next_in = ib; s.avail_in = ain; s.next_out = ob; s.avail_out = aout; r = inflate(&s, flush);
   `if (r == Z_MEM_ERROR) return 0;` used, made, pos += used, tout += made, ra = ref_adler32(ra, ob, made),
   rc = ref_crc32(rc, ob, made); then seg_L2 (given), from the state ik_mid for the new pos' and out' (out
   followed by the bytes made), with what check_facts' ck_inflate gives. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessRef Zlib.proof.adler32.MainLib.
Require Zlib.proof.crc32.HarnessRef.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.inflate_common.HarnessLib Zlib.proof.harness.inflate_common.HarnessLe32.
Require Import Zlib.proof.harness.inflate_check.IKLawCS Zlib.proof.harness.inflate_check.IKGlobals
               Zlib.proof.harness.inflate_check.IKFacts.
Require Import Zlib.harness.x_inflate_check.code.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.harness.inflate_check.IKMainKit.
Require Zlib.proof.uncompr.URunRet Zlib.proof.crc32.Combine.
Local Open Scope logic.

(* the call's buffers: the objects ib / ob (law's CS) as inflate()'s InBuf / OutBuf (inflate unit's CS) *)
Lemma ikc_bufs_pre L ibp obp ain aout (ci co: list val):
  Zlength co = aout ->
  data_at Ews (tarray tuchar ain) ci ibp * malloc_token Ews (tarray tuchar ain) ibp *
  data_at Ews (tarray tuchar aout) co obp * malloc_token Ews (tarray tuchar aout) obp
  |-- bufs_opt (Some L) (InBuf Ews ibp 0 ain ci) (Some (OutBuf Ews obp 0 aout co)) [] true true.
Proof.
  intros Hc. unfold bufs_opt.
  rewrite <- (ik_bytes_inflate_cs Ews ain ci ibp), <- (ik_tok_inflate_cs Ews ain ibp),
          <- (ik_bytes_inflate_cs Ews aout co obp), <- (ik_tok_inflate_cs Ews aout obp).
  assert (Eo: sublist 0 0 co ++ byte_vals [] ++ sublist (0 + Zlength (@nil Z)) aout co = co).
  { rewrite sublist_nil. simpl. rewrite sublist_same by lia. reflexivity. }
  unfold in_rep, out_opt, out_rep, in_tok, out_tok; rewrite Eo; cancel.
Qed.

Lemma ikc_bufs_post L ibp obp ain aout (ci co: list val) (ow: list Z):
  bufs_opt (Some L) (InBuf Ews ibp 0 ain ci) (Some (OutBuf Ews obp 0 aout co)) ow true true
  |-- data_at Ews (tarray tuchar ain) ci ibp * malloc_token Ews (tarray tuchar ain) ibp *
      data_at Ews (tarray tuchar aout) (sublist 0 0 co ++ byte_vals ow ++ sublist (0 + Zlength ow) aout co) obp *
      malloc_token Ews (tarray tuchar aout) obp.
Proof.
  unfold bufs_opt, in_rep, out_opt, out_rep, in_tok, out_tok.
  rewrite (ik_bytes_inflate_cs Ews ain ci ibp), (ik_tok_inflate_cs Ews ain ibp),
          (ik_bytes_inflate_cs Ews aout _ obp), (ik_tok_inflate_cs Ews aout obp). cancel.
Qed.

Lemma ikc_in_ptr sh p n c: isptr p -> in_ptr (InBuf sh p 0 n c) 0 = p.
Proof. intros P. destruct p; try contradiction. simpl. rewrite Ptrofs.add_zero. reflexivity. Qed.
Lemma ikc_out_ptr sh p n c: isptr p -> out_ptr (OutBuf sh p 0 n c) 0 = p.
Proof. intros P. destruct p; try contradiction. simpl. rewrite Ptrofs.add_zero. reflexivity. Qed.

(* the continuation (call_ok's second hypothesis), named to keep goals readable *)
Definition ikc_K {Espec: OracleKind} I gv vs vosn w srcp src adler0 Fr (Inv: environ -> mpred) pos
    ain aout stop ibp obp q bs : Prop :=
  forall pos' out' r z' L' (cont: list val),
     ik_mid_facts w srcp src adler0 pos' out' r z' -> I w src pos' out' z' L' -> live_ok L' ->
     Zlength cont = aout ->
     semax Delta_m
       (ik_mid gv vs vosn w srcp src adler0 pos' out' r stop ibp obp z' (l_sp L')
          (state_mem gv vs L' * mem_mgr gv * zfuncs gv * tables_rep Ers gv * crc_table_at Ers gv *
           malloc_token Ews (tarray tuchar (Zlength src)) srcp *
           malloc_token Ews (tarray tuchar ain) ibp *
           data_at Ews (tarray tuchar ain) (bytes_rep (sublist pos (pos + ain) src)) ibp *
           malloc_token Ews (tarray tuchar aout) obp * data_at Ews (tarray tuchar aout) cont obp *
           data_at Tsh (tptr tuchar) q vosn *
           malloc_token Ews (tarray tuchar aout) q * data_at Ews (tarray tuchar aout) (bytes_rep bs) q * Fr))
       seg_L2 (ik_PL Inv).

Lemma call_core {Espec: OracleKind} I gv vs vosn w srcp src adler0 Fr (Inv: environ -> mpred) pos out z L
    ain aout flush stop ibp obp q bs :
  ik_buf_facts I w srcp src adler0 pos out z L ain aout flush stop ibp obp q bs ->
  ikc_K I gv vs vosn w srcp src adler0 Fr Inv pos ain aout stop ibp obp q bs ->
  semax Delta_m (ik_buf gv vs vosn w srcp src adler0 Fr pos out z L ain aout flush stop ibp obp q bs)
    seg_L1 (ik_PL Inv).
Proof.
  intros BF K.
  destruct BF as (G & HI & Hpos & Hout & Hraw & Hain & Hpa & Haout & Hbsl & Hbsb & Hfl & Hst & Pib & Pob & Pq).
  pose proof G as G'. destruct G' as (CF & Hwok & Hw & Hsrc & Hsb & Psrc & Had0).
  unfold ik_buf. rewrite ik_istream_unfold. Intros.
  assert_PROP (isptr vs) as Pvs by entailer!.
  unfold seg_L1, Delta_m, Gmain_k, POST_m. simplify_func_tycontext. abbreviate_semax.
  forward. forward. forward. forward.
  set (sub := sublist pos (pos + ain) src) in *.
  rewrite <- ik_tup_set.
  set (ib := InBuf Ews ibp 0 ain (bytes_rep sub)).
  set (o := OutBuf Ews obp 0 aout (bytes_rep bs)).
  set (z1 := ik_set_zf_call z (in_ptr ib 0) ain (out_ptr o 0) aout).
  replace (ik_set_zf_call z ibp ain obp aout) with z1 by (unfold z1, ib, o; rewrite ikc_in_ptr, ikc_out_ptr; auto).
  assert (Z1ok: zf_ok z1).
  { destruct H as (? & ? & ? & ? & ? & ?). unfold z1, ik_set_zf_call, zf_ok; simpl. rep_lia. }
  assert (Hsub: Zlength sub = ain) by (unfold sub; rewrite Zlength_sublist; lia).
  sep_apply (ik_istream_fold gv Tsh vs z1 L); auto.
  sep_apply (ikc_bufs_pre L ibp obp ain aout (bytes_rep sub) (bytes_rep bs)).
  { rewrite Zlength_bytes_rep; auto. }
  fold ib o.
  assert (Hhd: i_head (l_s L) = false) by (eapply (ck_head I CF); eauto).
  forward_call (gv, Tsh, vs, z1, Some L, ib, sub, Some o, flush, Ers, Ers, true, true).
  { rewrite ik_istream_opt, ik_is_live by auto. simpl head_opt. unfold head_mem; rewrite Hhd. cancel. }
  { unfold z1, ik_set_zf_call; simpl zf_ai; simpl zf_ao; simpl zf_no; simpl zf_ni.
    unfold ib, o, in_tok_ok, out_tok_ok, in_ok, out_ok.
    assert (bytes_ok sub) by (apply Forall_sublist; exact Hsb).
    rewrite ?Zlength_bytes_rep.
    repeat match goal with |- _ /\ _ => split end; auto with share; try rep_lia; try discriminate.
    rewrite Z.add_0_l, sublist_same; [reflexivity | auto | rewrite Zlength_bytes_rep; auto].
  }
  Intros vret. destruct vret as [[[r z'] st'] ow]. simpl fst in *; simpl snd in *.
  match goal with Hx: inflate_rel _ _ _ _ _ _ _ _ _ _ _ |- _ => rename Hx into Hrel end.
  assert (Hr: -5 <= r <= 2).
  { destruct Hrel as [[_ [-> _]] | [_ [L0 [o0 [res [winp [_ [_ [Hrun [_ [-> _]]]]]]]]]]].
    - unfold Z_STREAM_ERROR; lia.
    - eapply Zlib.proof.uncompr.URunRet.run2_ret; [| exact Hrun]. simpl; unfold Z_OK; lia. }
  destruct (ck_inflate I CF w src pos out z L vs flush ib sub o ain aout r z' st' ow HI H1 H
              ltac:(destruct vs; try contradiction; discriminate) Hpos Hain Hpa Hsrc Hsb Haout Hfl
              ltac:(discriminate) eq_refl Hrel) as [L' [Est CP]].
  subst st'. clear Hrel.
  rewrite ik_istream_opt, !ik_is_live by auto.
  pose proof (ikc_bufs_post L ibp obp ain aout (bytes_rep sub) (bytes_rep bs) ow) as BP.
  fold ib o in BP. sep_apply BP. clear BP.
  forward_if.
  { forward. Exists (Int.repr 0). sep_apply ik_istream_to_undef. entailer!. }
  assert (Hne: r <> Z_MEM_ERROR) by (intro E; subst r; apply H2; reflexivity).
  specialize (CP Hne). unfold check_post in CP. cbv zeta in CP.
  destruct CP as (Hai & Hao & Hlow & Hob & Hraw' & Hhdr & Hchk & Hend & HI').
  assert (Hhd': i_head (l_s L') = false) by (eapply (ck_head I CF); exact HI').
  simpl head_opt. unfold head_mem; rewrite Hhd'.
  rewrite ik_istream_unfold. Intros.
  set (cont := sublist 0 0 (bytes_rep bs) ++ byte_vals ow ++ sublist (0 + Zlength ow) aout (bytes_rep bs)).
  assert (Hcont: Zlength cont = aout).
  { unfold cont. rewrite sublist_nil, !Zlength_app, Zlength_sublist; rewrite ?Zlength_bytes_rep; try lia.
    unfold byte_vals; rewrite ?Zlength_map, ?Zlength_nil; lia. }
  assert (Hcs: sublist 0 (0 + Zlength ow) cont = bytes_rep ow).
  { unfold cont. rewrite sublist_nil. simpl app. rewrite sublist_app1; rewrite ?Zlength_map; try lia.
    rewrite sublist_same; rewrite ?Zlength_map; auto. all: unfold byte_vals; rewrite ?Zlength_map; lia. }
  forward. forward. forward. forward. forward. forward.
  rewrite !sub_repr, add_repr.
  rewrite (Int.unsigned_repr (aout - zf_ao z')) by rep_lia.
  rewrite add64_repr, <- Hlow.
  replace (Zlength out + Zlength ow) with (Zlength (out ++ ow)) by (rewrite Zlength_app; lia).
  assert (Hv1: adler_valid 1) by (cbv; repeat split; congruence).
  pose proof (ref_adler32_valid 1 out Hv1) as Hra. destruct Hra as [Hra _].
  assert (Hcb: cbuf_ok false obp Ews obp 0 aout (Zlength ow) cont ow).
  { unfold cbuf_ok. split; [destruct obp; try contradiction; simpl; rewrite Ptrofs.add_zero; reflexivity |].
    repeat split; auto; try lia. }
  rewrite <- (ik_bytes_adler_cs Ews aout cont obp).
  forward_call (ref_adler32 1 out, obp, Ews, obp, 0, aout, cont, Zlength ow, ow).
  rewrite (ref_adler32_app 1 out ow Hv1).
  pose proof (Zlib.proof.crc32.Combine.ref_crc32_range 0 out Hout) as Hrc.
  forward_call (ref_crc32 0 out, obp, Ews, obp, 0, aout, cont, Zlength ow, ow).
  { unfold Zlib.proof.crc32.GF2.is32 in Hrc. rep_lia. }
  rewrite (Zlib.proof.crc32.Combine.ref_crc32_app 0 out ow Hout).
  rewrite ?ik_bytes_crc_cs, ?ik_bytes_adler_cs.
  assert (MF: ik_mid_facts w srcp src adler0 (pos + (ain - zf_ai z')) (out ++ ow) r z').
  { unfold ik_mid_facts.
    refine (conj Hw (conj _ (conj Hsrc (conj Hsb (conj Psrc (conj Had0 (conj _ (conj H3 (conj _ (conj _
              (conj Hhdr (conj Hchk Hend))))))))))));
    [lia | apply Forall_app; auto | rep_lia | intros Hw0; rewrite Hraw'; auto]. }
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
  eapply semax_pre; [ | apply (K (pos + (ain - zf_ai z')) (out ++ ow) r z' L' cont MF HI' H4 Hcont)].
  unfold ik_mid. entailer!.
Qed.

Lemma call_ok {Espec: OracleKind} I gv vs vosn w srcp src adler0 Fr (Inv: environ -> mpred) pos out z L
    ain aout flush stop ibp obp q bs :
  ik_buf_facts I w srcp src adler0 pos out z L ain aout flush stop ibp obp q bs ->
  (forall pos' out' r z' L' cont,
     ik_mid_facts w srcp src adler0 pos' out' r z' -> I w src pos' out' z' L' -> live_ok L' ->
     Zlength cont = aout ->
     semax Delta_m
       (ik_mid gv vs vosn w srcp src adler0 pos' out' r stop ibp obp z' (l_sp L')
          (state_mem gv vs L' * mem_mgr gv * zfuncs gv * tables_rep Ers gv * crc_table_at Ers gv *
           malloc_token Ews (tarray tuchar (Zlength src)) srcp *
           malloc_token Ews (tarray tuchar ain) ibp *
           data_at Ews (tarray tuchar ain) (bytes_rep (sublist pos (pos + ain) src)) ibp *
           malloc_token Ews (tarray tuchar aout) obp * data_at Ews (tarray tuchar aout) cont obp *
           data_at Tsh (tptr tuchar) q vosn *
           malloc_token Ews (tarray tuchar aout) q * data_at Ews (tarray tuchar aout) (bytes_rep bs) q * Fr))
       seg_L2 (ik_PL Inv)) ->
  semax Delta_m (ik_buf gv vs vosn w srcp src adler0 Fr pos out z L ain aout flush stop ibp obp q bs)
    seg_L1 (ik_PL Inv).
Proof. intros BF K. apply (call_core I gv vs vosn w srcp src adler0 Fr Inv pos out z L ain aout flush stop ibp obp q bs BF K). Qed.
