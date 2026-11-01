(* Law inflate_dict, main, inflate half: the stores into s, r = inflate(&s, flush), `if (r == Z_MEM_ERROR) return 0;`, made, pos += ain - s.avail_in (ITMainInfKit.v it_call_stmt); then seg_L2 (given). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessRef Zlib.proof.adler32.HarnessBytes
               Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.inflate_common.HarnessLib.
Require Import Zlib.proof.harness.inflate_common.DRefSpec.
Require Import Zlib.proof.harness.inflate_dict.ITLawCS Zlib.proof.harness.inflate_dict.ITGlobals
               Zlib.proof.harness.inflate_dict.ITFacts Zlib.proof.harness.inflate_dict.ITMainKit
               Zlib.proof.harness.inflate_dict.ITMainInfKit.
Require Import Zlib.harness.x_inflate_dict.code.
Require Import Zlib.proof.crc32.Spec.
Require Zlib.proof.uncompr.URunRet Zlib.proof.uncompr.URunFrame.
Local Open Scope logic.

(* the call's buffers: the objects ib / ob (law's CS) as inflate()'s InBuf / OutBuf (inflate unit's CS) *)
Lemma itcall_bufs_pre L ibp obp ain aout (ci co: list val):
  Zlength co = aout ->
  data_at Ews (tarray tuchar ain) ci ibp * malloc_token Ews (tarray tuchar ain) ibp *
  data_at Ews (tarray tuchar aout) co obp * malloc_token Ews (tarray tuchar aout) obp
  |-- bufs_opt (Some L) (InBuf Ews ibp 0 ain ci) (Some (OutBuf Ews obp 0 aout co)) [] true true.
Proof.
  intros Hc. unfold bufs_opt.
  rewrite <- (it_bytes_inflate_cs Ews ain ci ibp), <- (it_tok_inflate_cs Ews ain ibp),
          <- (it_bytes_inflate_cs Ews aout co obp), <- (it_tok_inflate_cs Ews aout obp).
  assert (Eo: sublist 0 0 co ++ byte_vals [] ++ sublist (0 + Zlength (@nil Z)) aout co = co).
  { rewrite sublist_nil. simpl. rewrite sublist_same by lia. reflexivity. }
  unfold in_rep, out_opt, out_rep, in_tok, out_tok; rewrite Eo; cancel.
Qed.

Lemma itcall_bufs_post L ibp obp ain aout (ci co: list val) (ow: list Z):
  bufs_opt (Some L) (InBuf Ews ibp 0 ain ci) (Some (OutBuf Ews obp 0 aout co)) ow true true
  |-- data_at Ews (tarray tuchar ain) ci ibp * malloc_token Ews (tarray tuchar ain) ibp *
      data_at Ews (tarray tuchar aout) (sublist 0 0 co ++ byte_vals ow ++ sublist (0 + Zlength ow) aout co) obp *
      malloc_token Ews (tarray tuchar aout) obp.
Proof.
  unfold bufs_opt, in_rep, out_opt, out_rep, in_tok, out_tok.
  rewrite (it_bytes_inflate_cs Ews ain ci ibp), (it_tok_inflate_cs Ews ain ibp),
          (it_bytes_inflate_cs Ews aout _ obp), (it_tok_inflate_cs Ews aout obp). cancel.
Qed.

Lemma itcall_in_ptr sh p n c: isptr p -> in_ptr (InBuf sh p 0 n c) 0 = p.
Proof. intros P. destruct p; try contradiction. simpl. rewrite Ptrofs.add_zero. reflexivity. Qed.
Lemma itcall_out_ptr sh p n c: isptr p -> out_ptr (OutBuf sh p 0 n c) 0 = p.
Proof. intros P. destruct p; try contradiction. simpl. rewrite Ptrofs.add_zero. reflexivity. Qed.

(* inflate() keeps i_head (whether the application gave a gz_header): run2 from any mode of a live stream *)
Lemma itcall_run2_head flush fx dx m0 res:
  Zlib.proof.inflate.Model.HEAD <= i_mode (m_s m0) <= Zlib.proof.inflate.Model.SYNC ->
  Zlib.proof.inflate.Model2.run2 flush fx dx m0 res -> i_head (m_s (r_m res)) = i_head (m_s m0).
Proof.
  intros Hm Hrun.
  destruct (Z_le_gt_dec (i_mode (m_s m0)) Zlib.proof.inflate.Model.BAD) as [Hv | Hv].
  - apply (Zlib.proof.uncompr.URunFrame.run2_frame flush fx dx m0 res); [unfold Zlib.proof.uncompr.URunFrame.vmode; lia | exact Hrun].
  - destruct Hrun as (o & L & R).
    assert (E: exists r, Zlib.proof.inflate.Model2.stepf2 flush fx dx m0 = IRet r m0).
    { unfold Zlib.proof.inflate.Model2.stepf2, Zlib.proof.inflate.Model2.step2, m_mode.
      unfold Zlib.proof.inflate.Model.HEAD, Zlib.proof.inflate.Model.SYNC, Zlib.proof.inflate.Model.BAD in *.
      assert (i_mode (m_s m0) = 16210 \/ i_mode (m_s m0) = 16211) as [-> | ->] by lia;
        cbv [Z.eqb Zlib.proof.inflate.Model.HEAD]; simpl; eexists; reflexivity. }
    destruct E as [r E].
    inversion L; subst; rewrite E in *; try discriminate.
    match goal with Hx: IRet _ _ = IRet _ _ |- _ => injection Hx as <- <- end.
    simpl in R. subst res. reflexivity.
Qed.

Lemma itcall_rel_head flush strmp z L ib inp o r z' L' ow:
  live_ok L -> inflate_rel flush strmp z (Some L) ib inp (Some o) r z' (Some L') ow ->
  i_head (l_s L') = i_head (l_s L).
Proof.
  intros LV [(_ & _ & _ & E & _) | (_ & L0 & o0 & res & winp & E0 & _ & Hrun & _ & _ & _ & _ & _ & E)].
  - injection E as ->. reflexivity.
  - injection E0 as E0. subst L0. injection E as E. subst L'. simpl.
    assert (Hm: Zlib.proof.inflate.Model.HEAD <= i_mode (m_s (m_init z L inp)) <= Zlib.proof.inflate.Model.SYNC).
    { destruct LV as (_ & SW & _). pose proof (sw_mode _ SW) as M.
      unfold m_init. simpl. destruct (Z.eqb_spec (i_mode (l_s L)) Zlib.proof.inflate.Model.TYPE); simpl; auto.
      unfold Zlib.proof.inflate.Model.HEAD, Zlib.proof.inflate.Model.SYNC, Zlib.proof.inflate.Model.TYPEDO; lia. }
    rewrite (itcall_run2_head _ _ _ _ _ Hm Hrun).
    unfold m_init. simpl. destruct (_ =? _); reflexivity.
Qed.

Lemma it_call {Espec: OracleKind} : it_call_stmt.
Proof.
  intros I gv vw vs vosn vdl dictp badp datap srcp G wsel dcont scont Fr Inv Brk
         pos lim opos dset z L aout flush ibp obp q bs GL BF K.
  destruct BF as (HI & Hlim & Haout & Hbsl & Hbsb & Hfl & Pib & Pob & Pq).
  pose proof GL as GL'. destruct GL' as (CF & Gok & Hws & Hdc & Hdcs & Hsc & Hscs & Hdb & Hdab & Hsb & _).
  pose proof (it_range I CF _ _ _ _ _ _ _ HI) as (_ & Hpos & Hopos).
  assert (Hsl: Zlength (it_src G) <= 2 ^ 19) by (destruct Gok as (_ & _ & _ & _ & ? & _); auto).
  assert (Hdl: Zlength (it_data G) <= 2 ^ 18) by (destruct Gok as (_ & _ & _ & ? & _); auto).
  unfold it_buf. rewrite it_istream_unfold. Intros.
  assert_PROP (isptr vs) as Pvs by entailer!.
  unfold seg_L1, Delta_m, Gmain_k, POST_m. simplify_func_tycontext. abbreviate_semax.
  forward. forward. forward. forward.
  set (sub := sublist pos lim (it_src G)) in *.
  rewrite <- it_tup_set.
  set (ib := InBuf Ews ibp 0 (lim - pos) (bytes_rep sub)).
  set (o := OutBuf Ews obp 0 aout (bytes_rep bs)).
  set (z1 := it_set_zf_call z (in_ptr ib 0) (lim - pos) (out_ptr o 0) aout).
  replace (it_set_zf_call z ibp (lim - pos) obp aout) with z1
    by (unfold z1, ib, o; rewrite itcall_in_ptr, itcall_out_ptr; auto).
  assert (Z1ok: zf_ok z1).
  { destruct H as (? & ? & ? & ? & ? & ?). unfold z1, it_set_zf_call, zf_ok; simpl. rep_lia. }
  assert (Hsub: Zlength sub = lim - pos) by (unfold sub; rewrite Zlength_sublist; lia).
  sep_apply (it_istream_fold gv Tsh vs z1 L); auto.
  sep_apply (itcall_bufs_pre L ibp obp (lim - pos) aout (bytes_rep sub) (bytes_rep bs)).
  { rewrite Zlength_bytes_rep; auto. }
  fold ib o.
  assert (Hhd: i_head (l_s L) = false) by (eapply (it_head I CF); eauto).
  forward_call (gv, Tsh, vs, z1, Some L, ib, sub, Some o, flush, Ers, Ers, true, true).
  { rewrite it_istream_opt, it_is_live by auto. simpl head_opt. unfold head_mem; rewrite Hhd. cancel. }
  { unfold z1, it_set_zf_call; simpl zf_ai; simpl zf_ao; simpl zf_no; simpl zf_ni.
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
  destruct (it_inflate I CF G pos opos dset z L vs flush lim ib sub o aout r z' st' ow HI H1 H
              ltac:(destruct vs; try contradiction; discriminate) Hlim Haout Hfl
              ltac:(discriminate) eq_refl Hrel) as [L' [Est CP]].
  subst st'.
  pose proof (itcall_rel_head _ _ _ _ _ _ _ _ _ _ _ H1 Hrel) as Hhd'. rewrite Hhd in Hhd'. clear Hrel.
  rewrite it_istream_opt, !it_is_live by auto.
  pose proof (itcall_bufs_post L ibp obp (lim - pos) aout (bytes_rep sub) (bytes_rep bs) ow) as BP.
  fold ib o in BP. sep_apply BP. clear BP.
  forward_if.
  { forward. Exists (Int.repr 0). sep_apply it_istream_to_undef. entailer!. }
  assert (Hne: r <> Z_MEM_ERROR) by (intro E; subst r; apply H2; reflexivity).
  specialize (CP Hne).
  pose proof CP as CP'. unfold it_post in CP'. cbv zeta in CP'.
  destruct CP' as (Hai & Hao & Hlow & Hob & _).
  simpl head_opt. unfold head_mem; rewrite Hhd'.
  rewrite it_istream_unfold. Intros.
  forward. forward. forward. forward.
  rewrite sub_repr, add_repr, sub_repr.
  set (cont := sublist 0 0 (bytes_rep bs) ++ byte_vals ow ++ sublist (0 + Zlength ow) aout (bytes_rep bs)).
  assert (Hcont: Zlength cont = aout).
  { unfold cont. rewrite sublist_nil, !Zlength_app, Zlength_sublist; rewrite ?Zlength_bytes_rep; try lia.
    unfold byte_vals; rewrite ?Zlength_map, ?Zlength_nil; lia. }
  assert (Hcs: sublist 0 (aout - zf_ao z') cont = bytes_rep ow).
  { rewrite <- Hlow. unfold cont. rewrite sublist_nil. simpl app. rewrite sublist_app1; rewrite ?Zlength_map; try lia.
    rewrite sublist_same; rewrite ?Zlength_map; auto. all: unfold byte_vals; rewrite ?Zlength_map; lia. }
  assert (MF: it_mid_facts I G pos lim opos dset aout ibp obp q bs r (pos + (lim - pos - zf_ai z'))
                (aout - zf_ao z') z' L' ow cont).
  { unfold it_mid_facts. repeat match goal with |- _ /\ _ => split end;
      first [assumption | reflexivity | rep_lia]. }
  sep_apply (it_istream_fold gv Tsh vs z' L'); auto.
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
  eapply semax_pre; [ | apply (K r _ _ z' L' ow cont MF)].
  unfold it_mid. entailer!.
Qed.
