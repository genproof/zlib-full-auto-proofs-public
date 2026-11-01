(* Law inflate_header, main: the loop body from the stores into s to the update of pos (IHMainKit.v segL10,
   positions L10 .. L17): s.next_in = ib; s.avail_in = ain; s.next_out = ob; s.avail_out = aout;
   r = inflate(&s, flush) (with head_mem: the stream holds h); `if (r == Z_MEM_ERROR) return 0;`;
   gp_assert(r == Z_OK || r == Z_BUF_ERROR || r == Z_STREAM_END || r == Z_DATA_ERROR);
   pos += ain - s.avail_in; then segL18 (given), with what ihf_inflate (IHFacts.v) gives.
   As inflate_check/IKMainCall.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.crc32.HarnessRef.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.inflate_common.HarnessLib.
Require Import Zlib.proof.harness.inflate_header.IHLawCS Zlib.proof.harness.inflate_header.IHGlobals
               Zlib.proof.harness.inflate_header.IHHelpers Zlib.proof.harness.inflate_header.IHFacts
               Zlib.proof.harness.inflate_header.IHMainStmt.
Require Import Zlib.harness.x_inflate_header.code.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.harness.inflate_header.IHMainKit.
Require Zlib.proof.uncompr.URunFrame.
Local Open Scope logic.

(* inflate()'s model keeps i_head (whether the stream holds a gz_header), in every mode *)
Definition ihc_om (o: Zlib.proof.inflate.Model.iout) : mst :=
  match o with Zlib.proof.inflate.Model.IBrk m => m | Zlib.proof.inflate.Model.IRet _ m => m end.

Lemma ihc_step_head flush fx dx m:
  i_head (m_s (ihc_om (Zlib.proof.inflate.Model2.stepf2 flush fx dx m))) = i_head (m_s m).
Proof.
  destruct (Z_le_gt_dec Zlib.proof.inflate.Model.HEAD (i_mode (m_s m)));
  [destruct (Z_le_gt_dec (i_mode (m_s m)) Zlib.proof.inflate.Model.BAD) |].
  - pose proof (Zlib.proof.uncompr.URunFrame.step2_ok flush fx dx _ (Zlib.proof.uncompr.URunFrame.fast_fr fx dx) m
                  ltac:(unfold Zlib.proof.uncompr.URunFrame.vmode; lia)) as S.
    unfold Zlib.proof.inflate.Model2.stepf2.
    destruct (Zlib.proof.inflate.Model2.step2 _ _ _ _ m); simpl in *;
      unfold Zlib.proof.uncompr.URunFrame.fr in S; tauto.
  - unfold Zlib.proof.inflate.Model2.stepf2, Zlib.proof.inflate.Model2.step2, Zlib.proof.inflate.Model.m_mode.
    repeat match goal with |- context [if Z.eqb ?a ?b then _ else _] =>
      let E := fresh "E" in destruct (Z.eqb a b) eqn:E;
      [apply Z.eqb_eq in E; rewrite E in *; exfalso; compute in l, g; first [congruence | tauto] | ] end;
    try match goal with |- context [if ?c then _ else _] => destruct c end; reflexivity.
  - unfold Zlib.proof.inflate.Model2.stepf2, Zlib.proof.inflate.Model2.step2, Zlib.proof.inflate.Model.m_mode.
    repeat match goal with |- context [if Z.eqb ?a ?b then _ else _] =>
      let E := fresh "E" in destruct (Z.eqb a b) eqn:E;
      [apply Z.eqb_eq in E; rewrite E in *; exfalso; compute in g; first [congruence | tauto] | ] end;
    try match goal with |- context [if ?c then _ else _] => destruct c end; reflexivity.
Qed.

Lemma ihc_loop_head flush fx dx m o:
  Zlib.proof.inflate.Model2.loop2 flush fx dx m o -> i_head (m_s (ihc_om o)) = i_head (m_s m).
Proof.
  induction 1 as [m r m' E|m m' E Lv|m m' o E Lv L IH].
  - pose proof (ihc_step_head flush fx dx m) as S. rewrite E in S. exact S.
  - pose proof (ihc_step_head flush fx dx m) as S. rewrite E in S. exact S.
  - pose proof (ihc_step_head flush fx dx m) as S. rewrite E in S. simpl in S. rewrite IH, S. reflexivity.
Qed.

Lemma ihc_rel_head flush strmp z L ib inp ob r z' L' ow:
  inflate_rel flush strmp z (Some L) ib inp ob r z' (Some L') ow -> i_head (l_s L') = i_head (l_s L).
Proof.
  intros [(_ & _ & _ & E & _) | (_ & L1 & o & res & winp & E1 & _ & Hrun & _ & _ & _ & _ & _ & E)].
  - inversion E; subst; reflexivity.
  - inversion E1; subst L1. injection E as E. rewrite E. simpl.
    destruct Hrun as (o2 & Lp & R).
    pose proof (ihc_loop_head _ _ _ _ _ Lp) as Hh.
    replace (i_head (m_s (m_init z L inp))) with (i_head (l_s L)) in Hh
      by (unfold m_init; simpl; destruct (_ =? _); reflexivity).
    destruct o2 as [m | r0 m]; simpl in Hh.
    + destruct R.
      * simpl. exact Hh.
      * destruct (Zlib.proof.uncompr.URunFrame.leave_fin_fr flush m) as (_ & _ & _ & D & _). rewrite D. exact Hh.
    + subst res. simpl. exact Hh.
Qed.

(* the member's length and bytes *)
Lemma ihc_src_len g: ih_ok g -> 0 <= Zlength (ih_src g) <= 2 ^ 20.
Proof.
  intros (_ & _ & _ & _ & Hx & _ & Hn & _ & Hc & _).
  pose proof (Zlength_nonneg (g_xf g)). pose proof (Zlength_nonneg (g_nf g)). pose proof (Zlength_nonneg (g_cf g)).
  unfold ih_src, ih_hdr.
  destruct (fl g 2), (fl g 4), (fl g 8), (fl g 16); autorewrite with sublist; simpl; lia.
Qed.

Lemma ihc_src_bytes g: ih_ok g -> is_bytes (ih_src g).
Proof.
  intros (Hf & Hm & Hx & Ho & Hxl & Hxb & Hnl & Hnb & Hcl & Hcb & _).
  assert (Hst: 0 <= ih_stored g <= 65535).
  { unfold ih_stored. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia.
    change (Z.ones 16) with 65535.
    match goal with |- context [?a mod ?m] => pose proof (Z.mod_pos_bound a m ltac:(lia)) end. lia. }
  pose proof (Zlength_nonneg (g_xf g)).
  assert (Hnz: forall l, Forall (fun b => 0 < b <= 255) l -> is_bytes l).
  { intros l Hl. unfold is_bytes. eapply Forall_impl; [ | exact Hl]. intros a Ha. simpl in Ha. rep_lia. }
  unfold ih_src, ih_hdr, is_bytes.
  repeat rewrite Forall_app.
  repeat split.
  - repeat constructor; try rep_lia;
      match goal with |- context [?a mod 256] => pose proof (Z.mod_pos_bound a 256 ltac:(lia)); rep_lia end.
  - destruct (fl g 4); [ | constructor]. apply Forall_app. split; [ | exact Hxb].
    repeat constructor; try (pose proof (Z.mod_pos_bound (Zlength (g_xf g)) 256); rep_lia);
      try (apply Z.div_pos; lia);
      match goal with |- ?a / 256 <= _ => cut (a / 256 < 256); [rep_lia | apply Z.div_lt_upper_bound; lia] end.
  - destruct (fl g 8); [ | constructor]. apply Forall_app. split; [apply Hnz; exact Hnb | repeat constructor; rep_lia].
  - destruct (fl g 16); [ | constructor]. apply Forall_app. split; [apply Hnz; exact Hcb | repeat constructor; rep_lia].
  - destruct (fl g 2); [ | constructor].
    repeat constructor; try (pose proof (Z.mod_pos_bound (ih_stored g) 256); rep_lia);
      try (apply Z.div_pos; lia);
      match goal with |- ?a / 256 <= _ => cut (a / 256 < 256); [rep_lia | apply Z.div_lt_upper_bound; lia] end.
  - repeat constructor; rep_lia.
  - unfold Zrepeat. simpl. repeat constructor; rep_lia.
Qed.

(* the call's buffers: the objects ib / ob (law's CS) as inflate()'s InBuf / OutBuf (inflate unit's CS) *)
Lemma ihc_bufs_pre L ibp obp ain aout (ci co: list val):
  Zlength co = aout ->
  data_at Ews (tarray tuchar ain) ci ibp * malloc_token Ews (tarray tuchar ain) ibp *
  data_at Ews (tarray tuchar aout) co obp * malloc_token Ews (tarray tuchar aout) obp
  |-- bufs_opt (Some L) (InBuf Ews ibp 0 ain ci) (Some (OutBuf Ews obp 0 aout co)) [] true true.
Proof.
  intros Hc. unfold bufs_opt.
  rewrite <- (ih_bytes_inflate_cs Ews ain ci ibp), <- (ih_tok_inflate_cs Ews ain ibp),
          <- (ih_bytes_inflate_cs Ews aout co obp), <- (ih_tok_inflate_cs Ews aout obp).
  assert (Eo: sublist 0 0 co ++ byte_vals [] ++ sublist (0 + Zlength (@nil Z)) aout co = co).
  { rewrite sublist_nil. simpl. rewrite sublist_same by lia. reflexivity. }
  unfold in_rep, out_opt, out_rep, in_tok, out_tok; rewrite Eo; cancel.
Qed.

Lemma ihc_bufs_post L ibp obp ain aout (ci co: list val) (ow: list Z):
  bufs_opt (Some L) (InBuf Ews ibp 0 ain ci) (Some (OutBuf Ews obp 0 aout co)) ow true true
  |-- data_at Ews (tarray tuchar ain) ci ibp * malloc_token Ews (tarray tuchar ain) ibp *
      data_at Ews (tarray tuchar aout) (sublist 0 0 co ++ byte_vals ow ++ sublist (0 + Zlength ow) aout co) obp *
      malloc_token Ews (tarray tuchar aout) obp.
Proof.
  unfold bufs_opt, in_rep, out_opt, out_rep, in_tok, out_tok.
  rewrite (ih_bytes_inflate_cs Ews ain ci ibp), (ih_tok_inflate_cs Ews ain ibp),
          (ih_bytes_inflate_cs Ews aout _ obp), (ih_tok_inflate_cs Ews aout obp). cancel.
Qed.

Lemma ihc_in_ptr sh p n c: isptr p -> in_ptr (InBuf sh p 0 n c) 0 = p.
Proof. intros Pp. destruct p; try contradiction. simpl. rewrite Ptrofs.add_zero. reflexivity. Qed.
Lemma ihc_out_ptr sh p n c: isptr p -> out_ptr (OutBuf sh p 0 n c) 0 = p.
Proof. intros Pp. destruct p; try contradiction. simpl. rewrite Ptrofs.add_zero. reflexivity. Qed.

(* the continuation (call_ok's second hypothesis), named to keep goals readable *)
Definition ihc_K {Espec: OracleKind} I gv V g b P h0 H Fr (Inv: environ -> mpred) pos ain aout stop
    ibp obp q bs : Prop :=
  forall pos' r z' L' inb cont,
     ih_mid_facts I V g b P h0 H pos pos' ain r z' L' aout stop ibp obp q inb cont bs ->
     semax Delta_m (ih_mid gv V g b P h0 H Fr pos' r z' L' ain aout stop ibp obp q inb cont bs) segL18 (ih_PL Inv).

(* the side goals of the tests of r (concrete): true equations, or a false hypothesis between ints *)
Ltac ihc_c := first [ reflexivity | vm_compute; reflexivity
  | exfalso; match goal with
     | Hx: @eq int _ _ |- _ => apply (f_equal Int.unsigned) in Hx; vm_compute in Hx; discriminate Hx
     | Hx: ~ (@eq int _ _) |- _ => apply Hx; vm_compute; reflexivity
     | Hx: @eq bool _ _ |- _ => vm_compute in Hx; discriminate Hx
     end ].
Ltac ihc_r Hr4 := destruct Hr4 as [-> | [-> | [-> | ->]]]; ihc_c.

Lemma call_core {Espec: OracleKind} I gv V g b P h0 H Fr (Inv: environ -> mpred) pos z L ain aout flush stop
    ibp obp q bs:
  ih_buf_facts I V g b P h0 H pos z L ain aout flush stop ibp obp q bs ->
  ihc_K I gv V g b P h0 H Fr Inv pos ain aout stop ibp obp q bs ->
  semax Delta_m (ih_buf gv V g b P h0 H Fr pos z L ain aout flush stop ibp obp q bs) segL10 (ih_PL Inv).
Proof.
  intros BF K.
  pose proof BF as BF'.
  destruct BF' as (G & HI & HLok & Hpos & Hain & Hpa & Haout & Hbsl & Hbsb & Hfl & Hst & Pib & Pob & Pq).
  pose proof G as G'. destruct G' as (CF & F53 & _).
  pose proof (proj1 F53) as Gok.
  pose proof (ihc_src_len g Gok) as Hsl.
  destruct (ihf_live I CF _ _ _ _ _ _ HI) as (Hhd & _).
  unfold ih_buf. rewrite ih_istream_unfold. Intros.
  destruct V as [vs vh vxs vns vcs vosn]. simpl v_s_; simpl v_h_; simpl v_xs_; simpl v_ns_; simpl v_cs_; simpl v_osn_.
  assert_PROP (isptr vs) as Pvs by entailer!.
  unfold segL10, Delta_m, Gmain, ih_PL, POST_b, POST_m. simplify_func_tycontext. abbreviate_semax.
  forward. forward. forward. forward.
  set (sub := sublist pos (pos + ain) (ih_src g)) in *.
  rewrite <- ih_tup_set.
  set (ib := InBuf Ews ibp 0 ain (bytes_rep sub)).
  set (o := OutBuf Ews obp 0 aout (bytes_rep bs)).
  set (z1 := ih_zcall z (in_ptr ib 0) ain (out_ptr o 0) aout).
  replace (ih_zcall z ibp ain obp aout) with z1 by (unfold z1, ib, o; rewrite ihc_in_ptr, ihc_out_ptr; auto).
  assert (Z1ok: zf_ok z1).
  { match goal with Hz: zf_ok z |- _ => pose proof Hz as Zk end. unfold zf_ok in Zk.
    unfold z1, ih_zcall, zf_ok; simpl. rep_lia. }
  assert (Hsub: Zlength sub = ain) by (unfold sub; rewrite Zlength_sublist; lia).
  sep_apply (ih_istream_fold gv Tsh vs z1 L); auto.
  sep_apply (ihc_bufs_pre L ibp obp ain aout (bytes_rep sub) (bytes_rep bs)).
  { rewrite Zlength_bytes_rep; auto. }
  fold ib o.
  forward_call (gv, Tsh, vs, z1, Some L, ib, sub, Some o, flush, Ers, Ers, true, true).
  { rewrite ih_istream_opt, ih_is_live by auto. simpl head_opt. cancel. }
  { unfold z1, ih_zcall; simpl zf_ai; simpl zf_ao; simpl zf_no; simpl zf_ni.
    unfold ib, o, in_tok_ok, out_tok_ok, in_ok, out_ok.
    assert (bytes_ok sub) by (apply Forall_sublist; apply (ihc_src_bytes g Gok)).
    rewrite ?Zlength_bytes_rep.
    repeat match goal with |- _ /\ _ => split end; auto with share; try rep_lia; try discriminate.
    rewrite Z.add_0_l, sublist_same; [reflexivity | auto | rewrite Zlength_bytes_rep; auto].
  }
  Intros vret. destruct vret as [[[r z'] st'] ow]. simpl fst in *; simpl snd in *.
  match goal with Hx: inflate_rel _ _ _ _ _ _ _ _ _ _ _ |- _ => rename Hx into Hrel end.
  destruct (ih_rel_live _ _ _ _ _ _ _ _ _ _ _ Hrel) as (L' & Est & Esp & Ehp & Ehs & Exb & Enb & Ecb).
  subst st'.
  destruct (ihf_inflate I CF g (b_w b) h0 pos z L vs flush ib sub o ain aout r z' (Some L') ow Gok HI H2 H0
              ltac:(destruct vs; try contradiction; discriminate) Hpos Hain Hpa Haout Hfl
              ltac:(discriminate) eq_refl Hrel) as [L'' [E'' Hpost]].
  injection E'' as <-.
  assert (Hhd': i_head (l_s L') = true) by (rewrite (ihc_rel_head _ _ _ _ _ _ _ _ _ _ _ Hrel); exact Hhd).
  destruct HLok as (Lhp & Lhs & Lxb & Lnb & Lcb). simpl v_h_ in Lhp.
  rewrite ih_istream_opt, !ih_is_live by auto.
  simpl head_opt.
  pose proof (ihc_bufs_post L ibp obp ain aout (bytes_rep sub) (bytes_rep bs) ow) as BP.
  fold ib o in BP. sep_apply BP. clear BP.
  forward_if.
  { forward. Exists (Int.repr 0).
    sep_apply (ih_istream_to_undef gv vs z' (Some L')).
    sep_apply (ih_head_mem_undef L' _ Hhd' Ehp ltac:(congruence)).
    entailer!. }
  assert (Hne: r <> Z_MEM_ERROR).
  { intro E. subst r. match goal with Hx: Int.repr _ <> Int.neg _ |- _ => apply Hx; reflexivity end. }
  pose proof Hpost as Hpost'. unfold ih_post in Hpost'. cbv zeta in Hpost'.
  destruct Hpost' as (Hr & Hai & _ & _ & _ & _ & _ & _).
  assert (Hr4: r = Z_OK \/ r = Z_BUF_ERROR \/ r = Z_STREAM_END \/ r = Z_DATA_ERROR) by tauto.
  clear Hr.
  Intros. rewrite ih_istream_unfold. Intros.
  ifpost _t'50 (Int.repr (b2z (Z.eqb r 0 || Z.eqb r (-5)))).
  { forward. entailer!. ihc_r Hr4. }
  { forward. entailer!. ihc_r Hr4. }
  ifpost _t'51 (Int.repr (b2z (Z.eqb r 0 || Z.eqb r (-5) || Z.eqb r 1))).
  { forward. entailer!. ihc_r Hr4. }
  { forward. entailer!. ihc_r Hr4. }
  ifpost _t'52 (Int.repr 1).
  { forward. entailer!. }
  { forward. entailer!. ihc_r Hr4. }
  forward_call (Int.repr 1).
  forward. forward.
  rewrite sub_repr, add_repr.
  sep_apply (ih_istream_fold gv Tsh vs z' L'); auto.
  set (cont := sublist 0 0 (bytes_rep bs) ++ byte_vals ow ++ sublist (0 + Zlength ow) (Zlength bs) (bytes_rep bs)).
  assert_PROP (Zlength cont = Zlength bs) as Hcont by entailer!.
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
  eapply semax_pre; [ | apply (K (pos + (ain - zf_ai z')) r z' L' (bytes_rep sub) cont) ].
  { unfold ih_mid. simpl v_s_; simpl v_h_; simpl v_xs_; simpl v_ns_; simpl v_cs_; simpl v_osn_. entailer!. }
  unfold ih_mid_facts.
  assert (Hinb: Zlength (bytes_rep sub) = ain) by (rewrite Zlength_bytes_rep; auto).
  repeat match goal with |- _ /\ _ => split end; auto; try lia.
  unfold ih_Lok; simpl; repeat split; congruence.
Qed.

Lemma call_ok {Espec: OracleKind} I gv V g b P h0 H Fr (Inv: environ -> mpred) pos z L ain aout flush stop
    ibp obp q bs:
  ih_buf_facts I V g b P h0 H pos z L ain aout flush stop ibp obp q bs ->
  (forall pos' r z' L' inb cont,
     ih_mid_facts I V g b P h0 H pos pos' ain r z' L' aout stop ibp obp q inb cont bs ->
     semax Delta_m (ih_mid gv V g b P h0 H Fr pos' r z' L' ain aout stop ibp obp q inb cont bs) segL18 (ih_PL Inv)) ->
  semax Delta_m (ih_buf gv V g b P h0 H Fr pos z L ain aout flush stop ibp obp q bs) segL10 (ih_PL Inv).
Proof. intros BF K. apply (call_core I gv V g b P h0 H Fr Inv pos z L ain aout flush stop ibp obp q bs BF K). Qed.
