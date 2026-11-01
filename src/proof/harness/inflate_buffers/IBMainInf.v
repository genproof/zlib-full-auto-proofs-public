(* Law inflate_buffers, main: the branch `r = inflate(&s, flush)` (op < 200; next_in / next_out Z_NULL when nin / nout). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.inflate_common.HarnessLib.
Require Import Zlib.proof.harness.inflate_buffers.IBLawCS Zlib.proof.harness.inflate_buffers.IBGlobals
               Zlib.proof.harness.inflate_buffers.IBFacts Zlib.proof.harness.inflate_buffers.IBMainKit.
Require Import Zlib.harness.x_inflate_buffers.code.
Require Import Zlib.proof.crc32.Spec.

(* the call's buffers: next_in Z_NULL (nin) or ib, next_out Z_NULL (nout) or ob *)
Definition ibi_ib (nin: bool) (ibp: val) (ain: Z) (c: list val) : inbuf :=
  if nin then InNull else InBuf Ews ibp 0 ain c.
Definition ibi_ob (nout: bool) (obp: val) (aout: Z) (c: list val) : option outbuf :=
  if nout then None else Some (OutBuf Ews obp 0 aout c).
(* what the call does not take of them *)
Definition ibi_rin (nin: bool) (ibp: val) (ain: Z) (c: list val) : mpred :=
  if nin then (@data_at CS Ews (tarray tuchar ain) c ibp * @malloc_token CS Ews (tarray tuchar ain) ibp)%logic
  else emp.
Definition ibi_rout (nout: bool) (obp: val) (aout: Z) (c: list val) : mpred :=
  if nout then (@data_at CS Ews (tarray tuchar aout) c obp * @malloc_token CS Ews (tarray tuchar aout) obp)%logic
  else emp.

Lemma ibi_bufs_pre L nin nout ibp obp ain aout (ci co: list val):
  Zlength co = aout ->
  (@data_at CS Ews (tarray tuchar ain) ci ibp * @malloc_token CS Ews (tarray tuchar ain) ibp *
   @data_at CS Ews (tarray tuchar aout) co obp * @malloc_token CS Ews (tarray tuchar aout) obp)%logic
  |-- (bufs_opt (Some L) (ibi_ib nin ibp ain ci) (ibi_ob nout obp aout co) [] true true *
       ibi_rin nin ibp ain ci * ibi_rout nout obp aout co)%logic.
Proof.
  intros Hc. unfold bufs_opt, ibi_ib, ibi_ob, ibi_rin, ibi_rout.
  rewrite <- (bytes_inflate_cs Ews ain ci ibp), <- (tok_inflate_cs Ews ain ibp),
          <- (bytes_inflate_cs Ews aout co obp), <- (tok_inflate_cs Ews aout obp).
  assert (Eo: sublist 0 0 co ++ byte_vals [] ++ sublist (0 + Zlength (@nil Z)) aout co = co).
  { rewrite sublist_nil. simpl. rewrite sublist_same by lia. reflexivity. }
  destruct nin, nout; unfold in_rep, out_opt, out_rep, in_tok, out_tok; rewrite ?Eo; cancel.
Qed.

Definition ibi_oc (nout: bool) (aout: Z) (co: list val) (ow: list Z) : list val :=
  if nout then co else sublist 0 0 co ++ byte_vals ow ++ sublist (0 + Zlength ow) aout co.

Lemma ibi_bufs_post L nin nout ibp obp ain aout (ci co: list val) (ow: list Z):
  (bufs_opt (Some L) (ibi_ib nin ibp ain ci) (ibi_ob nout obp aout co) ow true true *
   ibi_rin nin ibp ain ci * ibi_rout nout obp aout co)%logic
  |-- (@data_at CS Ews (tarray tuchar ain) ci ibp * @malloc_token CS Ews (tarray tuchar ain) ibp *
       @data_at CS Ews (tarray tuchar aout) (ibi_oc nout aout co ow) obp *
       @malloc_token CS Ews (tarray tuchar aout) obp)%logic.
Proof.
  unfold bufs_opt, ibi_ib, ibi_ob, ibi_rin, ibi_rout, ibi_oc.
  set (X := sublist 0 0 co ++ byte_vals ow ++ sublist (0 + Zlength ow) aout co).
  destruct nin, nout; unfold in_rep, out_opt, out_rep, in_tok, out_tok; fold X.
  - cancel.
  - rewrite (bytes_inflate_cs Ews aout X obp), (tok_inflate_cs Ews aout obp). cancel.
  - rewrite (bytes_inflate_cs Ews ain ci ibp), (tok_inflate_cs Ews ain ibp). cancel.
  - rewrite (bytes_inflate_cs Ews aout X obp), (tok_inflate_cs Ews aout obp),
            (bytes_inflate_cs Ews ain ci ibp), (tok_inflate_cs Ews ain ibp). cancel.
Qed.

Definition ibi_nrm (b: Z) : Z := Int.unsigned (Int.repr b).

(* the bytes of ob after the call *)
Definition ibi_obl (nout: bool) (aout: Z) (bs ow: list Z) : list Z :=
  if nout then bs else map ibi_nrm ow ++ sublist (Zlength ow) aout bs.

Lemma ibi_oc_rep nout aout bs ow: Zlength bs = aout -> Zlength ow <= aout ->
  ibi_oc nout aout (bytes_rep bs) ow = bytes_rep (ibi_obl nout aout bs ow).
Proof.
  intros Hl Ho. unfold ibi_oc, ibi_obl. destruct nout; [reflexivity | ].
  rewrite sublist_nil, Z.add_0_l. unfold bytes_rep, byte_vals. simpl app.
  rewrite map_app, map_map. rewrite <- sublist_map. f_equal.
  apply map_ext. intros b. unfold ibi_nrm. rewrite Int.repr_unsigned. reflexivity.
Qed.

Lemma ibi_ow_bytes sh n (ow: list Z) (rest: list val) p:
  @data_at CS sh (tarray tuchar n) (byte_vals ow ++ rest) p |-- !! is_bytes (map ibi_nrm ow).
Proof.
  entailer!.
  apply Forall_app in H1. destruct H1 as [H1 _]. unfold byte_vals in H1. unfold is_bytes. clear -H1.
  induction ow as [|b ow IH]; simpl in *; constructor; inversion H1; subst.
  { unfold ibi_nrm. match goal with Hb: value_fits _ _ |- _ =>
      rewrite value_fits_eq in Hb; simpl in Hb; specialize (Hb ltac:(discriminate)); simpl in Hb end. rep_lia. }
  apply IH; auto.
Qed.

Lemma seg_inf_ok {Espec: OracleKind} gv vs vosn vdl srcp src pos aout flush arg op innull outnull stop ain ibp obp q bs z L
    Fr (Post: ret_assert) :
  ops_hyps srcp src pos aout flush arg op innull outnull stop ain ibp obp q bs L -> op < 200 ->
  semax Delta_m (ops_pre gv vs vosn vdl srcp src pos aout flush arg op innull outnull stop ain ibp obp q bs z L Fr)
    seg_inf
    (overridePost (ops_post gv vs vosn vdl srcp src pos aout flush arg op innull outnull stop ain ibp obp q z Fr) Post).
Proof.
  intros H Hop.
  destruct H as (FI & HI & Hpos & Hain & Hpa & Hsrc & Hsb & Haout & Hbsl & Hbsb & Hfl & Harg & Hopr & Hin & Hout & Hst & Psrc & Pib & Pob & Pq).
  unfold ops_pre, ops_locals.
  assert_PROP (isptr vs) as Pvs by entailer!.
  unfold seg_inf, Delta_m, Gmain_k. simplify_func_tycontext. abbreviate_semax.
  set (nin := ib_nin op innull) in *. set (nout := ib_nout op outnull) in *.
  set (sub := sublist pos (pos + ain) src) in *.
  assert (Hsub: Zlength sub = ain) by (unfold sub; rewrite Zlength_sublist; lia).
  assert (Bsub: bytes_ok sub) by (apply Forall_sublist; exact Hsb).
  set (ib := ibi_ib nin ibp ain (bytes_rep sub)).
  set (ob := ibi_ob nout obp aout (bytes_rep bs)).
  set (inp := if nin then [] else sub).
  set (z1 := ib_zcall z nin nout ibp obp ain aout).
  sep_apply (ibi_bufs_pre L nin nout ibp obp ain aout (bytes_rep sub) (bytes_rep bs)).
  { rewrite Zlength_bytes_rep; auto. }
  fold ib ob.
  assert (Hhd: i_head (l_s L) = false) by (destruct HI; auto).
  assert (Hni: zf_ni z1 = in_ptr ib 0).
  { unfold z1, ib, ibi_ib, ib_zcall; simpl. destruct nin; simpl; auto.
    destruct ibp; try contradiction. simpl. rewrite Ptrofs.add_zero. reflexivity. }
  assert (Hno: match ob with None => zf_no z1 = nullval | Some o => zf_no z1 = out_ptr o 0 end).
  { unfold z1, ob, ibi_ob, ib_zcall; simpl. destruct nout; simpl; auto.
    destruct obp; try contradiction. simpl. rewrite Ptrofs.add_zero. reflexivity. }
  assert_PROP (zf_ok z1 /\ live_ok L) as ZL by (unfold istream; entailer!).
  destruct ZL as [Z1ok LOK].
  forward_call (gv, Tsh, vs, z1, Some L, ib, inp, ob, flush, Ers, Ers, true, true).
  { rewrite ib_istream_opt, ib_is_live by auto. simpl head_opt. unfold head_mem; rewrite Hhd. cancel. }
  { clear Hni Hno. unfold ib, ob, inp, ibi_ib, ibi_ob in *. unfold z1 in *. cbn [ib_zcall zf_ai zf_ao zf_no zf_ni] in *.
    destruct nin, nout; simpl in *; repeat match goal with |- _ /\ _ => split end; auto with share; try rep_lia;
    try discriminate; rewrite ?Zlength_bytes_rep; try rep_lia;
    try (destruct obp; try contradiction; simpl; rewrite Ptrofs.add_zero; reflexivity);
    try (rewrite Hsub, sublist_same by (rewrite ?Zlength_bytes_rep; lia); reflexivity). }
  Intros vret. destruct vret as [[[r z'] st'] ow]. simpl fst; simpl snd.
  match goal with H: inflate_rel _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H into Hrel end.
  assert (Hai1: zf_ai z1 = ain) by reflexivity.
  assert (Hao1: zf_ao z1 = aout) by reflexivity.
  destruct (fi_inflate FI flush vs z1 L ib inp ob r z' st' ow LOK Z1ok HI
              ltac:(destruct vs; try contradiction; discriminate)
              ltac:(unfold inp; destruct nin; [constructor | exact Bsub])
              ltac:(unfold inp; destruct nin; [rewrite Zlength_nil; lia | rewrite Hsub; lia])
              ltac:(rewrite Hao1; rep_lia) Hni
              ltac:(unfold ib, inp, ibi_ib; destruct nin; auto)
              Hno Hrel)
    as (L' & -> & HI' & Hai' & Hao' & Hni' & Hnull & Hno' & Hnone & Hlow & Htot).
  clear Hrel.
  rewrite ib_istream_opt, !ib_is_live by auto.
  simpl head_opt. unfold head_mem at 1. rewrite (proj1 HI').
  pose proof (ibi_bufs_post L nin nout ibp obp ain aout (bytes_rep sub) (bytes_rep bs) ow) as BP.
  fold ib ob in BP. sep_apply BP. clear BP.
  assert_PROP (is_bytes (ibi_obl nout aout bs ow)) as Bobl.
  { unfold ibi_oc, ibi_obl. destruct nout.
    - entailer!.
    - rewrite sublist_nil. simpl app. sep_apply ibi_ow_bytes. entailer!.
      apply Forall_app; split; auto. apply Forall_sublist; auto. }
  rewrite ibi_oc_rep by lia.
  Intros.
  forward.
  destruct Post as [Pn Pb Pc Pr]; unfold overridePost; simpl RA_normal.
  unfold ops_post, ops_post_at, ops_locals.
  Exists (Int.signed (Int.repr r)) 0 z' L' (ibi_obl nout aout bs ow) bs.
  rewrite Int.repr_signed. fold nin nout.
  entailer!.
  rewrite Hai1 in Hai', Hni', Hnull, Htot. rewrite Hao1 in Hao', Hno', Hnone, Hlow, Htot.
  assert (Ht1: zf_tin z1 = zf_tin z) by reflexivity. assert (Ht2: zf_tout z1 = zf_tout z) by reflexivity.
  rewrite Ht1, Ht2 in Htot.
  unfold ops_out.
  pose proof (Int.signed_range (Int.repr r)) as Hrr.
  split; [lia | ]. split; [left; reflexivity | ].
  split; [lia | ]. split; [lia | ].
  split; [rewrite Hni'; unfold ib, ibi_ib; destruct nin; reflexivity | ].
  split; [intros E; unfold ib, ibi_ib in Hnull; rewrite E in Hnull; specialize (Hnull eq_refl); lia | ].
  split; [rewrite Hno'; unfold ob, ibi_ob; destruct nout; reflexivity | ].
  split; [intros E; unfold ob, ibi_ob in Hnone; rewrite E in Hnone; specialize (Hnone eq_refl); lia | ].
  split.
  { unfold ibi_obl. destruct nout; [reflexivity | ].
    rewrite Zlength_app, Zlength_map, Zlength_sublist by lia. lia. }
  split; [reflexivity | ]. split; [exact Bobl | ]. split; [exact Hbsb | ].
  split.
  { unfold ibi_obl. destruct nout eqn:En; [reflexivity | ].
    rewrite <- Hlow. rewrite sublist_app2 by (rewrite Zlength_map; lia).
    rewrite Zlength_map, Z.sub_diag. rewrite sublist_sublist by lia. f_equal; lia. }
  split; [intros E; discriminate | ].
  intros _ E. apply Htot. intros Em. rewrite Em in E. simpl in E.
  rewrite (proj2 (Z.ltb_lt op 200)) in E by lia. discriminate.
Qed.
