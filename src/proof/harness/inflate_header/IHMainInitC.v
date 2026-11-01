(* Law inflate_header, main, positions 70 .. 74 (IHMainInitKit.v): r = inflateGetHeader(&s, &h),
   gp_assert((r == Z_STREAM_ERROR) == (wbits < 16)) (ihf_wrap), the failure branch (gp_assert, inflateEnd,
   return 0), gp_assert(h.done == 0), pos = 0; establishes ih_inv (ihf_init) and ih_glob; then seg_75 (given). *)
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
Require Import Zlib.proof.harness.inflate_header.IHMainInitKit.
Local Open Scope logic.

(* a header buffer of head_buf: the buffer (head_rep), the token of a 0-size one (btok), the rest (ih_hrest) *)
Lemma ihc_buf_split bp q max bs:
  ihi_buf bp q max bs = ih_hbuf bp max bs * ih_btok bp max * ih_hrest bp q max bs.
Proof.
  unfold ihi_buf, ih_hbuf, ih_btok, ih_hrest.
  destruct (eq_dec bp nullval); [rewrite !emp_sepcon; reflexivity | ].
  destruct (zeq max 0); [subst max | ]; apply pred_ext; cancel.
Qed.

(* the gz_header and its buffers as inflateGetHeader wants them *)
Lemma ihc_pre vh xb nb cb xq nq cq h0 xmax nmax cmax:
  h_extra_max h0 = xmax -> h_name_max h0 = nmax -> h_comm_max h0 = cmax ->
  data_at Tsh (Tstruct _gz_header_s noattr) (ih_htup xb nb cb h0) vh * ihi_buf xb xq xmax (h_xbuf h0) *
  ihi_buf nb nq nmax (h_nbuf h0) * ihi_buf cb cq cmax (h_cbuf h0)
  |-- head_rep Tsh vh xb nb cb h0 * hdr_btoks xb nb cb h0 *
      (ih_hrest xb xq xmax (h_xbuf h0) * ih_hrest nb nq nmax (h_nbuf h0) * ih_hrest cb cq cmax (h_cbuf h0)).
Proof.
  intros <- <- <-. rewrite ih_head_rep_eq, !ihc_buf_split. unfold hdr_btoks.
  rewrite <- (ih_btok_eq xb), <- (ih_btok_eq nb), <- (ih_btok_eq cb). cancel.
Qed.

Lemma ihc_buf_ptr bp q max bs:
  ihi_buf bp q max bs |-- !! (bp <> nullval -> isptr bp /\ isptr q).
Proof. unfold ihi_buf. destruct (eq_dec bp nullval); entailer!. Qed.

(* the gz_header's buffers and tokens in head_mem *)
Definition ihc_hbufs (xb nb cb: val) (h0: hstate) : mpred :=
  ih_hbuf xb (h_extra_max h0) (h_xbuf h0) * ih_hbuf nb (h_name_max h0) (h_nbuf h0) *
  ih_hbuf cb (h_comm_max h0) (h_cbuf h0) *
  ih_btok xb (h_extra_max h0) * ih_btok nb (h_name_max h0) * ih_btok cb (h_comm_max h0).

Lemma ihc_head_mem sp w h0 vh xb nb cb:
  head_mem (ih_L0 sp w h0 vh Tsh xb nb cb) =
  data_at Tsh (Tstruct _gz_header_s noattr) (ih_htup xb nb cb (set_h_done h0 0)) vh * ihc_hbufs xb nb cb h0.
Proof.
  rewrite ih_head_mem_eq by reflexivity. unfold ihc_hbufs.
  destruct h0; simpl. rewrite !sepcon_assoc. reflexivity.
Qed.

Lemma hdr_ok {Espec: OracleKind} I gv V g b P sp adl rs H xbs nbs cbs text time xflags os elen hcrc done:
  ihi_f60 I g b P sp adl rs H xbs nbs cbs ->
  hwf (ihi_h0 b xbs nbs cbs text time xflags os elen hcrc done) ->
  (forall h0 H', ih_glob I g b P h0 H' ->
     semax Delta_m (ih_inv I gv V g b P h0 H' (version_lit gv * ih_hversion_lit gv)) seg_75 POST_b) ->
  semax Delta_m (ihi_s70 gv V g b P sp adl rs H (ihi_h0 b xbs nbs cbs text time xflags os elen hcrc done))
    seg_70 POST_b.
Proof.
  intros F60 HW K.
  destruct F60 as (CF & F53 & WOK & Psp & Hadl & Hrs & Hxl & Hxb & Hxq & Hxn & Hnl & Hnb & Hnq & Hnn &
                   Hcl & Hcb & Hcq & Hcn).
  remember (ihi_h0 b xbs nbs cbs text time xflags os elen hcrc done) as h0 eqn:Hh0.
  destruct V as [vs vh vxs vns vcs vosn]; destruct b as [w xmax nmax cmax xnul nnul cnul];
  destruct P as [srcp xfp nfp cfp]; destruct H as [xb nb cb xq nq cq].
  unfold ihi_s70, seg_70, Delta_m, Gmain, POST_b, POST_m.
  cbn [v_s_ v_h_ v_xs_ v_ns_ v_cs_ v_osn_ b_w b_xmax b_nmax b_cmax b_xnul b_nnul b_cnul p_src p_xf p_nf p_cf
       h_xb h_nb h_cb h_xq h_nq h_cq] in *.
  simplify_func_tycontext. abbreviate_semax.
  pose proof F53 as F53'. destruct F53' as (Hg & Hw & _). cbn [b_w] in Hw.
  assert (Hxm: h_extra_max h0 = xmax) by (subst h0; reflexivity).
  assert (Hnm: h_name_max h0 = nmax) by (subst h0; reflexivity).
  assert (Hcm: h_comm_max h0 = cmax) by (subst h0; reflexivity).
  assert (Hxp: h_xp h0 = negb (xnul =? 0)) by (subst h0; reflexivity).
  assert (Hnp: h_np h0 = negb (nnul =? 0)) by (subst h0; reflexivity).
  assert (Hcp: h_cp h0 = negb (cnul =? 0)) by (subst h0; reflexivity).
  set (L0 := init_live sp w). set (z0 := ihi_z_init adl rs L0).
  assert_PROP (isptr vs) as Pvs by entailer!.
  assert_PROP (isptr vh) as Pvh by entailer!.
  assert_PROP (zf_ok z0) as Zok by (unfold istream; entailer!).
  assert_PROP ((xb <> nullval -> isptr xb /\ isptr xq) /\ (nb <> nullval -> isptr nb /\ isptr nq) /\
               (cb <> nullval -> isptr cb /\ isptr cq)) as Pbufs.
  { sep_apply (ihc_buf_ptr xb xq xmax (h_xbuf h0)). sep_apply (ihc_buf_ptr nb nq nmax (h_nbuf h0)).
    sep_apply (ihc_buf_ptr cb cq cmax (h_cbuf h0)). entailer!. }
  replace_SEP 0 (istream_opt gv Tsh vs z0 (Some L0)).
  { rewrite ih_istream_opt by auto. entailer!. }
  gather_SEP 7 11 12 13.
  replace_SEP 0 (head_rep Tsh vh xb nb cb h0 * hdr_btoks xb nb cb h0 *
      (ih_hrest xb xq xmax (h_xbuf h0) * ih_hrest nb nq nmax (h_nbuf h0) * ih_hrest cb cq cmax (h_cbuf h0))).
  { entailer!. sep_apply ihc_pre; auto. cancel. }
  assert (EL: is_live vs (Some L0) = Some L0) by (apply ih_is_live; auto).
  assert (EW: (Z.land (i_wrap (l_s L0)) 2 =? 0) = (w <? 16)) by (apply (ihf_wrap I CF); auto).
  assert (Hxpn: h_xp h0 = true -> xb <> nullval)
    by (rewrite Hxp; intros E N; apply Hxn in N; subst; discriminate E).
  assert (Hnpn: h_np h0 = true -> nb <> nullval)
    by (rewrite Hnp; intros E N; apply Hnn in N; subst; discriminate E).
  assert (Hcpn: h_cp h0 = true -> cb <> nullval)
    by (rewrite Hcp; intros E N; apply Hcn in N; subst; discriminate E).
  forward_call (gv, Tsh, vs, z0, Some L0, vh, Tsh, xb, nb, cb, h0).
  { cancel. }
  rewrite EL, EW.
  destruct (Z.ltb_spec w 16) as [Wlt | Wge]; cbv beta iota zeta.
  - forward_call (Int.repr 1).
    { entailer!. unfold Int.lt. rewrite !Int.signed_repr by rep_lia. destruct (zlt w 16); [reflexivity | lia]. }
    forward_if; [ | discriminate ].
    forward_call (Int.repr 1).
    flatten_sepcon_in_SEP.
    forward_call (gv, Tsh, vs, z0, Some L0).
    { cancel. }
    rewrite (ih_istream_opt gv Tsh vs z0 None) by auto.
    sep_apply (ih_istream_to_undef gv vs z0 None).
    rewrite ih_head_rep_eq.
    sep_apply (data_at_data_at_ Tsh (Tstruct _gz_header_s noattr) (ih_htup xb nb cb h0) vh).
    forward. Exists (Int.repr 0). apply andp_right; [apply prop_right; reflexivity | ].
    sep_apply (data_at_data_at_ Tsh (tptr tuchar) xq vxs). sep_apply (data_at_data_at_ Tsh (tptr tuchar) nq vns).
    sep_apply (data_at_data_at_ Tsh (tptr tuchar) cq vcs). cancel.
  - forward_call (Int.repr 1).
    { entailer!. unfold Int.lt. rewrite !Int.signed_repr by rep_lia. destruct (zlt w 16); [lia | reflexivity]. }
    forward_if; [ exfalso; first [discriminate | contradiction] | ].
    set (L1 := ih_L0 sp w h0 vh Tsh xb nb cb).
    replace_SEP 0 (istream gv Tsh vs z0 (Some L1) * head_mem L1).
    { rewrite ih_istream_opt by auto. entailer!. apply derives_refl. }
    flatten_sepcon_in_SEP.
    replace_SEP 1 (data_at Tsh (Tstruct _gz_header_s noattr) (ih_htup xb nb cb (set_h_done h0 0)) vh *
                   ihc_hbufs xb nb cb h0).
    { unfold L1. rewrite ihc_head_mem. entailer!. }
    flatten_sepcon_in_SEP.
    forward.
    forward_call (Int.repr 1).
    gather_SEP 1 2.
    replace_SEP 0 (head_mem L1).
    { unfold L1. rewrite ihc_head_mem. entailer!. }
    forward.
    unfold abbreviate in POSTCONDITION, MORE_COMMANDS. subst POSTCONDITION MORE_COMMANDS.
    eapply semax_pre; [ | apply (K h0 (IHH xb nb cb xq nq cq)) ].
    2: { destruct Pbufs as (Px & Pn & Pc).
         unfold ih_glob; cbn [b_w b_xmax b_nmax b_cmax b_xnul b_nnul b_cnul h_xb h_nb h_cb h_xq h_nq h_cq].
         refine (conj CF (conj F53 (conj WOK (conj Wge (conj HW (conj Hxm (conj Hnm (conj Hcm
                   (conj Hxp (conj Hnp (conj Hcp _))))))))))).
         split; [intros E; split; [apply Hxn, E | apply Hxq, Hxn, E] | ].
         split; [intros E; apply Px; intros N; apply E, Hxn, N | ].
         split; [intros E; split; [apply Hnn, E | apply Hnq, Hnn, E] | ].
         split; [intros E; apply Pn; intros N; apply E, Hnn, N | ].
         split; [intros E; split; [apply Hcn, E | apply Hcq, Hcn, E] | ].
         intros E; apply Pc; intros N; apply E, Hcn, N. }
    assert (HI: I g w h0 0 z0 L1).
    { apply (ihf_init I CF); auto. }
    assert (Lok: ih_Lok (IHV vs vh vxs vns vcs vosn) (IHH xb nb cb xq nq cq) L1) by (repeat split; reflexivity).
    assert (Hpos: 0 <= 0 <= Zlength (ih_src g)) by (pose proof (Zlength_nonneg (ih_src g)); lia).
    unfold ih_inv, ih_at.
    cbn [v_s_ v_h_ v_xs_ v_ns_ v_cs_ v_osn_ b_w b_xmax b_nmax b_cmax b_xnul b_nnul b_cnul p_src p_xf p_nf p_cf
         h_xb h_nb h_cb h_xq h_nq h_cq].
    Exists 0 z0 L1.
    entailer!.
Qed.
