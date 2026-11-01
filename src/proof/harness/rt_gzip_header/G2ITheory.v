(* Law rt_gzip_header on the round-2 harness: the inflate side of the law (G2IFacts.g2_ifacts), pure Coq over the
   model of inflate().

   The invariant of the harness's loop is G2ICall.g2_P: pos bytes of O consumed, the stream inside the gzip header
   (its state determined by pos alone, G2IDefs.J2) or after it (the decode invariant of the generalized decode
   theory, RTIGW, and the complete gz_header).  After inflateInit2(16 + wb) and inflateGetHeader the stream is at
   HEAD with nothing consumed; each call either stops inside the header having consumed all its input
   (Z_BUF_ERROR, and O is not all read: the loop goes on), or passes the end of the header and decodes deflate's
   empty data, writing nothing; the header is then complete whatever the call returns. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.rt_gzip_header.G2IFacts.
Require Import Zlib.proof.harness.rt_gzip_header.G2IDefs.
Require Import Zlib.proof.roundtrip.RTIGW.
Require Import Zlib.proof.harness.rt_gzip_header.G2ICases.
Require Import Zlib.proof.harness.rt_gzip_header.G2ILay.
Require Import Zlib.proof.harness.rt_gzip_header.G2IBridge.
Require Import Zlib.proof.harness.rt_gzip_header.G2ICall.
Import ListNotations.
Local Open Scope Z_scope.

(* the state after inflateInit2(16 + wb) and inflateGetHeader *)
Lemma g2t_init_s sp wb h headp hsh xb nb cb : 9 <= wb <= 15 ->
  let L := head_live (init_live sp (16 + wb)) h headp hsh xb nb cb in
  i_mode (l_s L) = HEAD /\ i_wrap (l_s L) = 6 /\ i_hold (l_s L) = 0 /\ i_bits (l_s L) = 0 /\
  i_wsize (l_s L) = 0 /\ i_total (l_s L) = 0 /\ i_wbits (l_s L) = wb /\ i_last (l_s L) = 0 /\
  i_head (l_s L) = true /\ l_h L = set_h_done h 0.
Proof.
  intros W. assert (E: wb = 9 \/ wb = 10 \/ wb = 11 \/ wb = 12 \/ wb = 13 \/ wb = 14 \/ wb = 15) by lia.
  repeat destruct E as [E|E]; subst wb; repeat split; reflexivity.
Qed.

Lemma g2t_init (LAY: g2_lay_stmt) : forall wbd wb gh O sp z h headp hsh xb nb cb,
  RF.dfinal [] 2 wbd (Some gh) [] O -> g2_hdr_ok gh -> 9 <= wb <= 15 -> g2_bufs gh h ->
  Zlength O <= max_u64 ->
  live_ok8 (head_live (init_live sp (16 + wb)) h headp hsh xb nb cb) -> zf_ok z -> zf_tout z = 0 ->
  g2_P wb gh O h 0 z (head_live (init_live sp (16 + wb)) h headp hsh xb nb cb).
Proof.
  intros wbd wb gh O sp z h headp hsh xb nb cb DF HOK W B LO LV ZF TZ.
  destruct (LAY wbd wb gh O DF HOK W LO) as (xfl & bs & XFL & EO & GOK & LY & NH & RW & FU).
  set (L := head_live (init_live sp (16 + wb)) h headp hsh xb nb cb) in *.
  destruct (g2t_init_s sp wb h headp hsh xb nb cb W)
    as (Sm & Sw & Sh & Sb & Ss & St & Swb & Sl & Shd & Lh).
  fold L in Sm, Sw, Sh, Sb, Ss, St, Swb, Sl, Shd, Lh.
  assert (HW8: hwf8 (set_h_done h 0)) by (destruct LV as (_ & _ & _ & H8 & _); rewrite <- Lh; exact H8).
  exists xfl, bs. split; [|split; [exact TZ|split]].
  - unfold g2_fix. repeat (split; [assumption|]). exact HW8.
  - pose proof (Zlength_nonneg O). lia.
  - left. split; [|split; [|split]].
    + constructor; rewrite ?Lh; auto.
    + rewrite Lh. apply J2_HEAD; auto; try lia.
      * unfold bb2. rewrite Sh, Sb, sublist_nil. split; reflexivity.
      * unfold hx0; split; reflexivity.
      * unfold hn0; split; reflexivity.
      * unfold hc0; split; reflexivity.
    + destruct LY as [_ L2 L3 _]. unfold ih_xs in L3. destruct (fl (g2_g gh xfl) 4); lia.
    + rewrite Sm. unfold HEAD, Zlib.proof.inflate.Model.TYPE. lia.
Qed.

Lemma g2t_call (CS: g2_cases_stmt) (LAY: g2_lay_stmt /\ g2_out_stmt)
    (BR: g2_type_kd_stmt /\ g2_canon_init_stmt) (LO: rtigw_loop_stmt) :
  forall wb gh O h0 pos z L strmp ib inp o aout r z' st' ow,
    g2_P wb gh O h0 pos z L -> g2_call_pre O pos z L strmp ib inp o aout ->
    inflate_rel Z_FINISH strmp (offer_z z (in_ptr ib 0) (Zlength inp) (out_ptr o 0) aout) (Some L) ib inp (Some o)
      r z' st' ow ->
    r <> Z_MEM_ERROR ->
    exists L', st' = Some L' /\ 0 <= zf_ai z' <= Zlength inp /\ zf_ni z' = in_ptr ib (Zlength inp - zf_ai z') /\
      zf_ao z' = aout /\ zf_no z' = out_ptr o 0 /\ ow = [] /\
      (r = Z_BUF_ERROR -> pos + (Zlength inp - zf_ai z') < Zlength O ->
         g2_P wb gh O h0 (pos + (Zlength inp - zf_ai z')) z' L') /\
      (r <> Z_BUF_ERROR \/ pos + (Zlength inp - zf_ai z') = Zlength O ->
         g2_hdr_out gh h0 (l_s L') (l_h L')).
Proof.
  intros wb gh O h0 pos z L strmp ib inp o aout r z' st' ow (xfl & bs & FX & TZ & PR & PHD) CP REL NM.
  destruct (g2_rel O pos z L strmp ib inp o aout r z' st' ow CP REL) as (res & winp & RUN & Er & Eow & Ez & Est).
  subst r ow z' st'.
  assert (RES: g2_res_ok wb gh O h0 xfl bs pos inp aout res).
  { destruct PHD as [PH|PD].
    - exact (g2_call_h CS (proj1 BR) LO wb gh O h0 xfl bs pos z L strmp ib inp o aout res FX TZ PR PH CP RUN NM).
    - exact (g2_call_d (proj2 BR) LO wb gh O h0 xfl bs pos z L strmp ib inp o aout res FX TZ PR PD CP RUN NM). }
  destruct RES as (RI & SNX & OW & SOW & AOT & TO & PH').
  destruct (g2_zafter (offer_z z (in_ptr ib 0) (Zlength inp) (out_ptr o 0) aout) ib o res inp aout RI SOW AOT SNX)
    as (ZA & ZA1 & ZN & ZAO & ZNO & ZT).
  set (z' := z_after (offer_z z (in_ptr ib 0) (Zlength inp) (out_ptr o 0) aout) ib o res) in *.
  assert (USED: Zlength inp - zf_ai z' = m_snx (r_m res)) by lia.
  rewrite USED in ZN |- *.
  pose proof FX as (W & HOK & BUF & XFL & EO & GOK & LY & NH & RW & FU & HW8).
  destruct (g2_pre_facts O pos z L strmp ib inp o aout PR CP) as ((_ & PL & _) & _).
  set (L' := Live (l_sp L) winp (m_s (r_m res)) (m_h (r_m res)) (l_headp L) (l_hsh L) (l_xb L) (l_nb L) (l_cb L)).
  exists L'. split; [reflexivity|]. split; [exact ZA1|]. split; [exact ZN|]. split; [exact ZAO|].
  split; [exact ZNO|]. split; [exact OW|].
  assert (LH: ih_nh (g2_g gh xfl) <= Zlength O) by exact (l2_len _ _ LY).
  split.
  - intros _ LT. exists xfl, bs. split; [exact FX|]. split; [rewrite ZT; exact TO|]. split; [lia|].
    destruct PH' as [(_ & E & PH') | PD']; [left; rewrite E; exact PH' | right; exact PD'].
  - intros END. destruct PH' as [(RB & E & (_ & _ & PN & _)) | PD'].
    + exfalso. destruct END as [N|N]; [exact (N RB) | rewrite E in N; lia].
    + destruct PD' as (DV & HD & DN & X1 & X2 & X3).
      pose proof (g2_dinv_mode _ _ _ _ _ DV) as MD.
      destruct DV as (_ & (_ & _ & _ & GF) & _).
      apply (proj2 LAY gh xfl h0 (l_s L') (l_h L') HOK BUF XFL HD); auto.
      * apply g2_hdr_mode_after. cbn [l_s L']. lia.
      * cbn [l_s L']. apply GF; [reflexivity | unfold HEAD, Zlib.proof.inflate.Model.TYPE in *; lia
                                 | unfold FLAGS, Zlib.proof.inflate.Model.TYPE in *; lia].
Qed.

Lemma rtg2_itheory : g2_ifacts_stmt.
Proof.
  exists g2_P. constructor.
  - intros wb gh O h0 pos z L (xfl & bs & _ & _ & PR & _). exact PR.
  - intros wbd wb gh O sp z h headp hsh xb nb cb DF HOK W B LO LV ZF TZ.
    exact (g2t_init (proj1 g2_lay_out) wbd wb gh O sp z h headp hsh xb nb cb DF HOK W B LO LV ZF TZ).
  - exact (g2t_call g2_cases g2_lay_out (conj (proj1 g2_bridge) (proj2 g2_bridge (proj1 rtigw))) (proj2 rtigw)).
Qed.
