(* Law rt_gzip_header on the round-2 harness, inflate side: the invariant of the harness's inflate loop and one
   call of it.

   Between two calls, pos bytes of O consumed, the stream is in one of two phases: inside the gzip header
   ([g2_ph]: the header state J2 at position pos, the call left in a header mode), or after it ([g2_pd]: the decode
   invariant of the generalized decode theory at pos, the gz_header complete).  A call from [g2_ph] runs the header
   cases (G2IHLoop) and either leaves inside the header (Z_BUF_ERROR, all of its input consumed) or reaches the
   TYPE loop head, from where it is a decode call (G2IDec); a call from [g2_pd] is a decode call from its start.
   [g2_fix]: what does not change: the stream O (header, no data), its ghost and layout, the decode context. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.rt_gzip_header.G2IDefs.
Require Import Zlib.proof.roundtrip.RTIGW.
Require Import Zlib.proof.harness.rt_gzip_header.G2IHLoop.
Require Import Zlib.proof.harness.rt_gzip_header.G2IDec.
Require Import Zlib.proof.harness.rt_gzip_header.G2IBridge.
Require Zlib.proof.uncompr.URunFrame.
Require Zlib.proof.harness.inflate_header.IHTCall.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* The invariant                                                                                   *)

Definition g2_fix (wb: Z) (gh: DS.gzh) (O: list Z) (h0: hstate) (xfl: Z) (bs: list F.block) : Prop :=
  9 <= wb <= 15 /\ g2_hdr_ok gh /\ g2_bufs gh h0 /\ (xfl = 0 \/ xfl = 2 \/ xfl = 4) /\
  O = F.stream_bytes (F.WGzip (g2_H gh xfl)) [] bs /\
  g2h_ok (g2_g gh xfl) /\ lay2 (g2_g gh xfl) O /\
  ih_nh (g2_g gh xfl) = Zlength (F.gz_bytes (g2_H gh xfl)) /\
  rtigw_ok (g2_G gh xfl wb bs O) /\ full (g2_G gh xfl wb bs O) = [] /\ hwf8 (set_h_done h0 0).

(* inside the header (h0: the gz_header given to inflateGetHeader, which set its done to 0) *)
Definition g2_ph (wb: Z) (gh: DS.gzh) (O: list Z) (h0: hstate) (xfl pos: Z) (s: istate) (h: hstate) : Prop :=
  Jc2 wb (set_h_done h0 0) s h /\
  J2 (g2_g gh xfl) O (set_h_done h0 0) pos s h (i_hold s) (i_bits s) /\
  pos < ih_nh (g2_g gh xfl) /\ i_mode s <> Zlib.proof.inflate.Model.TYPE.

(* after the header *)
Definition g2_pd (wb: Z) (gh: DS.gzh) (O: list Z) (h0: hstate) (xfl: Z) (bs: list F.block) (pos: Z)
    (s: istate) (h: hstate) : Prop :=
  dinv (g2_G gh xfl wb bs O) pos [] s 0 /\ i_head s = true /\
  ih_done_ok (g2_g gh xfl) (set_h_done h0 0) h /\
  h_extra_max h = h_extra_max h0 /\ h_name_max h = h_name_max h0 /\ h_comm_max h = h_comm_max h0.

Definition g2_P : g2_inv := fun wb gh O h0 pos z L =>
  exists xfl bs, g2_fix wb gh O h0 xfl bs /\ zf_tout z = 0 /\ 0 <= pos <= Zlength O /\
    (g2_ph wb gh O h0 xfl pos (l_s L) (l_h L) \/ g2_pd wb gh O h0 xfl bs pos (l_s L) (l_h L)).

(* ---------------------------------------------------------------------------------------------- *)
(* Small facts                                                                                     *)

(* the modes of the decode invariant are after the header *)
Lemma g2_dinv_mode G pos out s t : dinv G pos out s t ->
  Zlib.proof.inflate.Model.TYPE <= i_mode s <= DONE.
Proof.
  intros (A & _). destruct A as (_ & A).
  unfold HEAD, FLAGS, TIME, OS, Zlib.proof.inflate.Model.TYPE, TYPEDO, STORED, COPY_, COPY, TABLE,
    LENLENS, CODELENS, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT, CHECK, LENGTH, DONE in *.
  repeat match goal with H: _ \/ _ |- _ => destruct H end;
    repeat match goal with H: _ /\ _ |- _ => destruct H end; try contradiction; lia.
Qed.

Lemma g2_hdr_mode_after md : Zlib.proof.inflate.Model.TYPE <= md -> hdr_mode md = false.
Proof.
  intros M. unfold hdr_mode. apply andb_false_iff. right. apply Z.leb_gt.
  unfold Zlib.proof.inflate.Model.TYPE in M. change IM.HCRC with 16188. lia.
Qed.

(* the modes of J2 *)
Lemma g2_J2_vmode g src h0 P s h hold bits : J2 g src h0 P s h hold bits ->
  HEAD <= i_mode s <= Zlib.proof.inflate.Model.TYPE.
Proof.
  intros J. destruct J;
    match goal with E: i_mode s = _ |- _ => rewrite E end;
    unfold HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC, Zlib.proof.inflate.Model.TYPE; lia.
Qed.

(* J2 reads the mode, last, check, flags and length of the state *)
Lemma g2_J2_proj g src h0 P s s' h hold bits :
  J2 g src h0 P s h hold bits ->
  i_mode s' = i_mode s -> i_last s' = i_last s -> i_check s' = i_check s -> i_flags s' = i_flags s ->
  i_length s' = i_length s ->
  J2 g src h0 P s' h hold bits.
Proof.
  intros H Em El Ec Ef En.
  assert (Ck: forall k, ck2 g src s k -> ck2 g src s' k) by (unfold ck2; intros k C F; rewrite Ec; auto).
  assert (Fg: fg g s -> fg g s') by (unfold fg; rewrite Ef; auto).
  destruct H;
    [ eapply J2_HEAD | eapply J2_FLAGS | eapply J2_TIME | eapply J2_OS | eapply J2_EXLEN | eapply J2_EXTRA
    | eapply J2_NAME | eapply J2_COMMENT | eapply J2_HCRC | eapply J2_TYPE ];
    rewrite ?Em, ?El, ?Ec, ?En; eauto.
Qed.

(* at the TYPE loop head, the header is complete *)
Lemma g2_J2_type g src h0 P s h hold bits : J2 g src h0 P s h hold bits ->
  i_mode s = Zlib.proof.inflate.Model.TYPE -> ih_done_ok g h0 h /\ P = ih_nh g.
Proof.
  intros J E. destruct J; try (exfalso; rewrite E in *;
    match goal with H: Zlib.proof.inflate.Model.TYPE = _ |- _ => discriminate H end); auto.
Qed.

(* the call's outcome in the stream fields *)
Lemma g2_zafter z1 ib o res inp aout :
  m_inp (r_m res) = inp -> m_sow (r_m res) = 0 -> m_aout (r_m res) = aout ->
  0 <= m_snx (r_m res) <= Zlength inp ->
  let z' := z_after z1 ib o res in
  zf_ai z' = Zlength inp - m_snx (r_m res) /\ 0 <= zf_ai z' <= Zlength inp /\
  zf_ni z' = in_ptr ib (Zlength inp - zf_ai z') /\ zf_ao z' = aout /\ zf_no z' = out_ptr o 0 /\
  zf_tout z' = m_tout (r_m res).
Proof.
  intros I S A N. cbv zeta. unfold z_after. cbv zeta. cbn [zf_ai zf_ni zf_ao zf_no zf_tout].
  rewrite I, S, A. split; [reflexivity|]. split; [lia|]. split; [f_equal; lia|].
  split; [lia|]. split; reflexivity.
Qed.

(* the offered fields *)
Lemma g2_offer_ok z ni ai no ao : zf_ok z -> 0 <= ai <= umax -> 0 <= ao <= umax -> zf_ok (offer_z z ni ai no ao).
Proof.
  intros (Z1 & Z2 & Z3 & Z4 & Z5 & Z6) A B. unfold offer_z, zf_ok, umax in *.
  cbn [zf_ai zf_ao zf_tin zf_tout zf_dt zf_adler]. change Int.max_unsigned with 4294967295.
  exact (conj A (conj B (conj Z3 (conj Z4 (conj Z5 Z6))))).
Qed.

(* inflate(): a live stream, an input buffer and an output buffer: the model's run *)
Lemma g2_rel O pos z L strmp ib inp o aout r z' st' ow :
  g2_call_pre O pos z L strmp ib inp o aout ->
  inflate_rel Z_FINISH strmp (offer_z z (in_ptr ib 0) (Zlength inp) (out_ptr o 0) aout) (Some L) ib inp (Some o)
    r z' st' ow ->
  exists res winp,
    run2 Z_FINISH lenfix_list distfix_list (m_init (offer_z z (in_ptr ib 0) (Zlength inp) (out_ptr o 0) aout) L inp) res /\
    r = r_ret res /\ ow = m_ow (r_m res) /\
    z' = z_after (offer_z z (in_ptr ib 0) (Zlength inp) (out_ptr o 0) aout) ib o res /\
    st' = Some (Live (l_sp L) winp (m_s (r_m res)) (m_h (r_m res)) (l_headp L) (l_hsh L) (l_xb L) (l_nb L) (l_cb L)).
Proof.
  intros (LV & SW & ZF & SN & IB & INOK & OUTOK & LA & LI & INP) REL.
  destruct REL as [(BAD & _) | (_ & L0 & o0 & res & winp & EL & EO & RUN & _ & ER & EOW & EZ & _ & EST)].
  { exfalso. destruct BAD as [B | [B | [B _]]].
    - unfold is_live in B. match type of B with context [if ?c then _ else _] => destruct c end; congruence.
    - discriminate.
    - contradiction. }
  injection EL as <-. injection EO as <-.
  exists res, winp. auto.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* One call                                                                                        *)

(* the outcome of a call: input consumed from pos, nothing written, total_out still 0; then inside the header
   (Z_BUF_ERROR, all the input consumed) or after it *)
Definition g2_res_ok (wb: Z) (gh: DS.gzh) (O: list Z) (h0: hstate) (xfl: Z) (bs: list F.block) (pos: Z)
    (inp: list Z) (aout: Z) (res: result) : Prop :=
  m_inp (r_m res) = inp /\ 0 <= m_snx (r_m res) <= Zlength inp /\ m_ow (r_m res) = [] /\ m_sow (r_m res) = 0 /\
  m_aout (r_m res) = aout /\ m_tout (r_m res) = 0 /\
  ((r_ret res = Z_BUF_ERROR /\ m_snx (r_m res) = Zlength inp /\
    g2_ph wb gh O h0 xfl (pos + Zlength inp) (m_s (r_m res)) (m_h (r_m res))) \/
   g2_pd wb gh O h0 xfl bs (pos + m_snx (r_m res)) (m_s (r_m res)) (m_h (r_m res))).

Lemma g2_pre_facts O pos z L strmp ib inp o aout :
  0 <= pos <= Zlength O -> g2_call_pre O pos z L strmp ib inp o aout ->
  ctx2 O pos inp /\ bytes_ok inp /\ 0 <= aout <= 4294967295 /\ Zlength inp <= 4294967295.
Proof.
  intros PR (LV & SW & ZF & SN & IB & INOK & OUTOK & LA & LI & INP).
  assert (LI2: Zlength inp <= Zlength O - pos /\ Zlength inp <= umax).
  { rewrite LI. unfold clipz. lia. }
  unfold umax in *.
  split; [split; [lia | split; [lia | exact INP]]|].
  split; [destruct ib; [contradiction | apply INOK]|].
  split; [destruct o; split; [apply OUTOK | lia] | lia].
Qed.

(* a call that starts inside the header *)
Lemma g2_call_h (CS: g2_cases_stmt) (BR: g2_type_kd_stmt) (LO: rtigw_loop_stmt) :
  forall wb gh O h0 xfl bs pos z L strmp ib inp o aout res,
  g2_fix wb gh O h0 xfl bs -> zf_tout z = 0 -> 0 <= pos <= Zlength O ->
  g2_ph wb gh O h0 xfl pos (l_s L) (l_h L) ->
  g2_call_pre O pos z L strmp ib inp o aout ->
  run2 Z_FINISH lenfix_list distfix_list (m_init (offer_z z (in_ptr ib 0) (Zlength inp) (out_ptr o 0) aout) L inp) res ->
  r_ret res <> Z_MEM_ERROR ->
  g2_res_ok wb gh O h0 xfl bs pos inp aout res.
Proof.
  intros wb gh O h0 xfl bs pos z L strmp ib inp o aout res FX TZ PR PH CP RUN NM.
  destruct (g2_pre_facts O pos z L strmp ib inp o aout PR CP) as (CX & BI & AO & LI).
  pose proof FX as (W & HOK & BUF & XFL & EO & GOK & LY & NH & RW & FU & HW8).
  destruct PH as (JC & JJ & PN & NT).
  pose proof CP as (LV & SW & ZF & SN & IB & INOK & OUTOK & LA & LI' & INP).
  set (g := g2_g gh xfl) in *. set (h0' := set_h_done h0 0) in *.
  set (z1 := offer_z z (in_ptr ib 0) (Zlength inp) (out_ptr o 0) aout) in *.
  set (m0 := m_init z1 L inp) in *.
  assert (M0s: m_s m0 = l_s L).
  { unfold m0, m_init. cbv zeta. rewrite (proj2 (Z.eqb_neq _ _) NT). reflexivity. }
  assert (M0m: m_mode m0 <> Zlib.proof.inflate.Model.TYPE) by (unfold m_mode; rewrite M0s; exact NT).
  assert (K0: Km2 g O h0' wb pos inp aout (zf_tin z) m0).
  { destruct LV as (_ & SWF & _).
    destruct ZF as (_ & _ & Z3 & _ & _ & Z6).
    constructor; unfold m0, m_init; cbv zeta; rewrite (proj2 (Z.eqb_neq _ _) NT);
      cbn [m_s m_h m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave m_adler m_tin m_tout m_snx m_sow
           z1 offer_z zf_ao zf_adler zf_msg zf_tin zf_tout].
    - reflexivity.
    - pose proof (Zlength_nonneg inp). lia.
    - reflexivity.
    - reflexivity.
    - exact TZ.
    - reflexivity.
    - left; reflexivity.
    - exact JC.
    - rewrite Z.add_0_r. exact JJ.
    - exact SWF.
    - unfold lrange. repeat split; auto; lia. }
  pose proof (URunFrame.run2_frame _ _ _ _ _
                ltac:(unfold URunFrame.vmode; rewrite M0s; pose proof (g2_J2_vmode _ _ _ _ _ _ _ _ JJ);
                      unfold BAD, Zlib.proof.inflate.Model.TYPE in *; lia) RUN)
    as (FI & FA & FS & FH & _).
  destruct RUN as (o0 & LP & RO).
  destruct (g2l_loop CS g O h0' wb pos inp aout (zf_tin z) Z_FINISH m0 o0 GOK HW8 LY CX LP K0 eq_refl M0m)
    as [(m' & -> & K' & L1) | (mT & KT & LT & MT & LPT)].
  - (* the call leaves inside the header *)
    pose proof (jc2_wsize _ _ _ _ (km2_jc _ _ _ _ _ _ _ _ _ K')) as Ws.
    pose proof (jc2_total _ _ _ _ (km2_jc _ _ _ _ _ _ _ _ _ K')) as Tt.
    inversion RO as [U Wn | ]; subst res.
    { exfalso. rewrite (Zlib.proof.harness.inflate_header.IHTCall.ihl_leave_ok Z_FINISH m' Ws
                          (km2_out _ _ _ _ _ _ _ _ _ K') (km2_ow _ _ _ _ _ _ _ _ _ K')) in U. discriminate. }
    destruct (g2l_fin m' Ws (km2_out _ _ _ _ _ _ _ _ _ K') (km2_ow _ _ _ _ _ _ _ _ _ K')
                (km2_tout _ _ _ _ _ _ _ _ _ K') Tt (km2_ret _ _ _ _ _ _ _ _ _ K'))
      as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17 & R18 &
          R19 & R20 & _).
    destruct (km2_lv _ _ _ _ _ _ _ _ _ K') as [E|(_ & NX & PL & NT')]; [rewrite E in L1; discriminate|].
    destruct (km2_fr _ _ _ _ _ _ _ _ _ K') as (FA' & _).
    unfold g2_res_ok. rewrite R6, R5, NX, R2, R3, R4, FA', R7.
    rewrite (km2_inp _ _ _ _ _ _ _ _ _ K').
    split; [reflexivity|]. split; [pose proof (Zlength_nonneg inp); lia|].
    do 4 (split; [reflexivity|]).
    left. split; [exact R1|]. split; [reflexivity|].
    pose proof (km2_jc _ _ _ _ _ _ _ _ _ K') as JC'.
    split; [|split; [|split]].
    + destruct JC' as [A1 A2 A3 A4 A5 A6 A7 A8].
      constructor; rewrite ?R8, ?R14, ?R15, ?R16, ?R17, ?R18; auto.
    + rewrite R19, R20, R8. rewrite <- NX.
      apply (g2_J2_proj _ _ _ _ _ _ _ _ _ (km2_j _ _ _ _ _ _ _ _ _ K')); auto.
    + rewrite <- NX. exact PL.
    + rewrite R9. exact NT'.
  - (* the header ends in the call: the rest is a decode call from the TYPE loop head *)
    destruct (km2_fr _ _ _ _ _ _ _ _ _ KT) as (FAT & _).
    destruct ZF as (_ & _ & Z3 & _).
    destruct (BR wb gh xfl bs O h0' pos inp aout (zf_tin z) mT W XFL EO GOK LY NH RW CX LI AO
                ltac:(unfold lrange; lia) KT LT MT) as (KD & MW).
    assert (HK: SK.hk mT) by (right; rewrite MT; apply g2_hdr_mode_after; lia).
    destruct (g2d_tail LO gh xfl wb bs O pos inp mT o0 res RW FU CX KD MW LT HK LPT RO NM)
      as (RC & SNX & OW & SOW & AOT & HH & TO & DV).
    unfold g2_res_ok. rewrite FI. split; [reflexivity|]. split; [exact SNX|]. split; [exact OW|].
    split; [exact SOW|]. split; [rewrite AOT; exact FAT|]. split; [exact TO|].
    right. split; [exact DV|]. split; [rewrite FH, M0s; exact (jc2_head _ _ _ _ JC)|].
    destruct (g2_J2_type _ _ _ _ _ _ _ _ (km2_j _ _ _ _ _ _ _ _ _ KT) MT) as (DN & _).
    pose proof (km2_jc _ _ _ _ _ _ _ _ _ KT) as JCT.
    rewrite HH. split; [exact DN|].
    split; [exact (jc2_xmax _ _ _ _ JCT)|]. split; [exact (jc2_nmax _ _ _ _ JCT)|]. exact (jc2_cmax _ _ _ _ JCT).
Qed.

(* a call that starts after the header *)
Lemma g2_call_d (BR: g2_canon_init_stmt) (LO: rtigw_loop_stmt) :
  forall wb gh O h0 xfl bs pos z L strmp ib inp o aout res,
  g2_fix wb gh O h0 xfl bs -> zf_tout z = 0 -> 0 <= pos <= Zlength O ->
  g2_pd wb gh O h0 xfl bs pos (l_s L) (l_h L) ->
  g2_call_pre O pos z L strmp ib inp o aout ->
  run2 Z_FINISH lenfix_list distfix_list (m_init (offer_z z (in_ptr ib 0) (Zlength inp) (out_ptr o 0) aout) L inp) res ->
  r_ret res <> Z_MEM_ERROR ->
  g2_res_ok wb gh O h0 xfl bs pos inp aout res.
Proof.
  intros wb gh O h0 xfl bs pos z L strmp ib inp o aout res FX TZ PR PD CP RUN NM.
  destruct (g2_pre_facts O pos z L strmp ib inp o aout PR CP) as (CX & BI & AO & LI).
  pose proof FX as (W & HOK & BUF & XFL & EO & GOK & LY & NH & RW & FU & HW8).
  destruct PD as (DV0 & HD & DN & X1 & X2 & X3).
  pose proof CP as (LV & SW & ZF & SN & IB & INOK & OUTOK & LA & LI' & INP).
  set (z1 := offer_z z (in_ptr ib 0) (Zlength inp) (out_ptr o 0) aout) in *.
  set (m0 := m_init z1 L inp) in *.
  pose proof (g2_dinv_mode _ _ _ _ _ DV0) as MD.
  assert (MD0: Zlib.proof.inflate.Model.TYPE <= i_mode (m_s m0) <= DONE).
  { unfold m0, m_init. cbv zeta. destruct (i_mode (l_s L) =? Zlib.proof.inflate.Model.TYPE); cbn [m_s];
      [cbn; unfold TYPEDO, DONE, Zlib.proof.inflate.Model.TYPE; lia | exact MD]. }
  assert (ZF1: zf_ok z1) by (apply g2_offer_ok; [exact ZF | unfold umax; pose proof (Zlength_nonneg inp); lia
                                                 | unfold umax; lia]).
  destruct (BR (g2_G gh xfl wb bs O) pos L z1 inp RW ltac:(cbn [z1 offer_z zf_tout]; rewrite TZ; exact DV0)
              LV ZF1 ltac:(cbn [z1 offer_z zf_ao]; lia) LI BI) as (KD & MW).
  assert (VM: URunFrame.vmode (i_mode (m_s m0)))
    by (unfold URunFrame.vmode; unfold BAD, DONE, HEAD, Zlib.proof.inflate.Model.TYPE in *; lia).
  pose proof (URunFrame.run2_frame _ _ _ _ _ VM RUN) as (FI & FA & FS & FH & _).
  destruct RUN as (o0 & LP & RO).
  assert (HK: SK.hk m0) by (right; apply g2_hdr_mode_after; unfold m_mode; lia).
  destruct (g2d_tail LO gh xfl wb bs O pos inp m0 o0 res RW FU CX KD MW eq_refl HK LP RO NM)
    as (RC & SNX & OW & SOW & AOT & HH & TO & DV).
  unfold g2_res_ok. rewrite FI. split; [reflexivity|]. split; [exact SNX|]. split; [exact OW|].
  split; [exact SOW|]. split; [exact AOT|]. split; [exact TO|].
  right. split; [exact DV|].
  split; [rewrite FH; unfold m0, m_init; cbv zeta; destruct (_ =? _); exact HD|].
  rewrite HH. cbn [m0 m_init m_h]. auto.
Qed.
