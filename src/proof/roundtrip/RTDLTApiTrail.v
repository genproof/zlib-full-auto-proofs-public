(** * deflate_api theory: stage 9 of deflate(), the trailer

    [c_deflate_trailer] after the compression stage (nothing pending; FINISH with all input consumed when the
    flush is Z_FINISH): Z_OK, or Z_STREAM_END with the trailer flushed, [Iend], and what deflate_api checks
    ([final_ok], from [final_ok_of]). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDLTApiOut Zlib.proof.roundtrip.RTDLTApiArith.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** Helpers *)
Lemma tk_pend_nil : forall s, d_pending s = 0 -> pend s = [].
Proof. intros s H. unfold pend. rewrite H, Z.add_0_r. apply sublist_nil. Qed.

Lemma tk_core_eq_wrap : forall s w, core_eq s (set_d_wrap s w).
Proof.
  intros s w. exact (core_eq_api_setters s (d_status s) (d_last_flush s) w (d_gzhead s)).
Qed.

Lemma tk_room : forall s, prm s -> 8 <= d_pending_buf_size s.
Proof.
  intros s (_ & _ & _ & Hhb & _ & _ & _ & HL & Hpbs & _).
  assert (2 ^ 7 <= 2 ^ (d_hash_bits s - 1)) by (apply Z.pow_le_mono_r; lia).
  lia.
Qed.

Lemma tk_put_trailer : forall s a t, prm s -> outok s -> d_pending s = 0 -> d_sym_next s = 0 ->
  1 <= d_wrap s <= 2 ->
  exists s1,
    (if d_wrap s =? 2 then
       c_dput_bytes s [Z.land a 255; Z.land (Z.shiftr a 8) 255; Z.land (Z.shiftr a 16) 255;
                       Z.land (Z.shiftr a 24) 255; Z.land t 255; Z.land (Z.shiftr t 8) 255;
                       Z.land (Z.shiftr t 16) 255; Z.land (Z.shiftr t 24) 255]
     else
       let* s := c_putShortMSB s (u32 (Z.shiftr a 16)) in
       c_putShortMSB s (u32 (Z.land a 65535))) = Some s1 /\
    pend s1 = trailer (d_wrap s) a t /\ outok s1 /\ core_eq s s1 /\ api_eq s s1 /\
    d_bi_valid s1 = d_bi_valid s.
Proof.
  intros s a t Hp Ho Hpd Hsym Hw.
  pose proof (tk_room s Hp) as Hr.
  assert (Hpo : d_po s = 0) by (destruct Ho as (_ & _ & _ & _ & _ & X); auto).
  pose proof (tk_pend_nil s Hpd) as Hpn.
  unfold trailer.
  destruct (Z.eqb_spec (d_wrap s) 2) as [E2|E2].
  - match goal with |- exists s1, c_dput_bytes _ ?l = _ /\ _ =>
      edestruct (dput_bytes_ok s l) as (s1 & E & Hpe & Ho1 & Hc & Ha & Hpo1 & Hb & Hpd1); eauto end.
    { rewrite Hpd. cbn. lia. }
    exists s1. split; [exact E|]. rewrite E2. cbn [Z.eqb Pos.eqb]. rewrite Hpe, Hpn. auto.
  - edestruct (putShortMSB2_ok s (u32 (Z.shiftr a 16)) (u32 (Z.land a 65535)))
      as (s1 & E & Hpe & Ho1 & Hc & Ha & Hpo1 & Hb & Hpd1); eauto.
    { lia. }
    exists s1. split; [exact E|].
    replace (d_wrap s) with 1 by lia. cbn [Z.eqb Pos.eqb]. rewrite Hpe, Hpn. auto.
Qed.

Lemma tk_bytes_app : forall l1 l2, bytes l1 -> bytes l2 -> bytes (l1 ++ l2).
Proof. intros l1 l2 H1 H2. unfold bytes in *. apply Forall_app. auto. Qed.

Lemma tk_bytes_app_r : forall l1 l2, bytes (l1 ++ l2) -> bytes l2.
Proof. intros l1 l2 H. unfold bytes in *. apply Forall_app in H. tauto. Qed.

Lemma tk_bytes_app_l : forall l1 l2, bytes (l1 ++ l2) -> bytes l1.
Proof. intros l1 l2 H. unfold bytes in *. apply Forall_app in H. tauto. Qed.

Lemma tk_final : forall dict wrap D O H body a t,
  0 <= wrap <= 2 -> hdr_good dict wrap H -> bytes O -> bytes D -> chk_ok wrap D a ->
  (wrap = 2 -> t = Zlength D) -> O = H ++ body ++ trailer wrap a t -> final_ok dict wrap D O a.
Proof.
  intros dict wrap D O H body a t Hw Hh HO HD Hc Ht E. subst O.
  apply final_ok_of; auto.
  apply tk_bytes_app_r in HO. apply tk_bytes_app_l in HO. exact HO.
Qed.

Lemma tk_zrun_step : forall inb aout tin tout z x,
  zrun inb aout tin tout z -> Zlength x <= z_avail_out z -> bytes x ->
  zrun inb aout tin tout
    (mkST (z_in z) (z_next_in z) (z_avail_in z) (z_total_in z) (z_out z ++ x)
          (z_avail_out z - Zlength x) (z_total_out z + Zlength x) (z_adler z) (z_msg z)).
Proof.
  intros inb aout tin tout z x (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8) Hx Hb.
  unfold zrun; cbn [z_in z_next_in z_avail_in z_total_in z_out z_avail_out z_total_out].
  rewrite Zlength_app.
  repeat split; try lia; auto.
  apply tk_bytes_app; auto.
Qed.

Lemma trailer_ok : forall W HI dict wrap D O inb aout tin tout flush s z,
  core_facts W -> hdr_facts HI ->
  Mid W HI dict wrap D O inb aout tin tout flush s z ->
  d_pending s = 0 -> 0 <= flush <= 5 -> aout <= 1048576 ->
  (flush = Z_FINISH -> d_status s = FINISH_STATE) ->
  (d_status s = BUSY_STATE \/ (d_status s = FINISH_STATE /\ z_avail_in z = 0)) ->
  exists s4 z4 c, c_deflate_trailer s z flush = Some (s4, z4, c) /\ d_gzhead s4 = d_gzhead s /\
    ((c = Z_OK /\ Mid W HI dict wrap D O inb aout tin tout flush s4 z4) \/
     (c = Z_STREAM_END /\ flush = Z_FINISH /\ z_avail_in z4 = 0 /\ zrun inb aout tin tout z4 /\ Iend s4 /\
      final_ok dict wrap (D ++ sublist 0 (z_next_in z4) inb) (O ++ z_out z4) (z_adler z4))).
Proof.
  intros W HI dict wrap D O inb aout tin tout flush s z HW HH HM Hpd Hfl Haout Hfs Hst.
  unfold c_deflate_trailer.
  destruct (Z.eqb_spec flush Z_FINISH) as [EF|NF].
  2: { cbn [negb]. exists s, z, Z_OK. split; [reflexivity|]. split; [reflexivity|]. left. auto. }
  subst flush. cbn [negb]. specialize (Hfs eq_refl).
  assert (Hai0 : z_avail_in z = 0).
  { destruct Hst as [Hst|[_ Hst]]; [|exact Hst]. rewrite Hfs in Hst. unfold FINISH_STATE, BUSY_STATE in Hst. lia. }
  clear Hst.
  pose proof HM as HM0.
  destruct HM as (Hz & Hsz1 & Hsz2 & HIa).
  pose proof Hz as Hz0.
  destruct Hz as (Hzin & Hni & Hai & Hti & Hao & Hzo & Hto & Hbo).
  destruct HIa as (HWs & Hos & Hwr & Hw2 & Hbd & Hld & Hlf & Hgz & Htout & HbO & HbD & Htin & Hfin & Hdz & Hph).
  destruct Hph as [H0 | [Hlf2 [H1 | [H2 | H3]]]].
  { exfalso. destruct H0 as [[[Hs _]|[Hs _]] _]; rewrite Hfs in Hs; unfold FINISH_STATE, INIT_STATE, GZIP_STATE in Hs; lia. }
  { exfalso. destruct H1 as (_ & _ & _ & _ & _ & H & k & HIk & _).
    destruct (hf_status HI HH _ _ _ _ HIk) as (_ & _ & Hs & _). rewrite Hfs in Hs.
    unfold FINISH_STATE, EXTRA_STATE, NAME_STATE, COMMENT_STATE, HCRC_STATE in Hs; lia. }
  { exfalso. destruct H2 as (Hs & _). rewrite Hfs in Hs. unfold FINISH_STATE, BUSY_STATE in Hs. lia. }
  destruct H3 as (_ & Hla & Hsy & Hbv & HOne & Hchk & H & body & Hhg & Hcase).
  pose proof (tk_pend_nil s Hpd) as Hpn.
  destruct (Z.leb_spec (d_wrap s) 0) as [Hw0|Hw0].
  - exists s, z, Z_STREAM_END. split; [reflexivity|]. split; [reflexivity|]. right.
    split; [reflexivity|]. split; [reflexivity|]. split; [exact Hai0|]. split; [exact Hz0|].
    split.
    { unfold Iend. split; [exact Hfs|]. split; [lia|]. split; [exact Hpd|]. split; [exact Hla|]. exact Hlf. }
    rewrite Hpn, app_nil_r in Hcase.
    apply tk_final with (H := H) (body := body) (t := z_total_in z); auto.
    { intros E2. specialize (Hw2 E2). subst dict. rewrite Zlength_nil in Htin. lia. }
    destruct Hcase as [[Hdw HO]|[Hwp [Hdw HO]]]; [|exact HO].
    assert (Ew : wrap = 0) by lia. rewrite Ew.
    change (trailer 0 (z_adler z) (z_total_in z)) with (@nil Z). rewrite app_nil_r. exact HO.
  - destruct Hcase as [[Hdw HO]|[? [? _]]]; [|lia].
    rewrite Hpn, app_nil_r in HO.
    pose proof (cf_prm W HW s HWs) as Hprm.
    edestruct (tk_put_trailer s (z_adler z) (z_total_in z)) as (s1 & E1 & Hp1 & Ho1 & Hc1 & Ha1 & Hb1);
      eauto; [lia|].
    rewrite E1. cbn [bind].
    assert (Hzo0 := Zlength_nonneg (z_out z)). assert (HO0 := Zlength_nonneg O).
    rewrite Zlength_app in Htout.
    edestruct (flush_pending_ok s1 z) as (s' & x & Ef & Hpx & Hlx & Hbx & Ho' & Hc' & Ha' & Hb' & Hpd' & Hpo');
      auto; try lia.
    rewrite Ef. cbn [bind].
    assert (Hdw' : d_wrap s' = wrap).
    { destruct Ha1 as (_ & W1 & _), Ha' as (_ & W2 & _). lia. }
    rewrite Hdw'. replace (wrap >? 0) with true by (symmetry; apply Z.gtb_lt; lia).
    eexists _, _, _. split; [reflexivity|].
    destruct Ha1 as (As1 & Aw1 & Ag1 & Ai1 & Al1 & Am1), Ha' as (As2 & Aw2 & Ag2 & Ai2 & Al2 & Am2).
    split; [cbn [d_gzhead set_d_wrap]; congruence|].
    assert (Hc4 : core_eq s (set_d_wrap s' (- wrap))).
    { eapply core_eq_trans; [exact Hc1|]. eapply core_eq_trans; [exact Hc'|]. apply tk_core_eq_wrap. }
    pose proof (core_eq_fields _ _ Hc4) as (_ & _ & _ & _ & _ & _ & Hla4 & _ & Hsy4 & _).
    cbn [d_lookahead d_sym_next set_d_wrap] in Hla4, Hsy4.
    assert (Hx : x ++ pend s' = trailer wrap (z_adler z) (z_total_in z)) by congruence.
    assert (Hxa : Zlength x <= z_avail_out z) by lia.
    pose proof (tk_zrun_step inb aout tin tout z x Hz0 Hxa Hbx) as Hz4.
    change (d_pending (set_d_wrap s' (- wrap))) with (d_pending s').
    destruct (Z.eqb_spec (d_pending s') 0) as [P0|P0]; cbn [negb].
    + right. cbn [z_avail_in z_next_in z_out z_adler].
      split; [reflexivity|]. split; [reflexivity|]. split; [exact Hai0|]. split; [exact Hz4|].
      split.
      { unfold Iend. cbn [d_status d_wrap d_pending d_lookahead d_last_flush set_d_wrap].
        split; [congruence|]. split; [lia|]. split; [exact P0|]. split; [congruence|]. rewrite Al2, Al1. exact Hlf. }
      rewrite (tk_pend_nil s' P0), app_nil_r in Hx.
      apply tk_final with (H := H) (body := body) (t := z_total_in z); auto.
      { rewrite app_assoc. apply tk_bytes_app; auto. }
      { intros E2. specialize (Hw2 E2). subst dict. rewrite Zlength_nil in Htin. lia. }
      rewrite app_assoc, HO, Hx, app_assoc. reflexivity.
    + left. split; [reflexivity|].
      unfold Mid. split; [exact Hz4|]. split; [exact Hsz1|]. split; [exact Hsz2|].
      cbn [z_next_in z_out z_total_in z_total_out z_adler].
      unfold Iapi.
      split; [exact (cf_frame W HW s _ HWs Hc4)|].
      split; [exact Ho'|].
      split; [exact Hwr|]. split; [exact Hw2|]. split; [exact Hbd|]. split; [exact Hld|].
      cbn [d_last_flush d_gzhead d_status set_d_wrap].
      split; [rewrite Al2, Al1; exact Hlf|].
      split; [intros h Eh; apply Hgz; congruence|].
      split; [rewrite app_assoc, !Zlength_app; lia|].
      split; [rewrite app_assoc; apply tk_bytes_app; auto|].
      split; [exact HbD|]. split; [exact Htin|].
      split; [intros _; exact (Hfin Hfs)|].
      split; [intros Hn; pose proof (core_eq_fields _ _ Hc4) as (_ & _ & _ & _ & B4 & S4 & L4 & _);
              rewrite B4, S4, L4; exact (Hdz Hn)|].
      right. split; [congruence|]. right. right.
      unfold ph3. cbn [d_status d_wrap d_bi_valid d_lookahead d_sym_next set_d_wrap].
      split; [congruence|]. split; [congruence|]. split; [congruence|].
      split; [change (d_bi_valid (set_d_wrap s' (- wrap))) with (d_bi_valid s'); lia|].
      split.
      { intros Hw Hn. apply HOne; auto. rewrite app_assoc in Hn. apply app_eq_nil in Hn. tauto. }
      split; [exact Hchk|].
      exists H, body. split; [exact Hhg|]. right. split; [lia|]. split; [reflexivity|].
      change (pend (set_d_wrap s' (- wrap))) with (pend s').
      rewrite <- !app_assoc, Hx, app_assoc, HO, <- app_assoc. reflexivity.
Qed.
