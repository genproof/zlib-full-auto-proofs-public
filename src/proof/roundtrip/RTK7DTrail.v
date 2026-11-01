(* The trailer stage of deflate() (c_deflate_trailer) keeps Mid7 unless it returns Z_STREAM_END:
   RTDDfXTrail.trailer_ok for the streams of RTK7Defs, from core_facts7 and hdr_facts7.  The trailer bytes
   carry total_in, which Mid7 counts modulo 2^64, as deflate() writes it. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTK7DMid.
Require Import Zlib.proof.roundtrip.RTDDfXTrail.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(* writing [x] to the output keeps the running stream of the call (RTDDfXTrail.tk_zrun_step for zrun7) *)
Lemma tk_zrun7_step : forall inb aout tin tout z x,
  zrun7 inb aout tin tout z -> Zlength x <= z_avail_out z -> bytes x ->
  zrun7 inb aout tin tout
    (mkST (z_in z) (z_next_in z) (z_avail_in z) (z_total_in z) (z_out z ++ x)
          (z_avail_out z - Zlength x) (z_total_out z + Zlength x) (z_adler z) (z_msg z)).
Proof.
  intros inb aout tin tout z x (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8) Hx Hb.
  unfold zrun7; cbn [z_in z_next_in z_avail_in z_total_in z_out z_avail_out z_total_out].
  rewrite Zlength_app.
  repeat split; try lia; auto.
  apply tk_bytes_app; auto.
Qed.

Lemma trailer_ok7 : forall W HI dict wrap D O inb aout tin tout flush s z s4 z4 c,
  core_facts7 W -> hdr_facts7 HI ->
  Mid7 W HI dict wrap D O inb aout tin tout flush s z ->
  d_pending s = 0 -> 0 <= flush <= 5 ->
  (flush = Z_FINISH -> d_status s = FINISH_STATE) ->
  (d_status s = BUSY_STATE \/ (d_status s = FINISH_STATE /\ z_avail_in z = 0)) ->
  c_deflate_trailer s z flush = Some (s4, z4, c) ->
  d_gzhead s4 = d_gzhead s /\
  ((c = Z_OK /\ Mid7 W HI dict wrap D O inb aout tin tout flush s4 z4) \/ c = Z_STREAM_END).
Proof.
  intros W HI dict wrap D O inb aout tin tout flush s z s4 z4 c HW HH HM Hpd Hfl Hfs Hst E.
  unfold c_deflate_trailer in E.
  destruct (Z.eqb_spec flush Z_FINISH) as [EF|NF].
  2: { cbn [negb] in E. injection E as <- <- <-. split; [reflexivity|]. left. auto. }
  subst flush. cbn [negb] in E. specialize (Hfs eq_refl).
  destruct (Z.leb_spec (d_wrap s) 0) as [Hw0|Hw0].
  { injection E as <- <- <-. split; [reflexivity|]. right. reflexivity. }
  assert (Hai0 : z_avail_in z = 0).
  { destruct Hst as [Hst|[_ Hst]]; [|exact Hst]. rewrite Hfs in Hst. unfold FINISH_STATE, BUSY_STATE in Hst. lia. }
  clear Hst.
  destruct HM as (Hz & Hsz1 & Hsz2 & Hsz3 & Hsz4 & HIa).
  pose proof Hz as Hz0.
  destruct Hz as (Hzin & Hni & Hai & Hti & Hao & Hzo & Hto & Hbo).
  destruct HIa as (HWs & Hos & Hwr & Hw2 & Hbd & Hld & Hlf & Hgz & Htout & HbO & HbD & HlD & Htin & Hfin & Hdz
                   & Hph).
  destruct Hph as [H0 | [Hlf2 [H1 | [H2 | H3]]]].
  { exfalso. destruct H0 as [[[Hs _]|[Hs _]] _]; rewrite Hfs in Hs; unfold FINISH_STATE, INIT_STATE, GZIP_STATE in Hs; lia. }
  { exfalso. destruct H1 as (_ & _ & _ & _ & _ & H & k & HIk & _).
    destruct (hf7_status HI HH _ _ _ _ HIk) as (_ & _ & Hs & _). rewrite Hfs in Hs.
    unfold FINISH_STATE, EXTRA_STATE, NAME_STATE, COMMENT_STATE, HCRC_STATE in Hs; lia. }
  { exfalso. destruct H2 as (Hs & _). rewrite Hfs in Hs. unfold FINISH_STATE, BUSY_STATE in Hs. lia. }
  destruct H3 as (_ & Hla & Hsy & Hbv & HOne & Hchk & H & body & Hhg & Hcase).
  pose proof (tk_pend_nil s Hpd) as Hpn.
  destruct Hcase as [[Hdw HO]|[? [? _]]]; [|lia].
  rewrite Hpn, app_nil_r in HO.
  pose proof (cf7_prm W HW s HWs) as Hprm.
  edestruct (tk_put_trailer s (z_adler z) (z_total_in z)) as (s1 & E1 & Hp1 & Ho1 & Hc1 & Ha1 & Hb1);
    eauto; [lia|].
  rewrite E1 in E. cbn [bind] in E.
  assert (Hzo0 := Zlength_nonneg (z_out z)). assert (HO0 := Zlength_nonneg O).
  rewrite Zlength_app in Htout.
  edestruct (flush_pending_ok7 s1 z) as (s' & x & Ef & Hpx & Hlx & Hbx & Ho' & Hc' & Ha' & Hb' & Hpd' & Hpo');
    auto; try lia.
  rewrite Ef in E. cbn [bind] in E.
  assert (Hdw' : d_wrap s' = wrap).
  { destruct Ha1 as (_ & W1 & _), Ha' as (_ & W2 & _). lia. }
  rewrite Hdw' in E. replace (wrap >? 0) with true in E by (symmetry; apply Z.gtb_lt; lia).
  injection E as <- <- <-.
  destruct Ha1 as (As1 & Aw1 & Ag1 & Ai1 & Al1 & Am1), Ha' as (As2 & Aw2 & Ag2 & Ai2 & Al2 & Am2).
  split; [cbn [d_gzhead set_d_wrap]; congruence|].
  assert (Hc4 : core_eq s (set_d_wrap s' (- wrap))).
  { eapply core_eq_trans; [exact Hc1|]. eapply core_eq_trans; [exact Hc'|]. apply tk_core_eq_wrap. }
  pose proof (core_eq_fields _ _ Hc4) as (_ & _ & _ & _ & _ & _ & Hla4 & _ & Hsy4 & _).
  cbn [d_lookahead d_sym_next set_d_wrap] in Hla4, Hsy4.
  assert (Hx : x ++ pend s' = trailer wrap (z_adler z) (z_total_in z)) by congruence.
  assert (Hxa : Zlength x <= z_avail_out z) by lia.
  pose proof (tk_zrun7_step inb aout tin tout z x Hz0 Hxa Hbx) as Hz4.
  change (d_pending (set_d_wrap s' (- wrap))) with (d_pending s').
  destruct (Z.eqb_spec (d_pending s') 0) as [P0|P0]; cbn [negb]; [right; reflexivity|].
  left. split; [reflexivity|].
  unfold Mid7. split; [exact Hz4|]. split; [exact Hsz1|]. split; [exact Hsz2|].
  split; [exact Hsz3|]. split; [exact Hsz4|].
  cbn [z_next_in z_out z_total_in z_total_out z_adler].
  unfold Iapi7.
  split; [exact (cf7_frame W HW s _ HWs Hc4)|].
  split; [exact Ho'|].
  split; [exact Hwr|]. split; [exact Hw2|]. split; [exact Hbd|]. split; [exact Hld|].
  cbn [d_last_flush d_gzhead d_status set_d_wrap].
  split; [rewrite Al2, Al1; exact Hlf|].
  split; [intros h Eh; apply Hgz; congruence|].
  split; [rewrite app_assoc, !Zlength_app; lia|].
  split; [rewrite app_assoc; apply tk_bytes_app; auto|].
  split; [exact HbD|]. split; [exact HlD|]. split; [exact Htin|].
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
