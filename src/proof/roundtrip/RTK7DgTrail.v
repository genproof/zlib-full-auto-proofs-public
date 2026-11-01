(* The trailer stage of deflate() keeps KMid, or gives RTFinal.dfinal at Z_STREAM_END (the functional half):
   RTDDgTrail.kf_trailer_ok for Mid7 and fpend_fspec7. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTK7DMid.
Require Import Zlib.proof.roundtrip.RTDDgTrail.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(* the gzip trailer stores total_in modulo 2^32: total_in modulo 2^64 gives the same bytes *)
Lemma tt7_u64_mod32 : forall x, u64 x mod 2 ^ 32 = x mod 2 ^ 32.
Proof.
  intros x. unfold u64. change 18446744073709551616 with (2 ^ 32 * 2 ^ 32).
  rewrite Z.rem_mul_r by lia. rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_mod. lia.
Qed.

(* RTDDgTrail.tt_trailer when total_in is the length of the data modulo 2^32 *)
Lemma tt7_trailer : forall wrap D a t, 1 <= wrap <= 2 -> chk_ok wrap D a ->
  (wrap = 2 -> t mod 2 ^ 32 = Zlength D mod 2 ^ 32) -> trailer wrap a t = ftrailer wrap D.
Proof.
  intros wrap D a t Hw [H1 H2] Ht. unfold trailer, ftrailer.
  destruct (Z.eqb_spec wrap 1) as [E1|E1].
  - rewrite (H1 E1). apply tt_trailer1.
  - assert (E2 : wrap = 2) by lia. rewrite E2. cbn [Z.eqb Pos.eqb].
    rewrite (H2 E2), tt_trailer2, (Ht E2). reflexivity.
Qed.

(* the header bytes are bytes for the headers rhdr_ok7 (RTDDgTrail.tt_gz_bytes_ok, tt_khdr_bytes) *)
Lemma tt7_cstr_bytes : forall o, rcstr_ok7 o ->
  bytes (match option_map (@removelast Z) o with Some n => n ++ [0] | None => [] end).
Proof.
  intros [l|] H; cbn [option_map]; [|constructor].
  destruct (H l eq_refl) as (l0 & -> & _ & Hb). rewrite removelast_last.
  apply tt_bytes_app; [|repeat constructor; lia].
  unfold bytes. eapply Forall_impl; [|exact Hb]. cbv beta. lia.
Qed.

Lemma tt7_gz_bytes_ok : forall gh xfl, (forall h, gh = Some h -> rhdr_ok7 h) -> 0 <= xfl < 256 ->
  bytes (F.gz_bytes (fhdr_of gh xfl)).
Proof.
  intros gh xfl Hh Hx.
  assert (B0 : bytes (F.gz_bytes0 (fhdr_of gh xfl))).
  { unfold F.gz_bytes0.
    assert (Hflg : 0 <= F.gz_flg (fhdr_of gh xfl) < 256).
    { unfold F.gz_flg. destruct (F.gz_text _), (F.gz_hcrc _), (F.gz_extra _), (F.gz_name _), (F.gz_comment _); lia. }
    apply tt_bytes_app; [repeat constructor; lia|].
    apply tt_bytes_app; [apply tt_le_bytes_ok|].
    destruct gh as [h|]; cbn [fhdr_of F.gz_xfl F.gz_os F.gz_extra F.gz_name F.gz_comment].
    - destruct (Hh h eq_refl) as (_ & _ & _ & _ & _ & Hex & Hn & Hc).
      apply tt_bytes_app.
      { repeat constructor; try lia; [apply Z.land_nonneg; lia|].
        rewrite tt_land255. apply Z.mod_pos_bound; lia. }
      apply tt_bytes_app.
      { destruct (DS.gz_extra h) as [x|] eqn:Ex; cbn [option_map]; [|constructor].
        apply tt_bytes_app; [apply tt_le_bytes_ok|]. apply Forall_sublist. exact (proj2 (Hex x eq_refl)). }
      apply tt_bytes_app; apply tt7_cstr_bytes; assumption.
    - repeat constructor; lia. }
  unfold F.gz_bytes. destruct (F.gz_hcrc _); [|exact B0].
  apply tt_bytes_app; [exact B0|apply tt_le_bytes_ok].
Qed.

Lemma tt7_khdr_bytes : forall dict wrap s HDR, 0 <= wrap <= 2 -> 9 <= d_w_bits s <= 15 ->
  (forall h, d_gzhead s = Some h -> rhdr_ok7 h) -> khdr dict wrap s HDR -> bytes HDR.
Proof.
  intros dict wrap s HDR Hw Hwb Hh Hk. unfold khdr in Hk.
  destruct (Z.eqb_spec wrap 0) as [E0|E0]; [subst HDR; constructor|].
  destruct (Z.eqb_spec wrap 1) as [E1|E1].
  - destruct Hk as (flg & (Hf & _) & ->).
    apply tt_bytes_app; [unfold zcmf; repeat constructor; lia|].
    destruct dict; [constructor|apply tt_be_bytes_ok].
  - destruct Hk as (xfl & Hx & ->). apply tt7_gz_bytes_ok; [exact Hh|lia].
Qed.


Lemma kf_trailer_ok7 : core_facts7 W3 -> hdr_facts7 hinv7 -> writer_fspec -> fpend_fspec7 ->
  forall dict wrap D O inb aout tin tout flush s z s4 z4 c,
  Mid7 W3 hinv7 dict wrap D O inb aout tin tout flush s z ->
  KMid dict wrap D O inb s z ->
  d_pending s = 0 -> 0 <= flush <= 5 ->
  (flush = Z_FINISH -> d_status s = FINISH_STATE) ->
  (d_status s = BUSY_STATE \/ (d_status s = FINISH_STATE /\ z_avail_in z = 0)) ->
  c_deflate_trailer s z flush = Some (s4, z4, c) ->
  d_w_bits s4 = d_w_bits s /\
  (c <> Z_STREAM_END -> KMid dict wrap D O inb s4 z4) /\
  (c = Z_STREAM_END ->
   dfinal dict wrap (d_w_bits s) (d_gzhead s) (D ++ sublist 0 (z_next_in z4) inb) (O ++ z_out z4)).
Proof.
  intros HC HF _ _ dict wrap D O inb aout tin tout flush s z s4 z4 c HM HK Hpd Hfl Hfs Hst Hrun.
  unfold c_deflate_trailer in Hrun.
  destruct (Z.eqb_spec flush Z_FINISH) as [EF|NF].
  2: { cbn [negb] in Hrun. injection Hrun as E1 E2 E3. subst s4 z4 c.
       split; [reflexivity|]. split; [intros _; exact HK|]. intros E. discriminate E. }
  subst flush. cbn [negb] in Hrun. specialize (Hfs eq_refl).
  assert (Hai0 : z_avail_in z = 0).
  { destruct Hst as [Hst|[_ Hst]]; [|exact Hst]. rewrite Hfs in Hst. unfold FINISH_STATE, BUSY_STATE in Hst. lia. }
  clear Hst.
  destruct HM as (Hz & Hsz1 & Hsz2 & Hsz3 & Hsz4 & HIa).
  pose proof Hz as Hz0.
  destruct Hz as (Hzin & Hni & Hai & Hti & Hao & Hzo & Hto & Hbo).
  destruct HIa as (HWs & Hos & Hwr & Hw2 & Hbd & Hld & Hlf & Hgz & Htout & HbO & HbD & HDl & Htin & Hfin & Hdz & Hph).
  destruct Hph as [H0 | [Hlf2 [H1 | [H2 | H3]]]].
  { exfalso. destruct H0 as [[[Hs _]|[Hs _]] _]; rewrite Hfs in Hs; unfold FINISH_STATE, INIT_STATE, GZIP_STATE in Hs; lia. }
  { exfalso. destruct H1 as (_ & _ & _ & _ & _ & H & k & HIk & _).
    destruct (hf7_status hinv7 HF _ _ _ _ HIk) as (_ & _ & Hs & _). rewrite Hfs in Hs.
    unfold FINISH_STATE, EXTRA_STATE, NAME_STATE, COMMENT_STATE, HCRC_STATE in Hs; lia. }
  { exfalso. destruct H2 as (Hs & _). rewrite Hfs in Hs. unfold FINISH_STATE, BUSY_STATE in Hs. lia. }
  destruct H3 as (_ & Hla & Hsy & Hbv & _ & Hchk & _).
  destruct HK as [[Hgn (BS & syms & Hkc & Hcase)] _].
  destruct Hcase as [(_ & Hs & _)|[[Hs _]|(_ & HBS & Hdat & HDR & Hkh & Hcase)]];
    [exact (False_ind _ (Hs Hfs))|rewrite Hfs in Hs; unfold FINISH_STATE, BUSY_STATE in Hs; lia|].
  set (D' := D ++ sublist 0 (z_next_in z) inb) in *. set (O' := O ++ z_out z) in *.
  pose proof (W3_prm s HWs) as Hprm.
  assert (Hwb : 9 <= d_w_bits s <= 15) by (destruct Hprm as (Hw & _); exact Hw).
  pose proof (tk_pend_nil s Hpd) as Hpn.
  assert (HbH : bytes HDR) by (eapply tt7_khdr_bytes; eauto).
  assert (Hbl : F.blocks_ok (2 ^ d_w_bits s) dict BS) by (destruct Hkc as ((_ & _ & _ & X & _) & _); exact X).
  assert (Hbv0 : 0 <= d_bi_valid s) by (destruct Hos as (_ & (X & _) & _); exact (proj1 X)).
  assert (Hfb : d_wrap s = wrap -> allbits O' s = F.bytes_bits HDR ++ enc_out 0 BS true ->
                d_bi_valid s = 0 /\ O' = HDR ++ F.deflate_bytes BS).
  { intros _ Hab. unfold allbits in Hab. rewrite Hpn, app_nil_r in Hab.
    destruct (tt_fin_bytes O' HDR BS (bibits s) HbO HbH) as [Hb0 HO]; auto.
    { unfold bibits. rewrite tt_bits_le_len by lia. lia. }
    split; [|exact HO].
    unfold bibits in Hb0. apply (f_equal (@Zlength bool)) in Hb0. rewrite tt_bits_le_len in Hb0 by lia.
    exact Hb0. }
  destruct (Z.leb_spec (d_wrap s) 0) as [Hw0|Hw0].
  - cbv iota in Hrun. injection Hrun as E1 E2 E3. subst s4 z4 c.
    split; [reflexivity|]. split; [intros C; exfalso; apply C; reflexivity|]. intros _.
    destruct Hcase as [[Hdw Hab]|(Hwp & Hdw & Hb0 & HO)].
    + destruct (Hfb Hdw Hab) as [_ HO].
      assert (Ew : wrap = 0) by lia.
      eapply tt_dfinal; eauto; try lia. change (O ++ z_out z) with O'. rewrite HO, Ew. unfold ftrailer. cbn [Z.eqb Pos.eqb]. rewrite app_nil_r. reflexivity.
    + rewrite Hpn, app_nil_r in HO. eapply tt_dfinal; eauto.
  - cbv iota in Hrun.
    destruct Hcase as [[Hdw Hab]|(Hwp & Hdw & _)]; [|lia].
    destruct (Hfb Hdw Hab) as [Hb0 HO].
    edestruct (tk_put_trailer s (z_adler z) (z_total_in z)) as (s1 & E1 & Hp1 & Ho1 & Hc1 & Ha1 & Hb1);
      eauto; [lia|].
    rewrite E1 in Hrun. cbn [bind] in Hrun.
    assert (Hzo0 := Zlength_nonneg (z_out z)). assert (HO0 := Zlength_nonneg O).
    unfold O' in Htout. rewrite Zlength_app in Htout.
    edestruct (flush_pending_ok7 s1 z) as (s' & x & Ef & Hpx & Hlx & Hbx & Ho' & Hc' & Ha' & Hb' & Hpd' & Hpo');
      auto; try lia.
    rewrite Ef in Hrun. cbn [bind] in Hrun.
    assert (Hdw' : d_wrap s' = wrap).
    { destruct Ha1 as (_ & W1 & _), Ha' as (_ & W2 & _). lia. }
    rewrite Hdw' in Hrun. replace (wrap >? 0) with true in Hrun by (symmetry; apply Z.gtb_lt; lia).
    injection Hrun as E4 E5 E6. subst s4 z4.
    destruct Ha1 as (As1 & Aw1 & Ag1 & Ai1 & Al1 & Am1), Ha' as (As2 & Aw2 & Ag2 & Ai2 & Al2 & Am2).
    assert (Hc4 : core_eq s (set_d_wrap s' (- wrap))).
    { eapply core_eq_trans; [exact Hc1|]. eapply core_eq_trans; [exact Hc'|]. apply tk_core_eq_wrap. }
    pose proof (core_eq_fields _ _ Hc4) as (_ & _ & Hwb4 & _).
    split; [exact Hwb4|].
    assert (Htr : trailer wrap (z_adler z) (z_total_in z) = ftrailer wrap D').
    { apply tt7_trailer; [lia|exact Hchk|].
      intros E2. specialize (Hw2 E2). subst dict. destruct Htin as (k & Hk & ->). rewrite Zlength_nil in Hk.
      replace k with 0 by lia. rewrite Z.add_0_r. apply tt7_u64_mod32. }
    assert (Hx : x ++ pend s' = ftrailer wrap D') by (rewrite <- Htr, <- Hdw, <- Hp1; congruence).
    change (d_pending (set_d_wrap s' (- wrap))) with (d_pending s') in E6.
    cbn [z_next_in z_out]. fold D'.
    destruct (Z.eqb_spec (d_pending s') 0) as [P0|P0]; cbn [negb] in E6; subst c.
    + split; [intros C; exfalso; apply C; reflexivity|]. intros _.
      rewrite (tk_pend_nil s' P0), app_nil_r in Hx.
      eapply tt_dfinal; eauto. rewrite app_assoc. fold O'. rewrite HO, Hx, app_assoc. reflexivity.
    + split; [|intros C; discriminate C]. intros _.
      unfold KMid, KFd. cbn [z_next_in z_out]. fold D'.
      split.
      * split; [intros Hn; cbn [d_gzhead set_d_wrap]; rewrite Ag2, Ag1; exact (Hgn Hn)|].
        exists BS, syms. split; [exact (kcore3_frame dict D' BS syms s _ Hc4 Hkc)|].
        right; right. cbn [d_status set_d_wrap]. split; [congruence|].
        split; [exact HBS|]. split; [exact Hdat|]. exists HDR.
        split; [apply (tt_khdr_eq dict wrap s); [exact Hwb4|cbn [d_gzhead set_d_wrap]; congruence|exact Hkh]|].
        right. split; [lia|]. split; [reflexivity|].
        split; [change (d_bi_valid (set_d_wrap s' (- wrap))) with (d_bi_valid s'); lia|].
        change (pend (set_d_wrap s' (- wrap))) with (pend s').
        rewrite app_assoc. fold O'. rewrite <- app_assoc, Hx, HO, <- app_assoc. reflexivity.
      * intros _ Hn. exfalso. apply Hn. cbn [d_status set_d_wrap]. congruence.
Qed.
