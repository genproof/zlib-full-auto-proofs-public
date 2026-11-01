(* The entry, header and trailer stages of deflate() on the streams of RTK7Defs run (RTK7DEntry.entry_ex7 gives
   the entry stage's run; here the header and trailer stages), and keep w_bits and strm->adler below 2^32.
   With RTK7AComp these are the facts RTK7Api needs to show that every deflate() call on Iapi7 is defined. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTK7DEntry Zlib.proof.roundtrip.RTK7DHdrSt Zlib.proof.roundtrip.RTK7DTrail.
Require Import Zlib.proof.roundtrip.RTK7DStuck Zlib.proof.roundtrip.RTDDfXTrail.
Require Zlib.proof.deflate.DetApiHdrSt.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** w_bits and strm->adler *)

(* flush_pending changes neither w_bits nor strm->adler *)
Lemma fp_keep : forall s z s' z', c_flush_pending s z = Some (s', z') ->
  d_w_bits s' = d_w_bits s /\ z_adler z' = z_adler z.
Proof.
  intros s z s' z' H. unfold c_flush_pending, bind in H.
  destruct (c_tr_flush_bits (d_out s)) as [o|]; [|discriminate].
  destruct (_ =? 0).
  { injection H as <- <-. destruct s; split; reflexivity. }
  destruct (mb_read _ _ _) as [b|]; [|discriminate].
  unfold out_put in H. destruct (_ <=? _); [|discriminate].
  destruct (_ =? 0); injection H as <- <-; destruct s, z; split; reflexivity.
Qed.

(* nor does the entry stage *)
Lemma entry_keep : forall s z flush s1 z1 o, c_deflate_entry s z flush = Some (s1, z1, o) ->
  d_w_bits s1 = d_w_bits s /\ z_adler z1 = z_adler z.
Proof.
  intros s z flush s1 z1 o H. unfold c_deflate_entry in H. revert H.
  destruct ((d_status s =? FINISH_STATE) && negb (flush =? Z_FINISH)).
  { intros H. injection H as <- <- _. destruct z; split; reflexivity. }
  destruct (z_avail_out z =? 0).
  { intros H. injection H as <- <- _. destruct z; split; reflexivity. }
  cbv zeta.
  assert (Fin : forall s2 z2, d_w_bits s2 = d_w_bits s -> z_adler z2 = z_adler z ->
     (if (d_status s2 =? FINISH_STATE) && negb (z_avail_in z2 =? 0)
      then Some (s2, set_z_msg z2 (Some Z_BUF_ERROR), Some Z_BUF_ERROR) else Some (s2, z2, None)) =
     Some (s1, z1, o) -> d_w_bits s1 = d_w_bits s /\ z_adler z1 = z_adler z).
  { intros s2 z2 A B. destruct ((d_status s2 =? FINISH_STATE) && negb (z_avail_in z2 =? 0));
      intros H'; injection H' as <- <- _; [destruct z2|]; split; assumption. }
  destruct (negb (d_pending (set_d_last_flush s flush) =? 0)).
  - unfold bind at 1.
    destruct (c_flush_pending (set_d_last_flush s flush) z) as [[s2 z2]|] eqn:E; [|discriminate].
    destruct (fp_keep _ _ _ _ E) as [E1 E2]. cbn [bind].
    destruct (z_avail_out z2 =? 0); cbn [then_stage bind].
    + intros H. injection H as <- <- _. destruct s2; split; assumption.
    + intros H. exact (Fin s2 z2 E1 E2 H).
  - destruct (z_avail_in z =? 0).
    + destruct (in_int (d_last_flush s * 2)); [|discriminate]. cbn [guard bind].
      destruct ((rank flush <=? rank (d_last_flush s)) && negb (flush =? Z_FINISH)); cbn [then_stage bind].
      * intros H. injection H as <- <- _. destruct z; split; reflexivity.
      * intros H. exact (Fin (set_d_last_flush s flush) z eq_refl eq_refl H).
    + cbn [then_stage bind]. intros H. exact (Fin (set_d_last_flush s flush) z eq_refl eq_refl H).
Qed.

(* a state related by core_eq has the same w_bits *)
Lemma core_eq_wbits : forall s s', core_eq s s' -> d_w_bits s' = d_w_bits s.
Proof.
  intros s s' [H _]. exact (f_equal d_w_bits H).
Qed.

(** ** The header stages *)

Lemma hdr_ex7 : forall W HI dict wrap D O inb aout tin tout flush s z,
  core_facts7 W -> hdr_facts7 HI ->
  Mid7 W HI dict wrap D O inb aout tin tout flush s z ->
  d_pending s = 0 -> d_last_flush s = flush -> 0 <= flush <= 5 -> 0 < z_avail_out z ->
  (d_status s = FINISH_STATE -> z_avail_in z = 0) ->
  exists s2 z2 r, hdr_stages s z = Some (s2, z2, r) /\ d_w_bits s2 = d_w_bits s /\
    (0 <= z_adler z < 4294967296 -> 0 <= z_adler z2 < 4294967296).
Proof.
  intros W HI dict wrap D O inb aout tin tout flush s z CF HF M Hpend Hlf Hfl Hao Hfin.
  destruct M as (ZR & Hsz1 & Hsz2 & Hsz3 & Hsz4 & IA).
  destruct IA as (HW & Hout & Hwr0 & Hw2 & Hbd & Hld & Hlfr & Hgz & Hto & HbO & HbD & HlD & Htin & HF6 & _ & Hph).
  pose proof ZR as (Zin & Zni & Zai & Zti & Zao & Zol & Zto & Zbo).
  assert (Hzao : 0 <= z_avail_out z <= 4294967295) by (pose proof (Zlength_nonneg (z_out z)); lia).
  assert (Hzto : 0 <= z_total_out z) by (rewrite Hto; apply Zlength_nonneg).
  assert (Hzto2 : z_total_out z + z_avail_out z <= 18446744073709551615) by (rewrite Hto, Zlength_app; lia).
  pose proof (cf7_prm _ CF _ HW) as Hprm.
  (* the header stages keep strm->adler a 32-bit value (DetApiHdrSt.hdr_stages_adq: the pending buffer and the
     gzip extra field hold bytes) *)
  assert (Hpbq : Zlib.proof.deflate.DetApiHdrSt.pbq s).
  { split; [apply Hout|]. intros h x E1 E2.
    destruct (Hgz h E1) as (_ & _ & _ & _ & _ & Hex & _). exact (proj2 (Hex x E2)). }
  assert (Hadq : forall s2 z2 r, hdr_stages s z = Some (s2, z2, r) ->
                 0 <= z_adler z < 4294967296 -> 0 <= z_adler z2 < 4294967296).
  { intros s2 z2 r HS A. exact (proj2 (Zlib.proof.deflate.DetApiHdrSt.hdr_stages_adq _ _ _ _ _ HS Hpbq A)). }
  destruct Hph as [P0 | [Hlf2 [P1 | [P2 | P3]]]].
  - destruct P0 as (Hst & Hw & HD & HO & _ & Hbv & Hsym & _ & _ & Hss & Had).
    assert (Hpre : hdr_pre7 HI s z (hdr_bytes s (z_adler z)) 0).
    { unfold hdr_pre7. split; [exact Hprm|]. split; [exact Hout|]. split; [exact Hpend|].
      split; [exact Hsym|]. split; [exact Hbv|]. split; [exact Hzao|]. split; [exact Hzto|].
      split; [exact Hzto2|]. split; [exact Hgz|].
      destruct Hst as [[Hst Hwl]|[Hst Hw2']]; [left|right; left]; repeat split; auto; lia. }
    destruct (hf7_run _ HF _ _ _ _ Hpre) as (s' & z' & r' & HS' & HP).
    exists s', z', r'. split; [exact HS'|]. split; [exact (core_eq_wbits _ _ (proj1 HP))|]. exact (Hadq _ _ _ HS').
  - destruct P1 as (Hw & HD & HOne & Hbv & Hsym & H & k & HIk & HOk).
    assert (Hpre : hdr_pre7 HI s z H k).
    { unfold hdr_pre7. split; [exact Hprm|]. split; [exact Hout|]. split; [exact Hpend|].
      split; [exact Hsym|]. split; [exact Hbv|]. split; [exact Hzao|]. split; [exact Hzto|].
      split; [exact Hzto2|]. split; [exact Hgz|]. right; right; exact HIk. }
    destruct (hf7_run _ HF _ _ _ _ Hpre) as (s' & z' & r' & HS' & HP).
    exists s', z', r'. split; [exact HS'|]. split; [exact (core_eq_wbits _ _ (proj1 HP))|]. exact (Hadq _ _ _ HS').
  - exists s, z, None. rewrite hdr_stages_busy by (left; apply P2). split; [reflexivity|]. split; [reflexivity|]. auto.
  - exists s, z, None. rewrite hdr_stages_busy by (right; apply P3). split; [reflexivity|]. split; [reflexivity|]. auto.
Qed.

(** ** The trailer *)

Lemma trailer_ex7 : forall W HI dict wrap D O inb aout tin tout flush s z,
  core_facts7 W -> hdr_facts7 HI ->
  Mid7 W HI dict wrap D O inb aout tin tout flush s z ->
  d_pending s = 0 -> 0 <= flush <= 5 ->
  (flush = Z_FINISH -> d_status s = FINISH_STATE) ->
  (d_status s = BUSY_STATE \/ (d_status s = FINISH_STATE /\ z_avail_in z = 0)) ->
  exists s4 z4 c, c_deflate_trailer s z flush = Some (s4, z4, c) /\ d_w_bits s4 = d_w_bits s /\
    z_adler z4 = z_adler z /\
    (c = Z_STREAM_END -> flush = Z_FINISH /\ z_avail_in z4 = 0 /\ zrun7 inb aout tin tout z4).
Proof.
  intros W HI dict wrap D O inb aout tin tout flush s z HW HH HM Hpd Hfl Hfs Hst.
  unfold c_deflate_trailer.
  destruct (Z.eqb_spec flush Z_FINISH) as [EF|NF].
  2: { cbn [negb]. exists s, z, Z_OK. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
       discriminate. }
  subst flush. cbn [negb]. specialize (Hfs eq_refl).
  assert (Hai0 : z_avail_in z = 0).
  { destruct Hst as [Hst|[_ Hst]]; [|exact Hst]. rewrite Hfs in Hst. unfold FINISH_STATE, BUSY_STATE in Hst. lia. }
  clear Hst.
  destruct HM as (Hz & Hsz1 & Hsz2 & Hsz3 & Hsz4 & HIa).
  pose proof Hz as Hz0.
  destruct Hz as (Hzin & Hni & Hai & Hti & Hao & Hzo & Hto & Hbo).
  destruct HIa as (HWs & Hos & Hwr & Hw2 & Hbd & Hld & Hlf & Hgz & Htout & HbO & HbD & HlD & Htin & Hfin & Hdz
                   & Hph).
  destruct (Z.leb_spec (d_wrap s) 0) as [Hw0|Hw0].
  { exists s, z, Z_STREAM_END. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    intros _. split; [reflexivity|]. split; [exact Hai0|exact Hz0]. }
  destruct Hph as [H0 | [Hlf2 [H1 | [H2 | H3]]]].
  { exfalso. destruct H0 as [[[Hs _]|[Hs _]] _]; rewrite Hfs in Hs; unfold FINISH_STATE, INIT_STATE, GZIP_STATE in Hs; lia. }
  { exfalso. destruct H1 as (_ & _ & _ & _ & _ & H & k & HIk & _).
    destruct (hf7_status HI HH _ _ _ _ HIk) as (_ & _ & Hs & _). rewrite Hfs in Hs.
    unfold FINISH_STATE, EXTRA_STATE, NAME_STATE, COMMENT_STATE, HCRC_STATE in Hs; lia. }
  { exfalso. destruct H2 as (Hs & _). rewrite Hfs in Hs. unfold FINISH_STATE, BUSY_STATE in Hs. lia. }
  destruct H3 as (_ & Hla & Hsy & Hbv & HOne & Hchk & H & body & Hhg & Hcase).
  destruct Hcase as [[Hdw HO]|[? [? _]]]; [|lia].
  pose proof (cf7_prm W HW s HWs) as Hprm.
  edestruct (tk_put_trailer s (z_adler z) (z_total_in z)) as (s1 & E1 & Hp1 & Ho1 & Hc1 & Ha1 & Hb1);
    eauto; [lia|].
  rewrite E1. cbn [bind].
  assert (Hzo0 := Zlength_nonneg (z_out z)). assert (HO0 := Zlength_nonneg O).
  rewrite Zlength_app in Htout.
  edestruct (flush_pending_ok7 s1 z) as (s' & x & Ef & Hpx & Hlx & Hbx & Ho' & Hc' & Ha' & Hb' & Hpd' & Hpo');
    auto; try lia.
  rewrite Ef. cbn [bind].
  assert (Hdw' : d_wrap s' = wrap).
  { destruct Ha1 as (_ & W1 & _), Ha' as (_ & W2 & _). lia. }
  rewrite Hdw'. replace (wrap >? 0) with true by (symmetry; apply Z.gtb_lt; lia).
  eexists _, _, _. split; [reflexivity|].
  assert (Hc4 : core_eq s (set_d_wrap s' (- wrap))).
  { eapply core_eq_trans; [exact Hc1|]. eapply core_eq_trans; [exact Hc'|]. apply tk_core_eq_wrap. }
  split; [exact (core_eq_wbits _ _ Hc4)|]. split; [reflexivity|].
  intros _. split; [reflexivity|]. cbn [z_avail_in]. split; [exact Hai0|].
  apply tk_zrun7_step; [exact Hz0|lia|exact Hbx].
Qed.
