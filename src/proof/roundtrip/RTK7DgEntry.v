(* The entry stage of deflate() keeps KMid (the functional half): RTDDgEntry.kf_entry_ok for Mid7 and
   fpend_fspec7. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTK7DMid.
Require Import Zlib.proof.roundtrip.RTDDfXEntry Zlib.proof.roundtrip.RTDDgEntry.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

Lemma kf_entry_ok7 : core_facts7 W3 -> hdr_facts7 hinv7 -> fpend_fspec7 ->
  forall dict wrap D O inb aout tin tout flush s z s1 z1 o,
  Mid7 W3 hinv7 dict wrap D O inb aout tin tout flush s z ->
  KMid dict wrap D O inb s z ->
  c_deflate_entry s z flush = Some (s1, z1, o) ->
  d_w_bits s1 = d_w_bits s /\ KMid dict wrap D O inb s1 z1.
Proof.
  intros Hcf Hhf Hfp dict wrap D O inb aout tin tout flush s z s1 z1 o M K E.
  pose proof (mid7_zout_ok7 _ _ _ _ _ _ _ _ _ _ _ _ _ M) as Hzk.
  destruct M as ((Hin & Hn0 & Hai & Hti & Hao0 & Hzl & Hto & Hzb) & Hsz1 & Hsz2 & Hsz3 & Hsz4 & IA).
  destruct IA as (HW & Hok & Hwr & Hw2 & Hbd & Hld & Hlf & Hgz & Htout & HbO & HbD & HDl & HtD & Hfin & _ & Hph).
  assert (Hbv : d_bi_valid s <= 7).
  { destruct Hph as [P|[_ [P|[P|P]]]];
      [destruct P as (_&_&_&_&_&P&_); lia | destruct P as (_&_&_&P&_); lia |
       destruct P as (_&_&P&_); lia | destruct P as (_&_&_&P&_); lia]. }
  (* the no-output cases *)
  assert (Same : forall s1' z1', core_eq s s1' -> d_status s1' = d_status s -> d_wrap s1' = d_wrap s ->
            d_gzhead s1' = d_gzhead s -> d_bi_valid s1' = d_bi_valid s -> pend s1' = pend s ->
            bibits s1' = bibits s -> z_next_in z1' = z_next_in z -> z_out z1' = z_out z ->
            d_w_bits s1' = d_w_bits s /\ KMid dict wrap D O inb s1' z1').
  { intros s1' z1' A1 A2 A3 A4 A5 A6 A7 A8 A9. split; [exact (kfe_wbits _ _ A1)|].
    eapply (kfe_frame dict wrap D O inb s z s1' z1' []); eauto; rewrite ?app_nil_r, ?app_nil_l; auto. }
  assert (Lf : forall f, d_w_bits (set_d_last_flush s f) = d_w_bits s /\
                         KMid dict wrap D O inb (set_d_last_flush s f) z).
  { intros f. apply Same; try reflexivity. apply ent_core_eq_lf. }
  unfold c_deflate_entry in E.
  destruct ((d_status s =? FINISH_STATE) && negb (flush =? Z_FINISH)) eqn:E1.
  { injection E as <- <- _. apply Same; try reflexivity. apply kfe_core_eq_refl. }
  destruct (z_avail_out z =? 0) eqn:E2.
  { injection E as <- <- _. apply Same; try reflexivity. apply kfe_core_eq_refl. }
  cbn zeta in E. change (d_pending (set_d_last_flush s flush)) with (d_pending s) in E.
  destruct (d_pending s =? 0) eqn:E3; cbn [negb] in E.
  - destruct (z_avail_in z =? 0) eqn:E4.
    + destruct (guard (in_int (d_last_flush s * 2))) eqn:Eg; [|discriminate]. cbn [bind] in E.
      destruct ((rank flush <=? rank (d_last_flush s)) && negb (flush =? Z_FINISH)) eqn:E5.
      * cbn [then_stage bind] in E. injection E as <- <- _.
        apply Same; try reflexivity. apply ent_core_eq_lf.
      * cbn [then_stage bind] in E.
        destruct ((d_status (set_d_last_flush s flush) =? FINISH_STATE) && negb (z_avail_in z =? 0));
          injection E as <- <- _; apply Same; try reflexivity; apply ent_core_eq_lf.
    + cbn [then_stage bind] in E.
      destruct ((d_status (set_d_last_flush s flush) =? FINISH_STATE) && negb (z_avail_in z =? 0));
        injection E as <- <- _; apply Same; try reflexivity; apply ent_core_eq_lf.
  -     destruct Hzk as (Zk1 & Zk2 & Zk3).
    destruct (flush_pending_ok7 (set_d_last_flush s flush) z)
      as (s' & x & Efp & Hpd & Hxl & Hbx & Hok' & Hce & Hae & Hbv' & Hpn & Hpo);
      [exact Hok|exact Hbv|exact Zk1|exact Zk2|exact Zk3|].
    assert (Hzk : zout_ok7 z) by (split; [exact Zk1|split; [exact Zk2|exact Zk3]]).
    assert (Hb8 : d_bi_valid (set_d_last_flush s flush) < 8).
    { change (d_bi_valid (set_d_last_flush s flush)) with (d_bi_valid s). lia. }
    destruct (Hfp (set_d_last_flush s flush) z s' _ Hok Hzk (or_introl Hb8) Efp)
      as [x' [Hzo Hbits]].
    destruct Hzo as (_ & _ & _ & _ & _ & _ & Hzo & _). cbn [z_out] in Hzo.
    apply app_inv_head in Hzo. subst x'.
    change (pend (set_d_last_flush s flush)) with (pend s) in Hpd, Hbits.
    change (bibits (set_d_last_flush s flush)) with (bibits s) in Hbits.
    change (d_bi_valid (set_d_last_flush s flush)) with (d_bi_valid s) in Hbv'.
    assert (Hbb : bibits s' = bibits s).
    { rewrite Hpd in Hbits. apply app_inv_head in Hbits. exact Hbits. }
    destruct Hae as (A1 & A2 & A3 & A4 & A5 & A6). cbn in A1, A2, A3, A4, A5, A6.
    assert (Hce' : core_eq s s') by (eapply ent_core_eq_trans; [apply ent_core_eq_lf|exact Hce]).
    rewrite Efp in E. cbn [bind z_avail_out] in E.
    assert (Fin : forall s1' z1', core_eq s s1' -> d_status s1' = d_status s -> d_wrap s1' = d_wrap s ->
              d_gzhead s1' = d_gzhead s -> d_bi_valid s1' = d_bi_valid s -> pend s1' = pend s' ->
              bibits s1' = bibits s' -> z_next_in z1' = z_next_in z -> z_out z1' = z_out z ++ x ->
              d_w_bits s1' = d_w_bits s /\ KMid dict wrap D O inb s1' z1').
    { intros s1' z1' B1 B2 B3 B4 B5 B6 B7 B8 B9. split; [exact (kfe_wbits _ _ B1)|].
      eapply (kfe_frame dict wrap D O inb s z s1' z1' x); eauto; congruence. }
    destruct (z_avail_out z - Zlength x =? 0) eqn:E4.
    + injection E as <- <- _. apply Fin; cbn; try reflexivity; try congruence.
      2:{ change (d_bi_valid (set_d_last_flush s' (-1))) with (d_bi_valid s'). exact Hbv'. }
      eapply ent_core_eq_trans; [exact Hce'|apply ent_core_eq_lf].
    + cbn [then_stage bind] in E.
      destruct ((d_status s' =? FINISH_STATE) && negb (z_avail_in _ =? 0));
        injection E as <- <- _; apply Fin; cbn; try reflexivity; try congruence; exact Hce'.
Qed.
