(* The entry stage of deflate() (c_deflate_entry) keeps Mid7: RTDDfXEntry.entry_ok for the streams of RTK7Defs,
   from core_facts7 and hdr_facts7. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTK7DMid.
Require Import Zlib.proof.roundtrip.RTDDfXEntry.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(* Iapi7 after a stage that only hands pending bytes [x] out (and sets last_flush) *)
Lemma ent_iapi_frame7 : forall W HI dict wrap D O fin s tin tout adler s' x,
  core_facts7 W -> hdr_facts7 HI -> Iapi7 W HI dict wrap D O fin s tin tout adler ->
  core_eq s s' -> outok s' -> d_status s' = d_status s -> d_wrap s' = d_wrap s -> d_gzhead s' = d_gzhead s ->
  d_gzindex s' = d_gzindex s -> d_bi_valid s' = d_bi_valid s ->
  pend s = x ++ pend s' -> bytes x -> d_pending s' = d_pending s - Zlength x ->
  -1 <= d_last_flush s' <= 5 ->
  Iapi7 W HI dict wrap D (O ++ x) fin s' tin (tout + Zlength x) adler.
Proof.
  intros W HI dict wrap D O fin s tin tout adler s' x CF HF IA Hce Hok Hst Hwr Hgz Hgi Hbv Hpd Hbx Hpn Hlf.
  destruct IA as (HW & Hok0 & Hwr0 & Hw2 & Hbd & Hld & Hlf0 & Hgz0 & Htout & HbO & HbD & HDl & Htin & Hfin & Hdz
                  & Hph).
  destruct (ent_core_eq_fields s s' Hce) as (Ebs & Ess & Ela & Epb & Esy).
  split; [eapply (cf7_frame W CF); eauto|].
  split; [exact Hok|]. do 4 (split; [assumption|]).
  split; [lia|]. split; [rewrite Hgz; exact Hgz0|].
  split; [rewrite Zlength_app; lia|]. split; [unfold bytes in *; apply Forall_app; auto|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [rewrite Hst; assumption|].
  split; [rewrite Ebs, Ess, Ela; exact Hdz|].
  destruct Hph as [P0|[_ Hph]].
  - left. destruct P0 as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11).
    assert (Hx : x = []).
    { unfold pend in Hpd. rewrite P5, Z.add_0_r, sublist_nil in Hpd. destruct x; [reflexivity|discriminate]. }
    subst x. rewrite P4. cbn [app Zlength]. rewrite Zlength_nil in Hpn.
    split; [rewrite Hst; exact P1|]. split; [congruence|]. split; [assumption|]. split; [reflexivity|].
    split; [lia|]. split; [lia|]. split; [congruence|]. split; [congruence|].
    split; [congruence|]. split; [rewrite Ess; assumption|]. assumption.
  - right. split; [lia|].
    destruct Hph as [P|[P|P]].
    + left. destruct P as (P1 & P2 & P3 & P4 & P5 & H & k & P6 & P7).
      split; [assumption|]. split; [assumption|]. split; [intro E; apply P3; destruct O; [reflexivity|discriminate]|].
      split; [lia|]. split; [lia|]. exists H, k. split.
      * eapply (hf7_frame HI HF); eauto.
      * rewrite app_ass, <- Hpd. exact P7.
    + right; left. destruct P as (P1 & P2 & P3 & P4 & P5 & H & body & P6 & P7).
      split; [congruence|]. split; [congruence|]. split; [lia|].
      split; [intros Hw; specialize (P4 Hw); destruct O; [contradiction|discriminate]|].
      split; [assumption|]. exists H, body. split; [assumption|].
      rewrite app_ass, <- Hpd. exact P7.
    + right; right. destruct P as (P1 & P2 & P3 & P4 & P5 & P6 & H & body & P7 & P8).
      split; [congruence|]. split; [congruence|]. split; [congruence|]. split; [lia|].
      split; [intros Hw; specialize (P5 Hw); destruct O; [contradiction|discriminate]|].
      split; [assumption|]. exists H, body. split; [assumption|].
      rewrite app_ass, <- Hpd, Hwr. exact P8.
Qed.

(* Mid7 after such a stage, at the start of a call (nothing consumed, the bytes [x] are the output so far) *)
Lemma ent_mid_step7 : forall W HI dict wrap D O inb aout tin tout flush s z s' x z',
  core_facts7 W -> hdr_facts7 HI -> Mid7 W HI dict wrap D O inb aout tin tout flush s z ->
  z_next_in z = 0 -> z_out z = [] ->
  core_eq s s' -> outok s' -> d_status s' = d_status s -> d_wrap s' = d_wrap s -> d_gzhead s' = d_gzhead s ->
  d_gzindex s' = d_gzindex s -> d_bi_valid s' = d_bi_valid s ->
  pend s = x ++ pend s' -> bytes x -> d_pending s' = d_pending s - Zlength x ->
  -1 <= d_last_flush s' <= 5 -> Zlength x <= z_avail_out z ->
  z_in z' = z_in z -> z_next_in z' = 0 -> z_avail_in z' = z_avail_in z -> z_total_in z' = z_total_in z ->
  z_out z' = x -> z_avail_out z' = z_avail_out z - Zlength x -> z_total_out z' = z_total_out z + Zlength x ->
  z_adler z' = z_adler z ->
  Mid7 W HI dict wrap D O inb aout tin tout flush s' z'.
Proof.
  intros W HI dict wrap D O inb aout tin tout flush s z s' x z' CF HF M Hni Hzo Hce Hok Hst Hwr Hgz Hgi Hbv
    Hpd Hbx Hpn Hlf Hxl Z1 Z2 Z3 Z4 Z5 Z6 Z7 Z8.
  destruct M as ((Hin & Hn0 & Hai & Hti & Hao0 & Hzl & Hto & Hzb) & Hsz1 & Hsz2 & Hsz3 & Hsz4 & IA).
  rewrite Hzo, Zlength_nil in *.
  split; [|do 4 (split; [assumption|])].
  - unfold zrun7. rewrite Z1, Z2, Z3, Z4, Z5, Z6, Z7. rewrite Hni in *. repeat split; auto; lia.
  - assert (Ef : fin_of flush inb z' = fin_of flush inb z) by (unfold fin_of; rewrite Z2, Hni; reflexivity).
    rewrite Ef, Z2, Z4, Z5, Z7, Z8. rewrite Hni in IA. rewrite sublist_nil, !app_nil_r in IA. rewrite sublist_nil, app_nil_r.
    eapply ent_iapi_frame7; eauto.
Qed.

(* the entry stage runs and keeps Mid7 (RTDDfXEntry.entry_ok for these streams) *)
Lemma entry_ex7 : forall W HI dict wrap D O inb aout tin tout flush s z,
  core_facts7 W -> hdr_facts7 HI ->
  Mid7 W HI dict wrap D O inb aout tin tout flush s z ->
  z_next_in z = 0 -> z_out z = [] -> z_avail_out z = aout -> 0 <= flush <= 5 ->
  exists s1 z1 o, c_deflate_entry s z flush = Some (s1, z1, o) /\ d_gzhead s1 = d_gzhead s /\
    Mid7 W HI dict wrap D O inb aout tin tout flush s1 z1 /\
    match o with
    | Some c => c = Z_OK \/ (c = Z_BUF_ERROR /\ z_next_in z1 = 0 /\ z_out z1 = [])
    | None => d_pending s1 = 0 /\ d_last_flush s1 = flush /\ 0 < z_avail_out z1 /\ d_status s1 = d_status s /\
              (d_status s1 = FINISH_STATE -> z_avail_in z1 = 0)
    end.
Proof.
  intros W HI dict wrap D O inb aout tin tout flush s z CF HF M Hni Hzo Hao Hfl.
  pose proof M as M0.
  destruct M as ((Hin & Hn0 & Hai & Hti & Hao0 & Hzl & Hto & Hzb) & Hsz1 & Hsz2 & Hsz3 & Hsz4 & IA).
  rewrite Hzo, Zlength_nil in *.
  destruct IA as (HW & Hok & Hwr & Hw2 & Hbd & Hld & Hlf & Hgz & Htout & HbO & HbD & HDl & Htin & Hfin & _ & Hph).
  assert (Hbv : d_bi_valid s <= 7).
  { destruct Hph as [P|[_ [P|[P|P]]]];
      [destruct P as (_&_&_&_&_&P&_); lia | destruct P as (_&_&_&P&_); lia |
       destruct P as (_&_&P&_); lia | destruct P as (_&_&_&P&_); lia]. }
  assert (HF2 : d_status s = FINISH_STATE -> flush = Z_FINISH /\ inb = []).
  { intros E. specialize (Hfin E). unfold fin_of in Hfin. rewrite Hni in Hfin.
    destruct (flush =? Z_FINISH) eqn:Ef; [|discriminate]. apply Z.eqb_eq in Ef. split; auto.
    injection Hfin; intro Hx. rewrite sublist_same in Hx by lia. exact Hx. }
  unfold c_deflate_entry.
  destruct ((d_status s =? FINISH_STATE) && negb (flush =? Z_FINISH)) eqn:E1.
  { exfalso. apply andb_true_iff in E1 as [E1 E2]. apply Z.eqb_eq in E1. destruct (HF2 E1) as [Ef _].
    rewrite Ef, Z.eqb_refl in E2. discriminate. }
  destruct (z_avail_out z =? 0) eqn:E2.
  { exists s, (set_z_msg z (Some Z_BUF_ERROR)), (Some Z_BUF_ERROR). split; [reflexivity|]. split; [reflexivity|].
    split; [exact M0|]. right. cbn. auto. }
  cbn zeta. change (d_pending (set_d_last_flush s flush)) with (d_pending s).
  assert (Hce1 : core_eq s (set_d_last_flush s flush)) by apply ent_core_eq_lf.
  assert (Hai0 : d_status s = FINISH_STATE -> z_avail_in z = 0).
  { intros E. destruct (HF2 E) as [_ ->]. rewrite Hai, Hni. reflexivity. }
  assert (Hin1 : in_int (d_last_flush s * 2) = true).
  { unfold in_int. apply andb_true_intro; split; apply Z.leb_le; lia. }
  assert (Mid1 : forall z', z_in z' = z_in z -> z_next_in z' = z_next_in z -> z_avail_in z' = z_avail_in z ->
            z_total_in z' = z_total_in z -> z_out z' = z_out z -> z_avail_out z' = z_avail_out z ->
            z_total_out z' = z_total_out z -> z_adler z' = z_adler z ->
            Mid7 W HI dict wrap D O inb aout tin tout flush (set_d_last_flush s flush) z').
  { intros z' Z1 Z2 Z3 Z4 Z5 Z6 Z7 Z8.
    eapply (ent_mid_step7 W HI dict wrap D O inb aout tin tout flush s z _ [] z' CF HF M0 Hni Hzo Hce1);
      cbn; try reflexivity; try exact Hok; try (rewrite Zlength_nil; lia); try lia; try congruence.
    unfold d_pending; cbn; lia. }
  destruct (d_pending s =? 0) eqn:E3; cbn [negb].
  - destruct (z_avail_in z =? 0) eqn:E4.
    + rewrite Hin1. cbn [guard bind].
      destruct ((rank flush <=? rank (d_last_flush s)) && negb (flush =? Z_FINISH)) eqn:E5.
      * exists (set_d_last_flush s flush), (set_z_msg z (Some Z_BUF_ERROR)), (Some Z_BUF_ERROR).
        split; [reflexivity|]. split; [reflexivity|]. split; [apply Mid1; reflexivity|].
        right. cbn. auto.
      * exists (set_d_last_flush s flush), z, None. cbn [then_stage bind]. cbn [d_status set_d_last_flush].
        rewrite E4. rewrite andb_false_r. split; [reflexivity|]. split; [reflexivity|].
        split; [apply Mid1; reflexivity|]. cbn.
        apply Z.eqb_eq in E3. apply Z.eqb_neq in E2. apply Z.eqb_eq in E4. repeat split; auto; lia.
    + exists (set_d_last_flush s flush), z, None. cbn [then_stage bind]. cbn [d_status set_d_last_flush].
      assert (E5 : (d_status s =? FINISH_STATE) && negb (z_avail_in z =? 0) = false).
      { destruct (Z.eqb_spec (d_status s) FINISH_STATE) as [E|E]; [|reflexivity].
        rewrite (Hai0 E) in E4. discriminate. }
      rewrite E5. split; [reflexivity|]. split; [reflexivity|].
      split; [apply Mid1; reflexivity|]. cbn.
      apply Z.eqb_eq in E3. apply Z.eqb_neq in E2. repeat split; auto; lia.
  - destruct (flush_pending_ok7 (set_d_last_flush s flush) z)
      as (s' & x & Efp & Hpd & Hxl & Hbx & Hok' & Hce & Hae & Hbv' & Hpn & Hpo).
    { exact Hok. } { exact Hbv. } { lia. } { rewrite Htout, app_nil_r. pose proof (Zlength_nonneg O). lia. }
    { rewrite Htout, app_nil_r. lia. }
    rewrite Efp. cbn [bind z_avail_out].
    destruct Hae as (A1 & A2 & A3 & A4 & A5 & A6). cbn in A1, A2, A3, A4, A5, A6.
    change (d_pending (set_d_last_flush s flush)) with (d_pending s) in Hpn, Hxl.
    change (d_bi_valid (set_d_last_flush s flush)) with (d_bi_valid s) in Hbv'.
    change (pend (set_d_last_flush s flush)) with (pend s) in Hpd.
    apply Z.eqb_neq in E3. apply Z.eqb_neq in E2.
    destruct (z_avail_out z - Zlength x =? 0) eqn:E4.
    + exists (set_d_last_flush s' (-1)), (mkST (z_in z) (z_next_in z) (z_avail_in z) (z_total_in z) (z_out z ++ x)
        (z_avail_out z - Zlength x) (z_total_out z + Zlength x) (z_adler z) (z_msg z)), (Some Z_OK).
      split; [reflexivity|]. split; [cbn; congruence|].
      split; [|left; reflexivity].
      eapply (ent_mid_step7 W HI dict wrap D O inb aout tin tout flush s z _ x _ CF HF M0 Hni Hzo).
      all: cbn; try reflexivity; try exact Hok'; try exact Hbx; try exact Hpd; try congruence; try lia.
      all: try (eapply ent_core_eq_trans; [exact Hce1|]; eapply ent_core_eq_trans; [exact Hce|];
                apply ent_core_eq_lf).
      all: try (rewrite Hzo; reflexivity).
      all: try exact Hbv'.
      all: try (unfold d_pending in *; cbn; lia).
    + assert (Hx : Zlength x = d_pending s).
      { apply Z.eqb_neq in E4. lia. }
      exists s', (mkST (z_in z) (z_next_in z) (z_avail_in z) (z_total_in z) (z_out z ++ x)
        (z_avail_out z - Zlength x) (z_total_out z + Zlength x) (z_adler z) (z_msg z)), None.
      cbn [then_stage bind z_avail_in].
      assert (E5 : (d_status s' =? FINISH_STATE) && negb (z_avail_in z =? 0) = false).
      { destruct (Z.eqb_spec (d_status s') FINISH_STATE) as [E|E]; [|reflexivity].
        rewrite A1 in E. rewrite (Hai0 E). reflexivity. }
      rewrite E5. split; [reflexivity|]. split; [congruence|].
      split.
      * eapply (ent_mid_step7 W HI dict wrap D O inb aout tin tout flush s z _ x _ CF HF M0 Hni Hzo).
        all: cbn; try reflexivity; try exact Hok'; try exact Hbx; try exact Hpd; try congruence; try lia.
        all: try (eapply ent_core_eq_trans; [exact Hce1|]; exact Hce).
        all: try (rewrite Hzo; reflexivity).
        all: try exact Hbv'.
        all: try (unfold d_pending in *; cbn; lia).
      * cbn. repeat split; try congruence; try lia.
Qed.


Lemma entry_ok7 : forall W HI dict wrap D O inb aout tin tout flush s z s1 z1 o,
  core_facts7 W -> hdr_facts7 HI ->
  Mid7 W HI dict wrap D O inb aout tin tout flush s z ->
  z_next_in z = 0 -> z_out z = [] -> z_avail_out z = aout -> 0 <= flush <= 5 ->
  c_deflate_entry s z flush = Some (s1, z1, o) ->
  d_gzhead s1 = d_gzhead s /\ Mid7 W HI dict wrap D O inb aout tin tout flush s1 z1 /\
  match o with
  | Some c => c = Z_OK \/ (c = Z_BUF_ERROR /\ z_next_in z1 = 0 /\ z_out z1 = [])
  | None => d_pending s1 = 0 /\ d_last_flush s1 = flush /\ 0 < z_avail_out z1 /\ d_status s1 = d_status s /\
            (d_status s1 = FINISH_STATE -> z_avail_in z1 = 0)
  end.
Proof.
  intros W HI dict wrap D O inb aout tin tout flush s z s1 z1 o CF HF M Hni Hzo Hao Hfl R.
  destruct (entry_ex7 W HI dict wrap D O inb aout tin tout flush s z CF HF M Hni Hzo Hao Hfl)
    as (s1' & z1' & o' & E & Rest).
  rewrite E in R. injection R as <- <- <-. exact Rest.
Qed.
