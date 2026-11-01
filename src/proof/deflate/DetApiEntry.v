(** * deflate() on [Iapi] without its size limits: stage 1, the entry

    [LTApiEntry.entry_ok] for [MidW] (DetApiMid.v): a call starting at next_in [nin] with up to 2^32 - 1 bytes of
    output space.  The entry stage only hands pending bytes out (flush_pending: [flush_pending_wide]) and sets
    last_flush / msg, so strm->adler is unchanged. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.DetApiMid.
Require Import Zlib.proof.deflate.LTApiEntry.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** [LTApiEntry.ent_mid_step] for [MidW]: [MidW] after a stage that only hands pending bytes [x] out and sets
    last_flush, at the start of a call (next_in = [nin], no output yet). *)
Lemma entw_mid_step : forall W HI dict wrap D O inb nin aout tin tout flush s z s' x z',
  core_facts W -> hdr_facts HI -> MidW W HI dict wrap D O inb nin aout tin tout flush s z ->
  z_next_in z = nin -> z_out z = [] ->
  core_eq s s' -> outok s' -> d_status s' = d_status s -> d_wrap s' = d_wrap s -> d_gzhead s' = d_gzhead s ->
  d_gzindex s' = d_gzindex s -> d_bi_valid s' = d_bi_valid s ->
  pend s = x ++ pend s' -> bytes x -> d_pending s' = d_pending s - Zlength x ->
  -1 <= d_last_flush s' <= 5 -> Zlength x <= z_avail_out z ->
  z_in z' = z_in z -> z_next_in z' = nin -> z_avail_in z' = z_avail_in z -> z_total_in z' = z_total_in z ->
  z_out z' = x -> z_avail_out z' = z_avail_out z - Zlength x -> z_total_out z' = z_total_out z + Zlength x ->
  z_adler z' = z_adler z ->
  MidW W HI dict wrap D O inb nin aout tin tout flush s' z'.
Proof.
  intros W HI dict wrap D O inb nin aout tin tout flush s z s' x z' CF HF M Hni Hzo Hce Hok Hst Hwr Hgz Hgi Hbv
    Hpd Hbx Hpn Hlf Hxl Z1 Z2 Z3 Z4 Z5 Z6 Z7 Z8.
  destruct M as ((Hin & Hn & Hai & Hti & Hao0 & Hzl & Hto & Hzb) & Hn0 & Hsz1 & Ha & Hsz2 & IA).
  rewrite Hzo, Zlength_nil in *.
  split; [|split; [assumption|split; [assumption|split; [assumption|split; [assumption|]]]]].
  - unfold zrunw. rewrite Z1, Z2, Z3, Z4, Z5, Z6, Z7. rewrite Hni in *. repeat split; auto; lia.
  - assert (Ef : fin_of flush inb z' = fin_of flush inb z) by (unfold fin_of; rewrite Z2, Hni; reflexivity).
    rewrite Ef, Z2, Z4, Z5, Z7, Z8. rewrite Hni in IA. rewrite sublist_nil, !app_nil_r in IA.
    rewrite sublist_nil, app_nil_r.
    eapply ent_iapi_frame; eauto.
Qed.

Lemma entryw_ok : forall W HI dict wrap D O inb nin aout tin tout flush s z,
  core_facts W -> hdr_facts HI ->
  MidW W HI dict wrap D O inb nin aout tin tout flush s z ->
  z_next_in z = nin -> z_out z = [] -> z_avail_out z = aout -> 0 <= flush <= 5 ->
  exists s1 z1 o, c_deflate_entry s z flush = Some (s1, z1, o) /\ d_gzhead s1 = d_gzhead s /\
    MidW W HI dict wrap D O inb nin aout tin tout flush s1 z1 /\ z_adler z1 = z_adler z /\
    match o with
    | Some c => c = Z_OK \/ (c = Z_BUF_ERROR /\ z_next_in z1 = nin /\ z_out z1 = [])
    | None => d_pending s1 = 0 /\ d_last_flush s1 = flush /\ 0 < z_avail_out z1 /\ d_status s1 = d_status s /\
              (d_status s1 = FINISH_STATE -> z_avail_in z1 = 0)
    end.
Proof.
  intros W HI dict wrap D O inb nin aout tin tout flush s z CF HF M Hni Hzo Hao Hfl.
  pose proof M as M0.
  destruct (midw_out _ _ _ _ _ _ _ _ _ _ _ _ _ _ M) as [HaoW HtoW].
  destruct M as ((Hin & Hn & Hai & Hti & Hao0 & Hzl & Hto & Hzb) & Hn0 & Hsz1 & Ha & Hsz2 & IA).
  rewrite Hzo, Zlength_nil in *.
  destruct IA as (HW & Hok & Hwr & Hw2 & Hbd & Hld & Hlf & Hgz & Htout & HbO & HbD & HtD & Hfin & _ & Hph).
  assert (Hbv : d_bi_valid s <= 7).
  { destruct Hph as [P|[_ [P|[P|P]]]];
      [destruct P as (_&_&_&_&_&P&_); lia | destruct P as (_&_&_&P&_); lia |
       destruct P as (_&_&P&_); lia | destruct P as (_&_&_&P&_); lia]. }
  assert (HF2 : d_status s = FINISH_STATE -> flush = Z_FINISH /\ z_avail_in z = 0).
  { intros E. specialize (Hfin E). unfold fin_of in Hfin. rewrite Hni in Hfin.
    destruct (flush =? Z_FINISH) eqn:Ef; [|discriminate]. apply Z.eqb_eq in Ef. split; auto.
    injection Hfin; intro Hx. apply (f_equal (@Zlength Z)) in Hx.
    rewrite Zlength_sublist, Zlength_nil in Hx by lia. lia. }
  unfold c_deflate_entry.
  destruct ((d_status s =? FINISH_STATE) && negb (flush =? Z_FINISH)) eqn:E1.
  { exfalso. apply andb_true_iff in E1 as [E1 E2]. apply Z.eqb_eq in E1. destruct (HF2 E1) as [Ef _].
    rewrite Ef, Z.eqb_refl in E2. discriminate. }
  destruct (z_avail_out z =? 0) eqn:E2.
  { exists s, (set_z_msg z (Some Z_BUF_ERROR)), (Some Z_BUF_ERROR). split; [reflexivity|]. split; [reflexivity|].
    split; [exact M0|]. split; [reflexivity|]. right. cbn. auto. }
  cbn zeta. change (d_pending (set_d_last_flush s flush)) with (d_pending s).
  assert (Hce1 : core_eq s (set_d_last_flush s flush)) by apply ent_core_eq_lf.
  assert (Hai0 : d_status s = FINISH_STATE -> z_avail_in z = 0) by (intros E; apply (HF2 E)).
  assert (Hin1 : in_int (d_last_flush s * 2) = true).
  { unfold in_int. apply andb_true_intro; split; apply Z.leb_le; lia. }
  assert (Mid1 : forall z', z_in z' = z_in z -> z_next_in z' = z_next_in z -> z_avail_in z' = z_avail_in z ->
            z_total_in z' = z_total_in z -> z_out z' = z_out z -> z_avail_out z' = z_avail_out z ->
            z_total_out z' = z_total_out z -> z_adler z' = z_adler z ->
            MidW W HI dict wrap D O inb nin aout tin tout flush (set_d_last_flush s flush) z').
  { intros z' Z1 Z2 Z3 Z4 Z5 Z6 Z7 Z8.
    eapply (entw_mid_step W HI dict wrap D O inb nin aout tin tout flush s z _ [] z' CF HF M0 Hni Hzo Hce1);
      cbn; try reflexivity; try exact Hok; try (rewrite Zlength_nil; lia); try lia; try congruence.
    unfold d_pending; cbn; lia. }
  destruct (d_pending s =? 0) eqn:E3; cbn [negb].
  - destruct (z_avail_in z =? 0) eqn:E4.
    + rewrite Hin1. cbn [guard bind].
      destruct ((rank flush <=? rank (d_last_flush s)) && negb (flush =? Z_FINISH)) eqn:E5.
      * exists (set_d_last_flush s flush), (set_z_msg z (Some Z_BUF_ERROR)), (Some Z_BUF_ERROR).
        split; [reflexivity|]. split; [reflexivity|]. split; [apply Mid1; reflexivity|].
        split; [reflexivity|]. right. cbn. auto.
      * exists (set_d_last_flush s flush), z, None. cbn [then_stage bind]. cbn [d_status set_d_last_flush].
        rewrite E4. rewrite andb_false_r. split; [reflexivity|]. split; [reflexivity|].
        split; [apply Mid1; reflexivity|]. split; [reflexivity|]. cbn.
        apply Z.eqb_eq in E3. apply Z.eqb_neq in E2. apply Z.eqb_eq in E4. repeat split; auto; lia.
    + exists (set_d_last_flush s flush), z, None. cbn [then_stage bind]. cbn [d_status set_d_last_flush].
      assert (E5 : (d_status s =? FINISH_STATE) && negb (z_avail_in z =? 0) = false).
      { destruct (Z.eqb_spec (d_status s) FINISH_STATE) as [E|E]; [|reflexivity].
        rewrite (Hai0 E) in E4. discriminate. }
      rewrite E5. split; [reflexivity|]. split; [reflexivity|].
      split; [apply Mid1; reflexivity|]. split; [reflexivity|]. cbn.
      apply Z.eqb_eq in E3. apply Z.eqb_neq in E2. repeat split; auto; lia.
  - destruct (flush_pending_wide (set_d_last_flush s flush) z)
      as (s' & x & Efp & Hpd & Hxl & Hbx & Hok' & Hce & Hae & Hbv' & Hpn & Hpo).
    { exact Hok. } { exact Hbv. } { exact HaoW. } { exact HtoW. }
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
      split; [|split; [reflexivity|left; reflexivity]].
      eapply (entw_mid_step W HI dict wrap D O inb nin aout tin tout flush s z _ x _ CF HF M0 Hni Hzo).
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
      split; [|split; [reflexivity|]].
      * eapply (entw_mid_step W HI dict wrap D O inb nin aout tin tout flush s z _ x _ CF HF M0 Hni Hzo).
        all: cbn; try reflexivity; try exact Hok'; try exact Hbx; try exact Hpd; try congruence; try lia.
        all: try (eapply ent_core_eq_trans; [exact Hce1|]; exact Hce).
        all: try (rewrite Hzo; reflexivity).
        all: try exact Hbv'.
        all: try (unfold d_pending in *; cbn; lia).
      * cbn. repeat split; try congruence; try lia.
Qed.
