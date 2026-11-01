(** * deflate_api theory: stage 1 of deflate(), the entry

    [c_deflate_entry] from the start of a call ([Mid] at the stream of the call, nothing consumed or produced):
    never Z_STREAM_ERROR (FINISH only with Z_FINISH), Z_BUF_ERROR without progress, Z_OK after flush_pending
    filled the output space, or on to the header stages with nothing pending and last_flush = flush. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTApiOut Zlib.proof.deflate.LTApiArith.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** flush_pending (a copy of the proof of LTApiOut.flush_pending_ok) *)
Lemma ent_definedb : forall b lo hi, mb_defined b lo hi -> mb_definedb b lo hi = true.
Proof.
  intros b lo hi [H0 [H1 H2]]. unfold mb_definedb.
  rewrite (proj2 (Z.leb_le _ _) H0), (proj2 (Z.leb_le _ _) H1). cbn [andb].
  apply forallb_forall. intros i Hi. apply in_map_iff in Hi. destruct Hi as [k [<- Hk]].
  apply in_seq in Hk. apply H2. lia.
Qed.

Lemma ent_bytes : forall b lo hi, mb_ok b -> mb_defined b lo hi -> bytes (sublist lo hi (mb_val b)).
Proof.
  intros b lo hi [L Hb] [H0 [H1 H2]]. unfold bytes. apply Forall_forall. intros v Hv.
  apply In_Znth in Hv. destruct Hv as [i [Hi <-]].
  destruct (Z_le_gt_dec lo hi).
  - rewrite Zlength_sublist in Hi by lia. rewrite Znth_sublist by lia. apply Hb; [lia|]. apply H2; lia.
  - rewrite sublist_nil_gen in Hi by lia. rewrite Zlength_nil in Hi. lia.
Qed.

Lemma ent_flush_pending : forall s z,
  outok s -> d_bi_valid s <= 7 -> 0 <= z_avail_out z <= 1073741824 -> 0 <= z_total_out z <= 1099511627776 ->
  exists s' x,
    c_flush_pending s z =
      Some (s', mkST (z_in z) (z_next_in z) (z_avail_in z) (z_total_in z) (z_out z ++ x)
                     (z_avail_out z - Zlength x) (z_total_out z + Zlength x) (z_adler z) (z_msg z)) /\
    pend s = x ++ pend s' /\ Zlength x = Z.min (d_pending s) (z_avail_out z) /\ bytes x /\
    outok s' /\ core_eq s s' /\ api_eq s s' /\ d_bi_valid s' = d_bi_valid s /\
    d_pending s' = d_pending s - Zlength x /\ (d_pending s' = 0 -> d_po s' = 0).
Proof.
  intros s z Hok Hbv Hao Hto.
  destruct s as [st po wr gzh gzi meth lf wsz wbits wmask win winsz prv hd insh hsz hbits hmask hshift bs mlen pm
                 mav ss ms la pl mcl mlm gm nm ins hw sl pbs tr pbm].
  destruct tr. destruct tr_out. destruct z.
  unfold outok, d_bi_valid, pend, d_pb, d_pending in *; cbn in *.
  destruct Hok as [Hmb [Hbits [Hpo0 [Hpos [Hdef Hp0]]]]].
  unfold c_flush_pending, c_tr_flush_bits, c_bi_flush, d_out, d_pending; cbn.
  destruct (o_bi_valid =? 16) eqn:E1; [lia|]. destruct (o_bi_valid >=? 8) eqn:E2; [lia|]. cbn.
  unfold bits_ok in Hbits; cbn in Hbits.
  assert (Hlen : (if o_pending >? z_avail_out then z_avail_out else u32 o_pending) = Z.min o_pending z_avail_out).
  { destruct (Z.gtb_spec o_pending z_avail_out). lia. unfold u32. rewrite Z.mod_small by lia. lia. }
  rewrite Hlen. clear Hlen.
  pose proof Hdef as Hdef'. destruct Hdef' as [Hd0 [Hd1 Hd2]]; cbn in Hd1, Hd2.
  pose proof Hmb as Hmb'. destruct Hmb' as [Hm1 Hm2]; cbn in Hm1, Hm2.
  destruct (Z.eqb_spec (Z.min o_pending z_avail_out) 0) as [H0|H0].
  - eexists _, []. rewrite app_nil_r, Zlength_nil, Z.sub_0_r, Z.add_0_r. split; [reflexivity|].
    cbn. unfold core_eq, api_eq, strip, sym_region, bits_ok, d_L; cbn.
    repeat split; auto; try lia; try (eapply proj1; apply Hm2; auto); try (eapply proj2; apply Hm2; auto);
      constructor.
  - unfold mb_read. rewrite ent_definedb.
    2:{ split; [|split]; cbn in *; try lia. intros; apply Hd2; lia. }
    replace ((0 <=? Z.min o_pending z_avail_out) && true)%bool with true
      by (symmetry; apply andb_true_iff; split; auto; apply Z.leb_le; lia).
    cbn. unfold out_put; cbn. rewrite Zlength_sublist by lia.
    replace (po + Z.min o_pending z_avail_out - po <=? z_avail_out) with true by (symmetry; apply Z.leb_le; lia).
    cbn. unfold u64. rewrite Z.mod_small by lia.
    set (len := Z.min o_pending z_avail_out) in *.
    assert (Hx : Zlength (sublist po (po + len) o_buf) = len) by (rewrite Zlength_sublist; lia).
    assert (Hxb : bytes (sublist po (po + len) o_buf)).
    { apply (ent_bytes {| mb_val := o_buf; mb_def := pbm |}); auto.
      split; [|split]; cbn; try lia. intros; apply Hd2; lia. }
    assert (Hsp : sublist po (po + o_pending) o_buf =
                  sublist po (po + len) o_buf ++ sublist (po + len) (po + o_pending) o_buf).
    { rewrite sublist_split with (mid := po + len) by lia. reflexivity. }
    destruct (Z.eqb_spec (o_pending - len) 0) as [H1|H1].
    + eexists _, (sublist po (po + len) o_buf). rewrite Hx. split; [reflexivity|].
      cbn. unfold core_eq, api_eq, strip, sym_region, bits_ok, d_L; cbn.
      rewrite H1. rewrite Hsp.
      repeat split; auto; try lia; try (eapply proj1; apply Hm2; auto); try (eapply proj2; apply Hm2; auto);
        try (cbn; lia).
      f_equal. rewrite sublist_nil_gen by lia. reflexivity.
    + eexists _, (sublist po (po + len) o_buf). rewrite Hx. split; [reflexivity|].
      cbn. unfold core_eq, api_eq, strip, sym_region, bits_ok, d_L; cbn.
      rewrite Hsp. replace (po + len + (o_pending - len)) with (po + o_pending) by lia.
      repeat split; auto; try lia; try (eapply proj1; apply Hm2; auto); try (eapply proj2; apply Hm2; auto);
        try (cbn; lia).
      cbn. intros; apply Hd2; lia.
Qed.

(** ** core_eq *)
Lemma ent_core_eq_trans : forall s1 s2 s3, core_eq s1 s2 -> core_eq s2 s3 -> core_eq s1 s3.
Proof.
  unfold core_eq. intros s1 s2 s3 (A1 & A2 & A3 & A4) (B1 & B2 & B3 & B4).
  repeat split; congruence.
Qed.

Lemma ent_core_eq_lf : forall s f, core_eq s (set_d_last_flush s f).
Proof. intros. unfold core_eq, strip, sym_region, d_L. cbn. repeat split; reflexivity. Qed.

Lemma ent_core_eq_fields : forall s s', core_eq s s' ->
  d_block_start s' = d_block_start s /\ d_strstart s' = d_strstart s /\
  d_lookahead s' = d_lookahead s /\ d_pending_buf_size s' = d_pending_buf_size s /\ d_sym_next s' = d_sym_next s.
Proof.
  intros s s' (A & _). unfold strip in A.
  pose proof (f_equal d_block_start A) as E1. pose proof (f_equal d_strstart A) as E2.
  pose proof (f_equal d_lookahead A) as E3. pose proof (f_equal d_pending_buf_size A) as E4.
  pose proof (f_equal d_sym_next A) as E5. cbn in E1, E2, E3, E4, E5.
  unfold d_sym_next, set_out in *. cbn in E5. destruct (d_tr s), (d_tr s'). cbn in *.
  repeat split; auto.
Qed.

(** ** Iapi after a stage that only hands pending bytes [x] out and sets last_flush *)
Lemma ent_iapi_frame : forall W HI dict wrap D O fin s tin tout adler s' x,
  core_facts W -> hdr_facts HI -> Iapi W HI dict wrap D O fin s tin tout adler ->
  core_eq s s' -> outok s' -> d_status s' = d_status s -> d_wrap s' = d_wrap s -> d_gzhead s' = d_gzhead s ->
  d_gzindex s' = d_gzindex s -> d_bi_valid s' = d_bi_valid s ->
  pend s = x ++ pend s' -> bytes x -> d_pending s' = d_pending s - Zlength x ->
  -1 <= d_last_flush s' <= 5 ->
  Iapi W HI dict wrap D (O ++ x) fin s' tin (tout + Zlength x) adler.
Proof.
  intros W HI dict wrap D O fin s tin tout adler s' x CF HF IA Hce Hok Hst Hwr Hgz Hgi Hbv Hpd Hbx Hpn Hlf.
  destruct IA as (HW & Hok0 & Hwr0 & Hw2 & Hbd & Hld & Hlf0 & Hgz0 & Htout & HbO & HbD & HtD & Hfin & Hdz & Hph).
  destruct (ent_core_eq_fields s s' Hce) as (Ebs & Ess & Ela & Epb & Esy).
  split; [eapply (cf_frame W CF); eauto|].
  split; [exact Hok|]. do 4 (split; [assumption|]).
  split; [lia|]. split; [rewrite Hgz; exact Hgz0|].
  split; [rewrite Zlength_app; lia|]. split; [unfold bytes in *; apply Forall_app; auto|].
  split; [assumption|]. split; [assumption|]. split; [rewrite Hst; assumption|].
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
      * eapply (hf_frame HI HF); eauto.
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

(** ** Mid after such a stage, at the start of a call *)
Lemma ent_mid_step : forall W HI dict wrap D O inb aout tin tout flush s z s' x z',
  core_facts W -> hdr_facts HI -> Mid W HI dict wrap D O inb aout tin tout flush s z ->
  z_next_in z = 0 -> z_out z = [] ->
  core_eq s s' -> outok s' -> d_status s' = d_status s -> d_wrap s' = d_wrap s -> d_gzhead s' = d_gzhead s ->
  d_gzindex s' = d_gzindex s -> d_bi_valid s' = d_bi_valid s ->
  pend s = x ++ pend s' -> bytes x -> d_pending s' = d_pending s - Zlength x ->
  -1 <= d_last_flush s' <= 5 -> Zlength x <= z_avail_out z ->
  z_in z' = z_in z -> z_next_in z' = 0 -> z_avail_in z' = z_avail_in z -> z_total_in z' = z_total_in z ->
  z_out z' = x -> z_avail_out z' = z_avail_out z - Zlength x -> z_total_out z' = z_total_out z + Zlength x ->
  z_adler z' = z_adler z ->
  Mid W HI dict wrap D O inb aout tin tout flush s' z'.
Proof.
  intros W HI dict wrap D O inb aout tin tout flush s z s' x z' CF HF M Hni Hzo Hce Hok Hst Hwr Hgz Hgi Hbv
    Hpd Hbx Hpn Hlf Hxl Z1 Z2 Z3 Z4 Z5 Z6 Z7 Z8.
  destruct M as ((Hin & Hn0 & Hai & Hti & Hao0 & Hzl & Hto & Hzb) & Hsz1 & Hsz2 & IA).
  rewrite Hzo, Zlength_nil in *.
  split; [|split; [assumption|split; [assumption|]]].
  - unfold zrun. rewrite Z1, Z2, Z3, Z4, Z5, Z6, Z7. rewrite Hni in *. repeat split; auto; lia.
  - assert (Ef : fin_of flush inb z' = fin_of flush inb z) by (unfold fin_of; rewrite Z2, Hni; reflexivity).
    rewrite Ef, Z2, Z4, Z5, Z7, Z8. rewrite Hni in IA. rewrite sublist_nil, !app_nil_r in IA. rewrite sublist_nil, app_nil_r.
    eapply ent_iapi_frame; eauto.
Qed.

Lemma entry_ok : forall W HI dict wrap D O inb aout tin tout flush s z,
  core_facts W -> hdr_facts HI ->
  Mid W HI dict wrap D O inb aout tin tout flush s z ->
  z_next_in z = 0 -> z_out z = [] -> z_avail_out z = aout -> aout <= 1048576 -> 0 <= flush <= 5 ->
  exists s1 z1 o, c_deflate_entry s z flush = Some (s1, z1, o) /\ d_gzhead s1 = d_gzhead s /\
    Mid W HI dict wrap D O inb aout tin tout flush s1 z1 /\
    match o with
    | Some c => c = Z_OK \/ (c = Z_BUF_ERROR /\ z_next_in z1 = 0 /\ z_out z1 = [])
    | None => d_pending s1 = 0 /\ d_last_flush s1 = flush /\ 0 < z_avail_out z1 /\ d_status s1 = d_status s /\
              (d_status s1 = FINISH_STATE -> z_avail_in z1 = 0)
    end.
Proof.
  intros W HI dict wrap D O inb aout tin tout flush s z CF HF M Hni Hzo Hao Haout Hfl.
  pose proof M as M0.
  destruct M as ((Hin & Hn0 & Hai & Hti & Hao0 & Hzl & Hto & Hzb) & Hsz1 & Hsz2 & IA).
  rewrite Hzo, Zlength_nil in *.
  destruct IA as (HW & Hok & Hwr & Hw2 & Hbd & Hld & Hlf & Hgz & Htout & HbO & HbD & HtD & Hfin & _ & Hph).
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
            Mid W HI dict wrap D O inb aout tin tout flush (set_d_last_flush s flush) z').
  { intros z' Z1 Z2 Z3 Z4 Z5 Z6 Z7 Z8.
    eapply (ent_mid_step W HI dict wrap D O inb aout tin tout flush s z _ [] z' CF HF M0 Hni Hzo Hce1);
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
  - destruct (ent_flush_pending (set_d_last_flush s flush) z)
      as (s' & x & Efp & Hpd & Hxl & Hbx & Hok' & Hce & Hae & Hbv' & Hpn & Hpo).
    { exact Hok. } { exact Hbv. } { lia. } { rewrite Htout, app_nil_r. pose proof (Zlength_nonneg O). lia. }
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
      eapply (ent_mid_step W HI dict wrap D O inb aout tin tout flush s z _ x _ CF HF M0 Hni Hzo).
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
      * eapply (ent_mid_step W HI dict wrap D O inb aout tin tout flush s z _ x _ CF HF M0 Hni Hzo).
        all: cbn; try reflexivity; try exact Hok'; try exact Hbx; try exact Hpd; try congruence; try lia.
        all: try (eapply ent_core_eq_trans; [exact Hce1|]; exact Hce).
        all: try (rewrite Hzo; reflexivity).
        all: try exact Hbv'.
        all: try (unfold d_pending in *; cbn; lia).
      * cbn. repeat split; try congruence; try lia.
Qed.

