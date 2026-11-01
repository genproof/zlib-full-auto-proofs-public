(** * The deflateBound accounting for the short laws: stage 1 of deflate() inside [MidW]

    The checks, last_flush, the flush of what is pending (DModel4.c_deflate_entry).  Port of
    LTBEntry.entry_stage to the invariants of LTWBDefs.v, with two more facts for the clip() loops (LawFactsW2):
    the core part of the state is unchanged, and at most the pending bytes are handed out.  The last clause: the
    single call of res_bound (Z_FINISH, all the data, b bytes of output space) does not stop here. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTWBKit.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** deflate()'s flush_pending (LTBEntry.en_flush_pending_ok) with up to 2^32-1 bytes of output space: [x],
    the first min(pending, avail_out) pending bytes, go to next_out; total_out does not wrap as long as
    total_out + avail_out stays below 2^64. *)
Lemma en_flush_pending_ok_w : forall s z,
  outok s -> d_bi_valid s <= 7 -> 0 <= z_avail_out z <= 4294967295 -> 0 <= z_total_out z -> z_total_out z + z_avail_out z <= 18446744073709551615 ->
  exists s' x,
    c_flush_pending s z =
      Some (s', mkST (z_in z) (z_next_in z) (z_avail_in z) (z_total_in z) (z_out z ++ x)
                     (z_avail_out z - Zlength x) (z_total_out z + Zlength x) (z_adler z) (z_msg z)) /\
    pend s = x ++ pend s' /\ Zlength x = Z.min (d_pending s) (z_avail_out z) /\ bytes x /\
    outok s' /\ core_eq s s' /\ api_eq s s' /\ d_bi_valid s' = d_bi_valid s /\
    d_pending s' = d_pending s - Zlength x /\ (d_pending s' = 0 -> d_po s' = 0).
Proof.
  intros s z Hok Hbv Hao Hto Hto'.
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
  - unfold mb_read. rewrite en_definedb.
    2:{ split; [|split]; cbn in *; try lia. intros; apply Hd2; lia. }
    replace ((0 <=? Z.min o_pending z_avail_out) && true)%bool with true
      by (symmetry; apply andb_true_iff; split; auto; apply Z.leb_le; lia).
    cbn. unfold out_put; cbn. rewrite Zlength_sublist by lia.
    replace (po + Z.min o_pending z_avail_out - po <=? z_avail_out) with true by (symmetry; apply Z.leb_le; lia).
    cbn. unfold u64. rewrite Z.mod_small by lia.
    set (len := Z.min o_pending z_avail_out) in *.
    assert (Hx : Zlength (sublist po (po + len) o_buf) = len) by (rewrite Zlength_sublist; lia).
    assert (Hxb : bytes (sublist po (po + len) o_buf)).
    { apply (en_bytes {| mb_val := o_buf; mb_def := pbm |}); auto.
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

Lemma entry_stage_w : forall W HI, core_facts_w W -> hdr_facts_w HI ->
  forall n b pos0 inb aout tin0 tout0 flush gz0 s z,
  MidW W HI n b pos0 inb aout tin0 tout0 flush gz0 s z -> z_next_in z = 0 -> z_out z = [] ->
  exists s1 z1 o, c_deflate_entry s z flush = Some (s1, z1, o) /\
    MidW W HI n b pos0 inb aout tin0 tout0 flush gz0 s1 z1 /\ z_next_in z1 = 0 /\
    d_status s1 = d_status s /\ d_wrap s1 = d_wrap s /\ core_eq s s1 /\
    (o = None -> Zlength (z_out z1) <= d_pending s) /\
    match o with
    | None => d_pending s1 = 0 /\ d_po s1 = 0 /\ d_bi_valid s1 <= 7 /\
              (d_status s1 = FINISH_STATE -> z_avail_in z1 = 0)
    | Some c => (c = Z_OK \/ c = Z_BUF_ERROR) /\ (c = Z_BUF_ERROR -> z_avail_out z1 = aout)
    end /\
    (flush = Z_FINISH -> pos0 = 0 -> b <= tout0 + aout -> d_status s <> FINISH_STATE -> o = None).
Proof.
  intros W HI CF HF n b pos0 inb aout tin0 tout0 flush gz0 s z HM Hni Hzo.
  pose proof HM as HM0.
  destruct HM as ((Hin & _ & Hav & Htin & Hao & Hol & Hto & Hby) & Hbytes & Hpos0 & Hle & Hfl & Hfin & Haout &
                  Htin0 & Htout0 & Hgz & Hbr).
  rewrite Hni in *. rewrite Hzo in *. rewrite Zlength_nil in Hol, Hto.
  destruct (brunw_facts W HI CF HF _ _ _ _ _ _ _ _ Hbr) as (Hp & Hbi & _ & Htb & Hb & _ & _ & _ & Hfn & Hnf).
  assert (Hfn' : d_status s = FINISH_STATE -> flush = Z_FINISH /\ z_avail_in z = 0).
  { intros E. destruct (Hfn E) as [E1 E2]. apply Z.eqb_eq in E2. split; [exact E2|].
    apply Hfin in E2. lia. }
  assert (Hst : (d_status s =? FINISH_STATE) && negb (flush =? Z_FINISH) = false).
  { destruct (Z.eqb_spec (d_status s) FINISH_STATE) as [E|E]; [|reflexivity].
    destruct (Hfn' E) as [-> _]. reflexivity. }
  assert (Hlf : -2 <= d_last_flush s <= 5)
    by (destruct Hbr as (? & ? & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hlf & _); exact Hlf).
  assert (Ho : outok s)
    by (destruct Hbr as (? & ? & _ & Ho & _); exact Ho).
  assert (Hm1 : MidW W HI n b pos0 inb aout tin0 tout0 flush gz0 (set_d_last_flush s flush) z).
  { apply (midw_step W HI CF HF _ _ _ _ _ _ _ _ _ s z _ _ [] HM0); try reflexivity.
    - rewrite app_nil_r. reflexivity.
    - rewrite Zlength_nil. lia.
    - rewrite Zlength_nil. lia.
    - rewrite Zlength_nil. lia.
    - constructor.
    - apply core_eq_lf.
    - cbn. destruct Hfl as [-> | ->]; unfold Z_NO_FLUSH, Z_FINISH; lia.
    - exact Ho.
    - rewrite Zlength_nil. change (d_pending (set_d_last_flush s flush)) with (d_pending s). lia. }
  unfold c_deflate_entry. rewrite Hst.
  destruct (Z.eqb_spec (z_avail_out z) 0) as [Ha0|Ha0].
  { exists s, (set_z_msg z (Some Z_BUF_ERROR)), (Some Z_BUF_ERROR).
    split; [reflexivity|]. split; [apply midw_msg; exact HM0|].
    split; [destruct z; exact Hni|]. split; [reflexivity|]. split; [reflexivity|].
    split; [apply core_eq_refl|]. split; [intros E; discriminate E|].
    split; [split; [right; reflexivity|intros _; destruct z; cbn in *; lia]|].
    intros Hf Hp0 Hbo Hns. specialize (Hnf Hns). lia. }
  change (d_pending (set_d_last_flush s flush)) with (d_pending s).
  destruct (Z.eqb_spec (d_pending s) 0) as [Hp0|Hp0]; cbn [negb].
  - destruct (Z.eqb_spec (z_avail_in z) 0) as [Hi0|Hi0].
    + assert (Hii : in_int (d_last_flush s * 2) = true).
      { unfold in_int. apply andb_true_intro. split; apply Z.leb_le; lia. }
      rewrite Hii. cbn [guard bind].
      destruct ((rank flush <=? rank (d_last_flush s)) && negb (flush =? Z_FINISH)) eqn:Er.
      * exists (set_d_last_flush s flush), (set_z_msg z (Some Z_BUF_ERROR)), (Some Z_BUF_ERROR).
        split; [reflexivity|]. split; [apply midw_msg; exact Hm1|].
        split; [destruct z; exact Hni|]. split; [reflexivity|]. split; [reflexivity|].
        split; [apply core_eq_lf|]. split; [intros E; discriminate E|].
        split; [split; [right; reflexivity|intros _; destruct z; cbn in *; lia]|].
        intros Hf. subst flush. apply andb_true_iff in Er. destruct Er as [_ Er]. discriminate Er.
      * exists (set_d_last_flush s flush), z, None.
        split; [unfold then_stage; cbn [bind]; apply entry_tail_none; intros E; exact (proj2 (Hfn' E))|].
        split; [exact Hm1|]. split; [exact Hni|]. split; [reflexivity|]. split; [reflexivity|].
        split; [apply core_eq_lf|]. split; [intros _; rewrite Hzo, Zlength_nil; lia|].
        split; [|intros; reflexivity].
        split; [exact Hp0|]. split; [destruct Ho as (_ & _ & _ & _ & _ & Hpo); exact (Hpo Hp0)|].
        split; [change (d_bi_valid (set_d_last_flush s flush)) with (d_bi_valid s); lia|]. intros E. exact (proj2 (Hfn' E)).
    + exists (set_d_last_flush s flush), z, None.
      split; [unfold then_stage; cbn [bind]; apply entry_tail_none; intros E; exact (proj2 (Hfn' E))|].
      split; [exact Hm1|]. split; [exact Hni|]. split; [reflexivity|]. split; [reflexivity|].
      split; [apply core_eq_lf|]. split; [intros _; rewrite Hzo, Zlength_nil; lia|].
      split; [|intros; reflexivity].
      split; [exact Hp0|]. split; [destruct Ho as (_ & _ & _ & _ & _ & Hpo); exact (Hpo Hp0)|].
      split; [change (d_bi_valid (set_d_last_flush s flush)) with (d_bi_valid s); lia|]. intros E. exact (proj2 (Hfn' E)).
  - destruct (en_flush_pending_ok_w (set_d_last_flush s flush) z) as
      (s2 & x & Ef & Epend & Ex & Hbx & Ho2 & Hce2 & Hae2 & Ebi2 & Ep2 & Epo2);
      [exact Ho|change (d_bi_valid (set_d_last_flush s flush)) with (d_bi_valid s); lia|lia|destruct z; cbn in *; lia|
       destruct z; cbn in *; lia|].
    change (d_pending (set_d_last_flush s flush)) with (d_pending s) in Ex, Ep2.
    change (d_bi_valid (set_d_last_flush s flush)) with (d_bi_valid s) in Ebi2.
    destruct Hae2 as (Est2 & Ewr2 & Egz2 & Egi2 & Elf2 & _). cbn in Est2, Ewr2, Egz2, Egi2, Elf2.
    rewrite Ef. cbn [bind z_avail_out].
    assert (Hm2 : forall lf, -2 <= lf <= 5 -> MidW W HI n b pos0 inb aout tin0 tout0 flush gz0
      (set_d_last_flush s2 lf)
      (mkST (z_in z) (z_next_in z) (z_avail_in z) (z_total_in z) (z_out z ++ x)
         (z_avail_out z - Zlength x) (z_total_out z + Zlength x) (z_adler z) (z_msg z))).
    { intros lf Hlf'. apply (midw_step W HI CF HF _ _ _ _ _ _ _ _ _ s z _ _ x HM0); try reflexivity.
      - pose proof (Z.min_spec (d_pending s) (z_avail_out z)). lia.
      - exact Hbx.
      - apply (core_eq_trans _ s2); [|apply core_eq_lf].
        apply (core_eq_trans _ (set_d_last_flush s flush)); [apply core_eq_lf|exact Hce2].
      - exact Est2.
      - exact Ewr2.
      - exact Egz2.
      - exact Egi2.
      - exact Hlf'.
      - exact Ho2.
      - exact Ebi2.
      - exact Ep2.
      - intros; contradiction. }
    pose proof (Z.min_spec (d_pending s) (z_avail_out z)) as Hmin.
    destruct (Z.eqb_spec (z_avail_out z - Zlength x) 0) as [Hz|Hz].
    + exists (set_d_last_flush s2 (-1)),
        (mkST (z_in z) (z_next_in z) (z_avail_in z) (z_total_in z) (z_out z ++ x)
           (z_avail_out z - Zlength x) (z_total_out z + Zlength x) (z_adler z) (z_msg z)), (Some Z_OK).
      split; [reflexivity|]. split; [apply Hm2; lia|].
      split; [exact Hni|]. split; [exact Est2|]. split; [exact Ewr2|].
      split; [apply (core_eq_trans _ s2); [apply (core_eq_trans _ (set_d_last_flush s flush)); [apply core_eq_lf|exact Hce2]|apply core_eq_lf]|].
      split; [intros E; discriminate E|].
      split; [split; [left; reflexivity|intros E; discriminate E]|].
      intros Hf Hpz Hbo Hns. specialize (Hnf Hns). lia.
    + assert (Hxp : Zlength x = d_pending s) by lia.
      exists s2,
        (mkST (z_in z) (z_next_in z) (z_avail_in z) (z_total_in z) (z_out z ++ x)
           (z_avail_out z - Zlength x) (z_total_out z + Zlength x) (z_adler z) (z_msg z)), None.
      assert (Hs2 : set_d_last_flush s2 (d_last_flush s2) = s2) by (destruct s2; reflexivity).
      split.
      { unfold then_stage; cbn [bind]. apply entry_tail_none. cbn. rewrite Est2.
        intros E. exact (proj2 (Hfn' E)). }
      split; [rewrite <- Hs2; apply Hm2; rewrite Elf2; destruct Hfl as [-> | ->];
              unfold Z_NO_FLUSH, Z_FINISH; lia|].
      split; [exact Hni|]. split; [exact Est2|]. split; [exact Ewr2|].
      split; [apply (core_eq_trans _ (set_d_last_flush s flush)); [apply core_eq_lf|exact Hce2]|].
      split; [intros _; cbn [z_out]; rewrite Zlength_app, Hzo, Zlength_nil; lia|].
      split; [|intros; reflexivity].
      assert (Hp2 : d_pending s2 = 0) by lia.
      split; [exact Hp2|]. split; [exact (Epo2 Hp2)|]. split; [lia|].
      cbn. rewrite Est2. intros E. exact (proj2 (Hfn' E)).
Qed.
