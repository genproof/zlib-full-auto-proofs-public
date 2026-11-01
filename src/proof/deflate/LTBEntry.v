(** * deflate_bound theory: deflate()'s entry stage inside [Mid]

    [Mid W HI n b pos0 inb aout tin0 tout0 flush gz0 s z] (LTBDefs): the state of one deflate() call with
    flush Z_NO_FLUSH or Z_FINISH.  The last clause of each lemma: deflate_bound's single call (Z_FINISH, all the
    data, b bytes of output space) never stops early. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTBOut Zlib.proof.deflate.LTBArith.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** Local copies of the proofs of LTBOut.out_proof and LTBArith.arith_proof, under names of this file. *)
Lemma en_definedb : forall b lo hi, mb_defined b lo hi -> mb_definedb b lo hi = true.
Proof.
  intros b lo hi [H0 [H1 H2]]. unfold mb_definedb.
  rewrite (proj2 (Z.leb_le _ _) H0), (proj2 (Z.leb_le _ _) H1). cbn [andb].
  apply forallb_forall. intros i Hi. apply in_map_iff in Hi. destruct Hi as [k [<- Hk]].
  apply in_seq in Hk. apply H2. lia.
Qed.

Lemma en_bytes : forall b lo hi, mb_ok b -> mb_defined b lo hi -> bytes (sublist lo hi (mb_val b)).
Proof.
  intros b lo hi [L Hb] [H0 [H1 H2]]. unfold bytes. apply Forall_forall. intros v Hv.
  apply In_Znth in Hv. destruct Hv as [i [Hi <-]].
  destruct (Z_le_gt_dec lo hi).
  - rewrite Zlength_sublist in Hi by lia. rewrite Znth_sublist by lia. apply Hb; [lia|]. apply H2; lia.
  - rewrite sublist_nil_gen in Hi by lia. rewrite Zlength_nil in Hi. lia.
Qed.

Lemma en_flush_pending_ok : forall s z,
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

Lemma en_body_div : forall c n, body c n =
  match c with
  | BTight => n + n / 4096 + n / 16384 + n / 33554432 + 7
  | BFixed => n + n / 8 + n / 256 + n / 512 + 4
  | BStore => n + n / 32 + n / 128 + n / 2048 + 7
  end.
Proof.
  intros c n; destruct c; unfold body; rewrite !Z.shiftr_div_pow2 by lia; reflexivity.
Qed.

Lemma en_divb : forall n d, 0 < d -> d * (n / d) <= n < d * (n / d) + d.
Proof. intros n d Hd. split; [apply Z.mul_div_le; lia|]. pose proof (Z.mul_succ_div_gt n d Hd). lia. Qed.

Ltac en_dv := repeat match goal with |- context [?n / ?d] =>
  let q := fresh "q" in pose proof (en_divb n d ltac:(lia)); set (q := n / d) in *; clearbody q end.

Lemma en_body_range : forall c n, 0 <= n <= 1048576 -> n + 4 <= body c n <= 2 * n + 7.
Proof. intros c n Hn. rewrite !en_body_div. destruct c; en_dv; lia. Qed.

Lemma en_acc_mid : forall c h e k n, 0 <= h -> 0 <= k -> minblk c * k <= e -> e <= n <= 1048576 ->
  xb c h e k + 10 <= 8 * (h + body c n).
Proof.
  intros c h e k n Hh Hk Hke Hn. rewrite !en_body_div. destruct c; unfold xb, minblk in *; en_dv.
  all: lia.
Qed.

Section Entry.
Variable W : dstate -> Prop.
Variable HI : hdr_inv.
Hypothesis CF : core_facts W.
Hypothesis HF : hdr_facts HI.

(** ** Helpers *)
Lemma outok_ranges : forall s, outok s -> 0 <= d_pending s /\ 0 <= d_bi_valid s.
Proof.
  intros s (_ & (B1 & _ & B3) & _). unfold d_pending, d_bi_valid. lia.
Qed.

Lemma core_eq_lf : forall s x, core_eq s (set_d_last_flush s x).
Proof. intros. unfold core_eq. repeat split; reflexivity. Qed.

Lemma tlen_range : forall w, 0 <= tlen w <= 8.
Proof. intros. unfold tlen. destruct (w =? 1); [lia|]. destruct (w =? 2); lia. Qed.

Lemma minblk_pos : forall c, 0 < minblk c.
Proof. destruct c; cbn; lia. Qed.

Lemma brun_facts : forall n b pos fin s tin tout adler,
  Brun W HI n b pos fin s tin tout adler ->
  0 <= d_pending s /\ 0 <= d_bi_valid s <= 7 /\ tout + d_pending s <= b /\ b <= 2113551 /\
  (d_status s = FINISH_STATE -> pos = n /\ fin = true) /\
  (d_status s <> FINISH_STATE -> tout + d_pending s < b).
Proof.
  intros n b pos fin s tin tout adler
    (H & w0 & HW & Ho & Hw0 & Hb & HH & Hn & Hpos & Htin & Htout & Hgz & Hlf & Hph).
  destruct (outok_ranges s Ho) as [Hp Hbi].
  pose proof (Zlength_nonneg H) as HH0. pose proof (tlen_range w0) as Ht.
  pose proof (en_body_range (bcls_of s) n Hn) as Hbr.
  unfold Gb in Hph.
  destruct Hph as [P0|[P1|[P2|P3]]].
  - destruct P0 as (Hst & _ & _ & _ & Ht0 & Hp0 & Hbi0 & _).
    rewrite Hst. unfold FINISH_STATE, INIT_STATE, GZIP_STATE.
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [destruct (w0 =? 2); intros; lia|]. intros; lia.
  - destruct P1 as (_ & _ & (k & HI1 & Hk) & _ & Hbi0 & _).
    destruct (hf_status HI HF _ _ _ _ HI1) as (_ & _ & Hst & _ & Hk2).
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [|intros; lia].
    unfold FINISH_STATE, EXTRA_STATE, NAME_STATE, COMMENT_STATE, HCRC_STATE in *. lia.
  - destruct P2 as (Hst & _ & Hbi7 & _ & E & k & HE & Hk0 & Hmk & Hg).
    destruct (cf_pos W CF s HW) as (L1 & L2 & L3 & L4).
    unfold ub in HE. unfold Gb in Hg. pose proof (minblk_pos (bcls_of s)).
    assert (0 <= E) by nia.
    pose proof (en_acc_mid (bcls_of s) (Zlength H) E k n HH0 Hk0 Hmk ltac:(lia)).
    rewrite Hst. unfold FINISH_STATE, BUSY_STATE.
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; intros; lia.
  - destruct P3 as (Hst & Hfin & Hpn & _ & _ & Hbi0 & _ & Hg). unfold Gb in Hg.
    split; [lia|]. split; [lia|].
    split; [destruct Hg as [(_ & Hg)|(_ & _ & Hg)]; lia|]. split; [lia|].
    split; [auto|]. intros; contradiction.
Qed.

Lemma brun_frame : forall n b pos fin s s' tin tout tout' adler,
  Brun W HI n b pos fin s tin tout adler ->
  core_eq s s' -> d_status s' = d_status s -> d_wrap s' = d_wrap s -> d_gzhead s' = d_gzhead s ->
  d_gzindex s' = d_gzindex s -> -2 <= d_last_flush s' <= 5 -> outok s' -> d_bi_valid s' = d_bi_valid s ->
  tout' + d_pending s' = tout + d_pending s -> 0 <= tout' ->
  (d_pending s = 0 -> hdr_bytes s' adler = hdr_bytes s adler) ->
  Brun W HI n b pos fin s' tin tout' adler.
Proof.
  intros n b pos fin s s' tin tout tout' adler
    (H & w0 & HW & Ho & Hw0 & Hb & HH & Hn & Hpos & Htin & Htout & Hgz & Hlf & Hph)
    Hce Est Ewr Egz Egi Hlf' Ho' Ebi Etp Ht' Ehd.
  destruct (outok_ranges s Ho) as [Hp Hbi]. destruct (outok_ranges s' Ho') as [Hp' Hbi'].
  pose proof (core_eq_fields s s' Hce) as (_ & _ & _ & _ & _ & _ & _ & Epbs & Esym & _).
  pose proof (bcls_core_eq s s' Hce) as Ecl. pose proof (ub_core_eq s s' Hce) as Eub.
  exists H, w0. rewrite Ecl.
  split; [exact (cf_frame W CF s s' HW Hce)|]. split; [exact Ho'|]. split; [exact Hw0|].
  split; [exact Hb|]. split; [exact HH|]. split; [exact Hn|]. split; [exact Hpos|].
  split; [exact Htin|]. split; [exact Ht'|].
  split; [unfold gzh_ok in *; rewrite Egz; exact Hgz|]. split; [exact Hlf'|].
  assert (EG : Gb s' tout' = Gb s tout) by (unfold Gb; lia).
  unfold bphase in *. rewrite EG, Est, Ewr, Esym, Eub, Ebi, Ecl.
  destruct Hph as [P0|[P1|[P2|P3]]].
  - left. destruct P0 as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
    rewrite Ehd by exact A6. repeat (split; [assumption|]). split; [lia|]. split; [lia|]. tauto.
  - right; left. destruct P1 as (A1 & A2 & (k & HI1 & Hk) & A4 & A5 & A6 & A7).
    split; [exact A1|]. split; [exact A2|]. split.
    + exists k. split; [|lia]. apply (hf_frame HI HF s s' adler H k HI1); auto.
    + auto.
  - right; right; left. exact P2.
  - right; right; right. exact P3.
Qed.

Lemma mid_msg : forall n b pos0 inb aout tin0 tout0 flush gz0 s z m,
  Mid W HI n b pos0 inb aout tin0 tout0 flush gz0 s z ->
  Mid W HI n b pos0 inb aout tin0 tout0 flush gz0 s (set_z_msg z m).
Proof. intros. destruct z; exact H. Qed.

Lemma entry_tail_none : forall s z,
  (d_status s = FINISH_STATE -> z_avail_in z = 0) ->
  (if (d_status s =? FINISH_STATE) && negb (z_avail_in z =? 0) then
     Some (s, set_z_msg z (Some Z_BUF_ERROR), Some Z_BUF_ERROR)
   else Some (s, z, None)) = Some (s, z, None).
Proof.
  intros s z H. destruct (Z.eqb_spec (d_status s) FINISH_STATE) as [E|E]; [|reflexivity].
  rewrite (H E). reflexivity.
Qed.

Lemma mid_step : forall n b pos0 inb aout tin0 tout0 flush gz0 s z s' z' x,
  Mid W HI n b pos0 inb aout tin0 tout0 flush gz0 s z ->
  z_in z' = z_in z -> z_next_in z' = z_next_in z -> z_avail_in z' = z_avail_in z ->
  z_total_in z' = z_total_in z -> z_out z' = z_out z ++ x -> z_avail_out z' = z_avail_out z - Zlength x ->
  z_total_out z' = z_total_out z + Zlength x -> z_adler z' = z_adler z ->
  Zlength x <= z_avail_out z -> bytes x ->
  core_eq s s' -> d_status s' = d_status s -> d_wrap s' = d_wrap s -> d_gzhead s' = d_gzhead s ->
  d_gzindex s' = d_gzindex s -> -2 <= d_last_flush s' <= 5 -> outok s' -> d_bi_valid s' = d_bi_valid s ->
  d_pending s' = d_pending s - Zlength x ->
  (d_pending s = 0 -> hdr_bytes s' (z_adler z) = hdr_bytes s (z_adler z)) ->
  Mid W HI n b pos0 inb aout tin0 tout0 flush gz0 s' z'.
Proof.
  intros n b pos0 inb aout tin0 tout0 flush gz0 s z s' z' x
    ((Hin & Hni & Hav & Htin & Hao & Hol & Hto & Hby) & Hbytes & Hpos0 & Hle & Hfl & Hfin & Haout &
     Htin0 & Htout0 & Hgz & Hbr)
    E1 E2 E3 E4 E5 E6 E7 E8 Hx Hbx Hce Est Ewr Egz Egi Hlf Ho Ebi Ep Ehd.
  pose proof (Zlength_nonneg x). pose proof (Zlength_nonneg (z_out z)).
  split; [|split; [exact Hbytes|]].
  { unfold cframe. rewrite E1, E2, E3, E4, E5, E6, E7, Zlength_app.
    repeat split; try lia; try assumption. unfold bytes in *. apply Forall_app. split; assumption. }
  repeat (split; [assumption|]). split; [rewrite Egz; exact Hgz|].
  rewrite E2, E4, E7, E8.
  apply (brun_frame _ _ _ _ s s' _ _ _ _ Hbr Hce Est Ewr Egz Egi Hlf Ho Ebi); [lia|lia|exact Ehd].
Qed.

(** Stage 1: the checks, last_flush, the flush of what is pending. *)
Lemma entry_stage : forall n b pos0 inb aout tin0 tout0 flush gz0 s z,
  Mid W HI n b pos0 inb aout tin0 tout0 flush gz0 s z -> z_next_in z = 0 -> z_out z = [] ->
  exists s1 z1 o, c_deflate_entry s z flush = Some (s1, z1, o) /\
    Mid W HI n b pos0 inb aout tin0 tout0 flush gz0 s1 z1 /\ z_next_in z1 = 0 /\
    d_status s1 = d_status s /\ d_wrap s1 = d_wrap s /\
    match o with
    | None => d_pending s1 = 0 /\ d_po s1 = 0 /\ d_bi_valid s1 <= 7 /\
              (d_status s1 = FINISH_STATE -> z_avail_in z1 = 0)
    | Some c => (c = Z_OK \/ c = Z_BUF_ERROR) /\ (c = Z_BUF_ERROR -> z_avail_out z1 = aout)
    end /\
    (flush = Z_FINISH -> pos0 = 0 -> b <= tout0 + aout -> d_status s <> FINISH_STATE -> o = None).
Proof.
  intros n b pos0 inb aout tin0 tout0 flush gz0 s z HM Hni Hzo.
  pose proof HM as HM0.
  destruct HM as ((Hin & _ & Hav & Htin & Hao & Hol & Hto & Hby) & Hbytes & Hpos0 & Hle & Hfl & Hfin & Haout &
                  Htin0 & Htout0 & Hgz & Hbr).
  rewrite Hni in *. rewrite Hzo in *. rewrite Zlength_nil in Hol, Hto.
  destruct (brun_facts _ _ _ _ _ _ _ _ Hbr) as (Hp & Hbi & Htb & Hb & Hfn & Hnf).
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
  assert (Hm1 : Mid W HI n b pos0 inb aout tin0 tout0 flush gz0 (set_d_last_flush s flush) z).
  { apply (mid_step _ _ _ _ _ _ _ _ _ s z _ _ [] HM0); try reflexivity.
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
    split; [reflexivity|]. split; [apply mid_msg; exact HM0|].
    split; [destruct z; exact Hni|]. split; [reflexivity|]. split; [reflexivity|].
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
        split; [reflexivity|]. split; [apply mid_msg; exact Hm1|].
        split; [destruct z; exact Hni|]. split; [reflexivity|]. split; [reflexivity|].
        split; [split; [right; reflexivity|intros _; destruct z; cbn in *; lia]|].
        intros Hf. subst flush. apply andb_true_iff in Er. destruct Er as [_ Er]. discriminate Er.
      * exists (set_d_last_flush s flush), z, None.
        split; [unfold then_stage; cbn [bind]; apply entry_tail_none; intros E; exact (proj2 (Hfn' E))|].
        split; [exact Hm1|]. split; [exact Hni|]. split; [reflexivity|]. split; [reflexivity|].
        split; [|intros; reflexivity].
        split; [exact Hp0|]. split; [destruct Ho as (_ & _ & _ & _ & _ & Hpo); exact (Hpo Hp0)|].
        split; [change (d_bi_valid (set_d_last_flush s flush)) with (d_bi_valid s); lia|]. intros E. exact (proj2 (Hfn' E)).
    + exists (set_d_last_flush s flush), z, None.
      split; [unfold then_stage; cbn [bind]; apply entry_tail_none; intros E; exact (proj2 (Hfn' E))|].
      split; [exact Hm1|]. split; [exact Hni|]. split; [reflexivity|]. split; [reflexivity|].
      split; [|intros; reflexivity].
      split; [exact Hp0|]. split; [destruct Ho as (_ & _ & _ & _ & _ & Hpo); exact (Hpo Hp0)|].
      split; [change (d_bi_valid (set_d_last_flush s flush)) with (d_bi_valid s); lia|]. intros E. exact (proj2 (Hfn' E)).
  - destruct (en_flush_pending_ok (set_d_last_flush s flush) z) as
      (s2 & x & Ef & Epend & Ex & Hbx & Ho2 & Hce2 & Hae2 & Ebi2 & Ep2 & Epo2);
      [exact Ho|change (d_bi_valid (set_d_last_flush s flush)) with (d_bi_valid s); lia|lia|destruct z; cbn in *; lia|].
    change (d_pending (set_d_last_flush s flush)) with (d_pending s) in Ex, Ep2.
    change (d_bi_valid (set_d_last_flush s flush)) with (d_bi_valid s) in Ebi2.
    destruct Hae2 as (Est2 & Ewr2 & Egz2 & Egi2 & Elf2 & _). cbn in Est2, Ewr2, Egz2, Egi2, Elf2.
    rewrite Ef. cbn [bind z_avail_out].
    assert (Hm2 : forall lf, -2 <= lf <= 5 -> Mid W HI n b pos0 inb aout tin0 tout0 flush gz0
      (set_d_last_flush s2 lf)
      (mkST (z_in z) (z_next_in z) (z_avail_in z) (z_total_in z) (z_out z ++ x)
         (z_avail_out z - Zlength x) (z_total_out z + Zlength x) (z_adler z) (z_msg z))).
    { intros lf Hlf'. apply (mid_step _ _ _ _ _ _ _ _ _ s z _ _ x HM0); try reflexivity.
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
      split; [|intros; reflexivity].
      assert (Hp2 : d_pending s2 = 0) by lia.
      split; [exact Hp2|]. split; [exact (Epo2 Hp2)|]. split; [lia|].
      cbn. rewrite Est2. intros E. exact (proj2 (Hfn' E)).
Qed.

End Entry.
