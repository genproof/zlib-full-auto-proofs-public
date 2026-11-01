(** * The deflateBound accounting for the short laws: stage 9 of deflate() (the trailer) inside [MidW]

    Port of LTBTrail.trailer_stage to the invariants of LTWBDefs.v.  Reached with Z_NO_FLUSH, or at FINISH_STATE
    with nothing pending and no input; with room for everything, Z_STREAM_END.  The core part of the state is
    unchanged. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTWBKit.
Require Import Zlib.proof.deflate.LTBTrail.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** flush_pending with up to 2^32-1 bytes of output space and total_out up to 2^63+2^62 (LTBTrail.tbo_flush_pending_ok
    with the limits of [MidW]; same proof). *)
Lemma tw_flush_pending_ok : forall s z,
  outok s -> d_bi_valid s <= 7 -> 0 <= z_avail_out z <= 4294967295 -> 0 <= z_total_out z <= 13835058055282163712 ->
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
  - unfold mb_read. rewrite LTBTrail.tbo_definedb.
    2:{ split; [|split]; cbn in *; try lia. intros; apply Hd2; lia. }
    replace ((0 <=? Z.min o_pending z_avail_out) && true)%bool with true
      by (symmetry; apply andb_true_iff; split; auto; apply Z.leb_le; lia).
    cbn. unfold out_put; cbn. rewrite Zlength_sublist by lia.
    replace (po + Z.min o_pending z_avail_out - po <=? z_avail_out) with true by (symmetry; apply Z.leb_le; lia).
    cbn. unfold u64. rewrite Z.mod_small by lia.
    set (len := Z.min o_pending z_avail_out) in *.
    assert (Hx : Zlength (sublist po (po + len) o_buf) = len) by (rewrite Zlength_sublist; lia).
    assert (Hxb : bytes (sublist po (po + len) o_buf)).
    { apply (LTBTrail.tbo_bytes {| mb_val := o_buf; mb_def := pbm |}); auto.
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

Section TrailW.
Variable W : dstate -> Prop.
Variable HI : hdr_inv.
Context (CF : core_facts_w W) (HF : hdr_facts_w HI).

Lemma tw_brun_gb : forall n b pos fin s tin tout adler,
  BrunW W HI n b pos fin s tin tout adler -> 0 <= d_pending s /\ 0 <= d_bi_valid s /\ Gb s tout <= 8 * b.
Proof.
  intros n b pos fin s tin tout adler (H & w0 & HW & Ho & Hw0 & Hb & HH & Hn & Hpos & Htin & Htout & Hgz & Hlf & Hph).
  assert (Hbo : 0 <= d_bi_valid s /\ 0 <= d_pending s).
  { destruct Ho as (_ & (X & _ & Y) & _). unfold d_bi_valid, d_pending. lia. }
  pose proof (tb_tlen w0). pose proof (body_range_w (bcls_of s) n (proj1 Hn)). pose proof (Zlength_nonneg H).
  split; [lia|]. split; [lia|].
  destruct Hph as [P0|[P1|[P2|P3]]].
  - destruct P0 as (_ & _ & _ & _ & Ht & Hpd & Hbv & _). unfold Gb. lia.
  - destruct P1 as (_ & _ & (k & HIk & Hk) & _ & Hbv & _).
    destruct (hw_status HI HF _ _ _ _ HIk) as (_ & _ & _ & _ & Hk2). unfold Gb. lia.
  - destruct P2 as (_ & _ & _ & _ & E & k & HE & Hk & Hm & Hg).
    destruct (cw_pos W CF s HW) as (A1 & A2 & A3 & A4).
    assert (0 <= ub s) by (unfold ub; lia).
    pose proof (acc_mid_w (bcls_of s) (Zlength H) E k n ltac:(lia) Hk Hm ltac:(lia)). lia.
  - destruct P3 as (_ & _ & _ & _ & _ & _ & _ & [(_ & Hg)|(_ & _ & Hg)]); lia.
Qed.

End TrailW.

Lemma trailer_stage_w : forall W HI, core_facts_w W -> hdr_facts_w HI ->
  forall n b pos0 inb aout tin0 tout0 flush gz0 s z,
  MidW W HI n b pos0 inb aout tin0 tout0 flush gz0 s z ->
  (flush = Z_NO_FLUSH \/ (d_status s = FINISH_STATE /\ d_pending s = 0 /\ d_po s = 0 /\ z_avail_in z = 0)) ->
  exists s4 z4 code, c_deflate_trailer s z flush = Some (s4, z4, code) /\
    d_gzhead s4 = gz0 /\ core_eq s s4 /\ cframe inb aout tin0 tout0 z4 /\ (code = Z_OK \/ code = Z_STREAM_END) /\
    z_total_out z4 <= b /\ (code = Z_STREAM_END -> z_avail_in z4 = 0) /\
    (code <> Z_STREAM_END -> MidW W HI n b pos0 inb aout tin0 tout0 flush gz0 s4 z4) /\
    (flush = Z_FINISH -> b <= tout0 + aout -> code = Z_STREAM_END).
Proof.
  intros W HI CF HF n b pos0 inb aout tin0 tout0 flush gz0 s z HM Hpre.
  pose proof HM as HM0.
  destruct HM as (Hcf & Hbin & Hp0 & Hpn & Hfl & Hfn & Haout & Htin0 & Htout0 & Hgz0 & HB).
  pose proof (tw_brun_gb W HI CF HF _ _ _ _ _ _ _ _ HB) as (Hpd0 & Hbv0 & HGb).
  pose proof (brunw_facts W HI CF HF _ _ _ _ _ _ _ _ HB) as (_ & _ & _ & _ & Hb33 & _).
  assert (Hto : z_total_out z <= b) by (unfold Gb in HGb; lia).
  unfold c_deflate_trailer.
  destruct (Z.eqb_spec flush Z_FINISH) as [EF|NF].
  2: { cbn [negb]. exists s, z, Z_OK.
       split; [reflexivity|]. split; [exact Hgz0|]. split; [apply core_eq_refl|]. split; [exact Hcf|]. split; [left; reflexivity|].
       split; [exact Hto|]. split; [intros X; discriminate X|]. split; [intros _; exact HM0|].
       intros X; contradiction. }
  subst flush. cbn [negb].
  destruct Hpre as [E|(Hfs & Hpd & Hpo & Hai)]; [discriminate E|].
  pose proof HB as HB0.
  destruct HB as (H & w0 & HW & Ho & Hw0 & Hb & HH & Hn & Hpos & Htin & Htout & Hgz & Hlf & Hph).
  destruct Hph as [P0|[P1|[P2|P3]]].
  { exfalso. destruct P0 as (Hs & _). rewrite Hfs in Hs. destruct (w0 =? 2); discriminate Hs. }
  { exfalso. destruct P1 as (_ & _ & (k & HIk & _) & _).
    destruct (hw_status HI HF _ _ _ _ HIk) as (_ & _ & Hs & _). rewrite Hfs in Hs.
    unfold FINISH_STATE, EXTRA_STATE, NAME_STATE, COMMENT_STATE, HCRC_STATE in Hs; lia. }
  { exfalso. destruct P2 as (Hs & _). rewrite Hfs in Hs. discriminate Hs. }
  destruct P3 as (_ & Hfin & Hposn & Hub & Hsy & Hbv & Had & Hcase).
  destruct (Z.leb_spec (d_wrap s) 0) as [Hw|Hw].
  { exists s, z, Z_STREAM_END.
    split; [reflexivity|]. split; [exact Hgz0|]. split; [apply core_eq_refl|]. split; [exact Hcf|]. split; [right; reflexivity|].
    split; [exact Hto|]. split; [intros _; exact Hai|]. split; [intros X; contradiction|].
    intros _ _; reflexivity. }
  destruct Hcase as [(Hdw & HG)|(_ & Hdw & _)]; [|lia].
  pose proof (cw_prm W CF s HW) as Hprm.
  edestruct (tb_put_trailer s (z_adler z) (z_total_in z)) as (s1 & E1 & Ho1 & Hc1 & Ha1 & Hb1 & Hpd1);
    eauto; [lia|].
  rewrite E1. cbn [bind].
  pose proof (tb_tlen w0). pose proof (body_range_w (bcls_of s) n (proj1 Hn)). pose proof (Zlength_nonneg H).
  pose proof Hcf as Hcf0.
  destruct Hcf as (Hzin & Hni & Hai' & Hti & Hao & Hzo & Hto' & Hbo).
  pose proof (Zlength_nonneg (z_out z)).
  edestruct (tw_flush_pending_ok s1 z) as (s' & x & Ef & Hpx & Hlx & Hbx & Ho' & Hc' & Ha' & Hb' & Hpd' & Hpo');
    auto; try lia.
  rewrite Ef. cbn [bind].
  destruct Ha1 as (As1 & Aw1 & Ag1 & Ai1 & Al1 & Am1), Ha' as (As2 & Aw2 & Ag2 & Ai2 & Al2 & Am2).
  assert (Hdw' : d_wrap s' = w0) by congruence.
  rewrite Hdw'. replace (w0 >? 0) with true by (symmetry; apply Z.gtb_lt; lia).
  eexists _, _, _. split; [reflexivity|].
  assert (Hc4 : core_eq s (set_d_wrap s' (- w0))).
  { eapply core_eq_trans; [exact Hc1|]. eapply core_eq_trans; [exact Hc'|].
    exact (core_eq_api_setters s' (d_status s') (d_last_flush s') (- w0) (d_gzhead s')). }
  pose proof (core_eq_fields _ _ Hc4) as (_ & _ & _ & _ & _ & _ & _ & _ & Hsy4 & _).
  change (d_sym_next (set_d_wrap s' (- w0))) with (d_sym_next s') in Hsy4.
  change (d_pending (set_d_wrap s' (- w0))) with (d_pending s').
  assert (Hxa : Zlength x <= z_avail_out z) by lia.
  pose proof (tb_cframe_step inb aout tin0 tout0 z x Hcf0 Hxa Hbx) as Hz4.
  assert (Hpd's : d_pending s' = tlen w0 - Zlength x) by (rewrite Hpd', Hpd1, Hdw; lia).
  assert (HGs : 8 * z_total_out z <= 8 * (Zlength H + body (bcls_of s) n)) by (unfold Gb in HG; lia).
  assert (Hcl : bcls_of (set_d_wrap s' (- w0)) = bcls_of s) by exact (bcls_core_eq _ _ Hc4).
  assert (Hto4 : z_total_out z + Zlength x + d_pending s' <= b) by lia.
  split; [cbn [d_gzhead set_d_wrap]; congruence|].
  split; [exact Hc4|].
  split; [exact Hz4|].
  split; [destruct (d_pending s' =? 0); cbn; auto|].
  split; [cbn [z_total_out]; lia|].
  split; [intros _; cbn [z_avail_in]; exact Hai|].
  split.
  - intros _.
    split; [exact Hz4|]. split; [exact Hbin|]. split; [exact Hp0|]. split; [exact Hpn|].
    split; [right; reflexivity|]. split; [exact Hfn|]. split; [exact Haout|]. split; [exact Htin0|].
    split; [exact Htout0|]. split; [cbn [d_gzhead set_d_wrap]; congruence|].
    cbn [z_next_in z_total_in z_total_out z_adler].
    exists H, w0.
    split; [exact (cw_frame W CF s _ HW Hc4)|].
    split; [exact Ho'|].
    split; [exact Hw0|]. split; [rewrite Hcl; exact Hb|]. split; [exact HH|]. split; [exact Hn|].
    split; [exact Hpos|]. split; [exact Htin|]. split; [lia|].
    split; [intros h Eh; apply Hgz; cbn [d_gzhead set_d_wrap] in Eh; congruence|].
    split; [cbn [d_last_flush set_d_wrap]; congruence|].
    right. right. right.
    cbn [d_status set_d_wrap].
    split; [congruence|]. split; [exact Hfin|]. split; [exact Hposn|].
    split; [rewrite (ub_core_eq _ _ Hc4); exact Hub|].
    split; [change (d_sym_next (set_d_wrap s' (- w0))) with (d_sym_next s'); congruence|].
    split; [change (d_bi_valid (set_d_wrap s' (- w0))) with (d_bi_valid s'); congruence|].
    split; [exact Had|].
    right. split; [lia|]. split; [reflexivity|].
    rewrite Hcl. unfold Gb.
    change (d_bi_valid (set_d_wrap s' (- w0))) with (d_bi_valid s').
    change (d_pending (set_d_wrap s' (- w0))) with (d_pending s').
    rewrite Hb', Hb1, Hbv. lia.
  - intros _ Hroom.
    destruct (Z.eqb_spec (d_pending s') 0) as [P|P]; [reflexivity|]. exfalso.
    assert (Zlength x = z_avail_out z) by lia.
    lia.
Qed.
