(** * deflate_bound theory: deflate()'s trailer inside [Mid]

    [Mid W HI n b pos0 inb aout tin0 tout0 flush gz0 s z] (LTBDefs): the state of one deflate() call with
    flush Z_NO_FLUSH or Z_FINISH.  The last clause of each lemma: deflate_bound's single call (Z_FINISH, all the
    data, b bytes of output space) never stops early. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTBOut Zlib.proof.deflate.LTBArith.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

Section Trail.
Variable W : dstate -> Prop.
Variable HI : hdr_inv.
Hypothesis CF : core_facts W.
Hypothesis HF : hdr_facts HI.

(** ** Helpers (copies of the proofs of LTBOut.v's out_proof and LTBArith.v's arith_proof) *)
Lemma tbo_definedb : forall b lo hi, mb_defined b lo hi -> mb_definedb b lo hi = true.
Proof.
  intros b lo hi [H0 [H1 H2]]. unfold mb_definedb.
  rewrite (proj2 (Z.leb_le _ _) H0), (proj2 (Z.leb_le _ _) H1). cbn [andb].
  apply forallb_forall. intros i Hi. apply in_map_iff in Hi. destruct Hi as [k [<- Hk]].
  apply in_seq in Hk. apply H2. lia.
Qed.

Lemma tbo_bytes : forall b lo hi, mb_ok b -> mb_defined b lo hi -> bytes (sublist lo hi (mb_val b)).
Proof.
  intros b lo hi [L Hb] [H0 [H1 H2]]. unfold bytes. apply Forall_forall. intros v Hv.
  apply In_Znth in Hv. destruct Hv as [i [Hi <-]].
  destruct (Z_le_gt_dec lo hi).
  - rewrite Zlength_sublist in Hi by lia. rewrite Znth_sublist by lia. apply Hb; [lia|]. apply H2; lia.
  - rewrite sublist_nil_gen in Hi by lia. rewrite Zlength_nil in Hi. lia.
Qed.

Lemma tbo_flush_pending_ok : forall s z,
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
  - unfold mb_read. rewrite tbo_definedb.
    2:{ split; [|split]; cbn in *; try lia. intros; apply Hd2; lia. }
    replace ((0 <=? Z.min o_pending z_avail_out) && true)%bool with true
      by (symmetry; apply andb_true_iff; split; auto; apply Z.leb_le; lia).
    cbn. unfold out_put; cbn. rewrite Zlength_sublist by lia.
    replace (po + Z.min o_pending z_avail_out - po <=? z_avail_out) with true by (symmetry; apply Z.leb_le; lia).
    cbn. unfold u64. rewrite Z.mod_small by lia.
    set (len := Z.min o_pending z_avail_out) in *.
    assert (Hx : Zlength (sublist po (po + len) o_buf) = len) by (rewrite Zlength_sublist; lia).
    assert (Hxb : bytes (sublist po (po + len) o_buf)).
    { apply (tbo_bytes {| mb_val := o_buf; mb_def := pbm |}); auto.
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

Lemma tbo_dput_byte_step : forall s c,
  prm s -> outok s -> d_po s = 0 -> d_sym_next s = 0 -> d_pending s + 1 <= d_pending_buf_size s ->
  exists s1, c_dput_byte s c = Some s1 /\ pend s1 = pend s ++ [u8 c] /\
    outok s1 /\ core_eq s s1 /\ api_eq s s1 /\ d_po s1 = 0 /\ d_bi_valid s1 = d_bi_valid s /\
    d_pending s1 = d_pending s + 1 /\ prm s1 /\ d_sym_next s1 = 0.
Proof.
  intros s c Hp Ho Hpo Hsn Hpb.
  pose proof Hp as Hp'.
  destruct Hp' as (_ & _ & _ & _ & _ & _ & _ & _ & Hpbs & Hlb & Hlm & _).
  destruct Ho as (Hmb & Hbo & Hpo0 & Hpe & Hdef & _).
  pose proof (proj2 (proj2 Hbo)) as Hpn.
  unfold d_pending in *.
  set (o := tr_out (d_tr s)) in *.
  assert (Hin : in_range (o_pending o) (Zlength (o_buf o)) = true).
  { unfold in_range. apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  unfold c_dput_byte, c_put_byte, d_out. fold o. destruct o as [b pn bb bv bu] eqn:Eo.
  cbn [o_buf o_pending o_bi_buf o_bi_valid o_bi_used] in *.
  unfold wr. rewrite Hin. cbn.
  eexists; split; [reflexivity|].
  assert (Eo' : tr_out (d_tr s) = mkOut b pn bb bv bu) by exact Eo.
  clearbody o. subst o.
  set (s1 := set_d_out s _).
  assert (T1 : tr_out (d_tr s1) = mkOut (upd_Znth pn b (u8 c)) (pn + 1) bb bv bu) by reflexivity.
  assert (T2 : d_pbm s1 = upd_Znth pn (d_pbm s) true) by reflexivity.
  assert (T3 : d_po s1 = d_po s) by reflexivity.
  assert (T4 : d_pending_buf_size s1 = d_pending_buf_size s) by reflexivity.
  assert (T5 : d_L s1 = d_L s) by reflexivity.
  assert (T6 : d_sym_next s1 = d_sym_next s) by reflexivity.
  assert (Hlen : Zlength (upd_Znth pn b (u8 c)) = Zlength b) by (rewrite upd_Znth_Zlength; lia).
  assert (Hlenm : Zlength (upd_Znth pn (d_pbm s) true) = Zlength (d_pbm s)) by (rewrite upd_Znth_Zlength; lia).
  assert (Hu8 : 0 <= u8 c < 256) by (unfold u8; apply Z.mod_pos_bound; lia).
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
  - unfold pend, d_pending. rewrite T1, T3, Eo', Hpo. cbn [o_buf o_pending].
    rewrite (sublist_split 0 pn (pn + 1)) by (rewrite ?Hlen; lia).
    rewrite sublist_upd_Znth_l by lia.
    rewrite sublist_len_1 by (rewrite ?Hlen; lia). rewrite upd_Znth_same by lia.
    rewrite !Z.add_0_l. reflexivity.
  - unfold outok, d_pb, d_pending. rewrite T1, T2, T3, T4. cbn [o_buf o_pending].
    unfold d_pb in Hmb, Hdef. rewrite Eo' in Hmb, Hdef. cbn [mb_val mb_def o_buf] in *.
    destruct Hmb as [Hm1 Hm2]. destruct Hdef as (_ & _ & Hd).
    split; [split|]; [cbn [mb_val mb_def]; lia| |].
    + cbn [mb_val mb_def]. intros i Hi Hdi. rewrite Hlen in Hi.
      destruct (Z.eq_dec i pn); [subst; rewrite upd_Znth_same by lia; lia|].
      cbn [mb_val mb_def] in *. rewrite upd_Znth_diff in Hdi by lia. rewrite upd_Znth_diff by lia. auto.
    + split; [unfold bits_ok in *; cbn in *; lia|].
      split; [lia|]. split; [lia|]. split; [|lia].
      split; [lia|]. split; [cbn [mb_val]; lia|]. cbn [mb_def]. intros i Hi.
      destruct (Z.eq_dec i pn); [subst; rewrite upd_Znth_same by lia; auto|].
      rewrite upd_Znth_diff by lia. apply Hd. lia.
  - unfold core_eq. split; [reflexivity|]. split; [|rewrite T1, T2, Eo'; cbn [o_buf]; split; lia].
    unfold sym_region. rewrite T1, T2, T5, T6, Eo', Hsn. cbn [o_buf]. rewrite Z.add_0_r, !sublist_nil. reflexivity.
  - repeat split.
  - rewrite T3; exact Hpo.
  - unfold d_bi_valid. rewrite T1, Eo'. reflexivity.
  - rewrite T1. reflexivity.
  - unfold prm in *. rewrite Eo' in Hp. rewrite T5, T4, T1, T2. cbn [o_buf] in *. rewrite Hlen, Hlenm. exact Hp.
  - rewrite T6. exact Hsn.
Qed.

Lemma tbo_dput_bytes_ok : forall s l,
  prm s -> outok s -> d_po s = 0 -> d_sym_next s = 0 -> d_pending s + Zlength l <= d_pending_buf_size s ->
  exists s1, c_dput_bytes s l = Some s1 /\ pend s1 = pend s ++ map u8 l /\
    outok s1 /\ core_eq s s1 /\ api_eq s s1 /\ d_po s1 = 0 /\ d_bi_valid s1 = d_bi_valid s /\
    d_pending s1 = d_pending s + Zlength l.
Proof.
  intros s l; revert s; induction l as [|c l IH]; intros s Hp Ho Hpo Hsn Hle.
  - exists s. cbn [c_dput_bytes map]. rewrite app_nil_r, Zlength_nil, Z.add_0_r.
    split; [reflexivity|]. split; [reflexivity|]. split; [exact Ho|].
    split; [unfold core_eq; repeat split; reflexivity|]. split; [unfold api_eq; repeat split; reflexivity|].
    split; [exact Hpo|]. split; reflexivity.
  - rewrite Zlength_cons in Hle. pose proof (Zlength_nonneg l).
    destruct (tbo_dput_byte_step s c) as (s1 & E1 & P1 & O1 & C1 & A1 & Po1 & B1 & D1 & Pr1 & Sn1); auto; [lia|].
    assert (Hbs : d_pending_buf_size s1 = d_pending_buf_size s) by exact (f_equal d_pending_buf_size (proj1 C1)).
    destruct (IH s1) as (s2 & E2 & P2 & O2 & C2 & A2 & Po2 & B2 & D2); auto; [lia|].
    exists s2. cbn [c_dput_bytes]. rewrite E1. cbn beta iota. split; [exact E2|].
    split; [rewrite P2, P1, <- app_assoc; reflexivity|]. split; [exact O2|].
    split; [unfold core_eq in *; destruct C1 as (? & ? & ? & ?), C2 as (? & ? & ? & ?);
            repeat split; congruence|].
    split; [unfold api_eq in *; destruct A1 as (? & ? & ? & ? & ? & ?), A2 as (? & ? & ? & ? & ? & ?);
            repeat split; congruence|].
    split; [exact Po2|]. split; [congruence|]. rewrite Zlength_cons. lia.
Qed.

Lemma tbo_body_div : forall c n, body c n =
  match c with
  | BTight => n + n / 4096 + n / 16384 + n / 33554432 + 7
  | BFixed => n + n / 8 + n / 256 + n / 512 + 4
  | BStore => n + n / 32 + n / 128 + n / 2048 + 7
  end.
Proof.
  intros c n; destruct c; unfold body; rewrite !Z.shiftr_div_pow2 by lia; reflexivity.
Qed.

Lemma tbo_divb : forall n d, 0 < d -> d * (n / d) <= n < d * (n / d) + d.
Proof. intros n d Hd. split; [apply Z.mul_div_le; lia|]. pose proof (Z.mul_succ_div_gt n d Hd). lia. Qed.

Ltac tbo_dv := repeat match goal with |- context [?n / ?d] =>
  let q := fresh "q" in pose proof (tbo_divb n d ltac:(lia)); set (q := n / d) in *; clearbody q end.

Lemma tbo_body_range : forall c n, 0 <= n <= 1048576 -> n + 4 <= body c n <= 2 * n + 7.
Proof. intros c n Hn. rewrite !tbo_body_div. destruct c; tbo_dv; lia. Qed.

Lemma tbo_acc_mid : forall c h e k n, 0 <= h -> 0 <= k -> minblk c * k <= e -> e <= n <= 1048576 ->
  xb c h e k + 10 <= 8 * (h + body c n).
Proof.
  intros c h e k n Hh Hk Hke Hn. rewrite !tbo_body_div. destruct c; unfold xb, minblk in *; tbo_dv.
  all: lia.
Qed.

Lemma tb_room : forall s, prm s -> 8 <= d_pending_buf_size s.
Proof.
  intros s (_ & _ & _ & Hhb & _ & _ & _ & HL & Hpbs & _).
  assert (2 ^ 7 <= 2 ^ (d_hash_bits s - 1)) by (apply Z.pow_le_mono_r; lia).
  lia.
Qed.

Lemma tb_tlen : forall w, 0 <= tlen w <= 8.
Proof. intros w. unfold tlen. destruct (w =? 1), (w =? 2); lia. Qed.

Lemma tb_put_trailer : forall s a t, prm s -> outok s -> d_pending s = 0 -> d_po s = 0 -> d_sym_next s = 0 ->
  1 <= d_wrap s <= 2 ->
  exists s1,
    (if d_wrap s =? 2 then
       c_dput_bytes s [Z.land a 255; Z.land (Z.shiftr a 8) 255; Z.land (Z.shiftr a 16) 255;
                       Z.land (Z.shiftr a 24) 255; Z.land t 255; Z.land (Z.shiftr t 8) 255;
                       Z.land (Z.shiftr t 16) 255; Z.land (Z.shiftr t 24) 255]
     else
       let* s := c_putShortMSB s (u32 (Z.shiftr a 16)) in
       c_putShortMSB s (u32 (Z.land a 65535))) = Some s1 /\
    outok s1 /\ core_eq s s1 /\ api_eq s s1 /\ d_bi_valid s1 = d_bi_valid s /\
    d_pending s1 = tlen (d_wrap s).
Proof.
  intros s a t Hp Ho Hpd Hpo Hsym Hw.
  pose proof (tb_room s Hp) as Hr.
  unfold tlen.
  destruct (Z.eqb_spec (d_wrap s) 2) as [E2|E2].
  - match goal with |- exists s1, c_dput_bytes _ ?l = _ /\ _ =>
      edestruct (tbo_dput_bytes_ok s l) as (s1 & E & Hpe & Ho1 & Hc & Ha & Hpo1 & Hb & Hpd1); eauto end.
    { rewrite Hpd. cbn. lia. }
    exists s1. split; [exact E|]. rewrite E2. cbn [Z.eqb Pos.eqb]. rewrite Hpd1, Hpd. cbn. auto.
  - rewrite putShortMSB2_eq.
    match goal with |- exists s1, c_dput_bytes _ ?l = _ /\ _ =>
      edestruct (tbo_dput_bytes_ok s l) as (s1 & E & Hpe & Ho1 & Hc & Ha & Hpo1 & Hb & Hpd1); eauto end.
    { rewrite Hpd. cbn. lia. }
    exists s1. split; [exact E|].
    replace (d_wrap s) with 1 by lia. cbn [Z.eqb Pos.eqb]. rewrite Hpd1, Hpd. auto.
Qed.

Lemma tb_cframe_step : forall inb aout tin tout z x,
  cframe inb aout tin tout z -> Zlength x <= z_avail_out z -> bytes x ->
  cframe inb aout tin tout
    (mkST (z_in z) (z_next_in z) (z_avail_in z) (z_total_in z) (z_out z ++ x)
          (z_avail_out z - Zlength x) (z_total_out z + Zlength x) (z_adler z) (z_msg z)).
Proof.
  intros inb aout tin tout z x (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8) Hx Hb.
  unfold cframe; cbn [z_in z_next_in z_avail_in z_total_in z_out z_avail_out z_total_out].
  rewrite Zlength_app.
  repeat split; try lia; auto.
  unfold bytes in *. apply Forall_app. auto.
Qed.

(** All bits produced so far are within the bound, in every phase. *)
Lemma tb_brun_gb : forall n b pos fin s tin tout adler,
  Brun W HI n b pos fin s tin tout adler -> 0 <= d_pending s /\ 0 <= d_bi_valid s /\ Gb s tout <= 8 * b.
Proof.
  intros n b pos fin s tin tout adler (H & w0 & HW & Ho & Hw0 & Hb & HH & Hn & Hpos & Htin & Htout & Hgz & Hlf & Hph).
  assert (Hbo : 0 <= d_bi_valid s /\ 0 <= d_pending s).
  { destruct Ho as (_ & (X & _ & Y) & _). unfold d_bi_valid, d_pending. lia. }
  pose proof (tb_tlen w0). pose proof (tbo_body_range (bcls_of s) n Hn). pose proof (Zlength_nonneg H).
  split; [lia|]. split; [lia|].
  destruct Hph as [P0|[P1|[P2|P3]]].
  - destruct P0 as (_ & _ & _ & _ & Ht & Hpd & Hbv & _). unfold Gb. lia.
  - destruct P1 as (_ & _ & (k & HIk & Hk) & _ & Hbv & _).
    destruct (hf_status HI HF _ _ _ _ HIk) as (_ & _ & _ & _ & Hk2). unfold Gb. lia.
  - destruct P2 as (_ & _ & _ & _ & E & k & HE & Hk & Hm & Hg).
    destruct (cf_pos W CF s HW) as (A1 & A2 & A3 & A4).
    assert (0 <= ub s) by (unfold ub; lia).
    pose proof (tbo_acc_mid (bcls_of s) (Zlength H) E k n ltac:(lia) Hk Hm ltac:(lia)). lia.
  - destruct P3 as (_ & _ & _ & _ & _ & _ & _ & [(_ & Hg)|(_ & _ & Hg)]); lia.
Qed.

(** Stage 9: the trailer (reached with Z_NO_FLUSH, or at FINISH_STATE with nothing pending and no input). *)
Lemma trailer_stage : forall n b pos0 inb aout tin0 tout0 flush gz0 s z,
  Mid W HI n b pos0 inb aout tin0 tout0 flush gz0 s z ->
  (flush = Z_NO_FLUSH \/ (d_status s = FINISH_STATE /\ d_pending s = 0 /\ d_po s = 0 /\ z_avail_in z = 0)) ->
  exists s4 z4 code, c_deflate_trailer s z flush = Some (s4, z4, code) /\
    d_gzhead s4 = gz0 /\ cframe inb aout tin0 tout0 z4 /\ (code = Z_OK \/ code = Z_STREAM_END) /\
    z_total_out z4 <= b /\ (code = Z_STREAM_END -> z_avail_in z4 = 0) /\
    (code <> Z_STREAM_END -> Mid W HI n b pos0 inb aout tin0 tout0 flush gz0 s4 z4) /\
    (flush = Z_FINISH -> b <= tout0 + aout -> code = Z_STREAM_END).
Proof.
  intros n b pos0 inb aout tin0 tout0 flush gz0 s z HM Hpre.
  pose proof HM as HM0.
  destruct HM as (Hcf & Hbin & Hp0 & Hpn & Hfl & Hfn & Haout & Htin0 & Htout0 & Hgz0 & HB).
  pose proof (tb_brun_gb _ _ _ _ _ _ _ _ HB) as (Hpd0 & Hbv0 & HGb).
  assert (Hto : z_total_out z <= b) by (unfold Gb in HGb; lia).
  unfold c_deflate_trailer.
  destruct (Z.eqb_spec flush Z_FINISH) as [EF|NF].
  2: { cbn [negb]. exists s, z, Z_OK.
       split; [reflexivity|]. split; [exact Hgz0|]. split; [exact Hcf|]. split; [left; reflexivity|].
       split; [exact Hto|]. split; [intros X; discriminate X|]. split; [intros _; exact HM0|].
       intros X; contradiction. }
  subst flush. cbn [negb].
  destruct Hpre as [E|(Hfs & Hpd & Hpo & Hai)]; [discriminate E|].
  pose proof HB as HB0.
  destruct HB as (H & w0 & HW & Ho & Hw0 & Hb & HH & Hn & Hpos & Htin & Htout & Hgz & Hlf & Hph).
  destruct Hph as [P0|[P1|[P2|P3]]].
  { exfalso. destruct P0 as (Hs & _). rewrite Hfs in Hs. destruct (w0 =? 2); discriminate Hs. }
  { exfalso. destruct P1 as (_ & _ & (k & HIk & _) & _).
    destruct (hf_status HI HF _ _ _ _ HIk) as (_ & _ & Hs & _). rewrite Hfs in Hs.
    unfold FINISH_STATE, EXTRA_STATE, NAME_STATE, COMMENT_STATE, HCRC_STATE in Hs; lia. }
  { exfalso. destruct P2 as (Hs & _). rewrite Hfs in Hs. discriminate Hs. }
  destruct P3 as (_ & Hfin & Hposn & Hub & Hsy & Hbv & Had & Hcase).
  destruct (Z.leb_spec (d_wrap s) 0) as [Hw|Hw].
  { exists s, z, Z_STREAM_END.
    split; [reflexivity|]. split; [exact Hgz0|]. split; [exact Hcf|]. split; [right; reflexivity|].
    split; [exact Hto|]. split; [intros _; exact Hai|]. split; [intros X; contradiction|].
    intros _ _; reflexivity. }
  destruct Hcase as [(Hdw & HG)|(_ & Hdw & _)]; [|lia].
  pose proof (cf_prm W CF s HW) as Hprm.
  edestruct (tb_put_trailer s (z_adler z) (z_total_in z)) as (s1 & E1 & Ho1 & Hc1 & Ha1 & Hb1 & Hpd1);
    eauto; [lia|].
  rewrite E1. cbn [bind].
  pose proof (tb_tlen w0). pose proof (tbo_body_range (bcls_of s) n Hn). pose proof (Zlength_nonneg H).
  pose proof Hcf as Hcf0.
  destruct Hcf as (Hzin & Hni & Hai' & Hti & Hao & Hzo & Hto' & Hbo).
  pose proof (Zlength_nonneg (z_out z)).
  edestruct (tbo_flush_pending_ok s1 z) as (s' & x & Ef & Hpx & Hlx & Hbx & Ho' & Hc' & Ha' & Hb' & Hpd' & Hpo');
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
    split; [exact (cf_frame W CF s _ HW Hc4)|].
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

End Trail.
