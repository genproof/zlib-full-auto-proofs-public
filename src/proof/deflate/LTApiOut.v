(** * deflate_api theory: the output part of deflate()'s own stages

    flush_pending (with at most 7 bits in the bit buffer: its bi_flush is a no-op), _tr_align and the empty stored
    block on a quiet state, put_byte / putShortMSB at the start of pending_buf; each keeps [outok] and only
    changes what [core_eq] / [api_eq] allow. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTApiDefs.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** What [core_eq] keeps *)
Lemma core_eq_fields : forall s s', core_eq s s' ->
  d_method s' = d_method s /\ d_w_size s' = d_w_size s /\ d_w_bits s' = d_w_bits s /\
  d_hash_bits s' = d_hash_bits s /\ d_block_start s' = d_block_start s /\ d_strstart s' = d_strstart s /\
  d_lookahead s' = d_lookahead s /\ d_pending_buf_size s' = d_pending_buf_size s /\
  d_sym_next s' = d_sym_next s /\ d_level s' = d_level s /\ d_strategy s' = d_strategy s /\ d_L s' = d_L s /\
  d_insert s' = d_insert s.
Proof.
  intros s s' [Hs _].
  pose proof (f_equal d_method Hs) as E1. pose proof (f_equal d_w_size Hs) as E2.
  pose proof (f_equal d_w_bits Hs) as E3. pose proof (f_equal d_hash_bits Hs) as E4.
  pose proof (f_equal d_block_start Hs) as E5. pose proof (f_equal d_strstart Hs) as E6.
  pose proof (f_equal d_lookahead Hs) as E7. pose proof (f_equal d_pending_buf_size Hs) as E8.
  pose proof (f_equal (fun x => tr_sym_next (d_tr x)) Hs) as E9.
  pose proof (f_equal (fun x => tr_level (d_tr x)) Hs) as E10.
  pose proof (f_equal (fun x => tr_strategy (d_tr x)) Hs) as E11.
  pose proof (f_equal (fun x => tr_lit_bufsize (d_tr x)) Hs) as E12.
  pose proof (f_equal d_insert Hs) as E13.
  cbn in *. unfold d_sym_next, d_level, d_strategy, d_L. tauto.
Qed.

Lemma core_eq_refl : forall s, core_eq s s.
Proof.
  intros s. unfold core_eq. tauto.
Qed.

Lemma core_eq_trans : forall s1 s2 s3, core_eq s1 s2 -> core_eq s2 s3 -> core_eq s1 s3.
Proof.
  intros s1 s2 s3 (A1 & B1 & C1 & D1) (A2 & B2 & C2 & D2). unfold core_eq.
  rewrite A2, B2, C2, D2. tauto.
Qed.

(** set_d_status / set_d_last_flush / set_d_wrap / set_d_gzhead change nothing [core_eq] sees. *)
Lemma core_eq_api_setters : forall s st lf w g,
  core_eq s (set_d_gzhead (set_d_wrap (set_d_last_flush (set_d_status s st) lf) w) g).
Proof.
  intros. unfold core_eq. repeat split; reflexivity.
Qed.

(** ** flush_pending *)
Lemma fp_definedb : forall b lo hi, mb_defined b lo hi -> mb_definedb b lo hi = true.
Proof.
  intros b lo hi [H0 [H1 H2]]. unfold mb_definedb.
  rewrite (proj2 (Z.leb_le _ _) H0), (proj2 (Z.leb_le _ _) H1). cbn [andb].
  apply forallb_forall. intros i Hi. apply in_map_iff in Hi. destruct Hi as [k [<- Hk]].
  apply in_seq in Hk. apply H2. lia.
Qed.

Lemma fp_bytes : forall b lo hi, mb_ok b -> mb_defined b lo hi -> bytes (sublist lo hi (mb_val b)).
Proof.
  intros b lo hi [L Hb] [H0 [H1 H2]]. unfold bytes. apply Forall_forall. intros v Hv.
  apply In_Znth in Hv. destruct Hv as [i [Hi <-]].
  destruct (Z_le_gt_dec lo hi).
  - rewrite Zlength_sublist in Hi by lia. rewrite Znth_sublist by lia. apply Hb; [lia|]. apply H2; lia.
  - rewrite sublist_nil_gen in Hi by lia. rewrite Zlength_nil in Hi. lia.
Qed.

Lemma flush_pending_ok : forall s z,
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
  - unfold mb_read. rewrite fp_definedb.
    2:{ split; [|split]; cbn in *; try lia. intros; apply Hd2; lia. }
    replace ((0 <=? Z.min o_pending z_avail_out) && true)%bool with true
      by (symmetry; apply andb_true_iff; split; auto; apply Z.leb_le; lia).
    cbn. unfold out_put; cbn. rewrite Zlength_sublist by lia.
    replace (po + Z.min o_pending z_avail_out - po <=? z_avail_out) with true by (symmetry; apply Z.leb_le; lia).
    cbn. unfold u64. rewrite Z.mod_small by lia.
    set (len := Z.min o_pending z_avail_out) in *.
    assert (Hx : Zlength (sublist po (po + len) o_buf) = len) by (rewrite Zlength_sublist; lia).
    assert (Hxb : bytes (sublist po (po + len) o_buf)).
    { apply (fp_bytes {| mb_val := o_buf; mb_def := pbm |}); auto.
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

(** ** _tr_align and the empty stored block, on a quiet state without symbols *)
(** Helpers for [tr_align_ok]: the checked bit writer computes the unchecked one when pending_buf has room;
    the mask is set exactly on the bytes written; the bytes written are bytes. *)
Definition ta_mafter (m m' : list bool) (lo hi : Z) : Prop :=
  lo <= hi /\ Zlength m' = Zlength m /\
  forall i, 0 <= i < Zlength m -> Znth i m' = (if (lo <=? i) && (i <? hi) then true else Znth i m).

Lemma ta_mafter_refl : forall m p, ta_mafter m m p p.
Proof.
  intros m p. split; [lia|]. split; [reflexivity|]. intros i Hi.
  destruct (Z.leb_spec p i), (Z.ltb_spec i p); simpl; auto; lia.
Qed.

Lemma ta_mafter_trans : forall m1 m2 m3 a b c,
  ta_mafter m1 m2 a b -> ta_mafter m2 m3 b c -> ta_mafter m1 m3 a c.
Proof.
  intros m1 m2 m3 a b c [Hab [L1 P1]] [Hbc [L2 P2]]. split; [lia|]. split; [lia|]. intros i Hi.
  rewrite P2 by lia. rewrite P1 by lia.
  destruct (Z.leb_spec b i), (Z.ltb_spec i c), (Z.leb_spec a i), (Z.ltb_spec i b); simpl; auto; lia.
Qed.

Lemma ta_mafter_upd : forall m p, ta_mafter m (upd_Znth p m true) p (p + 1).
Proof.
  intros m p. split; [lia|]. split; [apply Zlength_upd_Znth_any|]. intros i Hi.
  destruct (Z.eq_dec i p) as [->|Hne].
  - rewrite upd_Znth_same by lia. destruct (Z.leb_spec p p), (Z.ltb_spec p (p + 1)); simpl; auto; lia.
  - rewrite list_solver.Znth_upd_Znth_diff by lia.
    destruct (Z.leb_spec p i), (Z.ltb_spec i (p + 1)); simpl; auto; lia.
Qed.

(** The bytes [lo .. pending) of the buffer are bytes. *)
Definition ta_bin (lo : Z) (o : outbuf) : Prop :=
  forall i, lo <= i < o_pending o -> 0 <= Znth i (o_buf o) < 256.

Lemma ta_cpb : forall o m c, 0 <= o_pending o < Zlength (o_buf o) ->
  c_put_byte (o, m) c = Some (put_byte o c, upd_Znth (o_pending o) m true).
Proof.
  intros [b p bb bv bu] m c H. cbn in H. unfold c_put_byte, wr, in_range. cbn.
  replace ((0 <=? p) && (p <? Zlength b)) with true
    by (symmetry; apply andb_true_iff; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
  reflexivity.
Qed.

Lemma ta_pb_bin : forall o c lo, 0 <= lo <= o_pending o -> o_pending o < Zlength (o_buf o) ->
  ta_bin lo o -> ta_bin lo (put_byte o c).
Proof.
  intros o c lo H1 H2 B i Hi. unfold put_byte in *; cbn in *.
  destruct (Z.eq_dec i (o_pending o)) as [->|Hne].
  - rewrite upd_Znth_same by lia. unfold u8. apply Z.mod_pos_bound; lia.
  - rewrite Znth_upd_Znth_other by lia. apply B; lia.
Qed.

Lemma ta_cps : forall o m w, 0 <= o_pending o -> o_pending o + 2 <= Zlength (o_buf o) ->
  exists m', c_put_short (o, m) w = Some (put_short o w, m') /\ ta_mafter m m' (o_pending o) (o_pending o + 2).
Proof.
  intros o m w H1 H2. unfold c_put_short. rewrite ta_cpb by lia. cbn [bind].
  rewrite ta_cpb by (unfold put_byte; cbn; rewrite Zlength_upd_Znth_any; lia).
  eexists; split; [reflexivity|].
  eapply ta_mafter_trans; [apply ta_mafter_upd|]. unfold put_byte; cbn.
  replace (o_pending o + 2) with (o_pending o + 1 + 1) by lia. apply ta_mafter_upd.
Qed.

Lemma ta_ps_bin : forall o w lo, 0 <= lo <= o_pending o -> o_pending o + 2 <= Zlength (o_buf o) ->
  ta_bin lo o -> ta_bin lo (put_short o w).
Proof.
  intros o w lo H1 H2 B. unfold put_short. apply ta_pb_bin.
  - unfold put_byte; cbn; lia.
  - unfold put_byte; cbn; rewrite Zlength_upd_Znth_any; lia.
  - apply ta_pb_bin; auto; lia.
Qed.

Lemma ta_csb : forall o m value len,
  0 <= o_bi_valid o <= 16 -> 0 <= o_pending o -> o_pending o + 2 <= Zlength (o_buf o) ->
  exists m', c_send_bits (o, m) value len = Some (send_bits o value len, m') /\
    ta_mafter m m' (o_pending o) (o_pending (send_bits o value len)).
Proof.
  intros o m value len H1 H2 H3. unfold c_send_bits, send_bits.
  replace ((0 <=? o_bi_valid o) && (o_bi_valid o <=? Buf_size)) with true
    by (symmetry; apply andb_true_iff; split; apply Z.leb_le; unfold Buf_size; lia).
  cbn [guard bind].
  destruct (o_bi_valid o >? Buf_size - len).
  - set (bb := u16 (Z.lor (o_bi_buf o) (Z.shiftl (u16 value) (o_bi_valid o)))).
    destruct (ta_cps (set_bits o bb (o_bi_valid o)) m bb) as [m' [E M]]; [cbn; lia|cbn; lia|].
    rewrite E. cbn [bind]. exists m'. split; [reflexivity|].
    unfold put_short, put_byte, set_bits in *; cbn in *. replace (o_pending o + 1 + 1) with (o_pending o + 2) by lia.
    exact M.
  - exists m. split; [reflexivity|]. apply ta_mafter_refl.
Qed.

Lemma ta_sb_bin : forall o value len lo, 0 <= lo <= o_pending o -> o_pending o + 2 <= Zlength (o_buf o) ->
  ta_bin lo o -> ta_bin lo (send_bits o value len).
Proof.
  intros o value len lo H1 H2 B. unfold send_bits.
  destruct (o_bi_valid o >? Buf_size - len).
  - set (bb := u16 (Z.lor (o_bi_buf o) (Z.shiftl (u16 value) (o_bi_valid o)))).
    assert (H : ta_bin lo (put_short (set_bits o bb (o_bi_valid o)) bb)) by (apply ta_ps_bin; exact B || exact H1 || exact H2).
    exact H.
  - exact B.
Qed.

Lemma ta_cbf : forall o m, 0 <= o_pending o -> o_pending o + 2 <= Zlength (o_buf o) ->
  exists m', c_bi_flush (o, m) = Some (bi_flush o, m') /\
    ta_mafter m m' (o_pending o) (o_pending (bi_flush o)).
Proof.
  intros o m H1 H2. unfold c_bi_flush, bi_flush.
  destruct (o_bi_valid o =? 16).
  - destruct (ta_cps o m (o_bi_buf o)) as [m' [E M]]; auto. rewrite E. cbn [bind].
    exists m'. split; [reflexivity|]. unfold put_short, put_byte, set_bits; cbn.
    replace (o_pending o + 1 + 1) with (o_pending o + 2) by lia. exact M.
  - destruct (o_bi_valid o >=? 8).
    + rewrite ta_cpb by lia. cbn [bind]. eexists; split; [reflexivity|].
      unfold put_byte, set_bits; cbn. apply ta_mafter_upd.
    + exists m. split; [reflexivity|]. apply ta_mafter_refl.
Qed.

Lemma ta_bf_bin : forall o lo, 0 <= lo <= o_pending o -> o_pending o + 2 <= Zlength (o_buf o) ->
  ta_bin lo o -> ta_bin lo (bi_flush o).
Proof.
  intros o lo H1 H2 B. unfold bi_flush.
  destruct (o_bi_valid o =? 16); [|destruct (o_bi_valid o >=? 8)].
  - assert (H : ta_bin lo (put_short o (o_bi_buf o))) by (apply ta_ps_bin; auto). exact H.
  - assert (H : ta_bin lo (put_byte o (o_bi_buf o))) by (apply ta_pb_bin; auto; lia). exact H.
  - exact B.
Qed.

Lemma ta_end_len : Znth END_BLOCK static_ltree_len = 7.
Proof. vm_compute. reflexivity. Qed.
Lemma ta_end_code : Znth END_BLOCK static_ltree_code = 0.
Proof. vm_compute. reflexivity. Qed.
Lemma ta_rd_len : rd static_ltree_len END_BLOCK = Some 7.
Proof. vm_compute. reflexivity. Qed.
Lemma ta_rd_code : rd static_ltree_code END_BLOCK = Some 0.
Proof. vm_compute. reflexivity. Qed.

(** _tr_align on a buffer with nothing pending and at most 7 bits. *)
Lemma ta_some : forall o m, bits_ok o -> o_bi_valid o <= 7 -> o_pending o = 0 -> 6 <= Zlength (o_buf o) ->
  exists m', c_tr_align (o, m) = Some (tr_align o, m') /\ ta_mafter m m' 0 (o_pending (tr_align o)) /\
    ta_bin 0 (tr_align o) /\ bits_ok (tr_align o) /\ o_bi_valid (tr_align o) <= 7 /\
    1 <= o_pending (tr_align o) <= 2 /\ writes o (tr_align o).
Proof.
  intros o m Hb H7 Hp0 HL. unfold c_tr_align, tr_align.
  change (Z.shiftl STATIC_TREES 1) with 2.
  pose proof (send_bits_spec o 2 3 Hb ltac:(lia) ltac:(cbn; lia)) as [BP1 [V1 [B1 [P1 W1]]]].
  set (o1 := send_bits o 2 3) in *.
  destruct W1 as [W1a [W1b [W1c W1d]]].
  destruct (ta_csb o m 2 3) as [m1 [E1 M1]]; [destruct Hb; lia|lia|lia|].
  rewrite E1. cbn [bind]. unfold c_send_code. rewrite ta_rd_len. cbn [bind]. rewrite ta_rd_code. cbn [bind].
  assert (Hc : code_ok static_ltree_code static_ltree_len END_BLOCK)
    by (unfold code_ok; rewrite ta_end_len, ta_end_code; cbn; lia).
  pose proof (send_code_spec o1 END_BLOCK static_ltree_code static_ltree_len B1 Hc) as [BP2 [V2 [B2 [P2 W2]]]].
  unfold send_code in *. rewrite ta_end_len, ta_end_code in *.
  set (o2 := send_bits o1 0 7) in *.
  destruct W2 as [W2a [W2b [W2c W2d]]].
  destruct (ta_csb o1 m1 0 7) as [m2 [E2 M2]]; [lia|lia|lia|].
  change (send_bits o 2 3) with o1 in M1 |- *. rewrite E2. cbn [bind].
  pose proof (bi_flush_spec o2 B2) as [BP3 [B3 [V3 W3]]].
  destruct (ta_cbf o2 m2) as [m3 [E3 M3]]; [lia|lia|].
  destruct W3 as [W3a [W3b [W3c W3d]]].
  change (send_bits o1 0 7) with o2 in M2 |- *. rewrite E3. exists m3. split; [reflexivity|].
  assert (Hbp : bitpos (bi_flush o2) = o_bi_valid o + 10) by (unfold bitpos in *; lia).
  destruct B3 as [B3a [B3b B3c]].
  split; [eapply ta_mafter_trans; [rewrite Hp0 in M1; exact M1|]; eapply ta_mafter_trans; eauto|].
  split.
  { apply ta_bf_bin; [lia|lia|]. apply ta_sb_bin; [lia|lia|]. apply ta_sb_bin; [lia|lia|].
    intros i Hi; lia. }
  split; [split; [|split]; assumption|]. split; [auto|].
  split; [unfold bitpos in *; destruct Hb; lia|].
  eapply writes_trans; [|eapply writes_trans]; [split; [|split; [|split]]; eauto..].
Qed.

Lemma tr_align_ok : forall s,
  prm s -> outok s -> quiet s -> d_sym_next s = 0 ->
  exists om, c_tr_align (d_out s) = Some om /\
    outok (set_d_out s om) /\ core_eq s (set_d_out s om) /\ api_eq s (set_d_out s om) /\
    d_po (set_d_out s om) = 0 /\ d_bi_valid (set_d_out s om) <= 7 /\ bytes (pend (set_d_out s om)).
Proof.
  intros s P O Q S0.
  destruct Q as [Hp [Hpo Hbv]].
  destruct O as [[MBl MBv] [BO [PO0 [PObnd [MD PZ]]]]].
  destruct P as [Pwb [_ [_ [Phb [_ [_ [_ [PL [Psz [Pbuf [Ppbm _]]]]]]]]]]].
  assert (HL : 128 <= d_L s).
  { rewrite PL. change 128 with (2 ^ 7). apply Z.pow_le_mono_r; lia. }
  set (o := tr_out (d_tr s)) in *.
  set (m := d_pbm s) in *.
  assert (Hpo' : o_pending o = 0) by exact Hp.
  destruct (ta_some o m BO Hbv Hpo' ltac:(lia)) as [m' [E [M [Bn [Bk [V7 [P12 W]]]]]]].
  destruct M as [_ [Mlen Mi]]. destruct W as [_ [Wlen [_ Wi]]].
  cbn [mb_val mb_def d_pb] in MBl, MBv. fold o m in MBl, MBv.
  exists (tr_align o, m'). split; [exact E|].
  assert (Hout : outok (set_d_out s (tr_align o, m'))).
  { unfold outok, d_pb, d_po, d_pending, set_d_out, set_d_pbm, set_d_tr; cbn.
    rewrite Hpo. split; [split|].
    - cbn. lia.
    - cbn. intros i Hi Hdef. rewrite Wlen in Hi.
      destruct (Z_lt_le_dec i (o_pending (tr_align o))) as [Hlt|Hge].
      + apply Bn; lia.
      + rewrite Wi by lia. apply MBv; [exact Hi|].
        rewrite Mi in Hdef by lia.
        destruct (Z.leb_spec 0 i), (Z.ltb_spec i (o_pending (tr_align o))); simpl in Hdef; auto; lia.
    - split; [exact Bk|]. split; [lia|]. split; [unfold d_pending_buf_size in *; lia|].
      split; [|intros; reflexivity].
      split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn. rewrite Mi by lia.
      destruct (Z.leb_spec 0 i), (Z.ltb_spec i (o_pending (tr_align o))); simpl; auto; lia. }
  split; [exact Hout|].
  split.
  { unfold core_eq. split; [reflexivity|]. split.
    - unfold sym_region. change (d_L (set_d_out s (tr_align o, m'))) with (d_L s).
      change (d_sym_next (set_d_out s (tr_align o, m'))) with (d_sym_next s).
      rewrite S0, Z.add_0_r, !sublist_nil. reflexivity.
    - split; cbn; [exact Wlen|exact Mlen]. }
  split; [repeat split; reflexivity|].
  split; [exact Hpo|]. split; [exact V7|].
  unfold pend. change (d_po (set_d_out s (tr_align o, m'))) with (d_po s).
  change (d_pending (set_d_out s (tr_align o, m'))) with (o_pending (tr_align o)).
  change (o_buf (tr_out (d_tr (set_d_out s (tr_align o, m'))))) with (o_buf (tr_align o)).
  rewrite Hpo, Z.add_0_l. unfold bytes. apply Forall_forall. intros x Hx.
  apply In_Znth in Hx. destruct Hx as [j [Hj Hx]]. subst x.
  rewrite Zlength_sublist in Hj by lia. rewrite Znth_sublist by lia. apply Bn. lia.
Qed.

(** Helpers for [stored_empty_ok]: the output buffer with its mask, of length [N], whose defined bytes are
    bytes and whose first [pending] bytes are defined. *)
Definition se_inv (om : cout) (N : Z) : Prop :=
  Zlength (o_buf (fst om)) = N /\ Zlength (snd om) = N /\ 0 <= o_pending (fst om) /\
  (forall i, 0 <= i < N -> Znth i (snd om) = true -> 0 <= Znth i (o_buf (fst om)) < 256) /\
  (forall i, 0 <= i < o_pending (fst om) -> Znth i (snd om) = true).

Lemma se_put_byte : forall o m c N, se_inv (o, m) N -> o_pending o < N ->
  exists o' m', c_put_byte (o, m) c = Some (o', m') /\ se_inv (o', m') N /\
    o_pending o' = o_pending o + 1 /\ o_bi_buf o' = o_bi_buf o /\ o_bi_valid o' = o_bi_valid o /\
    o_bi_used o' = o_bi_used o.
Proof.
  intros o m c N [L1 [L2 [P0 [B D]]]] HP. cbn [fst snd] in *.
  unfold c_put_byte, wr, in_range, bind.
  rewrite L1. rewrite (proj2 (Z.leb_le 0 (o_pending o))) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia.
  cbn [andb].
  eexists _, _. split; [reflexivity|]. cbn [o_pending o_bi_buf o_bi_valid o_bi_used o_buf fst snd].
  split; [|repeat split; lia]. unfold se_inv; cbn [fst snd o_buf o_pending].
  split; [rewrite Zlength_upd_Znth_any; lia|]. split; [rewrite Zlength_upd_Znth_any; lia|]. split; [lia|]. split.
  - intros i Hi Hm. destruct (Z.eq_dec i (o_pending o)) as [->|ne].
    + rewrite upd_Znth_same by lia. unfold u8. apply Z.mod_pos_bound. lia.
    + rewrite upd_Znth_diff by lia. rewrite upd_Znth_diff in Hm by lia. apply B; auto.
  - intros i Hi. destruct (Z.eq_dec i (o_pending o)) as [->|ne].
    + rewrite upd_Znth_same by lia. reflexivity.
    + rewrite upd_Znth_diff by lia. apply D; lia.
Qed.

Lemma se_put_short : forall o m w N, se_inv (o, m) N -> o_pending o + 2 <= N ->
  exists o' m', c_put_short (o, m) w = Some (o', m') /\ se_inv (o', m') N /\
    o_pending o' = o_pending o + 2 /\ o_bi_buf o' = o_bi_buf o /\ o_bi_valid o' = o_bi_valid o /\
    o_bi_used o' = o_bi_used o.
Proof.
  intros o m w N I HP. unfold c_put_short.
  destruct (se_put_byte o m (Z.land w 255) N) as [o1 [m1 [E1 [I1 [P1 [B1 [V1 U1]]]]]]]; [auto|lia|].
  rewrite E1. cbn [bind].
  destruct (se_put_byte o1 m1 (Z.shiftr (u16 w) 8) N) as [o2 [m2 [E2 [I2 [P2 [B2 [V2 U2]]]]]]]; [auto|lia|].
  rewrite E2. eexists _, _. split; [reflexivity|]. split; [auto|]. repeat split; congruence || lia.
Qed.

Lemma se_windup : forall o m N bb bv, se_inv (o, m) N -> o_pending o = 0 -> 6 <= N -> 0 <= bv <= 16 ->
  exists o1 m1, c_bi_windup (set_bits o bb bv, m) = Some (o1, m1) /\ se_inv (o1, m1) N /\
    o_pending o1 <= 2 /\ o_bi_valid o1 = 0 /\ o_bi_buf o1 = 0.
Proof.
  intros o m N bb bv I P0 HN Hbv. unfold c_bi_windup, guard. cbn [set_bits o_bi_valid o_bi_buf].
  rewrite (proj2 (Z.leb_le 0 bv)) by lia. rewrite (proj2 (Z.leb_le bv 16)) by lia. cbn [andb bind].
  destruct (bv >? 8).
  - destruct (se_put_short (set_bits o bb bv) m bb N) as [o1 [m1 [E1 [I1 [P1 _]]]]]; [exact I|cbn; lia|].
    rewrite E1. cbn [bind]. eexists _, _. split; [reflexivity|]. split; [exact I1|].
    cbn [o_pending o_bi_valid o_bi_buf]. cbn in P1. lia.
  - destruct (bv >? 0).
    + destruct (se_put_byte (set_bits o bb bv) m bb N) as [o1 [m1 [E1 [I1 [P1 _]]]]]; [exact I|cbn; lia|].
      rewrite E1. cbn [bind]. eexists _, _. split; [reflexivity|]. split; [exact I1|].
      cbn [o_pending o_bi_valid o_bi_buf]. cbn in P1. lia.
    + cbn [bind]. eexists _, _. split; [reflexivity|]. split; [exact I|].
      cbn. lia.
Qed.

Lemma se_stored_empty : forall o m N,
  se_inv (o, m) N -> o_pending o = 0 -> bits_ok o -> o_bi_valid o <= 7 -> 6 <= N ->
  exists o' m', c_tr_stored_block (o, m) [] 0 0 = Some (o', m') /\ se_inv (o', m') N /\
    o_pending o' <= 6 /\ o_bi_valid o' = 0 /\ o_bi_buf o' = 0.
Proof.
  intros o m N I P0 [BV [BB _]] V7 HN.
  assert (Hp : 2 ^ o_bi_valid o <= 2 ^ 7) by (apply Z.pow_le_mono_r; lia).
  change (2 ^ 7) with 128 in Hp.
  assert (E1 : c_send_bits (o, m) (Z.shiftl STORED_BLOCK 1 + 0) 3 =
               Some (set_bits o (o_bi_buf o) (o_bi_valid o + 3), m)).
  { unfold c_send_bits, guard, Buf_size, STORED_BLOCK.
    rewrite (proj2 (Z.leb_le 0 (o_bi_valid o))) by lia. rewrite (proj2 (Z.leb_le (o_bi_valid o) 16)) by lia.
    cbn [andb bind]. replace (o_bi_valid o >? 16 - 3) with false by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
    replace (u16 (Z.lor (o_bi_buf o) (Z.shiftl (u16 (Z.shiftl 0 1 + 0)) (o_bi_valid o)))) with (o_bi_buf o).
    reflexivity.
    change (u16 (Z.shiftl 0 1 + 0)) with 0. rewrite Z.shiftl_0_l, Z.lor_0_r.
    unfold u16. rewrite Z.mod_small by lia. reflexivity. }
  unfold c_tr_stored_block. rewrite E1. cbn [bind].
  destruct (se_windup o m N (o_bi_buf o) (o_bi_valid o + 3)) as [o1 [m1 [W1 [I1 [P1 [V1 B1]]]]]]; auto; [lia|].
  rewrite W1. cbn [bind].
  destruct (se_put_short o1 m1 (u16 0) N) as [o2 [m2 [E2 [I2 [P2 [B2 [V2 _]]]]]]]; [auto|lia|].
  rewrite E2. cbn [bind].
  destruct (se_put_short o2 m2 (u16 (Z.lnot 0)) N) as [o3 [m3 [E3 [I3 [P3 [B3 [V3 _]]]]]]]; [auto|lia|].
  rewrite E3. cbn [bind negb Z.eqb].
  eexists _, _. split; [reflexivity|]. cbn [o_pending o_bi_valid o_bi_buf].
  rewrite Z.add_0_r. split; [exact I3|]. lia.
Qed.

Lemma stored_empty_ok : forall s,
  prm s -> outok s -> quiet s -> d_sym_next s = 0 ->
  exists om, c_tr_stored_block (d_out s) [] 0 0 = Some om /\
    outok (set_d_out s om) /\ core_eq s (set_d_out s om) /\ api_eq s (set_d_out s om) /\
    d_po (set_d_out s om) = 0 /\ d_bi_valid (set_d_out s om) = 0 /\ bytes (pend (set_d_out s om)).
Proof.
  intros s Hp Ho Hq Hsym.
  destruct Hp as [_ [_ [_ [Hhb [_ [_ [_ [HL [Hpbs [Hbl [Hml _]]]]]]]]]]].
  destruct Ho as [Hmb [Hbits [Hpo0 [Hpp [Hdef Hz]]]]].
  destruct Hq as [Hpend [Hpo Hbv]].
  assert (HL2 : 2 ^ 1 <= 2 ^ (d_hash_bits s - 1)) by (apply Z.pow_le_mono_r; lia).
  change (2 ^ 1) with 2 in HL2.
  set (N := 4 * d_L s).
  assert (I0 : se_inv (tr_out (d_tr s), d_pbm s) N).
  { unfold se_inv; cbn [fst snd]. change (d_pending s) with (o_pending (tr_out (d_tr s))) in Hpend.
    split; [lia|]. split; [lia|]. split; [lia|]. split.
    - intros i Hi Hm. destruct Hmb as [_ Hmb]. apply (Hmb i); cbn; [lia|exact Hm].
    - intros i Hi. lia. }
  destruct (se_stored_empty (tr_out (d_tr s)) (d_pbm s) N) as [o' [m' [E [I [P [V B]]]]]];
    [exact I0|exact Hpend|exact Hbits|exact Hbv|lia|].
  destruct I as [L1 [L2 [P0 [IB ID]]]]. cbn [fst snd] in L1, L2, P0, IB, ID.
  exists (o', m'). split; [exact E|].
  change (d_po (set_d_out s (o', m'))) with (d_po s).
  change (d_pending (set_d_out s (o', m'))) with (o_pending o').
  change (d_bi_valid (set_d_out s (o', m'))) with (o_bi_valid o').
  split; [|split; [|split; [|split; [|split]]]].
  - unfold outok. change (d_po (set_d_out s (o', m'))) with (d_po s).
    change (d_pending (set_d_out s (o', m'))) with (o_pending o').
    change (d_pending_buf_size (set_d_out s (o', m'))) with (d_pending_buf_size s).
    change (d_pb (set_d_out s (o', m'))) with (mkMB (o_buf o') m').
    change (tr_out (d_tr (set_d_out s (o', m')))) with o'.
    split; [|split; [|split; [|split; [|split]]]].
    + split; cbn [mb_def mb_val]; [lia|]. intros i Hi Hm. apply IB; [lia|exact Hm].
    + unfold bits_ok. rewrite V, B. change (2 ^ 0) with 1. lia.
    + lia.
    + lia.
    + split; [lia|]. cbn [mb_val mb_def]. split; [lia|]. intros i Hi. apply ID. lia.
    + intros _. exact Hpo.
  - split; [reflexivity|]. split; [|split].
    3: { change (d_pbm (set_d_out s (o', m'))) with m'. lia. }
    2: { change (tr_out (d_tr (set_d_out s (o', m')))) with o'. lia. }
    unfold sym_region. change (d_sym_next (set_d_out s (o', m'))) with (d_sym_next s).
    change (d_L (set_d_out s (o', m'))) with (d_L s). rewrite Hsym, Z.add_0_r, !sublist_nil. reflexivity.
  - repeat split; reflexivity.
  - exact Hpo.
  - exact V.
  - unfold pend. change (d_po (set_d_out s (o', m'))) with (d_po s).
    change (d_pending (set_d_out s (o', m'))) with (o_pending o').
    change (tr_out (d_tr (set_d_out s (o', m')))) with o'.
    rewrite Hpo, Z.add_0_l. apply Forall_forall_Znth. intros i Hi.
    rewrite Zlength_sublist in Hi by lia. rewrite Znth_sublist by lia.
    apply IB; [lia|]. apply ID. lia.
Qed.

(** ** put_byte and putShortMSB with pending_out at the start of pending_buf *)
Lemma dput_byte_step : forall s c,
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

Lemma dput_bytes_ok : forall s l,
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
    destruct (dput_byte_step s c) as (s1 & E1 & P1 & O1 & C1 & A1 & Po1 & B1 & D1 & Pr1 & Sn1); auto; [lia|].
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

Lemma putShortMSB2_eq : forall s b1 b2,
  (let* s := c_putShortMSB s b1 in c_putShortMSB s b2) =
  c_dput_bytes s [Z.shiftr b1 8; Z.land b1 255; Z.shiftr b2 8; Z.land b2 255].
Proof.
  intros. unfold c_putShortMSB. cbn [c_dput_bytes].
  destruct (c_dput_byte s (Z.shiftr b1 8)) as [s1|]; cbn [bind]; [|reflexivity].
  destruct (c_dput_byte s1 (Z.land b1 255)) as [s2|]; cbn [bind]; [|reflexivity].
  destruct (c_dput_byte s2 (Z.shiftr b2 8)) as [s3|]; cbn [bind]; [|reflexivity].
  destruct (c_dput_byte s3 (Z.land b2 255)) as [s4|]; reflexivity.
Qed.

Lemma putShortMSB2_ok : forall s b1 b2,
  prm s -> outok s -> d_po s = 0 -> d_sym_next s = 0 -> d_pending s + 4 <= d_pending_buf_size s ->
  exists s1, (let* s := c_putShortMSB s b1 in c_putShortMSB s b2) = Some s1 /\
    pend s1 = pend s ++ msb2 b1 ++ msb2 b2 /\
    outok s1 /\ core_eq s s1 /\ api_eq s s1 /\ d_po s1 = 0 /\ d_bi_valid s1 = d_bi_valid s /\
    d_pending s1 = d_pending s + 4.
Proof.
  intros s b1 b2 Hp Ho Hpo Hsym Hn.
  destruct (dput_bytes_ok s [Z.shiftr b1 8; Z.land b1 255; Z.shiftr b2 8; Z.land b2 255]) as (s1 & E & P & R);
    auto.
  exists s1. rewrite putShortMSB2_eq, E. split; [reflexivity|]. split; [rewrite P; reflexivity|].
  destruct R as (R1 & R2 & R3 & R4 & R5 & R6).
  split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R5|].
  rewrite R6. reflexivity.
Qed.
