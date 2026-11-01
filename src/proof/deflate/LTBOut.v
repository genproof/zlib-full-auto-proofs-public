(** * deflate_bound theory: the output part of deflate()'s own stages

    The same statements as LTApiOut.v of the deflate_api part: flush_pending (with at most
    7 bits in the bit buffer), put_byte / putShortMSB at the start of pending_buf; each keeps [outok] and only
    changes what [core_eq] / [api_eq] allow.  (core_eq_* copied with their proofs.) *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTBDefs.
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
Record out_facts : Prop := {
  ou_flush_pending_ok : forall s z,
  outok s -> d_bi_valid s <= 7 -> 0 <= z_avail_out z <= 1073741824 -> 0 <= z_total_out z <= 1099511627776 ->
  exists s' x,
    c_flush_pending s z =
      Some (s', mkST (z_in z) (z_next_in z) (z_avail_in z) (z_total_in z) (z_out z ++ x)
                     (z_avail_out z - Zlength x) (z_total_out z + Zlength x) (z_adler z) (z_msg z)) /\
    pend s = x ++ pend s' /\ Zlength x = Z.min (d_pending s) (z_avail_out z) /\ bytes x /\
    outok s' /\ core_eq s s' /\ api_eq s s' /\ d_bi_valid s' = d_bi_valid s /\
    d_pending s' = d_pending s - Zlength x /\ (d_pending s' = 0 -> d_po s' = 0);
  ou_dput_bytes_ok : forall s l,
  prm s -> outok s -> d_po s = 0 -> d_sym_next s = 0 -> d_pending s + Zlength l <= d_pending_buf_size s ->
  exists s1, c_dput_bytes s l = Some s1 /\ pend s1 = pend s ++ map u8 l /\
    outok s1 /\ core_eq s s1 /\ api_eq s s1 /\ d_po s1 = 0 /\ d_bi_valid s1 = d_bi_valid s /\
    d_pending s1 = d_pending s + Zlength l
}.

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

Lemma ltb_flush_pending_ok : forall s z,
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

Lemma ltb_dput_bytes_ok : forall s l,
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

Theorem out_proof : out_facts.
Proof.
  constructor; [exact ltb_flush_pending_ok | exact ltb_dput_bytes_ok].
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
Proof. exact (ou_flush_pending_ok out_proof). Qed.

Lemma dput_bytes_ok : forall s l,
  prm s -> outok s -> d_po s = 0 -> d_sym_next s = 0 -> d_pending s + Zlength l <= d_pending_buf_size s ->
  exists s1, c_dput_bytes s l = Some s1 /\ pend s1 = pend s ++ map u8 l /\
    outok s1 /\ core_eq s s1 /\ api_eq s s1 /\ d_po s1 = 0 /\ d_bi_valid s1 = d_bi_valid s /\
    d_pending s1 = d_pending s + Zlength l.
Proof. exact (ou_dput_bytes_ok out_proof). Qed.


(** ** put_byte and putShortMSB with pending_out at the start of pending_buf *)

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

(** ** The class, the parameters and the unblocked bytes are seen by [core_eq] *)
Lemma bcls_core_eq : forall s s', core_eq s s' -> bcls_of s' = bcls_of s.
Proof.
  intros s s' H. destruct (core_eq_fields s s' H) as (_ & _ & E3 & E4 & _ & _ & _ & _ & _ & E10 & E11 & _).
  unfold bcls_of, tight_b. rewrite E3, E4, E10, E11. reflexivity.
Qed.

Lemma ub_core_eq : forall s s', core_eq s s' -> ub s' = ub s.
Proof.
  intros s s' H. destruct (core_eq_fields s s' H) as (_ & _ & _ & _ & E5 & E6 & E7 & _).
  unfold ub. rewrite E5, E6, E7. reflexivity.
Qed.
