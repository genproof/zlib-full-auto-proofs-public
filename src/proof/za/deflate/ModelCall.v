(** * One deflate() call right after deflateInit2_: the model run is defined

    [first_call]: from [first_core_stmt] (ModelCore.v: the compression stage for calls of up to 2^32 - 1 bytes),
    the model of deflate() ([c_deflate], DModel4.v) on the stream a successful deflateInit2_ returned, given any
    flush, any input object of up to 2^32 - 1 bytes and up to 2^32 - 1 bytes of output space, is [Some].

    The call goes through deflate()'s stages ([LTDefs.c_deflate_stages]): the entry checks; the zlib header (2
    bytes) or the gzip header without gzhead (10 bytes) or nothing (raw), then flush_pending; one call of the
    compression function and the block_done branch (LTApiBd.bd_first_ok); the trailer.  The stage lemmas of the
    deflate_api theory (LTApi*.v) bound the output space by 2^20 bytes; only flush_pending reads it, so
    [flush_pending_w] restates LTApiOut.flush_pending_ok for any output space and everything else is reused. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.za.deflate.ModelCore.
Require Import Zlib.proof.deflate.LTApiOut Zlib.proof.deflate.LTApiBd Zlib.proof.deflate.LTApiTrail
  Zlib.proof.deflate.LTApiInit Zlib.proof.deflate.LTApiComp.
Require Zlib.proof.huffman.Lemmas.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** flush_pending for any output space (LTApiOut.flush_pending_ok, the same proof) *)
Lemma flush_pending_w : forall s z,
  outok s -> d_bi_valid s <= 7 -> 0 <= z_avail_out z <= 4294967295 -> 0 <= z_total_out z ->
  z_total_out z + z_avail_out z <= 18446744073709551615 ->
  exists s' x,
    c_flush_pending s z =
      Some (s', mkST (z_in z) (z_next_in z) (z_avail_in z) (z_total_in z) (z_out z ++ x)
                     (z_avail_out z - Zlength x) (z_total_out z + Zlength x) (z_adler z) (z_msg z)) /\
    pend s = x ++ pend s' /\ Zlength x = Z.min (d_pending s) (z_avail_out z) /\ bytes x /\
    outok s' /\ core_eq s s' /\ api_eq s s' /\ d_bi_valid s' = d_bi_valid s /\
    d_pending s' = d_pending s - Zlength x /\ (d_pending s' = 0 -> d_po s' = 0).
Proof.
  intros s z Hok Hbv Hao Hto Hsum.
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

(** [z'] is [z] after [k] bytes were written to next_out, nothing else changed but [adler]. *)
Definition zo (z z' : strm) (k a : Z) : Prop :=
  z_in z' = z_in z /\ z_next_in z' = z_next_in z /\ z_avail_in z' = z_avail_in z /\
  z_total_in z' = z_total_in z /\ 0 <= k <= z_avail_out z /\ z_avail_out z' = z_avail_out z - k /\
  z_total_out z' = z_total_out z + k /\ z_adler z' = a.

(** [flush_pending(strm); if (s->pending != 0) { s->last_flush = -1; return Z_OK; }] for any output space. *)
Lemma flush_or_return_w : forall s z,
  outok s -> d_bi_valid s <= 7 -> 0 <= z_avail_out z <= 4294967295 -> 0 <= z_total_out z ->
  z_total_out z + z_avail_out z <= 18446744073709551615 ->
  exists s' z' o, c_flush_or_return s z = Some (s', z', o) /\
    (o = None -> d_pending s' = 0 /\ d_po s' = 0 /\ outok s' /\ core_eq s s' /\ api_eq s s' /\
                 d_bi_valid s' = d_bi_valid s /\ exists k, k <= d_pending s /\ zo z z' k (z_adler z)).
Proof.
  intros s z Hok Hbv Hao Hto Hsum.
  destruct (flush_pending_w s z Hok Hbv Hao Hto Hsum)
    as (s' & x & E & _ & Hx & _ & Ho & Hc & Ha & Hb & Hp & Hpo).
  unfold c_flush_or_return. rewrite E. cbn [bind].
  destruct (negb (d_pending s' =? 0)) eqn:Hn.
  - eexists _, _, _. split; [reflexivity|]. intros; discriminate.
  - apply negb_false_iff, Z.eqb_eq in Hn.
    eexists _, _, _. split; [reflexivity|]. intros _.
    split; [exact Hn|]. split; [auto|]. split; [exact Ho|]. split; [exact Hc|]. split; [exact Ha|].
    split; [exact Hb|]. exists (Zlength x). pose proof (Zlength_nonneg x).
    split; [lia|]. unfold zo; cbn. repeat split; try reflexivity; lia.
Qed.

(** ** The header stages of the first call *)

Lemma putShortMSB_bytes : forall s b, c_putShortMSB s b = c_dput_bytes s [Z.shiftr b 8; Z.land b 255].
Proof.
  intros s b. unfold c_putShortMSB. cbn [c_dput_bytes].
  destruct (c_dput_byte s (Z.shiftr b 8)) as [s1|]; cbn [bind]; [|reflexivity].
  destruct (c_dput_byte s1 (Z.land b 255)); reflexivity.
Qed.

(** Stages 4 to 7 (EXTRA .. HCRC) of the header. *)
Definition hdr_rest (s : dstate) (z : strm) : option dres :=
  then_stage (c_deflate_extra s z) (fun s z =>
  then_stage (c_deflate_name s z) (fun s z =>
  then_stage (c_deflate_comment s z) (fun s z =>
  c_deflate_hcrc s z))).

Lemma hdr_stages_split : forall s z,
  hdr_stages s z = then_stage (c_deflate_zlib_header s z) (fun s z =>
                   then_stage (c_deflate_gzip_header s z) hdr_rest).
Proof. reflexivity. Qed.

Lemma gzip_rest_busy : forall s z, d_status s = BUSY_STATE ->
  then_stage (c_deflate_gzip_header s z) hdr_rest = Some (s, z, None).
Proof.
  intros s z H. unfold hdr_rest, c_deflate_gzip_header, c_deflate_extra, c_deflate_name, c_deflate_comment,
    c_deflate_hcrc, then_stage.
  destruct s; simpl in H; subst; reflexivity.
Qed.

Lemma room512 : forall s, prm s -> 512 <= d_pending_buf_size s.
Proof.
  intros s (_ & _ & _ & Hhb & _ & _ & _ & HL & Hpbs & _).
  assert (2 ^ 7 <= 2 ^ (d_hash_bits s - 1)) by (apply Z.pow_le_mono_r; lia).
  lia.
Qed.

Lemma hdr_rest_busy : forall s z, d_status s = BUSY_STATE -> hdr_rest s z = Some (s, z, None).
Proof.
  intros s z H. unfold hdr_rest, c_deflate_extra, c_deflate_name, c_deflate_comment, c_deflate_hcrc, then_stage.
  destruct s; simpl in H; subst; reflexivity.
Qed.

Lemma outok_status : forall s x, outok s -> outok (set_d_status s x).
Proof. intros s x H. exact H. Qed.

(** After the header stages of a fresh stream (status INIT for raw / zlib, GZIP without gzhead): either the call
    returns, or the state is BUSY with nothing pending and at most 10 bytes were written. *)
Lemma hdr_first : forall W s z,
  core_facts W -> W s -> outok s -> d_pending s = 0 -> d_bi_valid s = 0 ->
  d_sym_next s = 0 -> d_strstart s = 0 -> d_gzhead s = None ->
  ((d_status s = INIT_STATE /\ 0 <= d_wrap s <= 1) \/ (d_status s = GZIP_STATE /\ d_wrap s = 2)) ->
  0 <= z_avail_out z <= 4294967295 -> 0 <= z_total_out z <= 1099511627776 ->
  exists s' z' o, hdr_stages s z = Some (s', z', o) /\
    (o = None -> W s' /\ outok s' /\ quiet s' /\ d_bi_valid s' = 0 /\ d_sym_next s' = 0 /\
                 d_status s' = BUSY_STATE /\ d_wrap s' = d_wrap s /\ core_eq s s' /\
                 exists k, k <= 10 /\ zo z z' k (hdr_adler (d_wrap s) (z_adler z))).
Proof.
  intros W s z CF HW Hok Hpd Hbv Hsn Hss Hgz Hst Hao Hto.
  pose proof (cf_prm W CF s HW) as HP.
  pose proof (tk_room s HP) as Hroom.
  assert (Hpo : d_po s = 0) by (destruct Hok as (_ & _ & _ & _ & _ & X); auto).
  rewrite hdr_stages_split.
  destruct Hst as [[Hst Hw] | [Hst Hw]].
  - destruct (Z.eq_dec (d_wrap s) 0) as [Hw0|Hw0].
    + (* raw: nothing to write *)
      unfold c_deflate_zlib_header. cbv zeta. rewrite Hst, Hw0.
      change (INIT_STATE =? INIT_STATE) with true. cbn [andb Z.eqb].
      change (d_status (set_d_status s BUSY_STATE) =? INIT_STATE) with false. cbn [then_stage bind].
      rewrite gzip_rest_busy by reflexivity.
      eexists _, _, _. split; [reflexivity|]. intros _.
      split; [exact (cf_frame W CF _ _ HW (cs_core_eq_status s _))|].
      split; [exact (outok_status s _ Hok)|].
      split; [split; [exact Hpd|split; [exact Hpo|change (d_bi_valid s <= 7); lia]]|].
      split; [exact Hbv|]. split; [exact Hsn|]. split; [reflexivity|]. split; [exact Hw0|].
      split; [exact (cs_core_eq_status s _)|].
      exists 0. split; [lia|]. unfold zo, hdr_adler. cbn. repeat split; try reflexivity; lia.
    + (* zlib: the 2-byte header *)
      assert (Hw1 : d_wrap s = 1) by lia.
      unfold c_deflate_zlib_header. cbv zeta. rewrite Hst, Hw1. cbn [then_stage bind andb Z.eqb Pos.eqb].
      change (INIT_STATE =? INIT_STATE) with true. cbn [then_stage bind andb negb].
      rewrite Hst. change (INIT_STATE =? INIT_STATE) with true.
      rewrite putShortMSB_bytes.
      destruct (dput_bytes_ok s [Z.shiftr (zlib_header s) 8; Z.land (zlib_header s) 255])
        as (s1 & E1 & _ & O1 & C1 & A1 & Po1 & B1 & P1); auto.
      { rewrite Hpd. cbn. lia. }
      rewrite E1. cbn [bind].
      destruct (core_eq_fields _ _ C1) as (_ & _ & _ & _ & _ & F6 & _ & _ & F9 & _).
      rewrite F6, Hss. cbn [Z.eqb bind].
      destruct (flush_or_return_w (set_d_status s1 BUSY_STATE) (set_z_adler z 1))
        as (s2 & z2 & o & E2 & Q); try exact (outok_status s1 _ O1); cbn; try lia.
      { change (d_bi_valid (set_d_status s1 BUSY_STATE)) with (d_bi_valid s1). lia. }
      rewrite E2. destruct o as [c|].
      { cbn [then_stage]. eexists _, _, _. split; [reflexivity|]. intros; discriminate. }
      destruct (Q eq_refl) as (Pd2 & Po2 & O2 & C2 & (A21 & A22 & _) & B2 & k & Hk & Z2).
      cbn [then_stage bind]. rewrite gzip_rest_busy by exact A21.
      assert (C02 : core_eq s s2) by
        (eapply core_eq_trans; [exact C1|eapply core_eq_trans; [apply cs_core_eq_status|exact C2]]).
      eexists _, _, _. split; [reflexivity|]. intros _.
      split; [exact (cf_frame W CF _ _ HW C02)|]. split; [exact O2|].
      change (d_bi_valid (set_d_status s1 BUSY_STATE)) with (d_bi_valid s1) in B2.
      split; [split; [exact Pd2|split; [exact Po2|lia]]|]. split; [lia|].
      split; [destruct (core_eq_fields _ _ C02) as (_ & _ & _ & _ & _ & _ & _ & _ & X & _); congruence|].
      split; [exact A21|].
      split; [destruct A1 as (_ & A12 & _); rewrite A22; change (d_wrap s1 = 1); congruence|].
      split; [exact C02|].
      exists k. change (d_pending (set_d_status s1 BUSY_STATE)) with (d_pending s1) in Hk.
      rewrite P1, Hpd in Hk. cbn in Hk. split; [lia|].
      destruct Z2 as (Z21 & Z22 & Z23 & Z24 & Z25 & Z26 & Z27 & Z28).
      cbn [set_z_adler z_in z_next_in z_avail_in z_total_in z_avail_out z_total_out z_adler] in *.
      unfold zo. repeat split; try assumption; lia.
  - (* gzip without gzhead: the 10-byte header *)
    pose proof (room512 s HP) as Hr.
    unfold c_deflate_zlib_header. cbv zeta. rewrite Hst, Hw.
    change (GZIP_STATE =? INIT_STATE) with false. cbn [andb then_stage bind].
    rewrite Hst. change (GZIP_STATE =? INIT_STATE) with false. cbn [then_stage bind].
    unfold c_deflate_gzip_header. rewrite Hst. change (GZIP_STATE =? GZIP_STATE) with true. cbv zeta.
    destruct (dput_bytes_ok s [31; 139; 8]) as (s1 & E1 & _ & O1 & C1 & A1 & Po1 & B1 & P1); auto.
    { rewrite Hpd. cbn. lia. }
    rewrite E1. cbn [bind].
    assert (G1 : d_gzhead s1 = None) by (destruct A1 as (_ & _ & X & _); congruence). rewrite G1.
    destruct (core_eq_fields _ _ C1) as (_ & _ & _ & _ & _ & _ & _ & F8 & F9 & _).
    assert (W1 : W s1) by exact (cf_frame W CF _ _ HW C1).
    destruct (dput_bytes_ok s1 [0; 0; 0; 0; 0; xfl_byte s1; OS_CODE])
      as (s2 & E2 & _ & O2 & C2 & A2 & Po2 & B2 & P2); auto.
    { exact (cf_prm W CF s1 W1). } { congruence. }
    { rewrite P1, Hpd, F8. cbn. lia. }
    cbv zeta in E2. rewrite E2. cbn [bind].
    destruct (flush_or_return_w (set_d_status s2 BUSY_STATE) (set_z_adler z 0))
      as (s3 & z3 & o & E3 & Q); try exact (outok_status s2 _ O2); cbn; try lia.
    { change (d_bi_valid (set_d_status s2 BUSY_STATE)) with (d_bi_valid s2). lia. }
    rewrite E3. destruct o as [c|].
    { cbn [then_stage]. eexists _, _, _. split; [reflexivity|]. intros; discriminate. }
    destruct (Q eq_refl) as (Pd3 & Po3 & O3 & C3 & (A31 & A32 & _) & B3 & k & Hk & Z3).
    cbn [then_stage bind].
    change (then_stage (c_deflate_extra s3 z3) (fun s0 z0 => then_stage (c_deflate_name s0 z0) (fun s4 z1 =>
              then_stage (c_deflate_comment s4 z1) (fun s5 z2 => c_deflate_hcrc s5 z2))))
      with (hdr_rest s3 z3).
    rewrite hdr_rest_busy by exact A31.
    assert (C03 : core_eq s s3) by
      (eapply core_eq_trans; [exact C1|eapply core_eq_trans; [exact C2|
        eapply core_eq_trans; [apply cs_core_eq_status|exact C3]]]).
    eexists _, _, _. split; [reflexivity|]. intros _.
    split; [exact (cf_frame W CF _ _ HW C03)|]. split; [exact O3|].
    change (d_bi_valid (set_d_status s2 BUSY_STATE)) with (d_bi_valid s2) in B3.
    split; [split; [exact Pd3|split; [exact Po3|lia]]|]. split; [lia|].
    split; [destruct (core_eq_fields _ _ C03) as (_ & _ & _ & _ & _ & _ & _ & _ & X & _); congruence|].
    split; [exact A31|].
    split; [destruct A1 as (_ & A12 & _); destruct A2 as (_ & A22 & _); rewrite A32;
            change (d_wrap s2 = 2); congruence|].
    split; [exact C03|].
    exists k. change (d_pending (set_d_status s2 BUSY_STATE)) with (d_pending s2) in Hk.
    rewrite P2, P1, Hpd in Hk. cbn in Hk. split; [lia|].
    destruct Z3 as (Z31 & Z32 & Z33 & Z34 & Z35 & Z36 & Z37 & Z38).
    cbn [set_z_adler z_in z_next_in z_avail_in z_total_in z_avail_out z_total_out z_adler] in *.
    unfold zo, hdr_adler. cbn [Z.eqb Pos.eqb]. repeat split; try assumption; lia.
Qed.

(** ** The compression stage and the trailer *)

Lemma zstep_out : forall w z z' k x, zstep w z z' k x ->
  0 <= z_avail_out z <= 4294967295 -> 0 <= z_total_out z <= 1099511627776 ->
  0 <= z_avail_out z' <= 4294967295 /\ 0 <= z_total_out z' /\
  z_total_out z' + z_avail_out z' <= 18446744073709551615.
Proof.
  intros w z z' k x (_ & _ & _ & _ & _ & _ & _ & Hx & Hao & Hto & _) H1 H2.
  pose proof (Zlength_nonneg x).
  rewrite Hto, Hao. unfold u64. rewrite Z.mod_small by lia. lia.
Qed.

(** From a BUSY state with nothing in the window and nothing pending: the compression stage (one call of the
    compression function) and the trailer are defined. *)
Lemma comp_trailer_first : forall W s z flush,
  core_facts W -> cf_compress_w1 W -> W s -> outok s -> quiet s ->
  d_status s = BUSY_STATE -> ub s = 0 -> 0 <= d_wrap s <= 2 -> 0 <= flush <= 5 -> zin_w1 z ->
  adler_pre (d_wrap s) (z_adler z) ->
  exists r, (let* (s, z, o) := c_deflate_compress s z flush in
             match o with Some r => Some (s, z, r) | None => c_deflate_trailer s z flush end) = Some r.
Proof.
  intros W s z flush CF CW HW Hok Hq Hst Hub Hw Hfl Hz Had.
  pose proof Hz as (_ & _ & Hai & _ & Hao & _ & Hto).
  unfold c_deflate_compress.
  destruct (negb (z_avail_in z =? 0) || negb (d_lookahead s =? 0) ||
            (negb (flush =? Z_NO_FLUSH) && negb (d_status s =? FINISH_STATE))) eqn:Hc.
  2:{ cbn [bind]. unfold c_deflate_trailer.
      destruct (negb (flush =? Z_FINISH)) eqn:Hf; [eexists; reflexivity|].
      exfalso. apply negb_false_iff, Z.eqb_eq in Hf. subst flush. rewrite Hst in Hc.
      rewrite !orb_false_iff in Hc. destruct Hc as (_ & Hc). discriminate Hc. }
  destruct (CW s z flush HW Hok Hq Hfl Hz ltac:(lia) Hw Had) as (s' & z' & bs & evs & Hcf & Hcp).
  rewrite Hcf. cbn [bind].
  destruct Hcp as (HW' & Hok' & Hsp & Hapi & (k & x & Hzs & _ & _) & _ & _ & Hbs).
  destruct (zstep_out _ _ _ _ _ Hzs Hao Hto) as (Hao' & Hto' & Hsum').
  destruct bs.
  - destruct (z_avail_out z' =? 0); eexists; reflexivity.
  - destruct Hbs as (_ & Hf0 & Hf4 & Hai0 & Hub' & Hq' & Hsn').
    destruct (cs_ub0 _ _ CF HW' Hub') as [Hla Hss].
    destruct (bd_first_ok W s' flush CF HW' Hok' Hq' Hsn' Hla Hss) as (s2 & E2 & W2 & O2 & B2 & _).
    cbv zeta in E2. rewrite E2. cbn [bind].
    destruct (flush_pending_w s2 z' O2 B2 Hao' Hto' Hsum') as (s3 & x3 & E3 & _).
    rewrite E3. cbn [bind].
    cbn [z_avail_out]. destruct (z_avail_out z' - Zlength x3 =? 0); cbn [bind]; [eexists; reflexivity|].
    unfold c_deflate_trailer. rewrite (proj2 (Z.eqb_neq flush Z_FINISH) Hf4). eexists; reflexivity.
  - destruct (z_avail_out z' =? 0); eexists; reflexivity.
  - destruct Hbs as (_ & Hf4 & Hai0 & Hub' & Hsn' & Hq' & Hbi0).
    subst flush. unfold c_deflate_trailer. change (negb (Z_FINISH =? Z_FINISH)) with false. cbv iota. cbn [bind].
    destruct Hapi as (_ & Aw & _).
    destruct (d_wrap (set_d_status s' FINISH_STATE) <=? 0) eqn:Hw0; [eexists; reflexivity|].
    apply Z.leb_gt in Hw0. change (0 < d_wrap s') in Hw0.
    set (s1 := set_d_status s' FINISH_STATE).
    assert (W1 : W s1) by exact (cf_frame W CF _ _ HW' (cs_core_eq_status s' _)).
    destruct Hq' as (Hpd' & Hpo' & _).
    destruct (tk_put_trailer s1 (z_adler z') (z_total_in z') (cf_prm W CF s1 W1) (outok_status s' _ Hok')
                Hpd' Hsn' ltac:(change (d_wrap s1) with (d_wrap s'); lia))
      as (s4 & E4 & _ & O4 & _ & _ & B4).
    rewrite E4. cbn [bind].
    destruct (flush_pending_w s4 z' O4 ltac:(rewrite B4; change (d_bi_valid s1) with (d_bi_valid s'); lia)
                Hao' Hto' Hsum') as (s5 & x5 & E5 & _).
    rewrite E5. eexists; reflexivity.
Qed.

(** ** The entry stage of the first call *)
Lemma entry_first : forall s z flush,
  d_status s <> FINISH_STATE -> d_pending s = 0 -> d_last_flush s = -2 -> 0 <= flush <= 5 ->
  c_deflate_entry s z flush =
    if z_avail_out z =? 0 then Some (s, set_z_msg z (Some Z_BUF_ERROR), Some Z_BUF_ERROR)
    else Some (set_d_last_flush s flush, z, None).
Proof.
  intros s z flush Hst Hpd Hlf Hfl.
  unfold c_deflate_entry.
  rewrite (proj2 (Z.eqb_neq _ _) Hst). cbn [andb].
  destruct (z_avail_out z =? 0); [reflexivity|]. cbv zeta.
  change (d_pending (set_d_last_flush s flush)) with (d_pending s). rewrite Hpd. cbn [Z.eqb negb].
  destruct (z_avail_in z =? 0).
  - rewrite Hlf. cbn [Z.mul in_int Z.leb Z.compare guard bind andb Pos.compare Pos.compare_cont].
    replace (rank flush <=? rank (-2)) with false
      by (symmetry; apply Z.leb_gt; unfold rank; destruct (Z.gtb_spec flush 4); cbn; lia).
    simpl. rewrite (proj2 (Z.eqb_neq _ _) Hst). reflexivity.
  - simpl. rewrite (proj2 (Z.eqb_neq _ _) Hst). reflexivity.
Qed.

(** ** One deflate() call right after deflateInit2_ *)
Theorem first_call : first_core_stmt ->
  forall level method wbits mem strategy z0 s z1 inb aout flush,
    c_deflateInit2_ true true false level method wbits mem strategy true true true true true z0 =
      Some (Some s, z1, Z_OK) ->
    bytes inb -> Zlength inb <= 4294967295 -> 0 <= aout <= 4294967295 ->
    exists r, c_deflate s (mkST inb 0 (Zlength inb) (z_total_in z1) [] aout (z_total_out z1) (z_adler z1)
                                (z_msg z1)) flush = Some r.
Proof.
  intros Hcore level method wbits mem strategy z0 s z1 inb aout flush HI Hb Hl Ha.
  destruct (Hcore (proj1 Zlib.proof.huffman.Lemmas.huffman_lemmas)) as (W & CF & CW).
  assert (Hp : params_ok level method wbits mem strategy = true).
  { rewrite init_shape in HI. destruct (params_ok level method wbits mem strategy); [reflexivity|discriminate]. }
  destruct (cf_init W CF level method wbits mem strategy z0 Hp)
    as (s' & z' & E & HW & Hok & Hst & Hwr & Hgz & _ & Hlf & _ & Hpd & Hbv & Hss & Hla & Hbs & Hsn & _ & _ & _ & _ & Hz').
  rewrite E in HI. injection HI as -> <-. clear E.
  rewrite Hz'. cbn [z_total_in z_total_out z_adler z_msg].
  assert (Hcase : (d_status s = INIT_STATE /\ 0 <= d_wrap s <= 1) \/ (d_status s = GZIP_STATE /\ d_wrap s = 2)).
  { rewrite Hst, Hwr. unfold wrap_of. destruct (wbits <? 0); [|destruct (wbits >? 15)]; cbn;
      [left|right|left]; split; auto; lia. }
  assert (Hbad : bad_state s = false).
  { unfold bad_state, c_deflateStateCheck, status_ok.
    destruct Hcase as [[H _]|[H _]]; rewrite H; reflexivity. }
  rewrite c_deflate_stages, Hbad. cbn [orb].
  destruct ((flush >? Z_BLOCK) || (flush <? 0)) eqn:Hfl; [eexists; reflexivity|].
  assert (Hf : 0 <= flush <= 5).
  { apply orb_false_iff in Hfl as [H1 H2]. rewrite Z.gtb_ltb in H1. apply Z.ltb_ge in H1. apply Z.ltb_ge in H2.
    unfold Z_BLOCK in H1. lia. }
  rewrite entry_first; auto.
  2:{ destruct Hcase as [[H _]|[H _]]; rewrite H; discriminate. }
  cbn [z_avail_out].
  destruct (aout =? 0); cbn [then_stage bind]; [eexists; reflexivity|].
  set (z := mkST inb 0 (Zlength inb) 0 [] aout 0 (if wrap_of wbits =? 2 then 0 else 1) None).
  destruct (hdr_first W (set_d_last_flush s flush) z CF (cf_frame W CF _ _ HW (cs_core_eq_lf s flush))
              Hok Hpd Hbv Hsn Hss Hgz Hcase ltac:(cbn; lia) ltac:(cbn; lia))
    as (s2 & z2 & o & E2 & Q).
  rewrite E2. destruct o as [c|]; cbn [then_stage bind]; [eexists; reflexivity|].
  destruct (Q eq_refl) as (W2 & O2 & Q2 & B2 & S2 & St2 & Wr2 & C2 & k & Hk & Z2).
  change (d_wrap (set_d_last_flush s flush)) with (d_wrap s) in Wr2, Z2.
  destruct (core_eq_fields _ _ C2) as (_ & _ & _ & _ & F5 & F6 & F7 & _).
  change (d_block_start (set_d_last_flush s flush)) with (d_block_start s) in F5.
  change (d_strstart (set_d_last_flush s flush)) with (d_strstart s) in F6.
  change (d_lookahead (set_d_last_flush s flush)) with (d_lookahead s) in F7.
  destruct Z2 as (Z21 & Z22 & Z23 & Z24 & Z25 & Z26 & Z27 & Z28).
  cbn [z z_in z_next_in z_avail_in z_total_in z_avail_out z_total_out z_adler] in *.
  apply (comp_trailer_first W s2 z2 flush CF CW W2 O2 Q2 St2).
  - unfold ub. lia.
  - destruct Hcase as [[_ H]|[_ H]]; lia.
  - exact Hf.
  - unfold zin_w1. rewrite Z21, Z22, Z23, Z24, Z26, Z27. pose proof (Zlength_nonneg inb).
    repeat split; auto; lia.
  - rewrite Wr2, Z28. unfold adler_pre, hdr_adler. split; intros Hw.
    + rewrite Hw. cbn. exact adler_valid_1.
    + rewrite Hw. cbn. lia.
Qed.
