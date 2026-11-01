(** * deflate() on [Iapi] without its size limits: the invariant inside a call

    The stage lemmas of the deflate_api theory (LTApiEntry, LTApiHdrSt, LTApiComp, LTApiTrail) run a call
    offered the whole input object from next_in = 0 and at most 2^20 bytes of output space ([Mid], LTApiDefs.v).
    Law api_deterministic calls deflate() after a deflateParams() that may have consumed a part of the same input
    object, and offers up to 2^32 - 1 bytes of output space.  [MidW] is [Mid] for a call that starts at next_in
    [nin]: total_in counts the bytes consumed from [nin] on, the data are [D ++ sublist nin next_in inb], and the
    bounds are those of [api_deflate_wide] (DetWide.v).  The stages run under it with the facts of DetWide.v
    ([cf_compress_wide], [cf_still_wide], [hf_run_wide]); [MidW] gives the zwide / hdr_pre_wide bounds they
    need ([midw_zwide], [midw_out]). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.DetWide Zlib.proof.deflate.LTApiOut Zlib.proof.deflate.LTApiArith.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** The running stream of a call offered the input object [inb] from [nin] on and [aout] bytes of output
    space. *)
Definition zrunw (inb : list Z) (nin aout tin tout : Z) (z : strm) : Prop :=
  z_in z = inb /\ nin <= z_next_in z <= Zlength inb /\ z_avail_in z = Zlength inb - z_next_in z /\
  z_total_in z = tin + (z_next_in z - nin) /\
  0 <= z_avail_out z /\ Zlength (z_out z) = aout - z_avail_out z /\ z_total_out z = tout + Zlength (z_out z) /\
  bytes (z_out z).

(** [Mid] (LTApiDefs.v) for such a call, with the bounds of [api_deflate_wide]. *)
Definition MidW (W : dstate -> Prop) (HI : hdr_inv) (dict : list Z) (wrap : Z) (D O : list Z)
    (inb : list Z) (nin aout tin tout flush : Z) (s : dstate) (z : strm) : Prop :=
  zrunw inb nin aout tin tout z /\ 0 <= nin /\ Zlength D + (Zlength inb - nin) <= 1048576 /\
  aout <= 4294967295 /\ Zlength O + aout <= 8589934592 /\
  Iapi W HI dict wrap (D ++ sublist nin (z_next_in z) inb) (O ++ z_out z) (fin_of flush inb z) s
       (z_total_in z) (z_total_out z) (z_adler z).

(** ** The bounds [MidW] gives *)

(** The output space and total_out within the bounds of [zwide] / [hdr_pre_wide]. *)
Lemma midw_out : forall W HI dict wrap D O inb nin aout tin tout flush s z,
  MidW W HI dict wrap D O inb nin aout tin tout flush s z ->
  0 <= z_avail_out z <= 4294967295 /\ 0 <= z_total_out z <= 1099511627776.
Proof.
  intros W HI dict wrap D O inb nin aout tin tout flush s z
    ((_ & _ & _ & _ & Hao & Hzo & _ & _) & _ & _ & Ha & Ho & IA).
  destruct IA as (_ & _ & _ & _ & _ & _ & _ & _ & Htout & _).
  rewrite Zlength_app in Htout.
  pose proof (Zlength_nonneg O). pose proof (Zlength_nonneg (z_out z)). lia.
Qed.

(** The running stream satisfies [zwide] (input bytes given). *)
Lemma midw_zwide : forall W HI dict wrap D O inb nin aout tin tout flush s z,
  MidW W HI dict wrap D O inb nin aout tin tout flush s z -> bytes inb -> zwide z.
Proof.
  intros W HI dict wrap D O inb nin aout tin tout flush s z M Hb.
  destruct (midw_out _ _ _ _ _ _ _ _ _ _ _ _ _ _ M) as [Hao Hto].
  destruct M as ((Hin & Hn & Hai & Hti & _) & Hn0 & Hsz & _ & _ & IA).
  destruct IA as (_ & _ & _ & _ & _ & Hld & _ & _ & _ & _ & _ & Htin & _).
  rewrite Zlength_app, Zlength_sublist in Htin by lia.
  pose proof (Zlength_nonneg D). pose proof (Zlength_nonneg dict).
  unfold zwide. rewrite Hin. split; [exact Hb|]. lia.
Qed.

(** ** flush_pending with up to 2^32 - 1 bytes of output space *)

(** [LTApiOut.flush_pending_ok] with avail_out below 2^32 (the proof only needs total_out + avail_out far from
    2^64). *)
Lemma flush_pending_wide : forall s z,
  outok s -> d_bi_valid s <= 7 -> 0 <= z_avail_out z <= 4294967295 -> 0 <= z_total_out z <= 1099511627776 ->
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
