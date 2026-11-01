(* One deflate() call on the streams of RTK7Defs: the invariant inside a call and the facts every stage uses.

   RTDLTApiDefs.Mid (with RTDLTApiDefs.zrun) is the invariant inside a call for the deflate laws' limits.  Here:
   - [zrun7]: the running stream of a call offered the object [inb] and [aout] bytes of output space; total_in
     moves modulo 2^64 (the model adds with u64);
   - [Mid7]: [Iapi7] of the data consumed and the output produced so far, for an input object and an output
     space of at most 2^32 - 1 bytes and data / output of at most 2^64 - 1 bytes in all;
   - [stuck7]: FINISH_STATE with input left after Z_FINISH, where the defect of deflate_stored leads (RTK7Defs);
   - [flush_pending_ok7]: RTDLTApiOut.flush_pending_ok for any output space of a uInt;
   - [mid7_zin_ok7], [mid7_start], [Iapi7_bad_state]: the stream of a call is a [zin_ok7] stream, the start of a
     call, deflateStateCheck. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTK7Defs.
Require Export Zlib.proof.roundtrip.RTDDgDefs.
Require Import Zlib.proof.roundtrip.RTDLTCMisc.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** Inside a call *)

(* RTDLTApiDefs.zrun with total_in modulo 2^64 *)
Definition zrun7 (inb : list Z) (aout tin tout : Z) (z : strm) : Prop :=
  z_in z = inb /\ 0 <= z_next_in z <= Zlength inb /\ z_avail_in z = Zlength inb - z_next_in z /\
  z_total_in z = u64 (tin + z_next_in z) /\
  0 <= z_avail_out z /\ Zlength (z_out z) = aout - z_avail_out z /\ z_total_out z = tout + Zlength (z_out z) /\
  bytes (z_out z).

(* RTDLTApiDefs.Mid for Iapi7 and the sizes of the C types *)
Definition Mid7 (W : dstate -> Prop) (HI : hdr_inv) (dict : list Z) (wrap : Z) (D O : list Z)
    (inb : list Z) (aout tin tout flush : Z) (s : dstate) (z : strm) : Prop :=
  zrun7 inb aout tin tout z /\ Zlength inb <= 4294967295 /\ Zlength D + Zlength inb <= 18446744073709551615 /\
  aout <= 4294967295 /\ Zlength O + aout <= 18446744073709551615 /\
  Iapi7 W HI dict wrap (D ++ sublist 0 (z_next_in z) inb) (O ++ z_out z) (fin_of flush inb z) s
        (z_total_in z) (z_total_out z) (z_adler z).

(* the stream left in FINISH_STATE with input after Z_FINISH (deflate_stored defect, RTK7Defs.stored_cut) *)
Definition stuck7 (flush : Z) (s : dstate) (z : strm) : Prop :=
  flush = Z_FINISH /\ d_status s = FINISH_STATE /\ 0 < z_avail_in z.

(* the functional compressors on these streams, whichever the state selects *)
Definition compf_fspec7 : Prop := forall f, comp_fspec7 f c_compress_func.

(* deflate_stored does not change w_bits (a fact of the model, for the case of its defect where comp_fspec7 and
   cpost7 say nothing of the state) *)
Definition stored_wbits_stmt : Prop :=
  forall s z flush s' z' bs, c_deflate_stored s z flush = Some (s', z', bs) -> d_w_bits s' = d_w_bits s.

(** ** Facts *)

Lemma compf7_of :
  comp_fspec7 0 c_deflate_stored -> comp_fspec7 1 c_deflate_fast -> comp_fspec7 2 c_deflate_slow ->
  comp_fspec7 3 c_deflate_huff -> comp_fspec7 4 c_deflate_rle -> compf_fspec7.
Proof.
  intros H0 H1 H2 H3 H4 f s z flush s' z' bs dict D BS syms p HW Ho Hq Hfl Hz Hw Ha Hfn Hdi HD HK Hp Hp8 R.
  rewrite (compress_dispatch s z flush (W3_prm s HW)) in R.
  destruct (Z.eqb_spec (fn_of s) 0) as [E0|N0]; [eapply H0; eauto|].
  destruct (Z.eqb_spec (fn_of s) 1) as [E1|N1]; [eapply H1; eauto|].
  destruct (Z.eqb_spec (fn_of s) 2) as [E2|N2]; [eapply H2; eauto|].
  destruct (Z.eqb_spec (fn_of s) 3) as [E3|N3]; [eapply H3; eauto|].
  assert (E4 : fn_of s = 4).
  { destruct (W3_prm s HW) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hl & _).
    unfold fn_of in *.
    destruct (Z.eqb_spec (d_level s) 0); [congruence|].
    destruct (d_strategy s =? Z_HUFFMAN_ONLY); [congruence|].
    destruct (d_strategy s =? Z_RLE); [reflexivity|].
    exfalso. assert (Hc : forall l, 1 <= l <= 9 -> cfg_f l = 1 \/ cfg_f l = 2).
    { intros l Hl'.
      assert (l = 1 \/ l = 2 \/ l = 3 \/ l = 4 \/ l = 5 \/ l = 6 \/ l = 7 \/ l = 8 \/ l = 9) by lia.
      repeat match goal with H : _ \/ _ |- _ => destruct H end; subst l; vm_compute; auto. }
    destruct (Hc (d_level s) ltac:(lia)); congruence. }
  eapply H4; eauto.
Qed.

(* flush_pending on any output space of a uInt whose total_out does not wrap *)
Lemma flush_pending_ok7 : forall s z,
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

(* the stream inside a call is a stream of the C types *)
Lemma mid7_zin_ok7 : forall W HI dict wrap D O inb aout tin tout flush s z,
  Mid7 W HI dict wrap D O inb aout tin tout flush s z -> bytes inb -> zin_ok7 z.
Proof.
  intros W HI dict wrap D O inb aout tin tout flush s z
    ((Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8) & B1 & B2 & B3 & B4 & I) Hb.
  destruct I as (_ & _ & _ & _ & _ & _ & _ & _ & Ht & _).
  rewrite Zlength_app in Ht.
  pose proof (Zlength_nonneg O). pose proof (Zlength_nonneg (z_out z)).
  unfold zin_ok7. rewrite Z1. split; [exact Hb|].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [rewrite Z4; unfold u64; pose proof (Z.mod_pos_bound (tin + z_next_in z) 18446744073709551616); lia|]. lia.
Qed.

Lemma mid7_zout_ok7 : forall W HI dict wrap D O inb aout tin tout flush s z,
  Mid7 W HI dict wrap D O inb aout tin tout flush s z -> zout_ok7 z.
Proof.
  intros W HI dict wrap D O inb aout tin tout flush s z
    ((Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8) & B1 & B2 & B3 & B4 & I).
  destruct I as (_ & _ & _ & _ & _ & _ & _ & _ & Ht & _).
  rewrite Zlength_app in Ht.
  pose proof (Zlength_nonneg O). pose proof (Zlength_nonneg (z_out z)).
  unfold zout_ok7. lia.
Qed.

(* the start of a call *)
Lemma mid7_start : forall W HI dict wrap D O fin s tin tout adler inb aout flush msg,
  Iapi7 W HI dict wrap D O fin s tin tout adler -> bytes inb -> Zlength inb <= 4294967295 ->
  Zlength D + Zlength inb <= 18446744073709551615 ->
  0 <= aout <= 4294967295 -> Zlength O + aout <= 18446744073709551615 ->
  (forall R, fin = Some R -> flush = Z_FINISH /\ inb = R) ->
  Mid7 W HI dict wrap D O inb aout tin tout flush s (zcall inb 0 (Zlength inb) tin aout tout adler msg).
Proof.
  intros W HI dict wrap D O fin s tin tout adler inb aout flush msg HI' Hb Hl Hd Ha Ho Hfin.
  destruct HI' as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16).
  destruct A13 as (k & Hk & Htin).
  unfold Mid7, zrun7, zcall; cbn [z_in z_next_in z_avail_in z_total_in z_avail_out z_out z_total_out z_adler].
  split.
  { split; [reflexivity|]. split; [pose proof (Zlength_nonneg inb); lia|]. split; [lia|].
    split; [rewrite Z.add_0_r, Htin; unfold u64; rewrite Zmod_mod; reflexivity|].
    split; [lia|]. split; [rewrite Zlength_nil; lia|]. split; [rewrite Zlength_nil; lia|].
    constructor. }
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  replace (sublist 0 0 inb) with (@nil Z) by (unfold sublist; reflexivity).
  rewrite !app_nil_r.
  unfold Iapi7. do 12 (split; [assumption|]). split; [exists k; split; [exact Hk|exact Htin]|].
  split; [|exact (conj A15 A16)].
  intros Hst. destruct (Hfin _ (A14 Hst)) as [-> ->]. reflexivity.
Qed.

(* a stream satisfying Iapi7 passes deflateStateCheck *)
Lemma Iapi7_bad_state : forall W HI dict wrap D O fin s tin tout adler,
    hdr_facts7 HI -> Iapi7 W HI dict wrap D O fin s tin tout adler -> bad_state s = false.
Proof.
  intros W HI dict wrap D O fin s tin tout adler HF HI'.
  destruct HI' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hph).
  assert (Hst : d_status s = INIT_STATE \/ d_status s = GZIP_STATE \/ d_status s = EXTRA_STATE \/
                d_status s = NAME_STATE \/ d_status s = COMMENT_STATE \/ d_status s = HCRC_STATE \/
                d_status s = BUSY_STATE \/ d_status s = FINISH_STATE).
  { destruct Hph as [P0 | (_ & [P1 | [P2 | P3]])].
    - destruct P0 as [[[-> _] | [-> _]] _]; tauto.
    - destruct P1 as (_ & _ & _ & _ & _ & H & k & Hh & _).
      destruct (hf7_status HI HF s adler H k Hh) as (_ & _ & Hs & _). tauto.
    - destruct P2 as [-> _]. tauto.
    - destruct P3 as [-> _]. tauto. }
  unfold bad_state, c_deflateStateCheck, status_ok.
  destruct Hst as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; rewrite E; reflexivity.
Qed.

(* Mid7 is never stuck: in FINISH_STATE Iapi7 says that no input is left *)
Lemma mid7_not_stuck : forall W HI dict wrap D O inb aout tin tout flush s z,
  Mid7 W HI dict wrap D O inb aout tin tout flush s z -> ~ stuck7 flush s z.
Proof.
  intros W HI dict wrap D O inb aout tin tout flush s z
    ((Z1 & Z2 & Z3 & _) & _ & _ & _ & _ & I) (Hf & Hs & Ha).
  destruct I as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfin & _).
  specialize (Hfin Hs). unfold fin_of in Hfin. rewrite Hf in Hfin. cbn in Hfin.
  injection Hfin as Hn.
  assert (Hl : Zlength (sublist (z_next_in z) (Zlength inb) inb) = 0) by (rewrite Hn; reflexivity).
  rewrite Zlength_sublist in Hl by lia. lia.
Qed.
