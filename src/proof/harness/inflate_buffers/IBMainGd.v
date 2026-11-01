(* Law inflate_buffers, main: the branch inflateGetDictionary (210 <= op < 220): dl, the second call into ob, bytes_same, bytes_copy into osnap. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.inflate_common.HarnessLib.
Require Import Zlib.proof.harness.inflate_buffers.IBLawCS Zlib.proof.harness.inflate_buffers.IBGlobals
               Zlib.proof.harness.inflate_buffers.IBFacts Zlib.proof.harness.inflate_buffers.IBMainKit.
Require Import Zlib.harness.x_inflate_buffers.code.
Require Import Zlib.proof.crc32.Spec.

(* an array of bytes cut at n1 *)
Lemma gd_split_bytes sh n n1 l p: 0 <= n1 <= n -> Zlength l = n -> field_compatible (tarray tuchar n) [] p ->
  data_at sh (tarray tuchar n) (bytes_rep l) p =
  (data_at sh (tarray tuchar n1) (bytes_rep (sublist 0 n1 l)) p *
   data_at sh (tarray tuchar (n - n1)) (bytes_rep (sublist n1 n l)) (offset_val n1 p))%logic.
Proof.
  intros R Hl FC. unfold tarray.
  rewrite (split2_data_at_Tarray_tuchar sh n n1) by (unfold bytes_rep; rewrite ?Zlength_map; lia).
  rewrite field_address0_offset by auto with field_compatible.
  unfold bytes_rep; rewrite !sublist_map. simpl. rewrite Z.mul_1_l. reflexivity.
Qed.

(* the slice [lo, n) of a byte array *)
Lemma gd_cbuf_slice sh p lo n l: readable_share sh -> 0 <= lo <= n -> Zlength l = n -> is_bytes l ->
  cbuf_ok false (offset_val lo p) sh p lo n (n - lo) (bytes_rep l) (sublist lo n l).
Proof.
  intros R Hlo Hl Hb. unfold cbuf_ok. repeat split; auto; try lia.
  - rewrite Zlength_sublist; lia.
  - apply Forall_sublist; auto.
  - replace (lo + (n - lo)) with n by lia. unfold bytes_rep; rewrite sublist_map; reflexivity.
Qed.

(* ob after the second call: the dictionary, then the old bytes *)
Lemma gd_obl_facts (dict bs: list Z) wh aout: Zlength dict = wh -> 0 <= wh <= aout -> Zlength bs = aout ->
  bytes_ok dict -> is_bytes bs ->
  Zlength (dict ++ sublist wh aout bs) = aout /\ is_bytes (dict ++ sublist wh aout bs) /\
  sublist 0 wh (dict ++ sublist wh aout bs) = dict /\
  sublist wh aout (dict ++ sublist wh aout bs) = sublist wh aout bs.
Proof.
  intros Hd Hw Hb Bd Bb.
  assert (Ls: Zlength (sublist wh aout bs) = aout - wh) by (rewrite Zlength_sublist; lia).
  split3; [ | | split].
  - rewrite Zlength_app, Ls; lia.
  - apply Forall_app; split; [exact Bd | apply Forall_sublist; auto].
  - rewrite sublist_app1 by lia. rewrite sublist_same by lia. reflexivity.
  - rewrite sublist_app2 by lia. rewrite Hd, Z.sub_diag. rewrite sublist_same by lia. reflexivity.
Qed.

Lemma seg_gd_ok {Espec: OracleKind} gv vs vosn vdl srcp src pos aout flush arg op innull outnull stop ain ibp obp q bs z L
    Fr (Post: ret_assert) :
  ops_hyps srcp src pos aout flush arg op innull outnull stop ain ibp obp q bs L -> 210 <= op < 220 ->
  semax Delta_m (ops_pre gv vs vosn vdl srcp src pos aout flush arg op innull outnull stop ain ibp obp q bs z L Fr)
    seg_gd
    (overridePost (ops_post gv vs vosn vdl srcp src pos aout flush arg op innull outnull stop ain ibp obp q z Fr) Post).
Proof.
  intros H Hop.
  destruct H as (FI & HI & Hpos & Hain & Hpa & Hsrc & Hsb & Haout & Hbsl & Hbsb & Hfl & Harg & Hopr & Hin & Hout & Hst & Psrc & Pib & Pob & Pq).
  unfold ops_pre, ops_locals.
  assert_PROP (isptr vs) as Pvs by entailer!.
  unfold seg_gd, Delta_m, Gmain_k. simplify_func_tycontext. abbreviate_semax.
  rewrite ib_nin_ge, ib_nout_ge by lia.
  set (zc := ib_zcall z false false ibp obp ain aout).
  assert_PROP (isptr vdl) as Pdl by entailer!.
  forward.
  forward_call (gv, Tsh, vs, zc, Some L, DNull, vdl).
  { rewrite ib_istream_opt by auto. unfold dict_rep, len_rep.
    destruct (eq_dec vdl nullval) as [E|_]; [subst; contradiction|].
    rewrite uint_inflate_cs_. cancel. }
  { rewrite ib_is_live by auto. exact I. }
  rewrite ib_istream_opt, ib_is_live by auto.
  unfold dict_rep, len_rep.
  destruct (eq_dec vdl nullval) as [E|_]; [subst; contradiction|].
  rewrite uint_inflate_cs.
  assert_PROP (live_ok L /\ zf_ok zc) as LZ by (rewrite ib_istream_unfold; entailer!).
  destruct LZ as [LOK ZOK].
  destruct (fi_getdict FI L) as (Hwh & Hdl & Hdb); auto.
  set (dict := dict_bytes (l_s L)) in *.
  set (wh := i_whave (l_s L)) in *.
  forward_call (Int.repr 1).
  forward.
  forward_call (Int.repr 1).
  { entailer!. unfold Int.ltu. rewrite !Int.unsigned_repr by rep_lia. destruct zlt; [lia|reflexivity]. }
  forward.
  forward_if.
  { assert (Hle: wh <= aout) by lia.
    rewrite <- (bytes_inflate_cs Ews aout _ obp).
    forward_call (gv, Tsh, vs, zc, Some L, DBuf Ews obp 0 aout (bytes_rep bs), nullval).
    { rewrite ib_istream_opt by auto. cancel. }
    { rewrite ib_is_live by auto. simpl dict_ok. fold wh.
      split; [auto with typeclass_instances|].
      repeat split; auto; try rep_lia. unfold bytes_rep; rewrite Zlength_map; lia. }
    rewrite ib_istream_opt, ib_is_live by auto.
    unfold dict_rep, len_rep. rewrite if_true by auto. fold dict.
    rewrite Hdl, sublist_nil, app_nil_l, Z.add_0_l.
    rewrite (bytes_inflate_cs Ews aout _ obp).
    forward_call (Int.repr 1).
    forward. forward. forward. forward.
    set (obl := dict ++ sublist wh aout bs).
    destruct (gd_obl_facts dict bs wh aout) as (Lobl & Bobl & Sobl0 & Sobl1); auto; try lia.
    replace (byte_vals dict ++ sublist wh aout (bytes_rep bs)) with (bytes_rep obl)
      by (unfold obl, bytes_rep, byte_vals; rewrite map_app, sublist_map; reflexivity).
    assert_PROP (field_compatible (tarray tuchar aout) [] q) as FCq by entailer!.
    rewrite (gd_split_bytes Ews aout wh bs q) by (first [lia | auto]).
    rewrite <- (bytes_adler_cs Ews aout _ obp), <- (bytes_adler_cs Ews (aout - wh) _ (offset_val wh q)).
    Intros.
    forward_call (offset_val wh obp, Ews, obp, wh, aout, bytes_rep obl, sublist wh aout bs,
                  offset_val wh q, Ews, offset_val wh q, 0, aout - wh, bytes_rep (sublist wh aout bs),
                  sublist wh aout bs, aout - wh).
    { split.
      - rewrite <- Sobl1. apply gd_cbuf_slice; auto; lia.
      - assert (Ls: Zlength (sublist wh aout bs) = aout - wh) by (rewrite Zlength_sublist; lia).
        rewrite <- Ls. apply cbuf_ok_whole; auto. apply Forall_sublist; auto. }
    rewrite if_true by reflexivity.
    forward_call (Int.repr 1).
    forward. forward.
    rewrite <- (bytes_adler_cs Ews wh _ q).
    sep_apply (@data_at_data_at_ Zlib.units.Adler32.CS Ews (tarray tuchar wh) (bytes_rep (sublist 0 wh bs)) q).
    forward_call (q, Ews, obp, Ews, obp, 0, aout, bytes_rep obl, wh, dict).
    { unfold cbuf_ok. destruct obp; try contradiction. simpl. rewrite Ptrofs.add_zero.
      repeat split; auto; try lia.
      fold obl in Sobl0. rewrite Z.add_0_l. unfold bytes_rep; rewrite sublist_map, Sobl0. reflexivity. }
    rewrite (bytes_adler_cs Ews wh _ q), (bytes_adler_cs Ews aout _ obp),
      (bytes_adler_cs Ews (aout - wh) _ (offset_val wh q)).
    fold obl in Sobl0, Sobl1, Lobl, Bobl.
    replace (bytes_rep dict) with (bytes_rep (sublist 0 wh obl)) by (rewrite Sobl0; reflexivity).
    replace (bytes_rep (sublist wh aout bs)) with (bytes_rep (sublist wh aout obl)) by (rewrite Sobl1; reflexivity).
    gather_SEP (data_at Ews (tarray tuchar wh) _ q) (data_at Ews (tarray tuchar (aout - wh)) _ (offset_val wh q)).
    rewrite <- (gd_split_bytes Ews aout wh obl q) by (first [lia | auto]).
    destruct Post as [Pn Pb Pc Pr]; unfold overridePost; simpl RA_normal.
    unfold ops_post, ops_post_at, ops_locals.
    Exists 0 0 zc L obl obl.
    rewrite ib_nin_ge, ib_nout_ge by lia.
    entailer!.
    apply ops_out_same; auto; rep_lia. }
  forward.
  destruct Post as [Pn Pb Pc Pr]; unfold overridePost; simpl RA_normal.
  unfold ops_post, ops_post_at, ops_locals.
  Exists 0 0 zc L bs bs.
  rewrite ib_nin_ge, ib_nout_ge by lia.
  entailer!.
  apply ops_out_same; auto; rep_lia.
Qed.
