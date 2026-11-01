(* Law rt_session, sessions with a gzip header: the layout of deflate's finished gzip stream with a header
   (RTFinal.dfinal) in the input object src = O followed by any bytes: the header's ghost at the start of src and
   the decode context of src (SGzDefs.sgz_lay_ok). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.roundtrip.RTK7.
Require Import Zlib.proof.harness.rt_session.SGzDefs.
Require Import Zlib.proof.harness.inflate_header.IHTKitLay.
Require Import Zlib.proof.harness.rt_gzip_header.G2ILay.
Require Zlib.proof.roundtrip.RTIGzPassCtx.
Import ListNotations.
Local Open Scope Z_scope.

(* a session with a gzip header: deflateInit2's windowBits is 16 + wb with wb in 9..15 (windowBits 8 is accepted only
   with the zlib wrapper), deflate's window is wb and inflateInit2 is called with the same windowBits *)
Lemma sgz_wbits c : (exists level mem strategy, rparams_ok level 8 (sc_wbits c) mem strategy = true) ->
  sc_wrap c = 2 ->
  rwbe (sc_wbits c) = sc_wbits c - 16 /\ rts_iw (sc_wbits c) = sc_wbits c /\ 25 <= sc_wbits c <= 31.
Proof.
  intros (lv & mem & st & RP) W2. unfold sc_wrap in W2. unfold rparams_ok in RP. unfold rwbe, rts_iw.
  unfold rwb_of, rwrap_of in *. set (w := sc_wbits c) in *.
  destruct (Z.ltb_spec w 0); [discriminate|]. rewrite Z.gtb_ltb in *.
  destruct (Z.ltb_spec 15 w); [|discriminate].
  repeat rewrite andb_true_iff in RP. rewrite orb_true_iff in RP.
  destruct RP as ((((((((((_ & _) & _) & _) & R1) & R2) & _) & _) & _) & _) & R3).
  apply Z.leb_le in R1. apply Z.leb_le in R2.
  assert (w - 16 <> 8).
  { destruct R3 as [R3|R3]; [rewrite negb_true_iff in R3; apply Z.eqb_neq in R3; exact R3 | discriminate R3]. }
  rewrite (proj2 (Z.eqb_neq (w - 16) 8)) by exact H1. rewrite (proj2 (Z.eqb_neq w 8)) by lia.
  split; [reflexivity|]. split; [reflexivity|]. lia.
Qed.

Lemma sgz_lay : sgz_lay_stmt.
Proof.
  intros c D O src gh SC SR Egh.
  destruct SC as (RP & DF & _ & GW & HB & DL).
  assert (W2: sc_wrap c = 2) by (apply GW; rewrite Egh; discriminate).
  destruct (HB gh Egh) as (HOK & BUF).
  assert (HOK2: g2_hdr_ok gh) by exact HOK.
  destruct (sgz_wbits c RP W2) as (WE & WI & WR).
  rewrite W2, Egh, WE in DF.
  destruct DF as (Wd & bs & Wf & Dd & Dn & xfl & X & EO).
  rewrite Dn in Wf, Dd.
  set (wb := sc_wbits c - 16) in *.
  exists wb, xfl, bs.
  change (RF.fhdr_of (Some gh) xfl) with (g2_H gh xfl) in EO.
  destruct (g2_H_ok gh xfl HOK2 X) as (GZ & LN & LC & _).
  assert (XL: forall x, F.gz_extra (g2_H gh xfl) = Some x -> Zlength x <= 65535).
  { destruct GZ as (_ & _ & _ & GE & _). intros x Ex. rewrite Ex in GE. exact (proj1 GE). }
  destruct SR as (SL1 & SO & SB).
  set (H := g2_H gh xfl) in *.
  set (rest := F.deflate_bytes bs ++ F.le_bytes (Zlib.proof.crc32.Model.ref_crc32 0 (F.data [] bs)) 4 ++
               F.le_bytes (Zlength (F.data [] bs) mod 2 ^ 32) 4).
  assert (OR: O = F.gz_bytes H ++ rest) by (rewrite EO; reflexivity).
  assert (SRC: src = O ++ sublist (Zlength O) (Zlength src) src).
  { rewrite <- SO at 1. rewrite <- sublist_split by (pose proof (Zlength_nonneg O); lia).
    rewrite sublist_same by reflexivity. reflexivity. }
  assert (BY: is_bytes src).
  { unfold is_bytes. change Byte.max_unsigned with 255. eapply Forall_impl; [|exact SB]. cbv beta. intros; lia. }
  assert (NH: ih_nh (g2_gf H) = Zlength (F.gz_bytes H)).
  { rewrite (g2_hdr_bytes H XL), Zlength_app, ihl2_hdr_eq, !Zlength_app.
    pose proof (ihl2_lens (g2_gf H)) as (LA & LX & LN' & LC' & LH & _). lia. }
  assert (SL: Zlib.proof.rfc1951.DecodeDefs.slen (g2_G gh xfl wb bs src) = Zlength O).
  { unfold Zlib.proof.rfc1951.DecodeDefs.slen, g2_G.
    cbn [Zlib.proof.rfc1951.DecodeDefs.dc_w Zlib.proof.rfc1951.DecodeDefs.dc_hist Zlib.proof.rfc1951.DecodeDefs.dc_bs].
    fold H. rewrite <- EO. reflexivity. }
  unfold sgz_lay_ok. rewrite !g2_g_gf. fold H.
  split; [exact Egh|]. split; [rewrite WI; unfold wb; lia|]. split; [unfold wb; lia|].
  split; [exact HOK2|]. split; [exact BUF|]. split; [exact X|].
  split; [exact (g2_gf_ok H GZ LN LC)|].
  split.
  { rewrite SRC, OR, <- app_assoc. apply g2_lay; [exact GZ | exact LN | exact LC |].
    rewrite app_assoc, <- OR, <- SRC. exact BY. }
  split; [exact NH|].
  split; [rewrite NH, OR, Zlength_app; pose proof (Zlength_nonneg rest); lia|].
  split; [|split; [|exact SL]].
  - unfold RTIGW.rtigw_ok. rewrite SL. unfold g2_G.
    cbn [Zlib.proof.rfc1951.DecodeDefs.dc_w Zlib.proof.rfc1951.DecodeDefs.dc_wb Zlib.proof.rfc1951.DecodeDefs.dc_hist
         Zlib.proof.rfc1951.DecodeDefs.dc_bs Zlib.proof.rfc1951.DecodeDefs.dc_iw Zlib.proof.rfc1951.DecodeDefs.dc_src].
    fold H. rewrite <- EO.
    split; [|split; [|split; [|split; [|split; [|split]]]]].
    + unfold F.stream_ok, F.wrapper_ok. split; [lia|]. split; [split; [exact GZ | reflexivity]|].
      split; [exact I | exact Wf].
    + unfold Zlib.proof.rfc1951.DecodeDefs.accepts. cbn. left. reflexivity.
    + intros ? ? ? Ew. discriminate Ew.
    + lia.
    + unfold Zlib.proof.harness.rt_stream.UDFacts.max_size in SL1. lia.
    + exact BY.
    + exact SO.
  - unfold Zlib.proof.rfc1951.DecodeDefs.full, g2_G.
    cbn [Zlib.proof.rfc1951.DecodeDefs.dc_hist Zlib.proof.rfc1951.DecodeDefs.dc_bs].
    rewrite <- Dd. unfold F.data. rewrite Zlength_nil, sublist_same by reflexivity. reflexivity.
Qed.
