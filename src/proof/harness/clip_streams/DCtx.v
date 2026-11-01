(* The decode context of the stream deflate wrote (IDecode.dctx_stmt). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.harness.clip_streams.DFacts Zlib.proof.harness.clip_streams.IFacts
  Zlib.proof.harness.clip_streams.IDecode.
Require Zlib.proof.roundtrip.RTIPlain.
Import ListNotations.
Local Open Scope Z_scope.

(* the windowBits deflateInit2_ accepts, per wrapper: raw -9..-15, zlib 8..15 (8 written as 9), gzip 25..31 *)
Lemma dctx_wbits wbits : wbits_acc wbits = true ->
  (-15 <= wbits <= -9 /\ rwrap_of wbits = 0 /\ rwbe wbits = - wbits /\ iwb wbits = wbits) \/
  (8 <= wbits <= 15 /\ rwrap_of wbits = 1 /\ rwbe wbits = iwb wbits /\ trl_of wbits = 4) \/
  (25 <= wbits <= 31 /\ rwrap_of wbits = 2 /\ rwbe wbits = wbits - 16 /\ iwb wbits = wbits /\ trl_of wbits = 8).
Proof.
  unfold wbits_acc, rwbe, rwb_of, rwrap_of, iwb, trl_of. intros H.
  destruct (Z.ltb_spec wbits 0); [|destruct (Z.gtb_spec wbits 15)]; destruct (Z.ltb_spec wbits (-15));
    cbn [negb andb] in H; try discriminate; rewrite ?andb_true_iff, ?orb_true_iff, ?Z.leb_le, ?negb_true_iff in H;
    destruct (Z.eqb_spec wbits 8); destruct (Z.eqb_spec (- wbits) 8); destruct (Z.eqb_spec (wbits - 16) 8);
    rewrite ?Z.eqb_eq, ?Z.eqb_neq in H; lia.
Qed.

(* a well-formed stream without history, the bytes O, followed by anything in src, is a context of any length *)
Lemma dctx_of w wb bs iw D O src :
  stream_ok w wb [] bs -> accepts (DCtx w wb [] bs iw src) -> (forall h, w = WGzip h -> gz_simple h) ->
  (forall a b c, w = WZlib a b c -> c = None) -> data [] bs = D -> stream_bytes w [] bs = O ->
  Zlength O <= Zlength src <= 2 ^ 64 - 1 -> sublist 0 (Zlength O) src = O -> bytes_ok src ->
  dctx_ok7 (DCtx w wb [] bs iw src) /\ slen (DCtx w wb [] bs iw src) = Zlength O /\
  full (DCtx w wb [] bs iw src) = D.
Proof.
  intros Hok Hacc Hgz Hz Hd Hs Hl Hsub Hbo.
  assert (Hsl: slen (DCtx w wb [] bs iw src) = Zlength O) by (unfold slen; cbn; rewrite Hs; reflexivity).
  split; [|split; [exact Hsl|]].
  - unfold dctx_ok7. rewrite Hsl. cbn [dc_w dc_wb dc_hist dc_bs dc_src]. rewrite Hs.
    split; [exact Hok|]. split; [exact Hacc|]. split; [exact Hgz|].
    split; [intros a b c E; left; exact (Hz a b c E)|]. repeat split; tauto || lia.
  - unfold full. cbn [dc_hist dc_bs]. rewrite Zlib.proof.roundtrip.RTIPlain.rtip_expand_data, Hd. reflexivity.
Qed.

(* per wrapper: raw (the deflate bytes), zlib (deflate's header is Format's: FCHECK = 31 never happens without a
   dictionary), gzip (zlib's default header) *)
Lemma clip_dctx : dctx_stmt.
Proof.
  intros wbits D O src [Hacc Hfin] Hl Hsub Hbo.
  destruct Hfin as (Hwb & bs & Hwf & Hdat & Hsh).
  destruct (dctx_wbits wbits Hacc) as [(Hr & Ew & Eb & Ei) | [(Hr & Ew & Eb & Et) | (Hr & Ew & Eb & Ei & Et)]];
    rewrite Ew in Hsh.
  - destruct (dctx_of WRaw (rwbe wbits) bs (iwb wbits) D O src) as (G1 & G2 & G3);
      [split; [lia|]; split; [exact I|]; split; [exact I|exact Hwf]
      |unfold accepts; cbn; lia|intros h E; discriminate|intros ? ? ? E; discriminate
      |exact Hdat|symmetry; exact Hsh|lia|exact Hsub|exact Hbo|].
    exists (DCtx WRaw (rwbe wbits) [] bs (iwb wbits) src).
    split; [exact G1|]. split; [reflexivity|]. split; [exact G2|]. split; [exact G3|].
    split; [reflexivity|]. split; [reflexivity|]. split; [intros ? ? ? E; discriminate|].
    cbn. rewrite (proj2 (Z.ltb_lt wbits 0)) by lia. reflexivity.
  - destruct Hsh as (_ & flg & Hflg & HO). cbn [negb] in Hflg.
    pose proof Hflg as (Hf1 & Hf2 & Hf3).
    destruct (dctx_of (WZlib (rwbe wbits) (flg / 64) None) (rwbe wbits) bs (iwb wbits) D O src) as (G1 & G2 & G3).
    + split; [lia|]. split; [|split; [reflexivity|exact Hwf]].
      split; [lia|]. split; [|reflexivity]. split; [apply Z.div_pos; lia|].
      apply Z.lt_succ_r. apply Z.div_lt_upper_bound; lia.
    + unfold accepts; cbn [dc_w dc_iw dc_wb]. left; symmetry; exact Eb.
    + intros h E; discriminate.
    + intros ? ? ? E; injection E as _ _ <-; reflexivity.
    + exact Hdat.
    + rewrite HO. cbn [stream_bytes]. rewrite <- (Zlib.proof.roundtrip.RTIPlain.rtip_zhdr (rwbe wbits) flg Hwb Hflg).
      rewrite Hdat. reflexivity.
    + lia.
    + exact Hsub.
    + exact Hbo.
    + exists (DCtx (WZlib (rwbe wbits) (flg / 64) None) (rwbe wbits) [] bs (iwb wbits) src).
      split; [exact G1|]. split; [reflexivity|]. split; [exact G2|]. split; [exact G3|].
      split; [reflexivity|]. split; [reflexivity|]. split; [intros ? ? ? E; injection E as _ _ <-; reflexivity|].
      cbn. rewrite (proj2 (Z.ltb_ge wbits 0)) by lia. rewrite Et. reflexivity.
  - destruct Hsh as (_ & xfl & Hx & HO).
    destruct (dctx_of (WGzip (RTFinal.fhdr_of None xfl)) (rwbe wbits) bs (iwb wbits) D O src) as (G1 & G2 & G3).
    + split; [lia|]. split; [|split; [exact I|exact Hwf]].
      split; [|reflexivity]. unfold gz_ok, byte_ok; cbn. repeat split; lia.
    + unfold accepts; cbn [dc_w dc_iw dc_wb]. left; lia.
    + intros h E; injection E as <-. repeat split.
    + intros ? ? ? E; discriminate.
    + exact Hdat.
    + symmetry; exact HO.
    + lia.
    + exact Hsub.
    + exact Hbo.
    + exists (DCtx (WGzip (RTFinal.fhdr_of None xfl)) (rwbe wbits) [] bs (iwb wbits) src).
      split; [exact G1|]. split; [reflexivity|]. split; [exact G2|]. split; [exact G3|].
      split; [reflexivity|]. split; [reflexivity|]. split; [intros ? ? ? E; discriminate|].
      cbn. rewrite (proj2 (Z.ltb_ge wbits 0)) by lia. rewrite Et. reflexivity.
Qed.
