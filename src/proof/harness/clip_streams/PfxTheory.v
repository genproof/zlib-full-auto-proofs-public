(* rt_partial and rj_truncated: inflate() on a proper prefix of the stream (IFacts.pfx_facts), from the decode
   theory for calls of any size (Decode7) on the context of the stream (IDecode.dctx_stmt). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.harness.clip_streams.IFacts Zlib.proof.harness.clip_streams.IDecode.
Require Import Zlib.proof.roundtrip.RTIPlain.
Require Import Zlib.proof.uncompr.URunFrame.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* The bytes deflate wrote: bytes, at least one                                                    *)

Lemma pfx_pack_len bs : Zlength (Zlib.proof.rfc1951.Format.pack bs) = (Zlength bs + 7) / 8.
Proof.
  unfold Zlib.proof.rfc1951.Format.pack. rewrite Zlength_map, Zlength_correct, length_seq.
  apply Z2Nat.id. apply Z.div_pos; [pose proof (Zlength_nonneg bs); lia | lia].
Qed.

(* a non-empty list of blocks has a non-empty deflate stream (each block starts with its BFINAL bit) *)
Lemma pfx_deflate_len bs : bs <> [] -> 1 <= Zlength (Zlib.proof.rfc1951.Format.deflate_bytes bs).
Proof.
  intros NE. unfold Zlib.proof.rfc1951.Format.deflate_bytes. rewrite pfx_pack_len.
  unfold Zlib.proof.rfc1951.Format.deflate_bits.
  destruct bs as [|b r]; [congruence|]. cbn [Zlib.proof.rfc1951.Format.enc_blocks].
  set (e := Zlib.proof.rfc1951.Format.enc_block _ _ b).
  assert (1 <= Zlength e).
  { unfold e, Zlib.proof.rfc1951.Format.enc_block. rewrite Zlength_cons.
    match goal with |- context [Z.succ (Zlength ?l)] => pose proof (Zlength_nonneg l) end. lia. }
  rewrite !Zlength_app.
  match goal with |- context [Zlength e + Zlength ?l + Zlength ?l'] =>
    pose proof (Zlength_nonneg l); pose proof (Zlength_nonneg l') end.
  apply Z.div_le_lower_bound; lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The invariant of the call boundaries: a decode context of O, between calls at pos with out written *)

Definition pfx_inv : inv_t := fun wbits D O src pos out z L =>
  src = O /\ 0 <= pos <= Zlength O /\ (exists rest, D = out ++ rest) /\
  exists G, dctx_ok7 G /\ dc_src G = O /\ slen G = Zlength O /\ full G = D /\
    dinv G pos out (l_s L) (zf_tout z).

Lemma pfx_inv_ok : inv_ok pfx_inv.
Proof.
  intros wbits D O src pos out z L (-> & POS & PRE & G & _ & _ & _ & _ & _ & (_ & HD & _) & _ & _ & _).
  auto.
Qed.

(* the modes between calls are HEAD .. DONE *)
Lemma pfx_vmode G pos out s tout : dinv G pos out s tout -> vmode (i_mode s).
Proof.
  intros ((_ & AT) & _).
  unfold vmode.
  repeat match goal with H: _ \/ _ |- _ => destruct H as [H|H] end;
  repeat match goal with H: _ /\ _ |- _ => let E := fresh "E" in destruct H as [E _] end;
  repeat match goal with E: _ \/ _ |- _ => destruct E as [E|E] end; rewrite E; compute; split; discriminate.
Qed.

(* zlib's default gzip member (deflate without deflateSetHeader) *)
Lemma pfx_gz xfl bs D : (xfl = 0 \/ xfl = 2 \/ xfl = 4) ->
  bytes_ok (Zlib.proof.rfc1951.Format.stream_bytes
              (Zlib.proof.rfc1951.Format.WGzip (Zlib.proof.roundtrip.RTFinal.fhdr_of None xfl)) D bs) /\
  1 <= Zlength (Zlib.proof.rfc1951.Format.stream_bytes
              (Zlib.proof.rfc1951.Format.WGzip (Zlib.proof.roundtrip.RTFinal.fhdr_of None xfl)) D bs).
Proof.
  intros X. unfold Zlib.proof.rfc1951.Format.stream_bytes. cbv zeta.
  unfold Zlib.proof.roundtrip.RTFinal.fhdr_of, Zlib.proof.rfc1951.Format.gz_bytes; cbn [Zlib.proof.rfc1951.Format.gz_hcrc].
  unfold Zlib.proof.rfc1951.Format.gz_bytes0; cbn [Zlib.proof.rfc1951.Format.gz_extra
    Zlib.proof.rfc1951.Format.gz_name Zlib.proof.rfc1951.Format.gz_comment Zlib.proof.rfc1951.Format.gz_mtime
    Zlib.proof.rfc1951.Format.gz_xfl Zlib.proof.rfc1951.Format.gz_os].
  split.
  - unfold bytes_ok. rewrite !Forall_app.
    change compcert.lib.Integers.Byte.max_unsigned with 255.
    pose proof (rtip_le_ok 0 4) as L0. unfold bytes_ok in L0.
    change compcert.lib.Integers.Byte.max_unsigned with 255 in L0.
    pose proof (rtip_pack_ok (Zlib.proof.rfc1951.Format.deflate_bits bs)) as P. unfold bytes_ok in P.
    change compcert.lib.Integers.Byte.max_unsigned with 255 in P.
    pose proof (rtip_le_ok (Zlib.proof.crc32.Model.ref_crc32 0 (Zlib.proof.rfc1951.Format.data D bs)) 4) as L1.
    pose proof (rtip_le_ok (Zlength (Zlib.proof.rfc1951.Format.data D bs) mod 2 ^ 32) 4) as L2.
    unfold bytes_ok in L1, L2. change compcert.lib.Integers.Byte.max_unsigned with 255 in L1, L2.
    unfold Zlib.proof.rfc1951.Format.deflate_bytes.
    repeat split; auto; repeat constructor; cbn; lia.
  - rewrite !Zlength_app, Zlength_cons.
    repeat match goal with |- context [Zlength ?l] =>
      let H := fresh in pose proof (Zlength_nonneg l) as H; revert H; generalize (Zlength l) end.
    intros. lia.
Qed.

(* the bytes of a deflate run are bytes, at least one *)
Lemma pfx_dfinal wbits D O : dfinal_of wbits D O -> bytes_ok O /\ 1 <= Zlength O.
Proof.
  intros (_ & WB & bs & WF & _ & EO).
  assert (NE: bs <> []) by apply WF.
  pose proof (pfx_deflate_len bs NE) as LD.
  destruct (Zlib.proof.roundtrip.RTDIface.rwrap_of wbits) as [|[p|p|]|p].
  - subst O. split; [apply rtip_pack_ok | exact LD].
  - destruct EO as (_ & xfl & X & ->). apply pfx_gz; exact X.
  - destruct EO as (_ & xfl & X & ->). apply pfx_gz; exact X.
  - destruct EO as (_ & flg & (F1 & _) & ->).
    split.
    + unfold bytes_ok. rewrite !Forall_app. repeat split.
      * unfold Zlib.proof.roundtrip.RTFinal.zcmf.
        constructor; [change compcert.lib.Integers.Byte.max_unsigned with 255; lia|].
        constructor; [change compcert.lib.Integers.Byte.max_unsigned with 255; lia|constructor].
      * constructor.
      * apply rtip_pack_ok.
      * apply rtip_be_ok.
    + rewrite !Zlength_app, Zlength_cons.
      repeat match goal with |- context [Zlength ?l] =>
        let H := fresh in pose proof (Zlength_nonneg l) as H; revert H; generalize (Zlength l) end.
      intros. lia.
  - destruct EO as (_ & xfl & X & ->). apply pfx_gz; exact X.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The start and one call                                                                          *)

Lemma pfx_init (DC: dctx_stmt) (DI: decode_init7_stmt) wbits D O z sp :
  dfinal_of wbits D O -> Zlength O <= 2 ^ 64 - 1 -> init_ok (iwb wbits) z sp ->
  pfx_inv wbits D O O 0 [] z (init_live sp (iwb wbits)).
Proof.
  intros DF L64 (_ & _ & _ & _ & _ & T0 & _).
  destruct (pfx_dfinal _ _ _ DF) as [BY L1].
  destruct (DC wbits D O O DF ltac:(lia) (sublist_same 0 (Zlength O) O eq_refl eq_refl) BY)
    as (G & OK & SRC & SL & FU & HI & IW & ND & _).
  split; [reflexivity|]. split; [lia|]. split; [exists D; reflexivity|].
  exists G. split; [exact OK|]. split; [exact SRC|]. split; [exact SL|]. split; [exact FU|].
  rewrite T0, <- IW. apply DI; auto.
Qed.

Lemma pfx_call (DK: decode_call7_stmt) wbits D O pos out z L strmp flush ib inp o aout lim r z' st' ow :
  pfx_inv wbits D O O pos out z L -> call_pre O pos z L strmp flush ib inp o aout ->
  pos + Zlength inp <= lim -> lim < Zlength O ->
  inflate_rel flush strmp (offer_z z (in_ptr ib 0) (Zlength inp) (out_ptr o 0) aout) (Some L) ib inp (Some o)
    r z' st' ow ->
  r <> Z_MEM_ERROR -> zf_ok z' ->
  exists L', call_post ib inp o aout z' st' ow L' /\ r <> Z_STREAM_END /\
    pfx_inv wbits D O O (pos + (Zlength inp - zf_ai z')) (out ++ ow) z' L'.
Proof.
  intros (_ & POS & _ & G & OK & SRC & SL & FU & DV)
         (LV & ZF & SN & FL & IB & INOK & OUTOK & LI & LA & INP) LE LT REL NM ZF'.
  destruct REL as [(BAD & _) | (_ & L0 & o0 & res & winp & EL & EO & RUN & _ & ER & EOW & EZ & _ & EST)].
  { exfalso. destruct BAD as [B | [B | [B _]]].
    - unfold is_live in B. match type of B with context [if ?c then _ else _] => destruct c end; congruence.
    - discriminate.
    - contradiction. }
  injection EL as <-. injection EO as <-.
  set (z0 := offer_z z (in_ptr ib 0) (Zlength inp) (out_ptr o 0) aout) in *.
  assert (AO: 0 <= aout) by (destruct o; apply OUTOK).
  assert (ZF0: zf_ok z0).
  { destruct ZF as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6). unfold z0, offer_z, zf_ok; cbn.
    unfold umax in *. pose proof (Zlength_nonneg inp).
    split; [lia|]. split; [lia|]. exact (conj Z3 (conj Z4 (conj Z5 Z6))). }
  assert (P0: pos + Zlength inp <= Zlength (dc_src G)) by (rewrite SRC; lia).
  assert (INP': inp = sublist pos (pos + Zlength inp) (dc_src G)) by (rewrite SRC; exact INP).
  unfold umax in *.
  destruct (DK G pos out L z0 inp flush res OK DV LV ZF0 ltac:(cbn; lia) ltac:(lia) ltac:(lia) P0 INP' RUN)
    as [MEM | (RC & SNX & SOW & MAO & (rest & PRE) & DV' & _ & SE & _ & _)].
  { subst r. contradiction. }
  assert (VM: vmode (i_mode (m_s (m_init z0 L inp)))).
  { pose proof (pfx_vmode _ _ _ _ _ DV) as V. unfold m_init. cbv zeta.
    destruct (i_mode (l_s L) =? Zlib.proof.inflate.Model.TYPE); [compute; split; discriminate | exact V]. }
  destruct (run2_frame _ _ _ _ _ VM RUN) as (MI & _ & _).
  cbn [m_init m_inp] in MI.
  set (m := r_m res) in *.
  assert (AI: zf_ai z' = Zlength inp - m_snx m) by (subst z'; unfold z_after; cbv zeta; cbn [zf_ai]; fold m; rewrite MI; reflexivity).
  assert (AOz: zf_ao z' = aout - Zlength ow) by (subst z' ow; unfold z_after; cbv zeta; cbn [zf_ao]; fold m; rewrite MAO, SOW; reflexivity).
  exists (Live (l_sp L) winp (m_s m) (m_h m) (l_headp L) (l_hsh L) (l_xb L) (l_nb L) (l_cb L)).
  assert (EP: pos + (Zlength inp - zf_ai z') = pos + m_snx m) by lia.
  pose proof (Zlength_nonneg ow).
  destruct ZF' as (_ & ZA & _).
  split; [|split].
  - split; [exact EST|]. split; [lia|]. split; [lia|].
    split; [rewrite AI; subst z'; unfold z_after; cbv zeta; cbn [zf_ni]; fold m; f_equal; lia|].
    split; [rewrite AOz; subst z'; unfold z_after; cbv zeta; cbn [zf_no]; fold m; f_equal; rewrite SOW; subst ow; lia|].
    lia.
  - intros ES. rewrite ES in ER. destruct (SE (eq_sym ER)) as [_ E]. lia.
  - rewrite EP. split; [reflexivity|]. split; [lia|]. split.
    + exists rest. rewrite <- FU, PRE, EOW, app_assoc. reflexivity.
    + exists G. split; [exact OK|]. split; [exact SRC|]. split; [exact SL|]. split; [exact FU|].
      subst ow z'. unfold z_after; cbv zeta; cbn [zf_tout l_s]. exact DV'.
Qed.

Lemma pfx_theory : dctx_stmt -> decode_init7_stmt -> decode_call7_stmt -> pfx_stmt.
Proof.
  intros DC DI DK. exists pfx_inv. constructor.
  - exact pfx_inv_ok.
  - intros wbits D O DF. exact (proj2 (pfx_dfinal wbits D O DF)).
  - intros wbits D O z sp DF L64 _ IO. exact (pfx_init DC DI wbits D O z sp DF L64 IO).
  - intros. eapply pfx_call; eauto.
Qed.
