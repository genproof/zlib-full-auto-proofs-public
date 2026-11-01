(* Law rfc_trailing_bytes: inflate() on the stream followed by any bytes (TBFacts.tail_facts), from the decode
   theory for calls of any size (Decode7) on the context of the stream (IDecode.dctx_stmt). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.harness.clip_streams.IFacts Zlib.proof.harness.clip_streams.IDecode.
Require Import Zlib.proof.harness.clip_streams.TBFacts Zlib.proof.harness.clip_streams.PfxTheory.
Require Import compcert.lib.Integers.
Require Import Zlib.proof.uncompr.URunFrame.
Import ListNotations.
Local Open Scope Z_scope.

(* The invariant of the call boundaries: a decode context of the stream O read from src (O followed by any
   bytes), between calls at pos with out written *)
Definition tb_inv : inv_t := fun wbits D O src pos out z L =>
  0 <= pos <= Zlength src /\ (exists rest, D = out ++ rest) /\
  exists G, dctx_ok7 G /\ dc_src G = src /\ slen G = Zlength O /\ full G = D /\
    dinv G pos out (l_s L) (zf_tout z).

Lemma tb_inv_ok : inv_ok tb_inv.
Proof.
  intros wbits D O src pos out z L (POS & PRE & G & _ & _ & _ & _ & _ & (_ & HD & _) & _ & _ & _).
  auto.
Qed.

(* the start: after inflateInit2, position 0, nothing written *)
Lemma tb_init (DC: dctx_stmt) (DI: decode_init7_stmt) wbits D O src z sp :
  dfinal_of wbits D O -> init_ok (iwb wbits) z sp ->
  Zlength O <= Zlength src <= Ptrofs.max_unsigned -> sublist 0 (Zlength O) src = O -> bytes_ok src ->
  tb_inv wbits D O src 0 [] z (init_live sp (iwb wbits)).
Proof.
  intros DF (_ & _ & _ & _ & _ & T0 & _) LS SUB BY.
  assert (LS': Zlength O <= Zlength src <= 2 ^ 64 - 1).
  { split; [lia|]. eapply Z.le_trans; [apply LS|]. cbv; discriminate. }
  destruct (DC wbits D O src DF LS' SUB BY) as (G & OK & SRC & SL & FU & HI & IW & ND & _).
  split; [pose proof (Zlength_nonneg O); lia|]. split; [exists D; reflexivity|].
  exists G. split; [exact OK|]. split; [exact SRC|]. split; [exact SL|]. split; [exact FU|].
  rewrite T0, <- IW. apply DI; auto.
Qed.

(* one call: one of the codes Z_OK, Z_BUF_ERROR, Z_STREAM_END; Z_STREAM_END exactly at the end of O, otherwise the
   invariant at the new position *)
Lemma tb_call (DK: decode_call7_stmt) wbits D O src pos out z L strmp flush ib inp o aout r z' st' ow :
  tb_inv wbits D O src pos out z L -> call_pre src pos z L strmp flush ib inp o aout ->
  pos + Zlength inp <= Zlength src ->
  inflate_rel flush strmp (offer_z z (in_ptr ib 0) (Zlength inp) (out_ptr o 0) aout) (Some L) ib inp (Some o)
    r z' st' ow ->
  r <> Z_MEM_ERROR -> zf_ok z' ->
  exists L', call_post ib inp o aout z' st' ow L' /\
    (r = Z_OK \/ r = Z_BUF_ERROR \/ r = Z_STREAM_END) /\
    (r = Z_STREAM_END -> pos + (Zlength inp - zf_ai z') = Zlength O) /\
    (r <> Z_STREAM_END -> tb_inv wbits D O src (pos + (Zlength inp - zf_ai z')) (out ++ ow) z' L').
Proof.
  intros (POS & _ & G & OK & SRC & SL & FU & DV)
         (LV & ZF & SN & FL & IB & INOK & OUTOK & LI & LA & INP) LE REL NM ZF'.
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
  split; [|split; [|split]].
  - split; [exact EST|]. split; [lia|]. split; [lia|].
    split; [rewrite AI; subst z'; unfold z_after; cbv zeta; cbn [zf_ni]; fold m; f_equal; lia|].
    split; [rewrite AOz; subst z'; unfold z_after; cbv zeta; cbn [zf_no]; fold m; f_equal; rewrite SOW; subst ow; lia|].
    lia.
  - rewrite ER. exact RC.
  - intros ES. rewrite ES in ER. destruct (SE (eq_sym ER)) as [_ E]. lia.
  - intros _. rewrite EP. split; [lia|]. split.
    + exists rest. rewrite <- FU, PRE, EOW, app_assoc. reflexivity.
    + exists G. split; [exact OK|]. split; [exact SRC|]. split; [exact SL|]. split; [exact FU|].
      subst ow z'. unfold z_after; cbv zeta; cbn [zf_tout l_s]. exact DV'.
Qed.

Lemma tb_theory : dctx_stmt -> decode_init7_stmt -> decode_call7_stmt -> tail_stmt.
Proof.
  intros DC DI DK. exists tb_inv. constructor.
  - exact tb_inv_ok.
  - intros wbits D O src z sp DF _ _ IO LS SUB BY. exact (tb_init DC DI wbits D O src z sp DF IO LS SUB BY).
  - intros. eapply tb_call; eauto.
Qed.
