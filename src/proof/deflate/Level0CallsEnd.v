(** * Level 0 over several deflate() calls: the calls after all the data is consumed

    When the trailer of the Z_FINISH call did not fit ([Level0CallsTrail.l0x_trail_cut]), the harnesses' loop calls
    deflate() again with the rest of the output space and no input (Z_FINISH: no data is left):
    - [l0_call_pend]: it writes the pending trailer bytes and returns Z_STREAM_END with the whole output, or, when
      they fill the output space exactly (the output object then holds [room] bytes), Z_OK;
    - [l0_call_full]: after that Z_OK, the next call gets no output space and returns Z_BUF_ERROR. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.Level0CallsInv.
Import ListNotations.
Local Open Scope Z_scope.

(** With all [n] bytes consumed, the call gets no input and Z_FINISH. *)
Lemma l0_inb_end data k : 1 <= k -> l0_inb data (Zlength data) k = [].
Proof.
  intros Hk. unfold l0_inb, l0_piece. rewrite Z.sub_diag.
  replace (0 <=? 65535 * k) with true by (symmetry; apply Z.leb_le; lia).
  rewrite Z.add_0_r, sublist_nil. reflexivity.
Qed.

Lemma l0_flush_end n k : 1 <= k -> l0_flush n n k = Z_FINISH.
Proof.
  intros Hk. unfold l0_flush. rewrite Z.sub_diag.
  replace (0 <=? 65535 * k) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
Qed.

Lemma l0_call_pend wbits data room O s tin tout adler msg k H T1 :
  1 <= k -> l0_size wbits (Zlength data) <= room <= l0_max_u64 -> tout = Zlength O ->
  O = H ++ stored_blocks data ++ T1 -> Zlength H = l0_hlen wbits -> Zlength T1 + d_pending s = l0_tlen wbits ->
  l0_pend s ->
  let inb := l0_inb data (Zlength data) k in
  let aout := l0_clip (room - Zlength O) in
  exists s' z' code,
    c_deflate s (zcall inb 0 (Zlength inb) tin aout tout adler msg) (l0_flush (Zlength data) (Zlength data) k) =
      Some (s', z', code) /\
    l0_zres inb tin aout tout z' /\ z_avail_in z' = 0 /\ z_adler z' = adler /\ d_gzhead s' = None /\
    ((code = Z_OK /\ l0_clip (room - Zlength O) = d_pending s /\ Zlength (O ++ z_out z') = room /\
      d_status s' = FINISH_STATE) \/
     (code = Z_STREAM_END /\
      exists H T, O ++ z_out z' = H ++ stored_blocks data ++ T /\
        Zlength H = l0_hlen wbits /\ Zlength T = l0_tlen wbits /\
        z_total_out z' = l0_size wbits (Zlength data))).
Proof.
  intros Hk Hroom Hto HO HH HT Hp. cbv zeta.
  rewrite (l0_inb_end data k Hk), (l0_flush_end _ k Hk).
  pose proof (l0_tlen_range wbits) as Htl.
  pose proof Hp as (_ & _ & _ & _ & _ & _ & _ & Hp0 & _).
  assert (LO : Zlength O = Zlength H + (5 * l0_blocks (Zlength data) + Zlength data) + Zlength T1)
    by (rewrite HO, !Zlength_app, Zlength_stored_blocks; lia).
  unfold l0_size in Hroom.
  pose proof (Zlength_nonneg T1).
  set (aout := l0_clip (room - Zlength O)).
  assert (Ha : d_pending s <= aout <= 4294967295) by (unfold aout, l0_clip; lia).
  assert (Ha2 : aout <= room - Zlength O) by (unfold aout, l0_clip; lia).
  destruct (l0x_pend_call s [] tin aout tout adler msg Hp eq_refl Ha ltac:(rewrite Hto; apply Zlength_nonneg)
              ltac:(unfold l0_max_u64 in Hroom; lia))
    as (s' & z' & code & E & Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & G' & S' & Hc).
  exists s', z', code. split; [exact E|].
  split; [unfold l0_zres; rewrite Zlength_nil; repeat split; try assumption; lia|].
  split; [exact Z2|]. split; [exact Z9|]. split; [exact G'|].
  destruct Hc as [[Ea ->]|[Ea ->]].
  - left. split; [reflexivity|]. split; [exact Ea|]. split; [|exact S'].
    rewrite Zlength_app, Z6. unfold aout, l0_clip in Ea. lia.
  - right. split; [reflexivity|].
    exists H, (T1 ++ z_out z'). split; [rewrite HO, <- !app_assoc; reflexivity|].
    split; [exact HH|]. split; [rewrite Zlength_app, Z6; lia|].
    unfold l0_size. rewrite Z7, Hto, LO, HH. lia.
Qed.

Lemma l0_call_full (data : list Z) room (O : list Z) s tin tout adler msg k :
  1 <= k -> Zlength O = room -> d_status s = FINISH_STATE -> d_gzhead s = None ->
  let inb := l0_inb data (Zlength data) k in
  let aout := l0_clip (room - Zlength O) in
  exists s' z' code,
    c_deflate s (zcall inb 0 (Zlength inb) tin aout tout adler msg) (l0_flush (Zlength data) (Zlength data) k) =
      Some (s', z', code) /\
    l0_zres inb tin aout tout z' /\ d_gzhead s' = None /\ code = Z_BUF_ERROR.
Proof.
  intros Hk HO Hst Hg. cbv zeta.
  rewrite (l0_inb_end data k Hk), (l0_flush_end _ k Hk), HO, Z.sub_diag.
  change (l0_clip 0) with 0.
  rewrite (l0x_full_call s [] tin tout adler msg Hst eq_refl).
  do 3 eexists. split; [reflexivity|]. split; [|split; [exact Hg|reflexivity]].
  unfold l0_zres. cbn. repeat split; try lia. constructor.
Qed.

(** The case of the invariant with the trailer cut, when the call has room for more than the pending bytes:
    Z_STREAM_END with the whole output. *)
Lemma l0_callC wbits data room pos O s tin tout adler msg k :
  l0_com wbits data room pos O s tin tout adler -> l0_stC wbits data pos O s -> 1 <= k ->
  d_pending s < l0_clip (room - Zlength O) ->
  l0_call_post wbits data room pos O s tin tout adler msg k False.
Proof.
  intros (Hb & Hn & Hr & Hti & Hto & HbO & Hgz & Ha) (H & T1 & Hp & -> & HO & HH & HT & _) Hk Hlt.
  destruct (l0_call_pend wbits data room O s tin tout adler msg k H T1 Hk Hr Hto HO HH HT Hp)
    as (s' & z' & code & E & Hz & _ & _ & G' & Hc).
  unfold l0_call_post. cbv zeta.
  exists s', z', code. split; [exact E|].
  destruct Hz as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8).
  do 8 (split; [assumption|]). split; [exact G'|].
  destruct Hc as [(_ & Ea & _)|(-> & H' & T & E' & L1 & L2 & L3)]; [lia|].
  split; [discriminate|]. intros _. split; [reflexivity|]. exists H', T. auto.
Qed.
