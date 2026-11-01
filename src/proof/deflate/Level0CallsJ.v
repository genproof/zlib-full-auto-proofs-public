(** * Level 0 over several deflate() calls: the invariant of interface v2 of Level0Calls.v

    [l0_J] is [Level0CallsInv.l0_inv] or the state after the call that wrote the last pending trailer bytes into
    exactly the rest of the output space: all the data consumed, all of room produced, the stream finished (the
    next call gets no output space and returns Z_BUF_ERROR).  [l0_facts_J] derives the facts of Level0Calls.v
    from the calls in the first two states of [l0_inv] ([l0_callA_stmt], [l0_callB_stmt]: the first call, and a
    later one after Z_NO_FLUSH calls) and from Level0CallsEnd.v for the others. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.Level0CallsEnd.
Import ListNotations.
Local Open Scope Z_scope.

Definition l0_J (wbits : Z) (data : list Z) (room pos : Z) (O : list Z) (s : dstate) (tin tout adler : Z) : Prop :=
  l0_inv wbits data room pos O s tin tout adler \/
  (l0_com wbits data room pos O s tin tout adler /\ pos = Zlength data /\ Zlength O = room /\
   d_status s = FINISH_STATE).

Definition l0_callA_stmt : Prop :=
  forall wbits data room pos O s tin tout adler msg k,
    l0_com wbits data room pos O s tin tout adler -> l0_stA wbits pos O s adler -> 1 <= k <= 65532 ->
    exists Pc, l0_call_post wbits data room pos O s tin tout adler msg k Pc.

Definition l0_callB_stmt : Prop :=
  forall wbits data room pos O s tin tout adler msg k,
    l0_com wbits data room pos O s tin tout adler -> l0_stB wbits data pos O s adler -> 1 <= k <= 65532 ->
    exists Pc, l0_call_post wbits data room pos O s tin tout adler msg k Pc.

(** The conclusion of [lf_call] from [l0_call_post]. *)
Lemma l0_post_J wbits data room pos O s tin tout adler msg k Pc :
  l0_call_post wbits data room pos O s tin tout adler msg k Pc ->
  let inb := l0_inb data pos k in
  let aout := l0_clip (room - Zlength O) in
  exists s' z' code,
    c_deflate s (zcall inb 0 (Zlength inb) tin aout tout adler msg) (l0_flush (Zlength data) pos k) =
      Some (s', z', code) /\
    z_in z' = inb /\
    0 <= z_avail_in z' <= Zlength inb /\ z_next_in z' = Zlength inb - z_avail_in z' /\
    z_total_in z' = tin + (Zlength inb - z_avail_in z') /\
    0 <= z_avail_out z' <= aout /\ Zlength (z_out z') = aout - z_avail_out z' /\
    z_total_out z' = tout + (aout - z_avail_out z') /\ bytes (z_out z') /\
    d_gzhead s' = None /\
    (code = Z_OK ->
       l0_J wbits data room (pos + (Zlength inb - z_avail_in z')) (O ++ z_out z') s'
         (z_total_in z') (z_total_out z') (z_adler z')) /\
    (code = Z_STREAM_END ->
       exists H T, O ++ z_out z' = H ++ stored_blocks data ++ T /\
         Zlength H = l0_hlen wbits /\ Zlength T = l0_tlen wbits /\
         z_total_out z' = l0_size wbits (Zlength data)).
Proof.
  unfold l0_call_post. cbv zeta.
  intros (s' & z' & code & E & Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & G & Hok & Hnok).
  exists s', z', code. do 10 (split; [assumption|]).
  split; [intros Hc; left; exact (proj1 (Hok Hc))|].
  intros Hc. destruct (Z.eq_dec code Z_OK) as [E0|N0]; [subst; discriminate|].
  destruct (Hnok N0) as (_ & H & T & E1 & L1 & L2 & L3). exists H, T. auto.
Qed.

Lemma l0_facts_J : l0_callA_stmt -> l0_callB_stmt -> l0_facts l0_J.
Proof.
  intros CA CB. constructor.
  - (* lf_init *)
    intros vok sok snull wbits mem strategy a1 a2 a3 a4 a5 z0 os z1 data room Hi Hb Hn Hr.
    destruct (l0_inv_init vok sok snull wbits mem strategy a1 a2 a3 a4 a5 z0 os z1 data room Hi Hb Hn Hr)
      as (s & Es & HJ).
    exists s. split; [exact Es|]. left. exact HJ.
  - (* lf_range *)
    intros wbits data room pos O s tin tout adler [HJ|(Hc & Hp & HO & _)].
    + destruct (l0_inv_range _ _ _ _ _ _ _ _ _ HJ) as (A1 & A2 & A3 & A4 & A5).
      split; [exact A1|]. split; [exact A2|]. split; [lia|]. split; [exact A4|exact A5].
    + destruct Hc as (Hb & Hn & Hr & -> & -> & HbO & Hgz & Ha).
      pose proof (Zlength_nonneg data). pose proof (Zlength_nonneg O).
      unfold l0_max_size, l0_max_u64 in *.
      repeat split; auto; lia.
  - (* lf_call *)
    intros wbits data room pos O s tin tout adler msg k HJ Hk.
    destruct HJ as [(Hc & [HA|[HB|HC]])|(Hc & Hp & HO & Hst)].
    + destruct (CA wbits data room pos O s tin tout adler msg k Hc HA Hk) as (Pc & P).
      exact (l0_post_J _ _ _ _ _ _ _ _ _ _ _ _ P).
    + destruct (CB wbits data room pos O s tin tout adler msg k Hc HB Hk) as (Pc & P).
      exact (l0_post_J _ _ _ _ _ _ _ _ _ _ _ _ P).
    + (* the trailer was cut: the next call writes the pending bytes *)
      pose proof Hc as (Hb & Hn & Hr & Hti & Hto & HbO & Hgz & Ha).
      destruct HC as (H & T1 & Hpd & -> & HO & HH & HT & _).
      cbv zeta.
      destruct (l0_call_pend wbits data room O s tin tout adler msg k H T1 ltac:(lia) Hr Hto HO HH HT Hpd)
        as (s' & z' & code & E & Hz & Hai & Had & G' & Hcd).
      pose proof Hz as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8).
      exists s', z', code. do 9 (split; [assumption|]). split; [exact G'|].
      destruct Hcd as [(-> & Ea & EO & Hst')|(-> & H' & T & E' & L1 & L2 & L3)].
      * split; [|discriminate]. intros _. right.
        rewrite (l0_inb_end data k ltac:(lia)) in *. rewrite Hai, Zlength_nil in *.
        split; [|split; [lia|split; [exact EO|exact Hst']]].
        unfold l0_com. rewrite Z4, Z7, Had, Hti, Hto, Zlength_app, Z6.
        repeat split; auto; try lia. apply Forall_app. split; auto.
      * split; [discriminate|]. intros _. exists H', T. auto.
    + (* all of room produced: no output space, Z_BUF_ERROR *)
      pose proof Hc as (_ & _ & _ & _ & _ & _ & Hgz & _).
      subst pos.
      destruct (l0_call_full data room O s tin tout adler msg k ltac:(lia) HO Hst Hgz)
        as (s' & z' & code & E & Hz & G' & ->).
      cbv zeta. exists s', z', Z_BUF_ERROR. split; [exact E|].
      destruct Hz as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8).
      do 8 (split; [assumption|]). split; [exact G'|].
      split; intros C; discriminate.
Qed.
